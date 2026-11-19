# Patches to hashicorp/raft

Raft's source in this checkout is upstream's. The test image applies these patches, in
order, to a copy of it (`RAFT_PATCHES`, default `R1 R2 R3 R4`; `../scripts/build-env.sh`).
The model `../spec/HashicorpRaft.tla` is of raft with all four. Raft's own tests pass with
them; R4 includes a change to one expectation of `TestRaft_UserRestore` (below).

| | Patch | Fault in upstream raft | What it breaks | Upstream |
|---|---|---|---|---|
| R1 | `R1-deposed-replicator.patch` (`replication.go`) | A replicator that outlives its node's leadership still sends a request in the old term, built from the node's current log and commit index | Commit safety, leader completeness: with five nodes, a follower can commit entries that a leader of an intermediate term never had, and later delete them | Not reported |
| R2 | `R2-vote-write-order.patch` (`raft.go`, `persistVote`) | A vote is written as two stable-store writes, term first, then candidate. A crash between them leaves the new term with the previous candidate, and a request from that candidate is then granted without comparing logs | Leader completeness, state machine safety: a candidate missing a committed entry can be elected | [hashicorp/raft#746](https://github.com/hashicorp/raft/issues/746) |
| R3 | `R3-stopping-node-applies.patch` (`raft.go`, `processLogs`) | Each batch for the state machine is sent with a `select` against the shutdown channel; while stopping, one batch can be dropped and a later one delivered | The state machine is handed index k+n without k (not a Raft safety property; breaks the contract that every committed entry is applied in order) | Not reported |
| R4 | `R4-snapshot-counts-as-log.patch` (`raft.go`, `api.go`, `replication.go`, `raft_test.go`) | A follower looks up entries a snapshot covers in its log store, keeps a log that does not continue an installed snapshot, and installs snapshots that are not newer | Liveness and state machine regression: a follower that never catches up, a state machine moved back, `panic: log not found` | [hashicorp/raft#697](https://github.com/hashicorp/raft/issues/697) |

`RAFT_PATCHES="R2 R3 R4" ../scripts/local-run.sh 60` builds with a patch left out, checked
against the same model.

## R1. A deposed leader's replicator does not send

After building a request, `replicateTo` returns without sending unless the node is still
leader in the replicator's term. The check comes after the reads: a node leads a term at most
once and only the leader writes its log in its term, so if the node still leads after the
read, what it read is the term's leader log and a commit index reached in that term.

Without it, a replicator asleep in failure backoff wakes after its node has lost leadership
and sends once more, reading the log and commit index as they are now. A receiver still in
the old term accepts the request and can commit entries that a leader of a later term never
had; after it moves to that term it is made to delete them. This needs five servers: one must
commit in a later term without two others that are in intermediate terms.

In the model a request is a segment of its term's leader log (`ledLog`) with a commit index
covered by a prefix committed in that term or earlier (`CommittedIn`); without this bound the
model violates commit safety with five servers.

## R2. A vote's candidate is written before its term

`persistVote` writes `LastVoteCand` before `LastVoteTerm` instead of after. A node that
crashes between the two writes is left with an older term and the new candidate. The record
is consulted only for a request of the record's term, so the half-written record is never
read as a vote; the vote exists from the second write, and the reply follows it.

Upstream order: a crash leaves the new term with the previous candidate. If that candidate
asks for a vote in the new term, `requestVote` takes its "duplicate request" path and grants
it without comparing logs, and a candidate missing a committed entry can win. A leadership
transfer opens the same window without pre-votes. Pre-votes do not close it: a pre-vote is
not withdrawn when the voter's log grows.

Assumes the stable store keeps the order of completed writes across a crash (BoltDB commits
each write as a transaction). In the model, `SetVoteFor` changes only the record and
`SetVoteTerm` creates the vote.

## R3. A stopping node hands the state machine no further batch

Before each batch, `processLogs` checks the shutdown channel and drops the batch if the node
is stopping (its futures get `ErrRaftShutdown`, as before). The channel is closed once and
stays closed, so from the first dropped batch every later one is dropped: the state machine
receives a prefix of the batches, with no gap.

Upstream, the `select` between the FSM channel and the shutdown channel picks either when
both are ready, independently for each batch, so a stopping node can skip one batch and
deliver a later one.

In the trace check, each entry handed to the state machine is reported (`fsm.apply`), and
the binding accepts it only if every command since the last applied one has been applied.

## R4. A snapshot counts as log

One rule, applied in seven places: what a node's snapshot covers is part of its log, whether
or not the log store still has it, and a snapshot never moves a node back.

| Part | Where | With the patch |
|---|---|---|
| a | `appendEntries`, previous-entry check | At the snapshot's index the term is the snapshot's; below it the entry is committed and matches |
| b | `appendEntries`, entry loop | Entries the snapshot covers are skipped |
| c | `installSnapshot`, the log | The log is kept only if it has the snapshot's last entry with the snapshot's term; otherwise all of it is deleted. The snapshot is made durable first; a node stopped in between deletes the log at start (`NewRaft`) |
| d | `installSnapshot`, the request | A snapshot at or below the node's own snapshot or its applied index is acknowledged and not installed |
| e | `sendLatestSnapshot` | Sent only while the node leads its term, as for append requests (R1) |
| f | `takeSnapshot` | A snapshot the node finishes is recorded as newest only if it is newer than the one recorded |
| g | `appendEntries`, both lookups | If a lookup fails, the snapshot index is read again (a concurrent snapshot may have compacted the log) |

Upstream, three ways to fail: (1) a follower with uncommitted entries of an old term installs
a snapshot, keeps its log, then rejects every request continuing from the snapshot; the
leader resends the snapshot forever (hashicorp/raft#697). (2) A follower whose log runs past
the snapshot compacts it, and the next request's previous entry (the snapshot's last) is no
longer found; the same loop follows. (3) A delayed or resent snapshot is installed after the
follower applied past it, moving its state machine back. Runs of unpatched raft show all
three, and nodes exiting with `panic: log not found`.

In the model a snapshot install is an append request starting at index 1 whose entries are
all committed; the follower stores them with `DeleteSuffix`/`StoreEntries` and then makes
them its snapshot, so installing changes no log. Four invariants are added and proved
(`SnapshotWithinLog`, `BaseWithinSnapshot`, `SnapshotCommitted`, `SnapshotApplied`).

The patch changes one expectation of `TestRaft_UserRestore`: a follower that installs a
snapshot of a later index now discards its log store.

## Other changes in how raft is used

Configuration choices of the harness, not patches:

- **Heartbeat fast path off.** Raft lets the transport handle heartbeats on its own goroutine
  (`processHeartbeat`), concurrently with the main loop. That path has known safety and
  liveness problems: [#695](https://github.com/hashicorp/raft/issues/695) (log divergence),
  [#742](https://github.com/hashicorp/raft/issues/742) (a node votes twice in a term),
  [#666](https://github.com/hashicorp/raft/issues/666) (a stale leader keeps its lease),
  [#717](https://github.com/hashicorp/raft/issues/717) (panic on shutdown). The harness's
  transport routes heartbeats through the main loop, and the model has no fast path.
- **Pre-votes and leadership transfer** need no patch. A `TimeoutNow` request carries no term
  and is obeyed in any role, so a node that no longer leads can send one and a leader that
  receives one deposes itself; this costs an election, not safety, and the model allows it.

Known differences that are not changed:

| Behaviour | Status |
|---|---|
| A follower bounds its commit index by its whole log | The model uses the provable rule (`confirmed`); the trace check reports a run where the code goes past it |
| A stopping node finishes the step it had started (e.g. an election) | Nothing needed: the model has no stopping state |
