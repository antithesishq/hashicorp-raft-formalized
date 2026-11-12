# Changes to raft made for raft-kit

Each entry: what changed, why, and the evidence. The policy (PLAN.md, D6) is
to fix the implementation where it departs from provable Raft, in small
separate changes, rather than model the departure.

Raft's source carries no assertions and no Antithesis dependency: `raft.go`
and `go.mod` are upstream's. Assertions about raft are made by the driver,
from what the nodes forward:

| Assertion | Made from |
|---|---|
| Six fault-only paths are reached (election timeout, lease loss, previous-term mismatch, two vote refusals, stale-term step down) | raft's own warning for that path, in the node's forwarded log (`driver/src/logs.rs`, `RARE_PATHS`) |
| A node's current term never decreases; at most one candidate per term | the node's `stable.set` events (`driver/src/steps.rs`) |
| A follower never truncates committed or applied entries | the node's `log.delete` event, to which the log store wrapper adds the commit and applied indexes (`server/wrap.go`) |

The diff of raft against upstream is R1 below: 10 lines in `replication.go`.

## R1. A deposed leader's replicator does not send (`replication.go`)

After building a request, `replicateTo` returns without sending unless the
node is still the leader in the replicator's term.

- Behaviour before: a replicator is told to stop asynchronously. One asleep
  in failure backoff (up to about 10 s) wakes and sends once more. The
  request carries the term the node led, with entries and commit index read
  from the log as it is now, which a later leader may have rewritten. A
  receiver still in the old term accepts them.
- Why the check comes after the read, with no lock: if the node is leader
  of term t after the read, it was leader of t during it (a node leads a
  term at most once), and only the leader writes its log in its term. So
  what was read is the leader's log of term t. A check before the read
  leaves a window between the two.
- Evidence: with an earlier checker that had hooks inside raft, 8 such
  sends in 20 local chaos runs, and in one Antithesis run the replicator
  of a deposed leader reached the snapshot fallback 3 times because its
  log had been truncated under it.
- Safety: not shown unsafe. Bounded model checking of a model that allows
  these sends but reads the log in one step found no violation; a read
  torn by a truncation has not been modelled. The fix is kept because the
  proof wants every request to carry a segment of its term's leader log
  (`RequestsFromLed` in `Raft.tla`).
- How the request is reported: by the transport wrapper, when it is sent.
  That can be after the node has left the term, which is the same as a
  correct request delayed by the network, so the model's `SendAppend` reads
  the term's leader log (`ledLog`) and not the sender's state now.
- Undone (`scripts/sut-mutants.sh deposed-replicator-sends`), the trace
  check rejects a request whose content is not its term's leader log: 298
  rejections in an Antithesis run, none in ten local chaos runs
  (RESULTS.md). No safety property failed in those timelines.

## Reads by goroutines other than the main loop

| Goroutine | Reads | How the model allows a late report |
|---|---|---|
| `replicate` / `replicateTo` | log entries, commit index | `SendAppend` reads the term's leader log and the committed prefixes, not the node |
| `replicate` | last log index (in memory) | A stale value only shortens the batch |
| `heartbeat` | nothing; the request is fixed when the leadership starts | `SendAppend` with nothing in it |
| `electSelf` vote goroutines | nothing; the request is built by the main loop | The request is a fact from the start of the election |
| FSM goroutine | committed entries handed to it | Not reported |

## Known behaviours not changed

| Behaviour | Status |
|---|---|
| Heartbeat fast path races the main loop (hashicorp/raft#695) | Deferred. The workload keeps heartbeats on the main loop |
| A follower bounds its commit index by its whole log | Not changed. The model has the provable rule; no run has shown the code going past it |
| A vote is two writes; a kill between them leaves a term with no candidate, or with the previous candidate | Modelled as two steps |
| A stopping node can skip a batch when handing committed entries to the state machine, then deliver a later one (`processLogs`, `applyBatch`) | Not changed, not modelled. Fails the driver's applied-history check; seen 12 times in one Antithesis run (RESULTS.md) |
| A stopping node finishes the step it had chosen, such as starting an election | Needs nothing here: the model has no stopping role |
