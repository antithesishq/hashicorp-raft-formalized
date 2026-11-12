# raft-kit: design and decisions

Goal: a hashicorp/raft deployment whose runs are checked against a TLA+
model, live, in Antithesis, with

- no tracing code inside raft,
- a model small enough to prove,
- the parts that do not depend on raft factored into a library
  (`../tracekit`) that other targets can use.

## Decisions

| # | Decision |
|---|---|
| D1 | Events are taken at raft's interfaces (stable store, log store, transport, observer) by wrappers in the server binary. Run without a trace socket, the server just logs them at trace level. |
| D2 | Nothing inside raft reports anything. A message is reported when it is sent, which can be later than the read of the state it was built from; the model allows that (D3, D5). |
| D3 | The model is small-step: one action per disk write, message sent, reply, role change. Messages are facts in a set that only grows. A request can be acted on at any later time, any number of times. |
| D4 | The model has the provable follower commit rule: commit only up to the highest index confirmed against the leader of the request's term. The code uses the end of its log. Conformance tests whether the code ever commits past the model's rule; if it does, that is a finding, and the code may be fixed. |
| D5 | A request carries entries only from the log its sender had while it led the request's term (`ledLog` in the model). When it is sent does not matter. Raft is fixed to do the same (FIXES.md, R1). |
| D6 | Policy: where the implementation departs from provable Raft, fix the implementation rather than model the departure. Each fix is small, separate, and recorded in FIXES.md with its evidence. |
| D7 | Rule for any SUT: announce a durable write before making it. After a kill, at most the last announced write is uncertain, and the trace spec takes it back if the recovered state says it did not happen. |
| D8 | Assertions about raft are made by the driver from what the nodes forward: raft's own log lines and the wrapper events. Raft's source has no assertions and no Antithesis dependency. |
| D9 | Proofs are done in Veil (Lean 4) on a one-to-one translation of `Raft.tla`: same variables, actions and parameters, with equal state counts from both model checkers on shared bounded instances. `Raft.tla` stays the model that runs are checked against. Proofs are stored as explicit scripts so that checking is replay. |

## Layout

```
antithesis/tracekit/            generic, no raft knowledge
  go/        Sink: ordered, synchronous reports; announce-then-write
  driver/    collector, stream check runner, verdict assertions (Rust module)
  tla/       TraceKit.tla: the stream operator and four conventions
  stream/    TraceKit.java: the stream operator for TLC
  check/     streamcheck.py, replay.py
antithesis/raft-kit/            the raft target
  spec/      Raft.tla (proof model), MCRaft.* (bounded instances),
             RaftBinding.tla (event -> action)
  server/    a running-sum service on raft, with wrappers around what raft is given
  driver/    workload, client checks, per-node checks on forwarded events
  search/    the trace check as an Antithesis event-set query
  veil/      Raft.tla translated one to one into Veil (Lean 4), with proofs
  scripts/   local runs, batches, validator tests, mutants, model checking, launch
  FIXES.md   changes to raft: what, why, evidence
  RESULTS.md what has been run
```

## How the pieces work

1. **Wrappers emit events already in the binding's vocabulary.** The driver
   does no mapping. The mapping from events to model actions is all in
   `RaftBinding.tla`.
2. **One cursor, one model state per event, no search.** An event whose step
   implies a model action with no event of its own is written as a
   composite: a leader's commit before a send; acknowledge then follower
   commit at a reply.
3. **`LeaderCommit` does not depend on the node's role or term now.** The
   code moves a leader's commit index in a later main-loop step; by the time
   it shows (in a request, or in the commit index reported with a reply) the
   node may have stepped down. The action asks only that the node was
   elected in the entry's term, still holds the entry, and a quorum
   acknowledged it.
4. **`SendAppend` does not depend on the sender's state now either.** A
   request is built by a replicator goroutine and reported by the transport
   wrapper when it is sent. The action reads `ledLog[t]`, the log of term
   t's leader while it led, and bounds the commit index by the committed
   prefixes. A heartbeat is the same action with nothing in it.
5. **Reply guards are facts that stay true** (a vote that was recorded,
   entries that are in the log), because a reply is reported just after its
   handler, not inside it. The transport wrapper hands raft one request at
   a time and reports the reply before the next goes in.
6. **A request is reported when raft is handed it** (`rpc.recv`), and the
   binding keeps it until its reply is reported. The reply comes from the
   wrapper's goroutine, which Antithesis can hold back past a term change.
7. **The follower's commit index** is read from raft's public getter when
   the reply is reported.
8. **The wrappers wait for the `*Raft`**, which `NewRaft` returns only after
   starting raft's goroutines, and re-read the role before every write.
9. **Facts are forgotten during a run** (`GC` in the binding). This is sound
   because every guard of `Raft.tla` is positive in `msgs`; a wrong choice
   can only cause a false rejection. A request is forgotten when every copy
   sent has been replied to or its receiver has left its term. A term's
   leader log is forgotten when every node has left the term, and a request
   of such a term is accepted unchecked: nobody can accept it.
10. **A node's last announced write is taken back at its restart** if the
    recovered state says it did not happen. The pre-image is kept per node
    in the binding; `Raft.tla` has no notion of it.
11. **The TLA+ part of the library is small**: the stream operator and the
    four conventions, documented in `TraceKit.tla`. The cursor, the
    take-back and the forgetting are written out in the binding. A second
    target will show what can move.
12. **The timeline limit is 55,000 events**: TLC's limit of 65,535 states
    in one behaviour, less room for the forgetting steps.

## Time limits for TLC

No TLC run is started without a limit, and every result says whether the run
completed or was cut off.

| Kind of run | Limit |
|---|---|
| Exhaustive configuration expected to finish | 30 min |
| Breadth-first run that is time-boxed on purpose | 40 min |
| Random simulation (always with an explicit `-depth`) | 10 min |
| Seeded-error configuration | 10 min |
| Streaming check | None: it runs for the life of the timeline, which ends at 55,000 events |

Rules:
- All model-checking commands go through `scripts/mc.sh CONFIG LIMIT`. It
  writes TLC's output to a log file and prints one line: "completed, N
  states" or "stopped at the limit, depth D, N states".
- Output is never piped through a filter that loses it when the run is
  killed.
- `RESULTS.md` records for each run whether it completed or was cut off.
- A run that is expected to finish and does not is reported as such, and the
  bounds are reduced (for example by capping the number of facts,
  `MaxMsgs`); the limit is not quietly raised.

## Status and open items

See RESULTS.md for what has been run on the current version. Open:

- The exhaustive model check completes only at small bounds.
- Two seeded raft bugs need fault patterns local chaos rarely produces.
- Requests that are lost are kept by the binding until their receiver's
  term ends.
- Local chaos has no network partitions, so log truncation is exercised
  only in Antithesis.

## Later

- The remaining proofs in `veil/`: LogMatching first, then
  StateMachineSafety, LeaderCompleteness and CommittedEntriesPreserved.
  `LeaderLogIsLed`, `RequestsFromLed` and `ConfirmedWithinLog` in
  `Raft.tla` are the first supporting invariants to try.
- The stock heartbeat fast path: run with it on (expected: rejections at
  the hashicorp/raft#695 race, each at the offending write), fix the race
  in raft, rerun until clean. Until then the workload keeps heartbeats on
  the main loop.
- Features, one at a time, each as wrappers plus model actions: snapshots,
  PreVote, leadership transfer, membership change.
- A second SUT on `tracekit`, to test that the split is right.

## Budget

1,000 Antithesis compute hours in total for the raft work; about 480
committed as of 2026-11-12. One conformance run is 50 hours.
