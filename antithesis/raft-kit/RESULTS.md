# raft-kit results

What has been run on the current version, as of 2026-11-12. Everything after the
Antithesis section is local.

## Antithesis (turbo tier, 50 compute hours each, about 22 minutes)

| Run | Outcome |
|---|---|
| Clean, commit `7953078`: `ff1ba7b8a482e6c8716b34822263a1dd-67-0` | 684 timelines ended with their whole stream matched and the checker keeping up. No rejection, restart mismatch, safety violation or commit beyond confirmed. One driver assertion failed, 12 times in 3.3k: "nodes apply the same command and history at every log index" (below) |
| Seeded bug, R1 undone (`deposed-replicator-sends`): `11595620819720dcab345694a4fbafe5-67-0` | 298 rejections, "the nodes' reported steps are a behaviour of the model". No safety property failed |

In the clean run every assertion that local runs cannot exercise was
reached and held: 529 log truncations, none of committed or applied
entries; previous-term mismatch 203 times; a vote refused for an older last
term 650 times.

**The seeded bug is caught, but not shown unsafe.** The sampled rejection is
at an `rpc.send`: a node sends a request of term 2 carrying commit index 52,
which it read from its state long after it stopped leading term 2. The model
rejects it because the term's leader log is shorter than that. In the 298
timelines the safety properties still held up to the rejection, so undoing
R1 causes trace rejection and no observed safety violation.

**The failed driver assertion is a raft behaviour at shutdown, not a
conformance failure.** A node that is told to stop while it is replaying
its log to the state machine can hand the state machine a later batch
after dropping an earlier one: `processLogs` sends each batch with a
`select` between the state machine's channel and the shutdown channel, and
when both are ready Go picks either, batch by batch (`raft.go`,
`applyBatch`). In the sampled timeline raft2 applied indexes 4, 5, 7, 8 and
then 14, skipping 10 to 12, 260 ms after it began to stop. The process then
exits, so an in-memory state machine loses nothing; one that persists what
it applies would be left with a hole. It is upstream behaviour, unrelated
to raft-kit's change, and is not modelled (the model has no state machine).
See FIXES.md, known behaviours.

## Local conformance

| Check | Result |
|---|---|
| 10 chaos runs of 75 s (`scripts/local-batch.sh 10 75 1`) and 6 kill-heavy runs (`... 6 75 kills`) | 16 of 16 accepted live and again from the file: 86,198 events, 268 faults |
| Driver assertions in those runs | None failed. Term, vote-term and one-candidate checks held in all 16 |
| Validator tests (`scripts/validator-tests.sh`) | 3 recorded streams accepted; 12 mutations rejected, each at the changed event or the first event that depends on it |
| Reducer against TLC (`scripts/search-tests.sh`) | Same verdict at the same event on all 3 streams and 12 mutations |

What the 16 runs exercised (`scripts/coverage.py`, selected rows):

| Branch | Count |
|---|---|
| Restarts where the last announced write had happened / was taken back | 261 / 4 |
| Leaders elected | 97 |
| Later term adopted | 243 |
| Requests with entries sent / with several entries | 11,581 / 865 |
| Leader commit first shown by a request | 5,558 |
| Suffix deleted on a conflict | 0 |

Not exercised locally, because local chaos has no network partitions: log
truncation, and with it the driver's check that a follower never truncates
committed entries; and two of the six fault-only paths (previous-term
mismatch, candidate's last term behind). The clean Antithesis run above
reached all of them.

No run has shown a follower committing past what its leader had confirmed
(`CommitBeyondConfirmed`).

## Seeded bugs in raft (`scripts/sut-mutants.sh`)

| Bug | Result |
|---|---|
| Follower commits one entry past the leader's commit index | Rejected in run 1, event 59 |
| Leader commits what one server has stored | Rejected in run 1, event 39 |
| Node votes again in a term it has voted in | Rejected in the second chaos run, event 5,191, at the second vote's first write |
| Follower skips the previous-entry check | Not triggered in 10 chaos runs |
| A deposed leader's replicator sends (FIXES.md R1 undone) | Not triggered in 10 chaos runs |

The last two need a particular fault pattern before they do anything. For
the last one, the node must step down and have its log changed by a new
leader while one of its replicators is asleep; a late send of a request
that is still that term's leader log is correct and is accepted. Local chaos
did not produce that; the Antithesis run above did, 298 times.

## Model checking

3 servers, 1 value, batches of 1 entry, 2 workers. Limits are those of
PLAN.md. Invariants checked: the six safety properties, `TermMonotonic`,
and the three proof candidates `LeaderLogIsLed`, `RequestsFromLed`,
`ConfirmedWithinLog`.

| Configuration | Bounds | Outcome |
|---|---|---|
| `MCTiny5.cfg`: no restarts | terms <= 2, log <= 2, facts <= 5 | Completed: 520,652 states, no violation |
| `MCFullTiny5.cfg`: every action | same | Completed: 934,154 states, no violation |
| `MCFull.cfg`, `-simulate -depth 120` | terms <= 3, log <= 3, facts <= 7 | 10 min: 366,359 behaviours, 49.6 M states, no violation |

The bounded instances send, from each position, a full batch with the
highest commit index the model allows. What completes is small: two terms,
a log of two entries, five facts.

The unrestricted `Spec` without symmetry (`MCCount2/3/4.cfg`: facts <= 2,
3, 4) completes at 73,512 / 277,792 / 1,453,984 states with no violation.
The Veil model checker finds the same counts at the first two bounds
(`veil/README.md`).

Seeded errors in the model, all caught:

| Mutant | Outcome |
|---|---|
| `MCMutQuorum.cfg`: a quorum of one | `ElectionSafety` violated, under 10 s |
| `MCMutPrev.cfg`: no previous-entry check | `ConfirmedWithinLog` violated, under 10 s, breadth first and by simulation |
| `MCMutFreshness.cfg`: no log comparison for votes | `LeaderCompleteness` violated, by simulation, within 10 min |

## Raft against upstream

10 added lines in `replication.go` (FIXES.md, R1). Nothing else.

## Compute

About 480 of 1,000 Antithesis compute hours are committed for all of the
raft work, counting the two runs above at their 50-hour limits.

## Proofs

ElectionSafety and OneVotePerTerm are proved inductive in Lean for the Veil
translation of `Raft.tla`, with five supporting invariants: 119 stored
proofs, re-checked by `lake build` in about 3 minutes with no `sorry`
(`veil/README.md`). The other properties are model-checked only.
