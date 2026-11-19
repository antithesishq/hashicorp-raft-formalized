# TLAPS proofs of HashicorpRaft

Machine-checked proofs, with the [TLA+ Proof System](https://proofs.tlapl.us), that the
safety properties of `../HashicorpRaft.tla` hold in every reachable state. The theorems are
about the TLA+ module itself, not about a translation. `spec.sha256` records the spec files
the proofs were checked against.

## Theorems

In `RaftSafety.tla`:

| Theorem | Statement |
|---|---|
| `InvInvariant` | `Spec => []Inv` |
| `ElectionSafetyThm` | `Spec => []ElectionSafety` |
| `LogMatchingThm` | `Spec => []LogMatching` |
| `CommitSafetyThm` | `Spec => []CommitSafety` |
| `StateMachineSafetyThm` | `Spec => []StateMachineSafety` |
| `LeaderCompletenessThm` | `Spec => []LeaderCompleteness` |

`Inv` also has `OneVotePerTerm` as a conjunct, so it holds in every reachable state too.

**Assumptions.** Only the spec's own: `ASSUME ServerFinite == IsFiniteSet(Server)` (quorums
are counted with `Cardinality`), `Nil \notin Server`, and `PreVote`, `Snapshots \in BOOLEAN`.
The theorems have no further hypotheses; they hold for any finite set of servers, any
number of terms and entries, and both values of `PreVote` and `Snapshots`. No proof step
is omitted (`--strict` fails on any unproved obligation).

## The inductive invariant

`Inv` is defined in `RaftDefs.tla` (definitions only, so TLC can evaluate it). It uses
`ledLog[t]`, the log of the leader of term t, as the reference every log is compared to.

| Conjunct | Says |
|---|---|
| `TypeOK` | Types of all variables |
| `TermInv`, `VotesInv` | A node's vote term is at most its current term; every vote is at or before its voter's record |
| `OneVotePerTerm`, `ElectionSafety` | One candidate per voter and term; one leader per term |
| `VoteReqInv` | A vote request is of a term its sender has reached; until the term has a leader, it describes the sender's current log |
| `GrantInv` | A granted reply states a vote that exists |
| `LeadersInv` | Every leader has a leader log; while it is in its term its log is that leader log; a node in the leader role was elected in its term |
| `LogsInv` | Every entry of every log and leader log sits, with all entries before it, in the leader log of its term (`LMc`); terms along a log do not decrease and do not exceed the owner's term |
| `AppendInv` | An append request is from the leader of its term, carries a segment of that term's leader log, and a commit index covered by a commit in that term or earlier |
| `AckInv` | An acknowledgement is for entries the leader log has, from a node that reached the term |
| `ConfirmedInv` | What a leader confirmed of a node's log is a prefix of that leader's log |
| `AckerInv` | A node that acknowledged entry c of term t still has it, unless a later leader log up to its term lacks it |
| `VoterInv` | A node that acknowledged entry c of term t and later voted, voted for a candidate whose log is not behind that entry, unless a leader in between lacks it |
| `QuorumInv` | Every leader was elected by a quorum of voters for which `AckerInv`/`VoterInv`'s conclusion holds (`Good`) |
| `CommitsInv` | Every committed prefix is part of a prefix that a quorum acknowledged to the leader of a term at or before the commit's term |
| `CommitIndexInv` | A node's commit index covers a committed prefix that its log holds |
| `AppliedInv` | Every entry handed to a state machine is, at its index, in a committed prefix |

Leader completeness is the lemma `LeaderHas` (`RaftStatic.tla`): by induction on terms, a
prefix that a quorum acknowledged to the leader of term t is in every later leader log. The
quorum of acknowledgements and a later leader's quorum of votes share a node, which had
acknowledged the entry before voting (`QuorumInv`, `VoterInv`).

## Modules

Each module EXTENDS the previous one.

| Module | Contents |
|---|---|
| `RaftDefs` | `Inv` and helper operators. No proofs |
| `RaftBase` | Quorum intersection (needs `IsFiniteSet(Server)`), sequence lemmas, arithmetic helper `QArith` |
| `RaftFrame` | `InitInv`; frame lemmas: each conjunct is kept when its variables do not change |
| `RaftMono` | Frame lemmas for growing message sets and terms |
| `RaftSimple` | `<Action>Inv` for actions that do not change logs (role changes, pre-votes, `TimeoutNow`, snapshots, restart, apply) |
| `RaftCommit` | `SetVoteTerm`, `SendAppend`, `LeaderCommit`, `FollowerCommit` |
| `RaftStatic` | `LeaderHas` (induction on terms), `CommitLed` |
| `RaftExt` | Lemmas about extending logs and leader logs |
| `RaftLog`, `RaftLog2` | `Ack`; `DeleteSuffix`, `StoreEntries` |
| `RaftAppend`, `RaftElect` | `LeaderAppend`; `BecomeLeader` |
| `RaftSafety` | `NextInv` (case split over `Next`), `InvInvariant`, the theorems |

12 modules, 3,032 obligations.

`MCInv.tla` with `Inv_*.cfg` has TLC check the conjuncts of `Inv` on bounded instances.

## Checking

```sh
spec/proof/final.sh            # all modules, in order, --cleanfp --strict; one line per module in final.log
spec/proof/chk.sh RaftLog      # one module, with failures listed (development)
```

`TLAPM` selects the binary (default `tlapm` on `PATH`), `THREADS` the prover threads
(default 2), `MEM_KB` the virtual-memory cap (default 24 GB).

**Prover setup.** tlapm 1.6.0-pre (checked with build `bf665f4`), with its default backends:
Zenon, Isabelle and Z3 through the default SMT encoding. Notes:

- Z3 has no memory limit of its own, and one hard obligation can use all of a machine's
  memory. The scripts cap every prover process with `ulimit -v`; 24 GB is about the least
  Isabelle starts with.
- Products with a constant are rewritten as sums (`c * 2 = c + c`, lemma `QArith`) before
  the SMT backend reasons about them linearly.
- Goals with quantifiers are proved after extracting the needed conjuncts of `Inv` and
  hiding action definitions, which keeps obligations small enough for the backends.
