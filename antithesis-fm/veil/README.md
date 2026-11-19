# Lean proofs of HashicorpRaft

`RaftVeil.lean` is `../spec/HashicorpRaft.tla` translated into [Veil](https://veil.dev), a
Lean 4 framework for transition systems: the same variables, actions (with the same
parameters) and properties. Each TLA+ definition is quoted in a comment above its
translation. The file proves that 50 invariants hold initially and are preserved by each of
the 24 actions: 1,250 goals, every one with a stored proof checked by Lean's kernel.

## What is proved

The constants `PreVote` and `Snapshots` are left free, so every result holds for both values,
and for any finite number of servers and any number of terms and entries.

Every state invariant of `HashicorpRaft.tla` (18):

| Invariant | Statement |
|---|---|
| `ElectionSafety` | At most one server is elected in a term |
| `OneVotePerTerm` | A node never votes for two candidates in one term |
| `LogMatching` | Two logs with an entry of the same term at an index agree up to that index |
| `CommitSafety` | Two committed prefixes never disagree |
| `StateMachineSafety` | No two state machines are handed different entries at one index |
| `LeaderCompleteness` | A leader's log has every prefix committed under an earlier term |
| `CommittedEntriesPreserved` | A server keeps every prefix it committed |
| `LeaderLogIsLed`, `RequestsFromLed`, `ConfirmedWithinLog` | Bookkeeping: a leader's log is its term's leader log; requests are segments of it; `confirmed` is within the log |
| `PreVoteRequestsBounded`, `PreGrantsAnswer`, `TimeoutNowFromLeader`, `TransferIsCandidate` | Pre-vote and transfer facts are well formed |
| `SnapshotWithinLog`, `BaseWithinSnapshot`, `SnapshotCommitted`, `SnapshotApplied` | A snapshot is a committed prefix of its node's log; compaction deletes only what it covers; a state machine is never behind its snapshot |

Not stated in Lean: the step properties (`TermMonotonic`, `NoAppliesSkipped`,
`AppliedMonotonic`, `ElectionsLicensed`), and two state properties that follow from the
above (`SnapshotAgreesApplied`, `AcceptsAfterSnapshot`).

Supporting invariants (32), grouped:

| Group | Invariants say |
|---|---|
| Elections | A vote record is not ahead of its term; every vote is at or before its voter's record; a granted reply states an existing vote; every leader was voted for by a quorum |
| Leaders | A node in the leader role was elected in its term; nobody was elected in a term it has not reached; while the leader of t is in t, `ledLog[t]` is its log; a term has a leader log iff it had a leader; append requests come from the leader of their term |
| Logs | Logs start with the bootstrap entry; every entry is, with all before it, in the leader log of its term (`FromLed`); terms are positive, non-decreasing along a leader log, and not above the owner's term |
| Vote requests | A request is of a reached term and describes an existing log; one request per node and term; every vote answers a request; until its term has a leader, a candidate's log is the one its request describes; a leader log starts with the log its leader asked with |
| Acknowledgements | Acks go to the leader of their term; a node keeps what it acknowledged unless a later leader log up to its term lacks it (`AckedHeld`); a node that acknowledged and then voted, voted for a candidate that has the entries, unless a leader in between lacks them (`AckVote`); every leader has a quorum of such early voters (`EarlyQuorum`) |
| Commits | `confirmed` is a prefix of the confirming leader's log; every committed prefix is part of one a leader committed with a quorum of acknowledgements, in a term not after its own (`CommitRoot`); commit indexes are lengths of committed prefixes |
| Applies | Every entry handed to a state machine is in a committed prefix |

How the safety properties follow:

- `LogMatching` from `FromLed`: both logs agree with the leader log of that term.
- `leader_complete` (the core lemma, by induction on the later term): entries a quorum
  acknowledged to the leader of their term are in every later leader log. The quorum of
  acknowledgements meets the later leader's quorum of early votes in a node that
  acknowledged and then voted (`vote_cover`).
- `CommitSafety` from `CommitRoot` and `leader_complete` (`roots_cmp`);
  `LeaderCompleteness` likewise (`root_in_later`, `cand_complete`).
- `CommittedEntriesPreserved`: only `DeleteSuffix` shortens a log, at the first entry that
  conflicts with the term's leader log, which has every committed prefix (`delete_held`).
- `StateMachineSafety`: a node applies within its commit index, which covers a committed
  prefix it holds; committed prefixes agree.

`RequestsFromLed`, `CommitSafety` and `StateMachineSafety` rely on the model's rule that a
request of term t carries a commit index committed in term t or earlier (`CommittedIn`).

## Proof structure and checking

The file is ordered: model; invariants; lemmas (`-- Lemmas.`), ordinary Lean lemmas about
lists, sets and quorums; proofs (`-- Proofs.`), one section per action, one
`prove_veil_invariant_goal ACTION INVARIANT` per goal.

- Each proof first picks from the conjunction of the 50 invariants the ones it uses
  (`have hX := hinv.2.….1`) and drops the rest, so automation sees few hypotheses and adding
  an invariant does not slow existing proofs.
- Most goals are closed by `grind only [...]` with the named facts; the rest are written
  out using the lemmas. Initial-state goals use Veil's `tr` form.
- No SMT solver is involved: Veil's automatic `#check_invariants` cannot translate this
  model's set-typed state, so every proof is a Lean proof term. The trusted base is Lean's
  kernel and Veil's generation of the goals from the actions.

```sh
scripts/veil-check.sh        # splits the proofs by action into parallel Lean processes;
                             # every file must be ok (no error, no sorry)
cd veil && lake build        # the same check in one process
```

`veil-check.sh` runs min(cores, available memory / 2.5 GB) processes. On a 32-core machine
it takes about 7 minutes. `ACTIONS="Apply Restart"` checks only those actions.

## Same model as the TLA+

Equal state counts on shared bounded instances (no symmetry, unrestricted `Spec`). This is
evidence, not proof, that the translation is faithful.

| Instance | TLC | Veil | Distinct states |
|---|---|---|---|
| `PreVote` off, messages ≤ 2 | `scripts/mc.sh MCCount2.cfg 600` | `PREVOTE=0 scripts/veil-count.sh 2` | 6,488 |
| `PreVote` off, messages ≤ 3 | `MCCount3.cfg` | `PREVOTE=0 scripts/veil-count.sh 3` | 30,880 |
| `PreVote` off, messages ≤ 4 | `MCCount4.cfg` | `PREVOTE=0 scripts/veil-count.sh 4` | 202,840 |
| `PreVote` on, messages ≤ 4 | `MCCountPV4.cfg` | `scripts/veil-count.sh 4` | 17,704 |
| `PreVote` on, messages ≤ 5 | `MCCountPV5.cfg` | `scripts/veil-count.sh 5` | 113,968 |
| Snapshots, messages ≤ 4 | `MCCountSnap4.cfg` | `SNAPSHOTS=1 PREVOTE=0 scripts/veil-count.sh 4` | 227,032 |

All with three servers, one value, terms ≤ 2, logs ≤ 2, one entry per request.
`veil-count.sh` checks every invariant Veil's model checker can evaluate; the 15 between the
`PROOF-ONLY` marks quantify over all indexes and terms and are proved but not model-checked.

## Setup

Install [elan](https://github.com/leanprover/elan). `lean-toolchain` pins Lean 4.35.0;
`lakefile.lean` pins Veil to commit `1287c31d`; `lake-manifest.json` pins Veil's
dependencies. The first `lake build` or `scripts/veil-check.sh` fetches and compiles them into
`.lake/` (several minutes).
