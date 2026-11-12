# Raft.tla in Veil

`RaftVeil.lean` is `../spec/Raft.tla` translated one to one into
[Veil](https://veil.dev) (a Lean 4 framework): the same variables, the same
actions with the same parameters, the same properties. It exists so that the
model's invariants can be proved in Lean while `Raft.tla` stays the model
that runs are checked against.

## Keeping the two in step

1. A change to `Raft.tla` is made here too, definition by definition (each
   TLA+ definition is quoted above its translation).
2. Both model checkers are run on the same bounded instances and must find
   the same number of distinct states:

   | Bounds | TLC | Veil |
   |---|---|---|
   | terms <= 2, log <= 2, batch 1, facts <= 2 | `scripts/mc.sh MCCount2.cfg 600`: 73,512 | `scripts/veil-count.sh 2`: 73,512 |
   | the same with facts <= 3 | `MCCount3.cfg`: 277,792 | `scripts/veil-count.sh 3`: 277,792 |

   These use the unrestricted `Spec` with no symmetry reduction, because
   Veil has none. Equal counts are evidence, not a proof, that the models
   agree.
3. `lake build` in this directory re-checks every proof. A proof that the
   change broke fails by name (action and invariant).

## What is proved

| Property | Status |
|---|---|
| ElectionSafety, OneVotePerTerm | Proved inductive, together with five supporting invariants: 119 goals (16 actions and the initial state, times 7 invariants) |
| LogMatching, StateMachineSafety, LeaderCompleteness, CommittedEntriesPreserved, LeaderLogIsLed, RequestsFromLed, ConfirmedWithinLog | Model-checked only |
| TermMonotonic (a property of steps) | Not stated here |

The proofs are stored in the file: each names the facts it uses (`grind
only [...]`, `simp only [...]`, or explicit steps), so checking replays them
without searching a lemma library. `lake build` takes about 3 minutes on 4
cores, most of it Veil preparing each goal.

The five supporting invariants: a node's vote record is not ahead of its
term; every vote is at or before its voter's vote record; a vote in the
record's term is the recorded one; a granted reply states a vote that
exists; every leader was voted for by a quorum in its term.

Caveats:
- The proofs trust Lean's kernel and Veil's generation of the goals from
  the actions. No SMT solver is involved.
- Veil's automatic check (`#check_invariants`) does not work on this model:
  its SMT translation fails on set-typed state. Proofs are written with
  `prove_veil_invariant_goal ACTION INVARIANT using wp by ...`.
- For the initial state, the `wp` form of the goal does not finish
  preparing; those seven goals use the `tr` form.
- `server` has no decidable equality in the proof goals, so the set lemmas
  at the top of the file are stated without it.

## Setup

Lean is installed with elan; the toolchain is pinned in `lean-toolchain`.
`lakefile.lean` takes Veil from a local checkout at `/home/exedev/veil`
(commit `1287c31d`); the comment there shows how to fetch it instead. The
first `lake build` compiles Veil's dependencies and takes several minutes.
