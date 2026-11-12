# hashicorp/raft checked against a TLA+ model in Antithesis

This directory tests the core safety of hashicorp/raft. A 3-node cluster
runs under [Antithesis](https://antithesis.com) fault injection, and every
step each node takes is checked, while it runs, against a TLA+ model of
Raft. The model's safety properties are being proved in Lean.

Everything here is an addition to upstream raft. Raft's own source differs
from upstream by one 10-line fix in `replication.go`.

## Objectives

1. **Check the real code against a model, step by step.** A run passes only
   if the sequence of disk writes, messages and role changes that the nodes
   made is a behaviour of the model. A step the model does not allow fails
   the run at that step.
2. **Prove the model safe.** The model is written to be proved, and is kept
   small for that reason.
3. **Leave raft alone.** No tracing, test or model code inside raft. Steps
   are reported by wrappers around the stores and transport that any raft
   application hands to raft.
4. **Keep the general parts general.** What does not depend on raft is a
   separate library, `tracekit`.

## How it fits together

```text
 raft node x3                driver                      TLC
 ------------                ------                      ---
 raft (upstream + 1 fix)
   |  stores, transport
 wrappers  -- reports -->  collector -- one stream -->  RaftBinding.tla
 (server/wrap.go)          client workload              (event -> model action)
                           client-level checks          Raft.tla (the model)
                           verdict -> Antithesis assertions

 Raft.tla  <-- same variables, actions, state counts -->  RaftVeil.lean (proofs)
```

- Each node announces a durable write before making it and reports each
  message when it is sent or answered. The driver collects the reports
  into one ordered stream.
- TLC reads the stream as it is written. `RaftBinding.tla` says which model
  action each event is; there is no search over interleavings.
- The driver also runs a client workload (adds and reads on a running-sum
  state machine) and checks what clients see.
- `RaftVeil.lean` is the same model in [Veil](https://veil.dev), a Lean 4
  framework. The two model checkers must count the same states, so a proof
  about one is a proof about the model the runs are checked against.

## Layout

| Path | What it is |
|---|---|
| `raft-kit/` | The raft target. Start with `raft-kit/README.md` |
| `raft-kit/spec/` | `Raft.tla` (the model), `RaftBinding.tla` (events to actions), bounded instances for model checking |
| `raft-kit/server/` | The service under test: raft, a running-sum state machine, and the reporting wrappers |
| `raft-kit/driver/` | Workload, client checks, per-node checks, log forwarder |
| `raft-kit/veil/` | The model in Veil/Lean with stored proofs |
| `raft-kit/search/` | The same trace check as an Antithesis event-set query |
| `raft-kit/scripts/`, `config/`, `local/`, `traces/` | Local runs, tests, model checking, the Antithesis launch; recorded streams used as test fixtures |
| `tracekit/` | The library with no raft knowledge: report sink, collector, stream checker. See `tracekit/README.md` |

Documents in `raft-kit/`: `README.md` (how to run, what each event means),
`PLAN.md` (design decisions), `FIXES.md` (the change to raft and known raft
behaviours), `RESULTS.md` (what has been run and what it showed).

## What is checked

| Check | By |
|---|---|
| The nodes' reported steps are a behaviour of `Raft.tla` | TLC, on the live stream |
| The model's safety properties hold in every state the run reaches: election safety, one vote per term, log matching, state machine safety, leader completeness, committed entries preserved | TLC, on the live stream |
| A node's term and vote term never decrease; at most one candidate per term per node; a follower never truncates committed or applied entries | Driver, from the reported steps |
| At most one leader per term; nodes apply the same command at every index; acknowledged writes survive; linearizable reads see every acknowledged write | Driver, from the nodes' logs and client responses |
| Fault-only paths are actually reached (election timeout, lease loss, log mismatch, vote refusals, stale-term step down) | Driver, from raft's own warnings |
| The model's properties hold in all states of small bounded instances | TLC model checking |
| Election safety and one vote per term hold in all states, unbounded | Lean proofs (`raft-kit/veil`) |

## What is left out

- **Raft features:** snapshots, PreVote, leadership transfer and membership
  change are turned off or unused. The cluster is three fixed voters.
- **The heartbeat fast path** is off: heartbeats go through raft's main
  loop. With it on, raft has a known race that breaks safety
  (hashicorp/raft#695, below).
- **Liveness.** Only safety is modelled and checked.
- **The state machine** is not in the model. Applied histories are checked
  by the driver only.
- **Proofs** of log matching, state machine safety, leader completeness and
  committed entries preserved are not done; those are model-checked only.
- **One deliberate difference from the code:** in the model a follower
  commits only entries its leader has confirmed; the code uses the end of
  its log. A run where the two differ would be reported. None has.

## Findings so far

- **A deposed leader's replicator keeps sending** (fixed here; `FIXES.md`,
  R1). The trace check rejects the unfixed code; no safety violation has
  been shown.
- **A stopping node can skip a batch of committed entries** when handing
  them to the state machine, then deliver a later batch (upstream
  behaviour, not changed; `FIXES.md`, `RESULTS.md`).
- **hashicorp/raft#695** (open upstream): the heartbeat fast path races the
  main loop, and a deposed leader can stamp a client write with a term it
  does not lead, which diverges logs. An earlier workload on the local
  branch `antithesis-raft-sum` reproduces it. The fast path is off here
  until that race is fixed.

## Quick start

```sh
cd antithesis/raft-kit
scripts/local-run.sh 40          # local 3-node run, checked live (needs Docker, Java, the TLC jars)
scripts/validator-tests.sh       # recorded streams accepted, 12 mutations of them rejected
scripts/mc.sh MCTiny5.cfg 1800   # model checking, with a time limit
(cd veil && lake build)          # re-check the Lean proofs, about 3 minutes
scripts/launch.sh 50             # an Antithesis run of 50 compute hours
```

Setup details are in `raft-kit/README.md` and `raft-kit/veil/README.md`.
