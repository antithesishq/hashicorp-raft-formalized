# hashicorp/raft: a proved model, checked against the code

> [!IMPORTANT]
> The contents of this directory and all sub-directories are almost entirely AI-generated.
> While the researchers who produced it have manually reviewed claims for integrity, this
> artifact is only intended to serve as a demonstration of a research project, not an
> authoritative or maintained work; owners and users of the upstream hashicorp/raft project
> should not rely on it as is.

This directory holds a formal model of [hashicorp/raft](https://github.com/hashicorp/raft),
machine-checked proofs that the model is safe, and a test harness that checks the running
implementation against the model step by step under fault injection
([Antithesis](https://antithesis.com)). Everything here is an addition to the upstream
checkout this branch starts from (`a5b4692`). Raft's own source is not modified: the fixes
described below are patch files, applied when the test image is built.

## Claims

1. **A model of the implementation.** [`spec/HashicorpRaft.tla`](spec/HashicorpRaft.tla) is a TLA+ model of
   hashicorp/raft at the level of its interfaces: one action per durable write, message, reply
   and role change. It covers elections, log replication, commitment, application to the state
   machine, crashes and restarts, pre-votes, leadership transfer and snapshots, over a network
   that can delay, drop, duplicate and reorder messages.
2. **The model is safe, proved twice.** For any finite set of servers and any number of terms
   and log entries, with pre-votes and snapshots on or off:
   - **TLAPS** proves `Spec => []P` on [`HashicorpRaft.tla`](spec/HashicorpRaft.tla) itself for election safety, log
     matching, commit safety, state machine safety and leader completeness ([`spec/proof/`](spec/proof/)).
   - **Lean 4 / Veil** proves every state invariant of the model, those five included, on a
     line-by-line translation of it ([`veil/`](veil/)).
3. **The implementation follows the model.** In a test cluster, each node reports every
   durable write, message and role change from wrappers around the interfaces raft is given
   (stores, transport, state machine, observer). TLC checks, while the cluster runs, that the
   sequence of reported steps is a behaviour of the model and that the model's safety
   properties hold in every state reached. Raft with the five patches below passed this check
   in Antithesis runs totalling about 2,010 compute hours, on three and five nodes with
   crashes, restarts, pauses and network partitions: no step was rejected and no safety
   property failed.
4. **Five faults in upstream raft, each fixed by a small patch.** Three break Raft safety
   properties (R1, R2, R5), one breaks the state machine's contract (R3), one makes followers
   diverge from snapshots (R4). See [`patches/README.md`](patches/README.md).

The proofs are about the model; that the code follows the model is established by testing,
on the behaviours the tests reach. [`spec/README.md`](spec/README.md) lists every assumption and limitation.

## Layout

| Path | Contents |
|---|---|
| [`spec/`](spec/) | The TLA+ model `HashicorpRaft.tla`, the trace binding `RaftBinding.tla` (reported step → model actions), bounded instances for TLC. [`spec/README.md`](spec/README.md): what is modelled, the properties, assumptions and limitations |
| [`spec/proof/`](spec/proof/) | TLAPS proofs: 12 modules, 3,032 obligations. [`spec/proof/README.md`](spec/proof/README.md) |
| [`veil/`](veil/) | The model in Lean 4 / [Veil](https://veil.dev), with stored proofs: 50 invariants × (24 actions + initial state) = 1,250 goals. [`veil/README.md`](veil/README.md) |
| [`patches/`](patches/) | The five fixes to raft, one patch file each, and a reproducer for R5. [`patches/README.md`](patches/README.md) |
| [`server/`](server/) | The service under test: raft (BoltDB stores, TCP transport) with a running-sum state machine; `wrap.go` reports each step |
| [`driver/`](driver/) | The test driver (Rust): client workload, client-visible checks, collection of reports, the live trace check, Antithesis assertions |
| [`tracekit/`](tracekit/) | The raft-independent part of trace checking: report sink (Go), collector (Rust), streaming TLC checker (Python, Java), conventions ([`tracekit/tla/TraceKit.tla`](tracekit/tla/TraceKit.tla)) |
| [`traces/`](traces/) | Recorded report streams, used as test fixtures |
| [`scripts/`](scripts/) | Entry points: setup, model checking, Lean checks, local runs, trace-check tests, Antithesis launch |
| [`config/`](config/), [`local/`](local/) | Docker Compose files for Antithesis and for local runs |

## Verify independently

All commands run from this directory (`antithesis-fm/`).

### 1. Install

| Tool | Used for | Install |
|---|---|---|
| Java 17+, Python 3 | TLC and trace checking | system packages |
| Docker | local cluster runs; compiling the stream operator if `javac` is absent | system packages |
| elan (Lean 4) | Lean proofs. The toolchain (`v4.35.0`) is pinned in [`veil/lean-toolchain`](veil/lean-toolchain); Veil is pinned in [`veil/lakefile.lean`](veil/lakefile.lean) | `curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \| sh -s -- -y --default-toolchain none` |
| tlapm 1.6.0-pre | TLAPS proofs (bundles Isabelle, Zenon, Z3) | `curl -fsSL https://github.com/tlaplus/tlapm/releases/download/1.6.0-pre/tlapm-1.6.0-pre-x86_64-linux-gnu.tar.gz \| tar xz -C "$HOME" && export PATH=$HOME/tlapm/bin:$PATH` |

`1.6.0-pre` is a rolling pre-release. The proofs were checked with tlapm commit
[`bf665f4`](https://github.com/tlaplus/tlapm/commit/bf665f4); if the downloaded binary does not
run (it needs glibc 2.42 or later) or gives different results, build that commit
([DEVELOPING.md](https://github.com/tlaplus/tlapm/blob/bf665f4/DEVELOPING.md)) and set `TLAPM` to it.

Then:

```sh
scripts/setup.sh     # fetches tla2tools.jar v1.8.0 and CommunityModules, compiles the stream operator,
                     # lists missing tools
```

### 2. TLAPS proofs (about 15 minutes; needs up to 24 GB of memory)

```sh
(cd spec/proof && sha256sum -c spec.sha256)   # the proofs are about these exact spec files
spec/proof/final.sh                            # every module from a clean cache, --strict;
                                               # TLAPM=/path/to/tlapm to use another binary
```

Expected: one line per module, `All N obligations proved`, for all 12 modules, then
`DONE ... (exit 0)`. The theorems are in [`spec/proof/RaftSafety.tla`](spec/proof/RaftSafety.tla).

### 3. Lean proofs (about 10 minutes on 24+ cores, including the first Veil build)

```sh
scripts/veil-check.sh
```

Expected: last line `24 of 24 files ok` (Lean accepts all 1,250 theorems, no error, no `sorry`).
`cd veil && lake build` checks the same file in one process (slower).

That the Lean model is the TLA+ model is checked by counting states on shared bounded
instances. Both commands must print the same number (table in [`veil/README.md`](veil/README.md)):

```sh
scripts/mc.sh MCCount2.cfg 600            # TLC: `completed, 6488 states, no violation`
PREVOTE=0 scripts/veil-count.sh 2         # Veil: `No violation (explored 6488 states)`
```

### 4. Model checking with TLC

```sh
scripts/mc.sh MCFullTiny5.cfg 3600    # every action, restarts included: 413620 states, no violation
scripts/mc.sh MCSnap.cfg 3600         # snapshots: 1672432 states, no violation
```

Other instances are listed in [`spec/README.md`](spec/README.md). Output is one line (`completed, N states, no
violation`) and a log under `runs/mc/`.

### 5. Trace validation

```sh
scripts/validator-tests.sh                # no Docker: the recorded streams in traces/ are accepted,
                                          # and 29 mutations of them are rejected at the right event
scripts/local-run.sh 40                   # Docker: 3-node cluster of patched raft, checked live
CHAOS=1 scripts/local-run.sh 60           # with kills, restarts, pauses and network cuts
NODES=5 CHAOS=1 scripts/local-run.sh 60   # five nodes
```

A local run prints `kit live: matched N of N events` and `kit file: ACCEPTED`. Variants:
`PREVOTE=0`, `SNAPSHOTS=0`, `DRIVER_TRANSFER_RATE=0.5`, `CHAOS=kills|cuts`, and
`RAFT_PATCHES="R2 R3 R4 R5"` to build with a patch left out.

### 6. Antithesis

`scripts/launch.sh 50` builds the images and submits a 50-hour run. It needs an Antithesis
tenant and the `snouty` CLI. The run's properties are the live trace check, the model's safety
properties, and the driver's assertions ([`spec/README.md`](spec/README.md)).
