# raft-kit

hashicorp/raft checked against a small-step TLA+ model while it runs, with
no tracing code inside raft.

- `spec/Raft.tla` is the model: one action per disk write, message, reply
  and role change, over a set of messages that only grows. It is written to
  be proved.
- The server reports raft's steps from wrappers around the stores, the
  transport and the observer that raft is given (`server/wrap.go`). Raft's
  source differs from upstream by one 10-line fix (`FIXES.md`).
- `spec/RaftBinding.tla` says which model action each reported step is. The
  driver runs TLC on the stream of reports for the whole run.
- `../tracekit` holds everything that does not depend on raft.

- `veil/RaftVeil.lean` is the model again, in Veil/Lean, with the proofs
  (`veil/README.md`).

`PLAN.md` has the design and decisions, `FIXES.md` the changes made to raft,
`RESULTS.md` what has been run. `../README.md` is the overview.

## The service under test

`server/` is a small service built on this checkout of raft: each node runs
raft with a BoltDB log and stable store and the TCP transport, and its state
machine keeps a running sum of the integers clients add. HTTP on `:8000`:
`POST /add?op=&value=`, `GET /sum` (linearizable), `GET /sum?mode=stale`,
`GET /status`. Each node logs one line per role change and per applied
command; a forwarder (`driver/log-forward`) sends those lines, and raft's
warnings for fault-only paths, to the driver.

`driver/` (Rust, [hegel](https://hegel.dev)) sends adds and reads, checks
every response and every node's applied history against the others,
collects the reported steps and runs the stream check on them.

## Run it

Needs Docker, Java, and two jars in `../tracekit/tools` (not committed):

```sh
mkdir -p ../tracekit/tools && cd ../tracekit/tools
curl -sSLO https://github.com/tlaplus/tlaplus/releases/download/v1.8.0/tla2tools.jar
curl -sSLO https://github.com/tlaplus/CommunityModules/releases/latest/download/CommunityModules-deps.jar
```


| Command | What it does |
|---|---|
| `scripts/local-run.sh 40` | Fault-free run, checked live and again from the file |
| `CHAOS=1 scripts/local-run.sh 60` | With kills, restarts and pauses |
| `CHAOS=kills scripts/local-run.sh 60` | A kill every second or two |
| `scripts/local-batch.sh 20 60 1` | 20 chaos runs of 60 s, one verdict each (`kills` instead of `1` for kill-heavy) |
| `scripts/validator-tests.sh` | `traces/*` accepted, 12 mutations rejected at the changed event |
| `scripts/sut-mutants.sh` | Seeded bugs in raft must be rejected during the run |
| `scripts/coverage.py runs/*` | Which events and branches the runs exercised |
| `scripts/mc.sh MCTiny5.cfg 1800` | Model checking under a time limit |
| `scripts/veil-count.sh 2` | The Veil model's state count, to compare with `scripts/mc.sh MCCount2.cfg 600` |
| `scripts/launch.sh 50` | An Antithesis run of 50 compute hours |
| `../tracekit/stream/build.sh` | Compile the stream operator for local use |

Without `TRACEKIT_SOCKET` the server runs as any raft application would, and
`RAFT_LOG_LEVEL=trace` shows every reported step in its log.

## What is reported, and what it is in the model

| Report | From | Model action |
|---|---|---|
| `boot` (recovered term, vote, log end) | server start | `Restart`, after taking back the last write if it did not happen |
| `stable.set CurrentTerm` | stable store wrapper | `StartElection` (a candidate, next term) or `AdoptTerm` |
| `stable.set LastVoteTerm`, `LastVoteCand` | stable store wrapper | `SetVoteTerm`, `SetVoteFor` |
| `log.store` | log store wrapper | `LeaderAppend` or `StoreEntries` |
| `log.delete` | log store wrapper | `DeleteSuffix` |
| `role` | observer | `BecomeCandidate`, `BecomeLeader`, `BecomeFollower` |
| `rpc.send` append | transport wrapper | `LeaderCommit` if the commit index moved, then `SendAppend` |
| `rpc.send` heartbeat | transport wrapper | `SendAppend` with nothing in it |
| `rpc.send` vote | transport wrapper | Nothing; the request is a fact since the election started |
| `rpc.recv` | transport wrapper | Nothing; the binding keeps the request until its reply |
| `rpc.reply` | transport wrapper | `GrantVote`; or `Ack`, then `FollowerCommit` if the commit index moved |
| `rpc.return`, `rpc.fail` | transport wrapper | Nothing; a returned reply must be one the model saw sent |

Writes are announced before they are made. Replies are reported before they
leave and before the next request is handed to raft. A request is reported
when it is sent, which can be after its sender has left the term it built
it in; the model's send does not look at the sender's state now.

## Assertions about raft

Raft's source has none. The driver makes them from what the nodes forward:

| Assertion | From |
|---|---|
| Six fault-only paths are reached (election timeout, lease loss, previous-term mismatch, two vote refusals, stale-term step down) | raft's own warnings in the forwarded log (`driver/src/logs.rs`) |
| A node's current term never decreases; at most one candidate per term; a follower never truncates committed or applied entries | `stable.set` and `log.delete` events (`driver/src/steps.rs`) |
| One leader per term, terms across restarts, applied histories agree | the server's `raft-state` and `raft-apply` lines (`driver/src/logs.rs`, `model.rs`) |

## Checking a run by search query

The same check can run after the fact, as one Antithesis event-set query
over every timeline of a run, with no TLC involved:

| File | Role |
|---|---|
| `search/reducer.js` | `RaftBinding.tla` and the guards of the `Raft.tla` actions it uses, written by hand as one function `(state, event) -> [violations, state]` |
| `search/init.json` | The initial state |
| `search/check.js STREAM` | Runs the reducer locally under Node |
| `search/query.sh` | Wraps the reducer in a `fold` over the driver's `trace-kit` lines |
| `scripts/search-check.sh RUN_ID` | Runs the query on a run and prints what it found |
| `scripts/search-tests.sh` | Tests the reducer against TLC: same verdict at the same event on every fixture and mutation |

The run must be launched with `UNFILTERED=1 scripts/launch.sh HOURS`, which
keeps the printed stream in the run's events.

TLC and the TLA+ files are the authority. The reducer is a second
implementation, kept honest by `scripts/search-tests.sh`; a step it flags is
confirmed by replaying that timeline's stream through TLC. A flagged step is
a search result, not a failed property: it does not appear in the run's
report.

## Differences from the code, on purpose

- A follower commits only over the part of its log the leader has confirmed.
  The code uses the end of its log. A run where the two differ is reported
  as `CommitBeyondConfirmed`.

## Where the code was changed to match

- A request carries entries only from the log its sender had while it led
  the request's term. Upstream, a deposed leader's replicator can send what
  a later leader wrote (FIXES.md, R1).

## Scope

Three fixed voters; no snapshots, PreVote, leadership transfer or membership
change; heartbeats on the main loop (the fast path, hashicorp/raft#695, is
deferred).
