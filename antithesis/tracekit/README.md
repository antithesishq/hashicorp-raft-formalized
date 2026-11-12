# tracekit

The parts of live trace checking that do not depend on the system under
test or on its model. `../raft-kit` is the one target so far.

The idea: each program reports its steps (disk writes, messages, role
changes) to one collector; the collector writes them as a single ordered
stream; TLC reads the stream as it grows and requires each event to be a
step of a TLA+ model. The run fails at the first event the model cannot
take.

| Path | What it is |
|---|---|
| `go/sink.go` | `Sink`, for the program. `Do` announces a durable write and then makes it; `Emit` reports a step. A report goes to the program's logger and, if `TRACEKIT_SOCKET` is set, to the collector, in order, before the program continues |
| `driver/trace.rs` | Collector and check runner, a Rust module the test driver includes. Writes the stream, runs the checker for the life of the run, turns its verdict into Antithesis assertions |
| `check/streamcheck.py` | Runs TLC on a stream that is still being written; prints `ACCEPTED`, `REJECTED k`, `VIOLATED k` or `ERROR` |
| `check/replay.py` | Feeds a recorded stream to the checker at a given rate, for testing |
| `stream/TraceKit.java` | The TLC operator `StreamEvent(i)`: blocks until event i exists |
| `tla/TraceKit.tla` | `StreamEvent` for TLA+, and the four conventions a trace spec follows |
| `tools/` | The TLC jars (not committed; see `../raft-kit/README.md`) |

The four conventions, described in `tla/TraceKit.tla`:

1. One cursor over the stream, one model state per event.
2. An event that implies a model action with no event of its own is a
   composite step. The spec never searches.
3. A write is announced before it is made. After a kill, only the last
   announced write is uncertain, and the spec takes it back if the
   recovered state says it did not happen.
4. Facts that can no longer matter may be forgotten, provided every guard
   of the model only asks whether a fact is present. A wrong choice can
   cause a false rejection, never a false acceptance.

Limit: TLC allows 65,535 states in one behaviour, so a stream is ended
before that (raft-kit ends a timeline at 55,000 events).
