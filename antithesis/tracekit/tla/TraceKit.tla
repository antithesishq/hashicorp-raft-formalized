---- MODULE TraceKit ----
\* Common parts of a trace spec: a spec that says a recorded run is a
\* behaviour of a model. Nothing here depends on the model.
\*
\* The run is one stream of events, in the order a single collector received
\* them. Each program in the run reports a write before making it and a
\* message when it sends or answers it, and waits until the collector has
\* the report (tracekit.Sink). A message can be reported later than the
\* state it was built from was read; the model must allow a message to be
\* sent at any time after that state existed, as a network delay would.
\*
\* A trace spec built on this module follows four conventions.
\*
\* 1. One cursor. A variable holds the index of the next event; each step
\*    takes StreamEvent of it and requires the model action the event stands
\*    for. TLC, breadth first with one worker, then advances in step with
\*    whoever writes the stream, and stops when no model state can take the
\*    next event: the run has left the model there.
\*
\* 2. Composite steps instead of search. When an event implies a model
\*    action that has no event of its own (a leader's commit index moving),
\*    the event's step is written as that action followed by the event's
\*    own. The spec never guesses.
\*
\* 3. Announced writes. A program announces a durable write before making
\*    it, and the spec applies it at once. If the program is killed, the last
\*    announced write may not have happened. The spec keeps what is needed
\*    to take that one write back (LastWrite below) and does so if the state
\*    the program reports after restarting says so.
\*
\* 4. Forgetting facts. A model whose messages are a set that only grows is
\*    easy to reason about and expensive to replay. If every guard of the
\*    model is positive in that set (it only asks whether some fact is
\*    there), dropping facts can only disable steps, never enable one. A
\*    trace spec may therefore drop facts it can show are no longer needed;
\*    a wrong choice can cause a false rejection, never a false acceptance.
EXTENDS Naturals, Sequences

\* StreamEvent(i) is the i-th event of a stream that is still being written.
\* This definition is a placeholder: TLC replaces it with the Java method of
\* the same name (../stream/TraceKit.java), which blocks until the event
\* exists and returns [e |-> "End"] once the stream has ended.
StreamEvent(i) == CHOOSE ev : TRUE

Has(ev, field) == field \in DOMAIN ev

\* What a node's durable state was before its last announced write, as a
\* record the trace spec chooses; <<>> when there is nothing to take back.
NoWrite == <<>>
LastWrite(pre) == <<pre>>
====
