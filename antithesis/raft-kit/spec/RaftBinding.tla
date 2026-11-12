---- MODULE RaftBinding ----
\* The trace spec for raft-kit: what each reported step of hashicorp/raft is
\* in the model Raft. Conventions are those of TraceKit.
\*
\* Server names are the container names and Nil is "", so reported values
\* compare directly with model values.
EXTENDS Raft, TraceKit, TLC, Integers

VARIABLES
    i,        \* index of the next event
    ready,    \* nodes that have finished bootstrap
    undo,     \* per node: how to take back its last announced write
    done,     \* per node: for each request sent to it, copies not yet replied to
    pending,  \* per node: the append request it has been handed and not replied to
    \* Safety, checked step by step (Raft's `commits` history is too large to
    \* carry along a long run): the longest committed prefix seen, its
    \* length per leader term and per server, and the names of properties
    \* that a step broke.
    chain, termLen, srvLen, viol

tvars == <<vars, i, ready, undo, done, pending, chain, termLen, srvLen, viol>>

GCBatch == 32        \* forget facts only this many at a time

----
\* Facts as the model writes them, from reported fields.

VoteFact(src, r) ==
    [type |-> "vote", src |-> src, term |-> r.term,
     lastLogIndex |-> r.lastLogIndex, lastLogTerm |-> r.lastLogTerm]

AppendFact(src, dst, r) ==
    [type |-> "append", src |-> src, dst |-> dst, term |-> r.term,
     prevLogIndex |-> r.prevLogIndex, prevLogTerm |-> r.prevLogTerm,
     entries |-> r.entries, commit |-> r.commit]

AckFact(src, dst, r) ==
    [type |-> "ack", src |-> src, dst |-> dst, term |-> r.term,
     index |-> r.prevLogIndex + Len(r.entries)]

----
\* Announced writes (TraceKit, convention 3). The pre-image is small: the
\* scalar durable values, how much of the log to keep and what to put back,
\* the confirmed prefix, and the facts the write added.

Pre(n) ==
    [term |-> currentTerm[n], voteTerm |-> voteTerm[n], voteFor |-> voteFor[n],
     keep |-> Len(log[n]), suffix |-> <<>>, confirmed |-> confirmed[n]]

Remember(n, pre) ==
    undo' = [undo EXCEPT ![n] =
        LastWrite(pre @@ [msgs |-> msgs' \ msgs, votes |-> votes' \ votes])]

Forget(n) == undo' = [undo EXCEPT ![n] = NoWrite]

\* The durable state a restarted node reports.
Recovered(ev, t, vt, vf, l) ==
    /\ ev.term = t /\ ev.voteTerm = vt /\ ev.voteFor = vf
    /\ ev.lastIndex = Len(l) /\ ev.lastTerm = TermAt(l, Len(l))

\* Restart with node n's durable state set to (t, vt, vf, l): the model's
\* Restart, after taking back the last write if d is the pre-image.
RestartAs(n, t, vt, vf, l, conf, lostMsgs, lostVotes) ==
    /\ currentTerm' = [currentTerm EXCEPT ![n] = t]
    /\ voteTerm' = [voteTerm EXCEPT ![n] = vt]
    /\ voteFor' = [voteFor EXCEPT ![n] = vf]
    /\ log' = [log EXCEPT ![n] = l]
    /\ confirmed' = [confirmed EXCEPT ![n] = conf]
    /\ role' = [role EXCEPT ![n] = Follower]
    /\ commitIndex' = [commitIndex EXCEPT ![n] = 0]
    /\ msgs' = msgs \ lostMsgs
    /\ votes' = (votes \ lostVotes)
                \cup (IF vf # Nil THEN {[voter |-> n, term |-> vt, cand |-> vf]} ELSE {})
    \* If the write taken back was a leader's append, nobody was sent it.
    /\ ledLog' = IF role[n] = Leader /\ currentTerm[n] \in DOMAIN ledLog
                 THEN WithLed(currentTerm[n], l) ELSE ledLog
    /\ UNCHANGED <<leaders, commits>>

Boot(n, ev) ==
    IF n \notin ready
    THEN \* Not bootstrapped yet, or killed during bootstrap.
         /\ ready' = IF ev.lastIndex >= 1 THEN ready \cup {n} ELSE ready
         /\ ev.lastIndex >= 1 => Recovered(ev, currentTerm[n], voteTerm[n], voteFor[n], log[n])
         /\ UNCHANGED <<vars, undo>>
    ELSE /\ UNCHANGED ready
         /\ Forget(n)
         /\ \/ /\ Recovered(ev, currentTerm[n], voteTerm[n], voteFor[n], log[n])
               /\ Restart(n)
            \/ /\ undo[n] # NoWrite
               /\ LET u == undo[n][1]
                      l == SubSeq(log[n], 1, u.keep) \o u.suffix
                  IN /\ ~Recovered(ev, currentTerm[n], voteTerm[n], voteFor[n], log[n])
                     /\ Recovered(ev, u.term, u.voteTerm, u.voteFor, l)
                     /\ RestartAs(n, u.term, u.voteTerm, u.voteFor, l, u.confirmed, u.msgs, u.votes)

----
\* Writes.

StableSet(n, ev) ==
    IF n \notin ready THEN UNCHANGED <<vars, ready, undo>>
    ELSE /\ UNCHANGED ready
         /\ CASE ev.key = "CurrentTerm" ->
                   IF ev.value = currentTerm[n] THEN UNCHANGED vars
                   ELSE IF role[n] = Candidate /\ ev.value = currentTerm[n] + 1
                   THEN StartElection(n)
                   ELSE AdoptTerm(n, ev.value)
              [] ev.key = "LastVoteTerm" ->
                   ev.value = currentTerm[n] /\ SetVoteTerm(n)
              [] ev.key = "LastVoteCand" -> SetVoteFor(n, ev.value)
              [] OTHER -> FALSE
         /\ Remember(n, Pre(n))

\* Requests to n in n's current term that could have put these entries at
\* this index. They agree on the result.
Storing(n, first, es) ==
    {m \in msgs : /\ m.type = "append" /\ m.dst = n /\ m.term = currentTerm[n]
                  /\ first > m.prevLogIndex
                  /\ first - m.prevLogIndex <= Len(m.entries)
                  /\ SubSeq(m.entries, first - m.prevLogIndex, Len(m.entries)) = es}

LogStore(n, ev) ==
    IF n \notin ready
    THEN \* Bootstrap stores the configuration entry the model starts with.
         /\ ev.first = 1 /\ ev.entries = log[n]
         /\ ready' = ready \cup {n}
         /\ UNCHANGED <<vars, undo>>
    ELSE /\ UNCHANGED ready
         /\ ev.first = Len(log[n]) + 1
         /\ IF role[n] = Leader THEN LeaderAppend(n, ev.entries)
            ELSE \E m \in Storing(n, ev.first, ev.entries) :
                    StoreEntries(n, m, ev.first - m.prevLogIndex)
         /\ Remember(n, Pre(n))

Deleting(n, from) ==
    {m \in msgs : /\ m.type = "append" /\ m.dst = n /\ m.term = currentTerm[n]
                  /\ from > m.prevLogIndex
                  /\ from - m.prevLogIndex <= Len(m.entries)}

LogDelete(n, ev) ==
    /\ n \in ready
    /\ UNCHANGED ready
    /\ ev.to = Len(log[n])
    /\ \E m \in Deleting(n, ev.from) : DeleteSuffix(n, m, ev.from - m.prevLogIndex)
    /\ Remember(n, [Pre(n) EXCEPT !.keep = ev.from - 1,
                                  !.suffix = SubSeq(log[n], ev.from, Len(log[n]))])

----
\* Roles. A stopping node's role is overwritten from outside the main loop;
\* the model has no such role, so that report changes nothing.
Role(n, ev) ==
    /\ UNCHANGED <<ready, undo>>
    /\ CASE n \notin ready -> UNCHANGED vars
         [] ev.role = "follower" -> BecomeFollower(n)
         [] ev.role = "candidate" -> BecomeCandidate(n)
         [] ev.role = "leader" -> BecomeLeader(n)
         [] OTHER -> UNCHANGED vars

----
\* Requests sent.

\* A leader's commit index has no report of its own: it shows in the next
\* request the node sends or in the commit index reported with its next
\* reply, possibly after it stepped down. LedCommit(n, c) says index c can
\* be explained that way (Raft's LeaderCommit, for the term of the entry).
LedCommit(n, c) ==
    /\ c <= Len(log[n])
    /\ [server |-> n, term |-> log[n][c].term] \in leaders
    /\ IsQuorum(Acked(n, log[n][c].term, c))

\* The first c entries of l are committed (Raft's CommittedIn, on the
\* longest committed prefix seen instead of the history of all of them).
Known(l, c) ==
    \/ c = 0
    \/ c <= Len(l) /\ c <= Len(chain) /\ SubSeq(chain, 1, c) = SubSeq(l, 1, c)

\* SendAppend, after LeaderCommit if the request shows a commit index the
\* model has not seen yet. The request is reported when it is sent, which
\* can be after the node has left the term it built it in; it is checked
\* against that term's leader log, not against the node as it is now.
SendAppendWithCommit(n, j, r) ==
    LET t == r.term
        c == r.commit
        p == r.prevLogIndex
        k == Len(r.entries)
    IN /\ [server |-> n, term |-> t] \in leaders
       /\ t \in DOMAIN ledLog
       /\ j # n
       /\ LET l == ledLog[t] IN
          /\ p + k <= Len(l)
          /\ r.prevLogTerm = TermAt(l, p)
          /\ r.entries = SubSeq(l, p + 1, p + k)
          /\ IF c > commitIndex[n]
             THEN /\ LedCommit(n, c)
                  /\ c <= Len(l) /\ SubSeq(log[n], 1, c) = SubSeq(l, 1, c)
                  /\ commitIndex' = [commitIndex EXCEPT ![n] = c]
             ELSE /\ Known(l, c)
                  /\ UNCHANGED commitIndex
       /\ msgs' = msgs \cup {AppendFact(n, j, r)}
       /\ UNCHANGED <<durable, role, confirmed, votes, leaders, ledLog, commits>>

\* Every node has left term t: a request of that term can no longer be
\* accepted by anyone, and the term's facts and leader log are forgotten.
Over(t) == \A j \in Server : currentTerm[j] > t

Send(n, ev) ==
    /\ n \in ready
    /\ UNCHANGED <<ready, undo>>
    /\ CASE ev.kind = "vote" ->
              \* The request became a fact when the election started. A
              \* request goroutine can send it after every node has left
              \* that term, when the fact has been forgotten.
              /\ \/ VoteFact(n, ev.req) \in msgs
                 \/ \A j \in Server : currentTerm[j] > ev.req.term
              /\ UNCHANGED vars
         [] ev.kind \in {"heartbeat", "append"} ->
              IF Over(ev.req.term) THEN UNCHANGED vars
              ELSE SendAppendWithCommit(n, ev.peer, ev.req)
         [] OTHER -> FALSE

----
\* Replies. A reply is reported just after the handler finished, with the
\* node's commit index then.

\* The commit index reported with a reply moved, and the reply itself does
\* not explain it: the node committed as a leader earlier.
LateCommit(n, c) ==
    /\ LedCommit(n, c)
    /\ commitIndex' = [commitIndex EXCEPT ![n] = c]

Reply(n, ev) ==
    /\ UNCHANGED <<ready, undo>>
    /\ IF n \notin ready THEN UNCHANGED vars
       ELSE LET moved == ev.commit > commitIndex[n] IN
            CASE ev.kind = "vote" ->
                   IF ev.resp.granted
                   THEN /\ [voter |-> n, term |-> ev.req.term, cand |-> ev.src] \in votes
                        /\ msgs' = msgs \cup {[type |-> "grant", src |-> n, dst |-> ev.src,
                                                term |-> ev.req.term]}
                        /\ IF moved THEN LateCommit(n, ev.commit) ELSE UNCHANGED commitIndex
                        /\ UNCHANGED <<durable, role, confirmed, votes, leaders, ledLog, commits>>
                   ELSE /\ ev.resp.term <= currentTerm[n]
                        /\ IF moved THEN LateCommit(n, ev.commit) ELSE UNCHANGED commitIndex
                        /\ UNCHANGED <<durable, role, confirmed, msgs, votes, leaders, ledLog, commits>>
              [] ev.kind = "append" ->
                   IF ev.resp.success
                   THEN \* Ack, then FollowerCommit if this request explains
                        \* the commit index, else the late leader commit.
                        LET m == AppendFact(ev.src, n, ev.req)
                            last == m.prevLogIndex + Len(m.entries)
                        IN /\ m \in msgs /\ currentTerm[n] >= m.term
                           /\ PrevOk(n, m) /\ HasFirst(n, m, Len(m.entries))
                           /\ msgs' = msgs \cup {AckFact(n, ev.src, ev.req)}
                           /\ confirmed' = Confirm(n, m.term,
                                 IF confirmed[n].term = m.term
                                 THEN Max(confirmed[n].index, last) ELSE last)
                           /\ IF ~moved THEN UNCHANGED commitIndex
                              ELSE IF ev.commit <= m.commit
                              THEN commitIndex' = [commitIndex EXCEPT ![n] = ev.commit]
                              ELSE LateCommit(n, ev.commit)
                           /\ UNCHANGED <<durable, role, votes, leaders, ledLog, commits>>
                   ELSE /\ ev.resp.term <= currentTerm[n]
                        /\ IF moved THEN LateCommit(n, ev.commit) ELSE UNCHANGED commitIndex
                        /\ UNCHANGED <<durable, role, confirmed, msgs, votes, leaders, ledLog, commits>>
              [] OTHER -> FALSE

\* A reply that came back must be one the model saw sent.
Return(n, ev) ==
    /\ UNCHANGED <<vars, ready, undo>>
    /\ CASE ev.kind = "vote" ->
              ev.resp.granted =>
                 \/ [type |-> "grant", src |-> ev.peer, dst |-> n, term |-> ev.req.term] \in msgs
                 \/ currentTerm[n] > ev.req.term   \* forgotten: n has left that term
         [] ev.kind \in {"append", "heartbeat"} ->
              ev.resp.success =>
                 \/ \E a \in msgs : /\ a.type = "ack" /\ a.src = ev.peer /\ a.dst = n
                                    /\ a.term = ev.req.term
                                    /\ a.index >= ev.req.prevLogIndex + Len(ev.req.entries)
                 \* forgotten: n has left that term and its commit covers it
                 \/ /\ currentTerm[n] > ev.req.term
                    /\ commitIndex[n] >= ev.req.prevLogIndex + Len(ev.req.entries)
         [] OTHER -> FALSE

Bind(n, ev) ==
    CASE ev.e = "boot" -> Boot(n, ev)
      [] ev.e = "stable.set" -> StableSet(n, ev)
      [] ev.e = "log.store" -> LogStore(n, ev)
      [] ev.e = "log.delete" -> LogDelete(n, ev)
      [] ev.e = "role" -> Role(n, ev)
      [] ev.e = "rpc.send" -> Send(n, ev)
      [] ev.e = "rpc.reply" -> Reply(n, ev)
      [] ev.e = "rpc.return" -> Return(n, ev)
      [] ev.e \in {"rpc.fail", "rpc.recv"} -> UNCHANGED <<vars, ready, undo>>
      [] OTHER -> FALSE   \* includes Gap: the stream has a hole

----
\* Forgetting facts (TraceKit, convention 4). Every guard of Raft is
\* positive in msgs. Dropped here: requests their receiver has moved past or
\* has replied to, vote requests and grants of finished terms,
\* acknowledgements that a later one or the leader's commit index covers,
\* and the leader logs of terms every node has left.

\* done[n][m] counts the copies of request m that have been sent to n and
\* not replied to. The same request can be sent, and delivered, several
\* times (a retry, or a heartbeat, whose content never changes); it is needed
\* until every copy has been replied to. A restart of n does not end them:
\* a request reported as sent before n restarted can reach the new process.
\* Copies that are lost stay counted until n leaves the request's term.
\* pending[n] is the request n is handling: its reply is reported by another
\* goroutine and can come long after the handler, even after n has moved to
\* a later term, so that request must be kept.
Count(f, m) == IF m \in DOMAIN f THEN f[m] ELSE 0
Bump(f, m, d) == [x \in DOMAIN f \cup {m} |-> IF x = m THEN Count(f, m) + d ELSE f[x]]

Replied(n, ev) ==
    /\ done' = CASE ev.e = "rpc.reply" /\ ev.kind = "append" ->
                     [done EXCEPT ![n] = Bump(@, AppendFact(ev.src, n, ev.req), 0 - 1)]
                [] ev.e = "rpc.send" /\ ev.kind \in {"append", "heartbeat"} ->
                     [done EXCEPT ![ev.peer] = Bump(@, AppendFact(n, ev.peer, ev.req), 1)]
                [] OTHER -> done
    /\ pending' = CASE ev.e = "rpc.recv" -> [pending EXCEPT ![n] = <<AppendFact(ev.src, n, ev.req)>>]
                   [] ev.e = "rpc.reply" /\ ev.kind = "append" -> [pending EXCEPT ![n] = <<>>]
                   [] ev.e = "boot" -> [pending EXCEPT ![n] = <<>>]
                   [] OTHER -> pending

Garbage ==
    {m \in msgs :
        CASE m.type = "append" ->
               /\ pending[m.dst] # <<m>>
               /\ \/ currentTerm[m.dst] > m.term
                  \/ Count(done[m.dst], m) <= 0
          [] m.type = "vote" -> \A j \in Server : currentTerm[j] > m.term
          [] m.type = "grant" -> currentTerm[m.dst] > m.term
          [] m.type = "ack" ->
               \* A leader's commit can show long after it stepped down, so
               \* an acknowledgement stays until that commit index covers it.
               \/ currentTerm[m.dst] > m.term /\ commitIndex[m.dst] >= m.index
               \/ \E a \in msgs : /\ a.type = "ack" /\ a.src = m.src /\ a.dst = m.dst
                                  /\ a.term = m.term /\ a.index > m.index}

\* Leader logs of terms that are over.
StaleLed == {t \in DOMAIN ledLog : Over(t)}

GC ==
    /\ Cardinality(Garbage) >= GCBatch \/ StaleLed # {}
    /\ ledLog' = [t \in DOMAIN ledLog \ StaleLed |-> ledLog[t]]
    /\ msgs' = msgs \ Garbage
    /\ done' = [n \in Server |->
                  [m \in {x \in DOMAIN done[n] : x \in msgs \ Garbage} |-> done[n][m]]]
    /\ UNCHANGED <<currentTerm, voteTerm, voteFor, log, role, commitIndex, confirmed,
                   votes, leaders, commits, i, ready, undo, pending, chain, termLen, srvLen, viol>>

----
\* Safety, step by step. Only node n changes in an event's step.

Comparable(a, b) == IsPrefix(a, b) \/ IsPrefix(b, a)

Matching(a, b) ==
    \A k \in 1..Min(Len(a), Len(b)) :
        a[k].term = b[k].term => a[k] = b[k] /\ (k > 1 => a[k-1].term = b[k-1].term)

\* The term a commit in this step is recorded under: the leader whose log it
\* came from. A follower commit comes from the request it replies to.
CommitTerm(n, ev) ==
    IF /\ ev.e = "rpc.reply" /\ ev.kind = "append" /\ ev.resp.success
       /\ ev.commit <= ev.req.commit
    THEN ev.req.term
    ELSE log'[n][commitIndex'[n]].term

Track(n, ev) ==
    LET won  == role[n] # Leader /\ role'[n] = Leader
        adv  == commitIndex'[n] > commitIndex[n]
        newC == SubSeq(log'[n], 1, commitIndex'[n])
        ct   == IF adv THEN CommitTerm(n, ev) ELSE 0
        restarted == ev.e = "boot"
        follower == ev.e = "rpc.reply" /\ ev.kind = "append" /\ ev.resp.success
                    /\ ev.commit <= ev.req.commit
        old  == IF ct \in DOMAIN termLen THEN termLen[ct] ELSE 0
        logChanged == log'[n] # log[n]
    IN /\ chain' = IF adv /\ Len(newC) > Len(chain) THEN newC ELSE chain
       /\ termLen' = IF adv
                     THEN [x \in DOMAIN termLen \cup {ct} |->
                              IF x = ct THEN Max(old, Len(newC)) ELSE termLen[x]]
                     ELSE termLen
       /\ srvLen' = IF adv THEN [srvLen EXCEPT ![n] = Max(@, Len(newC))] ELSE srvLen
       /\ viol' = viol
            \cup (IF adv /\ ~Comparable(chain, newC) THEN {"StateMachineSafety"} ELSE {})
            \cup (IF \/ adv /\ \E j \in Server : /\ role'[j] = Leader /\ ct < currentTerm'[j]
                                                /\ ~IsPrefix(newC, log'[j])
                     \/ won /\ \E x \in DOMAIN termLen :
                                  x < currentTerm'[n]
                                  /\ ~IsPrefix(SubSeq(chain, 1, termLen[x]), log'[n])
                  THEN {"LeaderCompleteness"} ELSE {})
            \cup (IF logChanged /\ \E b \in Server \ {n} : ~Matching(log'[n], log[b])
                  THEN {"LogMatching"} ELSE {})
            \cup (IF (logChanged \/ adv) /\ ~IsPrefix(SubSeq(chain', 1, srvLen'[n]), log'[n])
                  THEN {"CommittedEntriesPreserved"} ELSE {})
            \cup (IF ~restarted /\ currentTerm'[n] < currentTerm[n]
                  THEN {"TermMonotonic"} ELSE {})
            \cup (IF adv /\ follower /\ commitIndex'[n] > confirmed'[n].index
                  THEN {"CommitBeyondConfirmed"} ELSE {})

----
Init0 ==
    /\ Init
    /\ i = 1
    /\ ready = {}
    /\ undo = [n \in Server |-> NoWrite]
    /\ done = [n \in Server |-> <<>>]
    /\ pending = [n \in Server |-> <<>>]
    /\ chain = <<>>
    /\ termLen = <<>>
    /\ srvLen = [n \in Server |-> 0]
    /\ viol = {}

Step ==
    /\ Cardinality(Garbage) < GCBatch /\ StaleLed = {}
    /\ LET ev == StreamEvent(i)
           n  == ev.node
       IN /\ ev.e # "End"
          /\ Bind(n, ev)
          /\ Replied(n, ev)
          /\ Track(n, ev)
    /\ i' = i + 1

Next0 == GC \/ Step
TraceSpec == Init0 /\ [][Next0]_tvars

\* StateMachineSafety, LeaderCompleteness, LogMatching,
\* CommittedEntriesPreserved and TermMonotonic held at every step, and no
\* follower committed beyond what its leader had confirmed.
Safe == viol = {}

LogTail(l) == SubSeq(l, Max(1, Len(l) - 5), Len(l))

Alias ==
    [i |-> i, viol |-> viol, currentTerm |-> currentTerm, role |-> role,
     voteTerm |-> voteTerm, voteFor |-> voteFor, commitIndex |-> commitIndex,
     confirmed |-> confirmed, lastIndex |-> [n \in Server |-> Len(log[n])],
     logTail |-> [n \in Server |-> LogTail(log[n])],
     msgs |-> msgs, leaders |-> leaders, ledTerms |-> DOMAIN ledLog, ready |-> ready, undo |-> undo]
====
