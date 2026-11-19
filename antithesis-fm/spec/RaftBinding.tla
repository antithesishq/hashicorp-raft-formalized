---- MODULE RaftBinding ----
\* Trace binding: maps each event reported by hashicorp/raft (patched, see
\* patches/README.md) to HashicorpRaft actions, following the conventions of
\* tracekit/tla/TraceKit.tla. Server names are container names and Nil is "",
\* so reported values compare directly with model values. Safety is checked
\* per step against compact summaries instead of the `commits`/`applied`
\* histories. See spec/README.md.
EXTENDS HashicorpRaft, TraceKit, TLC, Integers

VARIABLES
    i,        \* index of the next event
    ready,    \* nodes that have finished bootstrap
    undo,     \* per node: how to take back its last announced write
    done,     \* per node: for each request sent to it, copies not yet replied to
    pending,  \* per node: the append request it has been handed and not replied to
    \* Step-wise safety: longest committed prefix seen, its length per leader
    \* term and per server, and names of violated properties.
    chain, termLen, srvLen, viol,
    \* Nodes that received TimeoutNow and have not yet acted on it.
    tn,
    \* (R4) Per node: last index of an old log still in the store after an
    \* installed snapshot replaced it (0: none; negative: deletion announced).
    junk

tvars == <<vars, i, ready, undo, done, pending, chain, termLen, srvLen, viol, tn, junk>>

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

PreVoteFact(src, r) ==
    [type |-> "prevote", src |-> src, term |-> r.term,
     lastLogIndex |-> r.lastLogIndex, lastLogTerm |-> r.lastLogTerm]

PreGrantFact(src, dst, r) == [type |-> "pregrant", src |-> src, dst |-> dst, term |-> r.term]

TimeoutNowFact(src, dst) == [type |-> "timeoutnow", src |-> src, dst |-> dst]

\* InstallSnapshot (index, lastTerm) as the Installable append request.
SnapReq(n, q) ==
    [term |-> q.term, prevLogIndex |-> 0, prevLogTerm |-> 0,
     entries |-> IF q.term \in DOMAIN ledLog /\ q.index <= Len(ledLog[q.term])
                 THEN SubSeq(ledLog[q.term], 1, q.index) ELSE <<>>,
     commit |-> q.index]

\* A reported request as an append request.
AsAppend(n, ev) == IF ev.kind = "snapshot" THEN SnapReq(n, ev.req) ELSE ev.req

\* The requests to install the snapshot q that src has sent to n.
SnapFacts(n, src, q) ==
    {m \in msgs : /\ Installable(m) /\ m.src = src /\ m.dst = n /\ m.term = q.term
                  /\ Len(m.entries) = q.index /\ m.commit = q.index}

AckFact(src, dst, r) ==
    [type |-> "ack", src |-> src, dst |-> dst, term |-> r.term,
     index |-> r.prevLogIndex + Len(r.entries)]

----
\* Announced writes (TraceKit convention 3). Pre-image: scalar durable state,
\* log length to keep and suffix to restore, confirmed, and facts added.

Pre(n) ==
    [term |-> currentTerm[n], voteTerm |-> voteTerm[n], voteFor |-> voteFor[n],
     keep |-> Len(log[n]), suffix |-> <<>>, confirmed |-> confirmed[n],
     snap |-> snap[n], base |-> base[n]]

Remember(n, pre) ==
    undo' = [undo EXCEPT ![n] =
        LastWrite(pre @@ [msgs |-> msgs' \ msgs, votes |-> votes' \ votes])]

Forget(n) == undo' = [undo EXCEPT ![n] = NoWrite]

\* Snapshot and log-store front reported at boot (absent in older streams).
BootSnapIndex(ev) == IF Has(ev, "snapIndex") THEN ev.snapIndex ELSE 0
BootSnapTerm(ev) == IF Has(ev, "snapTerm") THEN ev.snapTerm ELSE 0
BootFirst(ev) == IF Has(ev, "firstIndex") THEN ev.firstIndex ELSE 1

\* The log a node sees at start with store l (front b deleted) and snapshot
\* sn: if the store is empty, its last entry is the snapshot's.
EffLog(l, sn, b) == IF b >= Len(l) /\ Len(sn) >= Len(l) THEN sn ELSE l

JunkAt(n) == IF junk[n] > 0 THEN junk[n] ELSE 0 - junk[n]

\* The boot report matches durable state (t, vt, vf, l, sn, b). (R4) A node
\* stopped between storing a snapshot and deleting the replaced log still
\* has that log (`junk`).
Recovered(n, ev, t, vt, vf, l, sn, b) ==
    /\ ev.term = t /\ ev.voteTerm = vt /\ ev.voteFor = vf
    /\ BootSnapIndex(ev) = Len(sn)
    /\ Len(sn) > 0 => BootSnapTerm(ev) = sn[Len(sn)].term
    /\ LET le == EffLog(l, sn, b)
           last == IF ev.lastIndex >= BootSnapIndex(ev) THEN <<ev.lastIndex, ev.lastTerm>>
                   ELSE <<BootSnapIndex(ev), BootSnapTerm(ev)>>
       IN \/ /\ last = <<Len(le), TermAt(le, Len(le))>>
             \* Front of the store, unless it ends before the snapshot.
             /\ ev.lastIndex <= BootSnapIndex(ev) \/ BootFirst(ev) = b + 1 \/ junk[n] # 0
          \/ junk[n] # 0 /\ ev.lastIndex = JunkAt(n)

\* Restart after undoing the last announced write (state from the pre-image).
RestartAs(n, t, vt, vf, l, sn, b, conf, lostMsgs, lostVotes) ==
    /\ currentTerm' = [currentTerm EXCEPT ![n] = t]
    /\ voteTerm' = [voteTerm EXCEPT ![n] = vt]
    /\ voteFor' = [voteFor EXCEPT ![n] = vf]
    /\ log' = [log EXCEPT ![n] = EffLog(l, sn, b)]
    /\ snap' = [snap EXCEPT ![n] = sn]
    /\ base' = [base EXCEPT ![n] = b]
    /\ confirmed' = [confirmed EXCEPT ![n] = conf]
    /\ role' = [role EXCEPT ![n] = Follower]
    /\ commitIndex' = [commitIndex EXCEPT ![n] = 0]
    /\ lastApplied' = [lastApplied EXCEPT ![n] = Len(sn)]
    /\ transfer' = [transfer EXCEPT ![n] = FALSE]
    /\ msgs' = msgs \ lostMsgs
    /\ votes' = votes \ lostVotes
    \* An undone leader append was never sent.
    /\ ledLog' = IF role[n] = Leader /\ currentTerm[n] \in DOMAIN ledLog
                 THEN WithLed(currentTerm[n], l) ELSE ledLog
    /\ UNCHANGED <<leaders, commits, applied>>

Boot(n, ev) ==
    IF n \notin ready
    THEN \* Not bootstrapped yet, or killed during bootstrap.
         /\ ready' = IF ev.lastIndex >= 1 THEN ready \cup {n} ELSE ready
         /\ ev.lastIndex >= 1 => Recovered(n, ev, currentTerm[n], voteTerm[n], voteFor[n], log[n], snap[n], base[n])
         /\ UNCHANGED <<vars, undo>>
    ELSE /\ UNCHANGED ready
         /\ Forget(n)
         /\ \/ /\ Recovered(n, ev, currentTerm[n], voteTerm[n], voteFor[n], log[n], snap[n], base[n])
               /\ Restart(n)
            \/ /\ undo[n] # NoWrite
               /\ LET u == undo[n][1]
                      l == SubSeq(log[n], 1, u.keep) \o u.suffix
                  IN /\ ~Recovered(n, ev, currentTerm[n], voteTerm[n], voteFor[n], log[n], snap[n], base[n])
                     /\ Recovered(n, ev, u.term, u.voteTerm, u.voteFor, l, u.snap, u.base)
                     /\ RestartAs(n, u.term, u.voteTerm, u.voteFor, l, u.snap, u.base, u.confirmed, u.msgs, u.votes)

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

\* Requests in n's term that could store es at index first (all agree).
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

\* log.delete is one of: the old log a snapshot replaced (R4, `junk`; no
\* step); a range already compacted (no step); CompactLog; or DeleteSuffix
\* from the first conflict.
LogDelete(n, ev) ==
    /\ n \in ready
    /\ UNCHANGED ready
    /\ \/ /\ junk[n] > 0 /\ ev.to = junk[n]
          /\ UNCHANGED <<vars, undo>>
       \/ /\ junk[n] <= 0 /\ ev.to <= base[n]
          /\ UNCHANGED <<vars, undo>>
       \/ /\ junk[n] <= 0 /\ ev.from <= base[n] + 1
          /\ CompactLog(n, ev.to)
          /\ Remember(n, Pre(n))
       \/ /\ junk[n] <= 0 /\ ev.from > base[n]
          /\ ev.to = Len(log[n])
          /\ \E m \in Deleting(n, ev.from) : DeleteSuffix(n, m, ev.from - m.prevLogIndex)
          /\ Remember(n, [Pre(n) EXCEPT !.keep = ev.from - 1,
                                        !.suffix = SubSeq(log[n], ev.from, Len(log[n]))])

----
\* role -> BecomeFollower/BecomeLeader, or TimeoutNow/BecomeCandidate
\* depending on a pending TimeoutNow. Other roles (set on shutdown, outside
\* the main loop) are no step.
Role(n, ev) ==
    /\ UNCHANGED <<ready, undo>>
    /\ CASE n \notin ready -> UNCHANGED vars
         [] ev.role = "follower" -> BecomeFollower(n)
         [] ev.role = "candidate" -> IF n \in tn THEN TimeoutNow(n) ELSE BecomeCandidate(n)
         [] ev.role = "leader" -> BecomeLeader(n)
         [] OTHER -> UNCHANGED vars

----
\* Requests sent.

\* A leader's commit is not reported directly; it shows in a later request,
\* reply or apply, possibly after stepping down. LedCommit(n, c): index c is
\* explained by LeaderCommit for the entry's term.
LedCommit(n, c) ==
    /\ c <= Len(log[n])
    /\ [server |-> n, term |-> log[n][c].term] \in leaders
    /\ IsQuorum(Acked(n, log[n][c].term, c))

\* CommittedIn over the summary: chain plus per-term lengths (termLen). Every
\* recorded prefix is a prefix of chain while CommitSafety holds.
RecordedIn(l, c, t) ==
    /\ c <= Len(l) /\ c <= Len(chain)
    /\ \E x \in DOMAIN termLen : x <= t /\ termLen[x] >= c
    /\ SubSeq(chain, 1, c) = SubSeq(l, 1, c)

\* c is not yet covered for term t, so the step must record a commit.
SendCommits(l, c, t) == c > 0 /\ ~RecordedIn(l, c, t)

\* rpc.send append/heartbeat/snapshot -> SendAppend, preceded by an unseen
\* LeaderCommit if c is not yet covered. Checked against ledLog[t], not the
\* sender's current state: the send may come after it left term t.
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
          /\ IF SendCommits(l, c, t)
             THEN /\ LedCommit(n, c)
                  /\ log[n][c].term <= t
                  /\ c <= Len(l) /\ SubSeq(log[n], 1, c) = SubSeq(l, 1, c)
                  /\ commitIndex' = [commitIndex EXCEPT ![n] = Max(@, c)]
             ELSE UNCHANGED commitIndex
       /\ msgs' = msgs \cup {AppendFact(n, j, r)}
       /\ UNCHANGED <<durable, role, transfer, lastApplied, confirmed, votes, leaders, ledLog, commits, applied>>

\* The guard of SendAppendWithCommit on current-state variables only.
FromLed(n, j, r) ==
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
          /\ SendCommits(l, c, t) =>
                /\ LedCommit(n, c)
                /\ log[n][c].term <= t
                /\ c <= Len(l) /\ SubSeq(log[n], 1, c) = SubSeq(l, 1, c)

\* The request n is handling explains commit index c (Ack + FollowerCommit),
\* for a commit index reported before that request's reply.
PendingAck(n) ==
    LET m == pending[n][1] IN
    [type |-> "ack", src |-> n, dst |-> m.src, term |-> m.term,
     index |-> m.prevLogIndex + Len(m.entries)]

PendingExplains(n, c) ==
    /\ pending[n] # <<>>
    /\ LET m == pending[n][1] IN
       /\ m \in msgs /\ currentTerm[n] = m.term
       /\ PrevOk(n, m) /\ HasFirst(n, m, Len(m.entries))
       /\ c <= m.commit

PendingConfirm(n) ==
    LET m == pending[n][1]
        last == m.prevLogIndex + Len(m.entries)
    IN Confirm(n, m.term, IF confirmed[n].term = m.term
                          THEN Max(confirmed[n].index, last) ELSE last)

\* Every node has left term t: its requests can no longer be accepted, and
\* its facts and leader log are forgotten.
Over(t) == \A j \in Server : currentTerm[j] > t

Send(n, ev) ==
    /\ n \in ready
    /\ UNCHANGED <<ready, undo>>
    /\ CASE ev.kind = "vote" ->
              \* Fact since StartElection; may be sent after it was forgotten.
              /\ \/ VoteFact(n, ev.req) \in msgs
                 \/ \A j \in Server : currentTerm[j] > ev.req.term
              /\ UNCHANGED vars
         [] ev.kind = "prevote" ->
              \* SendPreVote on the first copy matching the node's current
              \* state; a late copy of an abandoned attempt adds no fact.
              /\ PreVote
              /\ LET m == PreVoteFact(n, ev.req) IN
                 IF /\ m \notin msgs /\ role[n] = Candidate
                    /\ m = PreVoteRequest(n, currentTerm[n] + 1)
                 THEN SendPreVote(n) ELSE UNCHANGED vars
         [] ev.kind = "timeoutnow" ->
              IF TimeoutNowFact(n, ev.peer) \in msgs THEN UNCHANGED vars
              ELSE SendTimeoutNow(n, ev.peer)
         [] ev.kind \in {"heartbeat", "append"} ->
              IF Over(ev.req.term) THEN UNCHANGED vars
              ELSE FromLed(n, ev.peer, ev.req) /\ SendAppendWithCommit(n, ev.peer, ev.req)
         [] ev.kind = "snapshot" ->
              LET r == SnapReq(n, ev.req) IN
              IF Over(ev.req.term) THEN UNCHANGED vars
              ELSE /\ Len(r.entries) = ev.req.index /\ ev.req.index >= 1
                   /\ r.entries[ev.req.index].term = ev.req.lastTerm
                   /\ FromLed(n, ev.peer, r) /\ SendAppendWithCommit(n, ev.peer, r)
         [] OTHER -> FALSE

----
\* rpc.reply: reported after the handler, with the node's commit index.

\* A commit-index move the reply does not explain: an earlier leader commit.
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
                        /\ UNCHANGED <<durable, role, transfer, lastApplied, confirmed, votes, leaders, ledLog, commits, applied>>
                   ELSE /\ ev.resp.term <= currentTerm[n]
                        /\ IF moved THEN LateCommit(n, ev.commit) ELSE UNCHANGED commitIndex
                        /\ UNCHANGED <<durable, role, transfer, lastApplied, confirmed, msgs, votes, leaders, ledLog, commits, applied>>
              [] ev.kind = "prevote" ->
                   \* GrantPreVote, checked against the reported request; a
                   \* fact only if the request is one.
                   LET m == PreVoteFact(ev.src, ev.req) IN
                   /\ IF ev.resp.granted
                      THEN /\ ev.src # n /\ m.term >= currentTerm[n] /\ UpToDate(m, n)
                           /\ msgs' = IF m \in msgs THEN msgs \cup {PreGrantFact(n, ev.src, ev.req)}
                                      ELSE msgs
                      ELSE UNCHANGED msgs
                   /\ IF moved THEN LateCommit(n, ev.commit) ELSE UNCHANGED commitIndex
                   /\ UNCHANGED <<durable, role, transfer, lastApplied, confirmed, votes, leaders, ledLog, commits, applied>>
              [] ev.kind = "timeoutnow" ->
                   \* Already a candidate, so no role event was reported.
                   IF n \in tn THEN TimeoutNow(n) ELSE UNCHANGED vars
              [] ev.kind = "append" ->
                   IF ev.resp.success
                   THEN \* Ack, then FollowerCommit or LateCommit.
                        LET m == AppendFact(ev.src, n, ev.req)
                            last == m.prevLogIndex + Len(m.entries)
                        IN /\ m \in msgs /\ currentTerm[n] = m.term
                           /\ PrevOk(n, m) /\ HasFirst(n, m, Len(m.entries))
                           /\ msgs' = msgs \cup {AckFact(n, ev.src, ev.req)}
                           /\ confirmed' = Confirm(n, m.term,
                                 IF confirmed[n].term = m.term
                                 THEN Max(confirmed[n].index, last) ELSE last)
                           /\ IF ~moved THEN UNCHANGED commitIndex
                              ELSE IF ev.commit <= m.commit
                              THEN commitIndex' = [commitIndex EXCEPT ![n] = ev.commit]
                              ELSE LateCommit(n, ev.commit)
                           /\ UNCHANGED <<durable, role, transfer, lastApplied, votes, leaders, ledLog, commits, applied>>
                   ELSE /\ ev.resp.term <= currentTerm[n]
                        /\ IF moved THEN LateCommit(n, ev.commit) ELSE UNCHANGED commitIndex
                        /\ UNCHANGED <<durable, role, transfer, lastApplied, confirmed, msgs, votes, leaders, ledLog, commits, applied>>
              [] ev.kind = "snapshot" ->
                   IF ev.resp.success
                   THEN \* Ack: the node holds the snapshot's entries (R4).
                        /\ pending[n] # <<>>
                        /\ LET m == pending[n][1]
                               last == Len(m.entries)
                           IN /\ Installable(m) /\ last = ev.req.index
                              /\ m \in msgs /\ currentTerm[n] = m.term
                              /\ HasFirst(n, m, last)
                              /\ msgs' = msgs \cup {[type |-> "ack", src |-> n, dst |-> m.src,
                                                      term |-> m.term, index |-> last]}
                              /\ confirmed' = Confirm(n, m.term,
                                    IF confirmed[n].term = m.term
                                    THEN Max(confirmed[n].index, last) ELSE last)
                              /\ IF ~moved THEN UNCHANGED commitIndex
                                 ELSE IF ev.commit <= m.commit
                                 THEN commitIndex' = [commitIndex EXCEPT ![n] = ev.commit]
                                 ELSE LateCommit(n, ev.commit)
                              /\ UNCHANGED <<durable, role, transfer, lastApplied, votes, leaders, ledLog, commits, applied>>
                   ELSE /\ ev.resp.term <= currentTerm[n]
                        /\ IF moved THEN LateCommit(n, ev.commit) ELSE UNCHANGED commitIndex
                        /\ UNCHANGED <<durable, role, transfer, lastApplied, confirmed, msgs, votes, leaders, ledLog, commits, applied>>
              [] OTHER -> FALSE

\* rpc.return: a successful reply must be one the model saw sent.
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
         [] ev.kind = "snapshot" ->
              ev.resp.success =>
                 \/ \E a \in msgs : /\ a.type = "ack" /\ a.src = ev.peer /\ a.dst = n
                                    /\ a.term = ev.req.term /\ a.index >= ev.req.index
                 \/ currentTerm[n] > ev.req.term
         \* A pre-grant may answer a request that was never a fact.
         [] ev.kind \in {"prevote", "timeoutnow"} -> TRUE
         [] OTHER -> FALSE

----
\* fsm.apply runs on its own goroutine, so it can precede the reply that
\* moved the commit index. It carries the commit index at report time.

\* c is new and not a leader commit: the pending request must explain it.
ApplyFollows(n, c) == c > commitIndex[n] /\ ~LedCommit(n, c)

\* The FSM only sees commands, so one fsm.apply covers several Apply steps;
\* a command in between means one was skipped.
Skipped(n, k) == \E q \in (lastApplied[n] + 1)..(k - 1) : log[n][q].type = "command"

\* Reported commit index c, if new: LeaderCommit if possible, else Ack and
\* FollowerCommit for the pending request (its later reply repeats the Ack).
SeeCommit(n, c) ==
    IF c <= commitIndex[n] THEN UNCHANGED <<commitIndex, confirmed, msgs>>
    ELSE IF LedCommit(n, c)
    THEN /\ commitIndex' = [commitIndex EXCEPT ![n] = c]
         /\ UNCHANGED <<confirmed, msgs>>
    ELSE /\ pending[n] # <<>>
         /\ LET m == pending[n][1]
                last == m.prevLogIndex + Len(m.entries)
            IN /\ m \in msgs /\ currentTerm[n] = m.term
               /\ PrevOk(n, m) /\ HasFirst(n, m, Len(m.entries))
               /\ msgs' = msgs \cup {[type |-> "ack", src |-> n, dst |-> m.src,
                                       term |-> m.term, index |-> last]}
               /\ confirmed' = Confirm(n, m.term,
                     IF confirmed[n].term = m.term
                     THEN Max(confirmed[n].index, last) ELSE last)
               /\ c <= m.commit
               /\ commitIndex' = [commitIndex EXCEPT ![n] = c]

\* An apply queued before an install, reported after the snapshot was
\* stored: no step (the model jumped to the snapshot), but must match it.
LateApply(n, ev) ==
    /\ pending[n] # <<>> /\ Installable(pending[n][1])
    /\ ev.index <= Len(snap[n])
    /\ ev.index <= lastApplied[n]
    /\ snap[n][ev.index] = ev.entry

FsmApply(n, ev) ==
    LET k == ev.index
        c == ev.commit
    IN IF n \in ready /\ LateApply(n, ev) THEN UNCHANGED <<vars, ready, undo>> ELSE
       /\ n \in ready
       /\ UNCHANGED <<ready, undo>>
       /\ k > lastApplied[n] /\ k <= Len(log[n])
       /\ ev.entry.type = "command" /\ log[n][k] = ev.entry
       /\ ~Skipped(n, k)
       /\ SeeCommit(n, c)
       \* Apply, k - lastApplied[n] times.
       /\ k <= commitIndex'[n]
       /\ lastApplied' = [lastApplied EXCEPT ![n] = k]
       /\ UNCHANGED <<durable, role, transfer, votes, leaders, ledLog, commits, applied>>

----
\* Snapshots.

\* The pending install request matches the stored snapshot.
Installing(n, ev) ==
    /\ pending[n] # <<>>
    /\ Installable(pending[n][1])
    /\ Len(pending[n][1].entries) = ev.index
    /\ pending[n][1].entries[ev.index].term = ev.term

\* An install that replaces a log not continuing the snapshot: in the model
\* DeleteSuffix, StoreEntries and InstallSnapshot in one step. The store
\* still holds the old log, deleted next (`junk`).
Replaces(n, ev) ==
    /\ ev.e = "snap.store" /\ ev.kind = "install" /\ n \in ready
    /\ Installing(n, ev)
    /\ ~HasFirst(n, pending[n][1], ev.index)

\* First index where n's log differs from m's entries.
FirstDiff(n, m) ==
    CHOOSE q \in 1..(Len(m.entries) + 1) :
        /\ q = Len(m.entries) + 1 \/ q > Len(log[n]) \/ log[n][q].term # m.entries[q].term
        /\ \A x \in 1..(q - 1) : x <= Len(log[n]) /\ log[n][x].term = m.entries[x].term

SnapStore(n, ev) ==
    /\ n \in ready
    /\ UNCHANGED ready
    /\ IF ev.kind = "install"
       THEN /\ Installing(n, ev)
            /\ LET m == pending[n][1] IN
               IF Replaces(n, ev)
               THEN /\ m \in msgs /\ m.term = currentTerm[n]
                    /\ ev.index > Len(snap[n]) /\ ev.index > lastApplied[n]
                    /\ FirstDiff(n, m) > Len(snap[n])
                    /\ log' = [log EXCEPT ![n] = m.entries]
                    /\ base' = [base EXCEPT ![n] = ev.index]
                    /\ snap' = [snap EXCEPT ![n] = m.entries]
                    /\ lastApplied' = [lastApplied EXCEPT ![n] = ev.index]
                    /\ confirmed' = Confirm(n, m.term, ev.index)
                    /\ UNCHANGED <<currentTerm, voteTerm, voteFor, role, commitIndex, transfer,
                                   msgs, votes, leaders, ledLog, commits, applied>>
               ELSE InstallSnapshot(n, m)
            /\ Remember(n, [Pre(n) EXCEPT !.keep = 0, !.suffix = log[n]])
       ELSE \* takeSnapshot: Apply up to its index (past the last command,
            \* or before it, since the state is persisted later), after
            \* SeeCommit, then TakeSnapshot.
            LET k == ev.index IN
            IF k <= Len(snap[n])
            THEN \* Repeat snapshot at the same FSM state, or one finished
                 \* after a newer install: no step.
                 UNCHANGED <<vars, undo>>
            ELSE
            /\ k <= Len(log[n]) /\ log[n][k].term = ev.term
            /\ ~Skipped(n, k + 1)
            /\ SeeCommit(n, ev.commit)
            /\ k <= commitIndex'[n]
            /\ lastApplied' = [lastApplied EXCEPT ![n] = Max(@, k)]
            /\ snap' = [snap EXCEPT ![n] = Machine(n, k)]
            /\ UNCHANGED <<currentTerm, voteTerm, voteFor, log, base, role, transfer, votes, leaders, ledLog, commits, applied>>
            /\ Remember(n, Pre(n))

Bind(n, ev) ==
    CASE ev.e = "boot" -> Boot(n, ev)
      [] ev.e = "stable.set" -> StableSet(n, ev)
      [] ev.e = "log.store" -> LogStore(n, ev)
      [] ev.e = "log.delete" -> LogDelete(n, ev)
      [] ev.e = "role" -> Role(n, ev)
      [] ev.e = "rpc.send" -> Send(n, ev)
      [] ev.e = "rpc.reply" -> Reply(n, ev)
      [] ev.e = "rpc.return" -> Return(n, ev)
      [] ev.e = "fsm.apply" -> FsmApply(n, ev)
      [] ev.e = "snap.store" -> SnapStore(n, ev)
      [] ev.e \in {"rpc.fail", "rpc.recv"} -> UNCHANGED <<vars, ready, undo>>
      [] OTHER -> FALSE   \* includes Gap: the stream has a hole

----
\* Forgetting facts (TraceKit convention 4; all guards are positive in msgs):
\* requests the receiver passed or answered, votes and grants of finished
\* terms, acks superseded or no longer needed, leader logs of terms over.

\* done[n][m]: copies of m sent to n and not replied to (retries and
\* heartbeats repeat); kept across restarts of n, and lost copies count until
\* n leaves m's term. pending[n] is kept until its reply, which may be
\* reported much later, even after a term change.
Count(f, m) == IF m \in DOMAIN f THEN f[m] ELSE 0
Bump(f, m, d) == [x \in DOMAIN f \cup {m} |-> IF x = m THEN Count(f, m) + d ELSE f[x]]

Replied(n, ev) ==
    /\ done' = CASE ev.e = "rpc.reply" /\ ev.kind = "append" ->
                     [done EXCEPT ![n] = Bump(@, AppendFact(ev.src, n, ev.req), 0 - 1)]
                [] ev.e = "rpc.reply" /\ ev.kind = "snapshot" /\ pending[n] # <<>> ->
                     [done EXCEPT ![n] = Bump(@, pending[n][1], 0 - 1)]
                [] ev.e = "rpc.send" /\ ev.kind \in {"append", "heartbeat"} ->
                     [done EXCEPT ![ev.peer] = Bump(@, AppendFact(n, ev.peer, ev.req), 1)]
                [] ev.e = "rpc.send" /\ ev.kind = "snapshot" /\ ~Over(ev.req.term) ->
                     [done EXCEPT ![ev.peer] = Bump(@, AppendFact(n, ev.peer, SnapReq(n, ev.req)), 1)]
                [] OTHER -> done
    /\ pending' = CASE ev.e = "rpc.recv" /\ ev.kind = "append" -> [pending EXCEPT ![n] = <<AppendFact(ev.src, n, ev.req)>>]
                   [] ev.e = "rpc.recv" /\ ev.kind = "snapshot" ->
                        [pending EXCEPT ![n] = IF SnapFacts(n, ev.src, ev.req) = {} THEN <<>>
                                               ELSE <<CHOOSE m \in SnapFacts(n, ev.src, ev.req) : TRUE>>]
                   [] ev.e = "rpc.reply" /\ ev.kind \in {"append", "snapshot"} -> [pending EXCEPT ![n] = <<>>]
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
          \* Useless once the candidate reached that term.
          [] m.type = "prevote" -> currentTerm[m.src] >= m.term
          [] m.type = "pregrant" -> currentTerm[m.dst] >= m.term
          \* No term; at most one per pair of nodes.
          [] m.type = "timeoutnow" -> FALSE
          [] m.type = "ack" ->
               \* Kept while a late leader commit (LedCommit) may need it:
               \* until the commit index covers it and all its terms are over.
               \/ /\ commitIndex[m.dst] >= m.index
                  /\ \A l \in leaders : l.server = m.dst /\ l.term >= m.term => Over(l.term)
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
    /\ UNCHANGED <<currentTerm, voteTerm, voteFor, log, snap, base, role, commitIndex, lastApplied, transfer, confirmed,
                   votes, leaders, commits, applied, i, ready, undo, pending, chain, termLen, srvLen, viol, tn, junk>>

----
\* Safety, step by step. Only node n changes in an event's step.

Comparable(a, b) == IsPrefix(a, b) \/ IsPrefix(b, a)

Matching(a, b) ==
    \A k \in 1..Min(Len(a), Len(b)) :
        a[k].term = b[k].term => a[k] = b[k] /\ (k > 1 => a[k-1].term = b[k-1].term)

\* The commit a step makes: <<length, leader term, by follower>>. A leader
\* commit is recorded under its last entry's term, a follower's under the
\* request's term.
NoCommit == <<0, 0, FALSE>>
LedRec(n, c) == <<c, log[n][c].term, FALSE>>

CommitRec(n, ev) ==
    CASE ev.e = "rpc.send" /\ ev.kind \in {"heartbeat", "append"} ->
           IF Over(ev.req.term) THEN NoCommit
           ELSE IF SendCommits(ledLog[ev.req.term], ev.req.commit, ev.req.term)
           THEN LedRec(n, ev.req.commit) ELSE NoCommit
      [] ev.e = "rpc.send" /\ ev.kind = "snapshot" ->
           LET r == SnapReq(n, ev.req) IN
           IF Over(ev.req.term) THEN NoCommit
           ELSE IF SendCommits(ledLog[r.term], r.commit, r.term) THEN LedRec(n, r.commit) ELSE NoCommit
      [] ev.e = "rpc.reply" ->
           IF n \notin ready \/ ev.kind = "timeoutnow" \/ ev.commit <= commitIndex[n] THEN NoCommit
           ELSE IF ev.kind = "append" /\ ev.resp.success /\ ev.commit <= ev.req.commit
           THEN <<ev.commit, ev.req.term, TRUE>>
           ELSE IF ev.kind = "snapshot" /\ ev.resp.success /\ ev.commit <= ev.req.index
           THEN <<ev.commit, ev.req.term, TRUE>>
           ELSE LedRec(n, ev.commit)
      [] ev.e = "fsm.apply" /\ n \in ready /\ LateApply(n, ev) -> NoCommit
      [] ev.e \in {"fsm.apply", "snap.store"} /\ (ev.e = "snap.store" => ev.kind = "take") ->
           IF ev.commit <= commitIndex[n] THEN NoCommit
           ELSE IF ApplyFollows(n, ev.commit)
           THEN <<ev.commit, pending[n][1].term, TRUE>>
           ELSE LedRec(n, ev.commit)
      [] OTHER -> NoCommit

Track(n, ev) ==
    LET won  == role[n] # Leader /\ role'[n] = Leader
        rec  == CommitRec(n, ev)
        adv  == rec[1] > 0
        newC == SubSeq(log'[n], 1, rec[1])
        ct   == rec[2]
        follower == rec[3]
        restarted == ev.e = "boot"
        old  == IF ct \in DOMAIN termLen THEN termLen[ct] ELSE 0
        logChanged == log'[n] # log[n]
    IN /\ chain' = IF adv /\ Len(newC) > Len(chain) THEN newC ELSE chain
       /\ termLen' = IF adv
                     THEN [x \in DOMAIN termLen \cup {ct} |->
                              IF x = ct THEN Max(old, Len(newC)) ELSE termLen[x]]
                     ELSE termLen
       /\ srvLen' = IF adv THEN [srvLen EXCEPT ![n] = Max(@, Len(newC))] ELSE srvLen
       /\ viol' = viol
            \cup (IF adv /\ ~Comparable(chain, newC) THEN {"CommitSafety"} ELSE {})
            \* Each apply is compared with chain, which covers the commit
            \* index, so two differing applies at one index cannot both pass.
            \cup (IF ev.e = "fsm.apply" /\ ~(ev.index <= Len(chain') /\ chain'[ev.index] = ev.entry)
                  THEN {"StateMachineSafety"} ELSE {})
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
            \cup (IF adv /\ follower /\ rec[1] > confirmed'[n].index
                  THEN {"CommitBeyondConfirmed"} ELSE {})
            \* Snapshot properties.
            \cup (IF ~IsPrefix(snap'[n], log'[n]) THEN {"SnapshotWithinLog"} ELSE {})
            \cup (IF snap'[n] # snap[n] /\ ~IsPrefix(snap'[n], chain')
                  THEN {"SnapshotCommitted"} ELSE {})
            \cup (IF base'[n] > Len(snap'[n]) THEN {"BaseWithinSnapshot"} ELSE {})
            \cup (IF ~restarted /\ lastApplied'[n] < lastApplied[n]
                  THEN {"AppliedMonotonic"} ELSE {})

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
    /\ tn = {}
    /\ junk = [n \in Server |-> 0]

\* Coverage notes: late TimeoutNow, TimeoutNow to a leader, elections on
\* TimeoutNow or on a pre-vote quorum.
Electing(n, ev) ==
    /\ ev.e = "stable.set" /\ ev.key = "CurrentTerm" /\ n \in ready
    /\ role[n] = Candidate /\ ev.value = currentTerm[n] + 1

TransferNotes(n, ev) ==
    (IF ev.e = "rpc.send" /\ ev.kind = "timeoutnow" /\ role[n] # Leader
     THEN {"T-timeoutnow-late"} ELSE {})
    \cup (IF /\ ev.e = "role" /\ ev.role = "candidate" /\ n \in tn /\ n \in ready
              /\ role[n] = Leader
           THEN {"T-timeoutnow-to-leader"} ELSE {})
    \cup (IF Electing(n, ev) /\ transfer[n] THEN {"T-transfer-election"} ELSE {})
    \cup (IF Electing(n, ev) /\ PreVote /\ ~transfer[n] THEN {"P-prevote-election"} ELSE {})

\* Snapshot coverage notes. S-rejected-after-snapshot is allowed by the model
\* (any request may be rejected) but should not occur with patch R4.
SnapshotNotes(n, ev) ==
    (IF ev.e = "snap.store" /\ ev.kind = "take" /\ ev.index > Len(snap[n]) THEN {"S-snapshot-taken"} ELSE {})
    \cup (IF ev.e = "log.delete" /\ n \in ready /\ junk[n] <= 0 /\ ev.to > base[n] /\ ev.from <= base[n] + 1
           THEN {"S-log-compacted"} ELSE {})
    \cup (IF ev.e = "snap.store" /\ ev.kind = "install"
           THEN {"S-snapshot-installed"}
                \cup (IF Replaces(n, ev) THEN {"S-snapshot-replaces-log"} ELSE {})
           ELSE {})
    \cup (IF ev.e = "boot" /\ n \in ready /\ BootSnapIndex(ev) > 0 THEN {"S-restart-from-snapshot"} ELSE {})
    \cup (IF /\ ev.e = "rpc.reply" /\ ev.kind = "append" /\ ~ev.resp.success /\ n \in ready
              /\ ev.req.term = currentTerm[n] /\ snap[n] # <<>>
              /\ ev.req.prevLogIndex = Len(snap[n])
              /\ ev.req.prevLogTerm = snap[n][Len(snap[n])].term
           THEN {"S-rejected-after-snapshot"} ELSE {})

Notes(n, ev) ==
    TransferNotes(n, ev)
    \cup SnapshotNotes(n, ev)

Step ==
    /\ Cardinality(Garbage) < GCBatch /\ StaleLed = {}
    /\ LET ev == StreamEvent(i)
           n  == ev.node
       IN /\ ev.e # "End"
          /\ Bind(n, ev)
          /\ Replied(n, ev)
          /\ Track(n, ev)
          /\ tn' = CASE ev.e = "rpc.recv" /\ ev.kind = "timeoutnow" -> tn \cup {n}
                     [] ev.e = "role" /\ ev.role = "candidate" -> tn \ {n}
                     [] ev.e = "rpc.reply" /\ ev.kind = "timeoutnow" -> tn \ {n}
                     [] ev.e = "boot" -> tn \ {n}
                     [] OTHER -> tn
          /\ junk' = CASE Replaces(n, ev) /\ Len(log[n]) >= ev.index ->
                            [junk EXCEPT ![n] = Len(log[n])]
                       [] ev.e = "log.delete" /\ junk[n] > 0 /\ ev.to = junk[n] ->
                            [junk EXCEPT ![n] = 0 - junk[n]]
                       [] ev.e = "boot" ->
                            [junk EXCEPT ![n] = IF /\ junk[n] # 0 /\ BootSnapIndex(ev) = Len(snap[n])
                                                   /\ ev.lastIndex = JunkAt(n)
                                                THEN JunkAt(n) ELSE 0]
                       [] OTHER -> junk
          /\ \A x \in Notes(n, ev) : Note(x, i)
          \* Name each property violated at this step.
          /\ \A x \in viol' \ viol : Note(x, i)
    /\ i' = i + 1

Next0 == GC \/ Step
TraceSpec == Init0 /\ [][Next0]_tvars

\* No step-wise property (Track) was violated.
Safe == viol = {}

LogTail(l) == SubSeq(l, Max(1, Len(l) - 5), Len(l))

Alias ==
    [i |-> i, viol |-> viol, currentTerm |-> currentTerm, role |-> role,
     voteTerm |-> voteTerm, voteFor |-> voteFor, commitIndex |-> commitIndex,
     lastApplied |-> lastApplied, transfer |-> transfer, tn |-> tn,
     confirmed |-> confirmed, lastIndex |-> [n \in Server |-> Len(log[n])],
     logTail |-> [n \in Server |-> LogTail(log[n])],
     snapIndex |-> [n \in Server |-> Len(snap[n])], base |-> base, junk |-> junk, pending |-> pending,
     msgs |-> msgs, leaders |-> leaders, ledTerms |-> DOMAIN ledLog, ready |-> ready, undo |-> undo]
====
