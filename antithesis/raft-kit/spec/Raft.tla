---- MODULE Raft ----
\* Raft as hashicorp/raft implements it, in small steps, for proof.
\*
\* One action is one thing the implementation does that can be seen at its
\* boundary: one write to stable storage, one message sent, one reply, one
\* change of role. A handler in the code is several of these actions in a
\* row, and any prefix of them is a state of this model, so a process that
\* is killed between two writes needs no special treatment.
\*
\* Messages are facts. `msgs` only grows: a request says what its sender's
\* log looked like, a reply says what its sender had stored or voted. Any
\* fact can be acted on at any later time, any number of times, which covers
\* delay, loss, retries and requests handled after their caller gave up.
\*
\* Scope: three or more fixed voters; no snapshots, PreVote, leadership
\* transfer or membership change.
\*
\* One place differs from the code on purpose (../PLAN.md, D4): a follower
\* advances its commit index only over the part of its log that a request
\* from the leader has confirmed (`confirmed`). The code uses the end of
\* its whole log.
\*
\* One place the code was changed to match (../PLAN.md, D5; ../FIXES.md,
\* R1): a request carries entries only from the log its sender had while it
\* led the request's term (`ledLog`).
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Server,   \* the voters
          Values,   \* client command payloads
          Nil       \* "no server" / "no value"

ASSUME Nil \notin Server

Follower  == "follower"
Candidate == "candidate"
Leader    == "leader"

VARIABLES
    \* Durable, per node.
    currentTerm, voteTerm, voteFor, log,
    \* Volatile, per node.
    role, commitIndex,
    \* confirmed[i] = [term, index]: the first `index` entries of log[i] are
    \* the first `index` entries of the log of the leader of `term`.
    confirmed,
    \* Facts. msgs: requests and replies sent. votes: every (voter, term,
    \* candidate) a node's vote record has held. leaders: every (server,
    \* term) elected.
    msgs, votes, leaders,
    \* ledLog[t]: the log of the leader of term t as it was when that node
    \* last led t. Defined for the terms that have had a leader. A request
    \* can be sent long after it was built, so sending reads this and not
    \* the sender's log or role now.
    ledLog,
    \* History: every committed prefix observed, with the term of the leader
    \* whose log it was taken from. Read only by SendAppend, to bound the
    \* commit index a request carries.
    commits

durable  == <<currentTerm, voteTerm, voteFor, log>>
protoVars == <<currentTerm, voteTerm, voteFor, log, role, commitIndex,
               confirmed, msgs, votes, leaders, ledLog>>
vars == <<protoVars, commits>>

Min(a, b) == IF a <= b THEN a ELSE b
Max(a, b) == IF a >= b THEN a ELSE b
IsQuorum(S) == Cardinality(S) * 2 > Cardinality(Server)
IsPrefix(a, b) == Len(a) <= Len(b) /\ a = SubSeq(b, 1, Len(a))
TermAt(l, k) == IF k > 0 /\ k <= Len(l) THEN l[k].term ELSE 0
LastTerm(i) == TermAt(log[i], Len(log[i]))
Entry(t, ty, v) == [term |-> t, type |-> ty, value |-> v]

Init ==
    /\ currentTerm = [s \in Server |-> 1]
    /\ voteTerm    = [s \in Server |-> 0]
    /\ voteFor     = [s \in Server |-> Nil]
    \* Bootstrap writes the configuration entry at index 1, term 1.
    /\ log         = [s \in Server |-> <<Entry(1, "config", Nil)>>]
    /\ role        = [s \in Server |-> Follower]
    /\ commitIndex = [s \in Server |-> 0]
    /\ confirmed   = [s \in Server |-> [term |-> 0, index |-> 0]]
    /\ msgs        = {}
    /\ votes       = {}
    /\ leaders     = {}
    /\ ledLog      = <<>>
    /\ commits     = {}

----
\* Roles. The code changes role and term in separate steps.

BecomeCandidate(i) ==
    /\ role' = [role EXCEPT ![i] = Candidate]
    /\ UNCHANGED <<durable, commitIndex, confirmed, msgs, votes, leaders, ledLog, commits>>

BecomeFollower(i) ==
    /\ role' = [role EXCEPT ![i] = Follower]
    /\ UNCHANGED <<durable, commitIndex, confirmed, msgs, votes, leaders, ledLog, commits>>

----
\* Terms and votes: three separate writes.

VoteRequest(i, t) ==
    [type |-> "vote", src |-> i, term |-> t,
     lastLogIndex |-> Len(log[i]), lastLogTerm |-> LastTerm(i)]

\* electSelf: a candidate moves to the next term and its request for votes
\* becomes a fact.
StartElection(i) ==
    /\ role[i] = Candidate
    /\ currentTerm' = [currentTerm EXCEPT ![i] = @ + 1]
    /\ msgs' = msgs \cup {VoteRequest(i, currentTerm[i] + 1)}
    /\ UNCHANGED <<voteTerm, voteFor, log, role, commitIndex, confirmed, votes, leaders, ledLog, commits>>

\* A node adopts a later term that some other node has reached. It is a
\* follower from then on.
AdoptTerm(i, t) ==
    /\ t > currentTerm[i]
    /\ \E k \in Server \ {i} : currentTerm[k] >= t
    /\ currentTerm' = [currentTerm EXCEPT ![i] = t]
    /\ role' = [role EXCEPT ![i] = Follower]
    /\ UNCHANGED <<voteTerm, voteFor, log, commitIndex, confirmed, msgs, votes, leaders, ledLog, commits>>

\* A vote record counts only with a candidate in it.
Voted(i) == voteTerm[i] = currentTerm[i] /\ voteFor[i] # Nil

\* persistVote, first write: the vote record's term.
SetVoteTerm(i) ==
    /\ ~Voted(i)
    /\ voteTerm' = [voteTerm EXCEPT ![i] = currentTerm[i]]
    /\ UNCHANGED <<currentTerm, voteFor, log, role, commitIndex, confirmed, msgs, votes, leaders, ledLog, commits>>

UpToDate(m, i) ==
    \/ m.lastLogTerm > LastTerm(i)
    \/ m.lastLogTerm = LastTerm(i) /\ m.lastLogIndex >= Len(log[i])

\* persistVote, second write: the candidate. From here the vote exists.
SetVoteFor(i, c) ==
    /\ voteTerm[i] = currentTerm[i]
    /\ \A v \in votes : v.voter = i /\ v.term = voteTerm[i] => v.cand = c
    /\ \/ c = i /\ role[i] = Candidate
       \/ /\ c # i
          /\ \E m \in msgs :
                /\ m.type = "vote" /\ m.src = c /\ m.term = currentTerm[i]
                /\ UpToDate(m, i)
    /\ voteFor' = [voteFor EXCEPT ![i] = c]
    /\ votes' = votes \cup {[voter |-> i, term |-> voteTerm[i], cand |-> c]}
    /\ UNCHANGED <<currentTerm, voteTerm, log, role, commitIndex, confirmed, msgs, leaders, ledLog, commits>>

\* A granted reply states a vote the node holds or held.
GrantVote(i, c, t) ==
    /\ c # i
    /\ [voter |-> i, term |-> t, cand |-> c] \in votes
    /\ msgs' = msgs \cup {[type |-> "grant", src |-> i, dst |-> c, term |-> t]}
    /\ UNCHANGED <<durable, role, commitIndex, confirmed, votes, leaders, ledLog, commits>>

\* ledLog with term t set to l.
WithLed(t, l) == [u \in DOMAIN ledLog \cup {t} |-> IF u = t THEN l ELSE ledLog[u]]

Granted(i) ==
    {j \in Server \ {i} :
        [type |-> "grant", src |-> j, dst |-> i, term |-> currentTerm[i]] \in msgs}
    \cup (IF [voter |-> i, term |-> currentTerm[i], cand |-> i] \in votes THEN {i} ELSE {})

BecomeLeader(i) ==
    /\ role[i] = Candidate
    /\ IsQuorum(Granted(i))
    /\ role' = [role EXCEPT ![i] = Leader]
    /\ leaders' = leaders \cup {[server |-> i, term |-> currentTerm[i]]}
    /\ ledLog' = WithLed(currentTerm[i], log[i])
    /\ UNCHANGED <<durable, commitIndex, confirmed, msgs, votes, commits>>

----
\* Leader.

\* dispatchLogs: the leader stores entries of its own term.
LeaderAppend(i, es) ==
    /\ role[i] = Leader
    /\ Len(es) > 0
    /\ \A k \in 1..Len(es) : es[k].term = currentTerm[i]
    /\ log' = [log EXCEPT ![i] = @ \o es]
    /\ ledLog' = WithLed(currentTerm[i], log[i] \o es)
    /\ UNCHANGED <<currentTerm, voteTerm, voteFor, role, commitIndex, confirmed, msgs, votes, leaders, commits>>

\* The first c entries of l are committed: some committed prefix has them.
CommittedIn(l, c) ==
    \/ c = 0
    \/ /\ c <= Len(l)
       /\ \E k \in commits : c <= Len(k.entries) /\ SubSeq(k.entries, 1, c) = SubSeq(l, 1, c)

\* replicateTo, and heartbeat with p = n = c = 0: a request of term t from
\* the node that led t, with n entries after index p of the log it had as
\* that leader, and a commit index within what is committed of that log.
\* Nothing here depends on the sender's state now: the request is built by
\* a goroutine of its own and can be sent, like any message delivered,
\* after the node has stepped down or restarted.
SendAppend(i, j, t, p, n, c) ==
    /\ [server |-> i, term |-> t] \in leaders
    /\ j # i
    /\ p + n <= Len(ledLog[t])
    /\ CommittedIn(ledLog[t], c)
    /\ msgs' = msgs \cup {[type |-> "append", src |-> i, dst |-> j, term |-> t,
                           prevLogIndex |-> p, prevLogTerm |-> TermAt(ledLog[t], p),
                           entries |-> SubSeq(ledLog[t], p + 1, p + n), commit |-> c]}
    /\ UNCHANGED <<durable, role, commitIndex, confirmed, votes, leaders, ledLog, commits>>

Acked(i, t, c) ==
    {i} \cup {j \in Server \ {i} :
                 \E a \in msgs : /\ a.type = "ack" /\ a.src = j /\ a.dst = i
                                 /\ a.term = t /\ a.index >= c}

Committed(s, t) == [server |-> s, term |-> t, entries |-> SubSeq(log[s], 1, commitIndex'[s])]

\* The leader of term t commits an entry of that term that a quorum has
\* stored. Nothing here depends on its role now: the code moves the leader's
\* commit index in a later step of its main loop, by which time it may have
\* stepped down. What matters is that the entry is still in its log.
LeaderCommit(i, t, c) ==
    /\ [server |-> i, term |-> t] \in leaders
    /\ c > commitIndex[i]
    /\ c <= Len(log[i])
    /\ log[i][c].term = t
    /\ IsQuorum(Acked(i, t, c))
    /\ commitIndex' = [commitIndex EXCEPT ![i] = c]
    /\ commits' = commits \cup {Committed(i, t)}
    /\ UNCHANGED <<durable, role, confirmed, msgs, votes, leaders, ledLog>>

----
\* Follower, given an append request m addressed to it.

PrevOk(j, m) ==
    IF m.prevLogIndex = 0 THEN TRUE
    ELSE /\ m.prevLogIndex <= Len(log[j])
         /\ log[j][m.prevLogIndex].term = m.prevLogTerm

\* The first k entries of m are in j's log where m puts them.
HasFirst(j, m, k) ==
    \A q \in 1..k :
        /\ m.prevLogIndex + q <= Len(log[j])
        /\ log[j][m.prevLogIndex + q].term = m.entries[q].term

Confirm(j, t, k) == [confirmed EXCEPT ![j] = [term |-> t, index |-> k]]

\* appendEntries: delete the suffix that starts at the first conflict.
DeleteSuffix(j, m, k) ==
    /\ m \in msgs /\ m.type = "append" /\ m.dst = j
    /\ m.term = currentTerm[j]
    /\ PrevOk(j, m)
    /\ k \in 1..Len(m.entries)
    /\ HasFirst(j, m, k - 1)
    /\ m.prevLogIndex + k <= Len(log[j])
    /\ log[j][m.prevLogIndex + k].term # m.entries[k].term
    /\ log' = [log EXCEPT ![j] = SubSeq(@, 1, m.prevLogIndex + k - 1)]
    /\ confirmed' = Confirm(j, m.term, m.prevLogIndex + k - 1)
    /\ UNCHANGED <<currentTerm, voteTerm, voteFor, role, commitIndex, msgs, votes, leaders, ledLog, commits>>

\* appendEntries: store the entries of m from the k-th on, at the end of the log.
StoreEntries(j, m, k) ==
    /\ m \in msgs /\ m.type = "append" /\ m.dst = j
    /\ m.term = currentTerm[j]
    /\ PrevOk(j, m)
    /\ k \in 1..Len(m.entries)
    /\ HasFirst(j, m, k - 1)
    /\ m.prevLogIndex + k = Len(log[j]) + 1
    /\ log' = [log EXCEPT ![j] = @ \o SubSeq(m.entries, k, Len(m.entries))]
    /\ confirmed' = Confirm(j, m.term, m.prevLogIndex + Len(m.entries))
    /\ UNCHANGED <<currentTerm, voteTerm, voteFor, role, commitIndex, msgs, votes, leaders, ledLog, commits>>

\* A successful reply: j's log holds everything m carries.
Ack(j, m) ==
    /\ m \in msgs /\ m.type = "append" /\ m.dst = j
    /\ currentTerm[j] >= m.term
    /\ PrevOk(j, m)
    /\ HasFirst(j, m, Len(m.entries))
    /\ LET last == m.prevLogIndex + Len(m.entries)
       IN /\ msgs' = msgs \cup {[type |-> "ack", src |-> j, dst |-> m.src,
                                 term |-> m.term, index |-> last]}
          /\ confirmed' = Confirm(j, m.term,
                                  IF confirmed[j].term = m.term
                                  THEN Max(confirmed[j].index, last) ELSE last)
    /\ UNCHANGED <<durable, role, commitIndex, votes, leaders, ledLog, commits>>

\* The follower commits what the leader has committed, within the part of
\* its log that this leader has confirmed.
FollowerCommit(j, m, c) ==
    /\ m \in msgs /\ m.type = "append" /\ m.dst = j
    /\ m.term = confirmed[j].term
    /\ c > commitIndex[j]
    /\ c <= Min(m.commit, confirmed[j].index)
    /\ commitIndex' = [commitIndex EXCEPT ![j] = c]
    /\ commits' = commits \cup {Committed(j, m.term)}
    /\ UNCHANGED <<durable, role, confirmed, msgs, votes, leaders, ledLog>>

----
\* Process restart. Durable state survives. A vote record found on disk is
\* a vote, including one whose candidate was left over from an earlier term
\* by a kill between the two writes.
Restart(i) ==
    /\ role' = [role EXCEPT ![i] = Follower]
    /\ commitIndex' = [commitIndex EXCEPT ![i] = 0]
    /\ votes' = IF voteFor[i] # Nil
                THEN votes \cup {[voter |-> i, term |-> voteTerm[i], cand |-> voteFor[i]]}
                ELSE votes
    /\ UNCHANGED <<durable, confirmed, msgs, leaders, ledLog, commits>>

----
ProtoNext ==
    \/ \E i \in Server :
          \/ BecomeCandidate(i) \/ BecomeFollower(i) \/ BecomeLeader(i)
          \/ StartElection(i) \/ SetVoteTerm(i) \/ Restart(i)
          \/ \E t \in {currentTerm[k] : k \in Server} : AdoptTerm(i, t)
          \/ \E c \in Server : SetVoteFor(i, c)
          \/ \E v \in votes : v.voter = i /\ GrantVote(i, v.cand, v.term)
          \/ \E ty \in {"noop", "barrier"} : LeaderAppend(i, <<Entry(currentTerm[i], ty, Nil)>>)
          \/ \E v \in Values : LeaderAppend(i, <<Entry(currentTerm[i], "command", v)>>)
          \/ \E c \in 1..Len(log[i]), l \in leaders : l.server = i /\ LeaderCommit(i, l.term, c)
          \/ \E j \in Server, l \in leaders :
                /\ l.server = i
                /\ \E p, n, c \in 0..Len(ledLog[l.term]) : SendAppend(i, j, l.term, p, n, c)
    \/ \E m \in msgs :
          /\ m.type = "append"
          /\ \/ Ack(m.dst, m)
             \/ \E k \in 1..Len(m.entries) : DeleteSuffix(m.dst, m, k) \/ StoreEntries(m.dst, m, k)
             \/ \E c \in 1..m.commit : FollowerCommit(m.dst, m, c)

Next == ProtoNext
Spec == Init /\ [][Next]_vars

----
\* Safety properties.

\* At most one server is elected in a term.
ElectionSafety ==
    \A a, b \in leaders : a.term = b.term => a.server = b.server

\* A node's vote record never names two candidates in one term.
OneVotePerTerm ==
    \A a, b \in votes : a.voter = b.voter /\ a.term = b.term => a.cand = b.cand

\* Equal terms at an index imply equal prefixes.
LogMatching ==
    \A a, b \in Server :
        \A k \in 1..Min(Len(log[a]), Len(log[b])) :
            log[a][k].term = log[b][k].term =>
                SubSeq(log[a], 1, k) = SubSeq(log[b], 1, k)

\* Two committed prefixes never disagree.
StateMachineSafety ==
    \A a, b \in commits : IsPrefix(a.entries, b.entries) \/ IsPrefix(b.entries, a.entries)

\* A leader holds every prefix committed from the log of an earlier leader.
LeaderCompleteness ==
    \A i \in Server, c \in commits :
        role[i] = Leader /\ c.term < currentTerm[i] => IsPrefix(c.entries, log[i])

\* A server keeps every prefix it committed.
CommittedEntriesPreserved ==
    \A c \in commits : IsPrefix(c.entries, log[c.server])

\* Three invariants a proof will lean on, checked along with the properties.
\* A leader's log is its term's leader log.
LeaderLogIsLed ==
    \A i \in Server : role[i] = Leader =>
        /\ currentTerm[i] \in DOMAIN ledLog
        /\ log[i] = ledLog[currentTerm[i]]

\* What a leader has confirmed of a node's log is in that log.
ConfirmedWithinLog ==
    \A i \in Server : confirmed[i].index <= Len(log[i])

\* Every request carries a segment of its term's leader log, and a commit
\* index that covers only committed entries of it.
RequestsFromLed ==
    \A m \in msgs : m.type = "append" =>
        /\ m.term \in DOMAIN ledLog
        /\ m.prevLogIndex + Len(m.entries) <= Len(ledLog[m.term])
        /\ m.prevLogTerm = TermAt(ledLog[m.term], m.prevLogIndex)
        /\ m.entries = SubSeq(ledLog[m.term], m.prevLogIndex + 1, m.prevLogIndex + Len(m.entries))
        /\ CommittedIn(ledLog[m.term], m.commit)

\* A node's term never decreases.
TermMonotonic ==
    [][\A i \in Server : currentTerm'[i] >= currentTerm[i]]_vars
====
