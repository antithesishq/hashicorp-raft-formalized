---- MODULE RaftLog ----
\* The follower's actions on an append request: Ack, DeleteSuffix, StoreEntries.
EXTENDS RaftExt

\* What an append request says about its term's leader log.
LEMMA AppendFacts ==
    ASSUME TypeOK, LeadersInv, AppendInv, LogsInv, NEW m \in msgs, m.type = "append"
    PROVE  /\ m.src \in Server /\ m.dst \in Server /\ m.dst # m.src
           /\ [server |-> m.src, term |-> m.term] \in leaders
           /\ m.term \in Nat /\ m.term \in DOMAIN ledLog /\ ledLog[m.term] \in Seq(EntryT)
           /\ LMc(ledLog, ledLog[m.term])
           /\ m.prevLogIndex \in Nat /\ m.entries \in Seq(EntryT)
           /\ m.prevLogIndex + Len(m.entries) <= Len(ledLog[m.term])
           /\ m.prevLogTerm = TermAt(ledLog[m.term], m.prevLogIndex)
           /\ \A q \in 1..Len(m.entries) : m.entries[q] = ledLog[m.term][m.prevLogIndex + q]
<1>1. /\ m.src \in Server /\ m.dst \in Server /\ m.dst # m.src
      /\ [server |-> m.src, term |-> m.term] \in leaders
      /\ m.prevLogIndex \in Nat /\ m.entries \in Seq(EntryT)
      /\ m.prevLogIndex + Len(m.entries) <= Len(ledLog[m.term])
      /\ m.prevLogTerm = TermAt(ledLog[m.term], m.prevLogIndex)
      /\ \A q \in 1..Len(m.entries) : m.entries[q] = ledLog[m.term][m.prevLogIndex + q]
  BY DEF AppendInv
<1>2. m.term \in DOMAIN ledLog BY <1>1 DEF LeadersInv
<1>3. m.term \in Nat /\ ledLog[m.term] \in Seq(EntryT) BY <1>2 DEF TypeOK
<1>4. LMc(ledLog, ledLog[m.term]) BY <1>2 DEF LogsInv, LMlog
<1> QED BY <1>1, <1>2, <1>3, <1>4

\* A node that has the entry before a request and the first k entries of
\* the request has the leader log of the request's term up to there.
LEMMA PrefixAgree ==
    ASSUME TypeOK, LeadersInv, AppendInv, LogsInv, NEW j \in Server,
           NEW m \in msgs, m.type = "append", PrevOk(j, m),
           NEW k \in Nat, k <= Len(m.entries), HasFirst(j, m, k),
           NEW r \in Nat, r = m.prevLogIndex + k
    PROVE  /\ r <= Len(log[j]) /\ r <= Len(ledLog[m.term])
           /\ \A q \in 1..r : log[j][q] = ledLog[m.term][q]
<1> DEFINE T == m.term
<1> DEFINE p == m.prevLogIndex
<1>a. /\ T \in DOMAIN ledLog /\ ledLog[T] \in Seq(EntryT) /\ LMc(ledLog, ledLog[T])
      /\ p \in Nat /\ m.entries \in Seq(EntryT)
      /\ p + Len(m.entries) <= Len(ledLog[T])
      /\ m.prevLogTerm = TermAt(ledLog[T], p)
      /\ \A q \in 1..Len(m.entries) : m.entries[q] = ledLog[T][p + q]
  BY AppendFacts
<1>b. log[j] \in Seq(EntryT) /\ LMc(ledLog, log[j]) BY DEF TypeOK, LogsInv, LMlog
<1>1. CASE r = 0
  <2>1. Len(log[j]) \in Nat /\ Len(ledLog[T]) \in Nat BY <1>a, <1>b
  <2>2. \A q \in 1..r : FALSE BY <1>1
  <2> QED BY <1>1, <2>1, <2>2
<1>2. CASE r > 0
  <2>1. r <= Len(log[j]) /\ r <= Len(ledLog[T]) /\ log[j][r].term = ledLog[T][r].term
    <3>1. CASE k = 0
      <4>1. r = p /\ p # 0 BY <3>1, <1>2, <1>a
      <4>2. p <= Len(log[j]) /\ log[j][p].term = m.prevLogTerm BY <4>1 DEF PrevOk
      <4>3. p <= Len(ledLog[T]) /\ p > 0 BY <4>1, <1>a
      <4>4. TermAt(ledLog[T], p) = ledLog[T][p].term BY <4>3 DEF TermAt
      <4> QED BY <4>1, <4>2, <4>3, <4>4, <1>a
    <3>2. CASE k > 0
      <4>1. k \in 1..k /\ k \in 1..Len(m.entries) BY <3>2, <1>a
      <4>2. p + k <= Len(log[j]) /\ log[j][p + k].term = m.entries[k].term
        BY <4>1 DEF HasFirst
      <4>3. m.entries[k] = ledLog[T][p + k] BY <4>1, <1>a
      <4> QED BY <4>2, <4>3, <1>a
    <3> QED BY <3>1, <3>2
  <2>2. r \in 1..Len(log[j]) /\ r \in 1..Len(ledLog[T]) BY <2>1, <1>2, <1>a, <1>b
  <2>3. \A q \in 1..r : log[j][q] = ledLog[T][q] BY <2>1, <2>2, <1>a, <1>b, Match
  <2> QED BY <2>1, <2>3
<1> QED BY <1>1, <1>2

LEMMA AckActInv == ASSUME Inv, NEW j \in Server, NEW m, Ack(j, m) PROVE Inv'
<1> DEFINE T == m.term
<1> DEFINE last == m.prevLogIndex + Len(m.entries)
<1> DEFINE ni == IF confirmed[j].term = T THEN Max(confirmed[j].index, last) ELSE last
<1> DEFINE a == [type |-> "ack", src |-> j, dst |-> m.src, term |-> T, index |-> last]
<1>0. /\ m \in msgs /\ m.type = "append" /\ m.dst = j /\ currentTerm[j] = T
      /\ PrevOk(j, m) /\ HasFirst(j, m, Len(m.entries))
      /\ msgs' = msgs \cup {a}
      /\ confirmed' = [confirmed EXCEPT ![j] = [term |-> T, index |-> ni]]
      /\ UNCHANGED <<transfer, durable, role, commitIndex, lastApplied, votes, leaders, ledLog,
                     commits, applied>>
  BY DEF Ack, Confirm
<1>a. /\ TypeOK /\ TermInv /\ VotesInv /\ LeadersInv /\ AppendInv /\ LogsInv /\ AckInv
      /\ ConfirmedInv /\ AckerInv /\ VoterInv /\ QuorumInv
  BY DEF Inv
<1>b. /\ T \in Nat /\ T \in DOMAIN ledLog /\ ledLog[T] \in Seq(EntryT)
      /\ m.prevLogIndex \in Nat /\ m.entries \in Seq(EntryT) /\ last \in Nat
      /\ log[j] \in Seq(EntryT)
  <2>1. /\ m.term \in Nat /\ m.term \in DOMAIN ledLog /\ ledLog[m.term] \in Seq(EntryT)
        /\ m.prevLogIndex \in Nat /\ m.entries \in Seq(EntryT)
    BY <1>0, <1>a, AppendFacts
  <2> QED BY <2>1, <1>a DEF TypeOK
<1>c. /\ last <= Len(log[j]) /\ last <= Len(ledLog[T])
      /\ \A q \in 1..last : log[j][q] = ledLog[T][q]
  <2>1. Len(m.entries) \in Nat /\ Len(m.entries) <= Len(m.entries) BY <1>b
  <2> QED BY <1>0, <1>a, <1>b, <2>1, PrefixAgree
<1>d. a.type = "ack" /\ a.src = j /\ a.term = T /\ a.index = last OBVIOUS
<1>e. /\ confirmed[j].term \in Nat /\ confirmed[j].index \in Nat /\ ni \in Nat
      /\ \/ ni = last
         \/ ni = confirmed[j].index /\ confirmed[j].term = T
  BY <1>a, <1>b DEF TypeOK, Max
<1>f. \A jj, t, c : IsAcker(jj, t, c)' /\ ~IsAcker(jj, t, c) => jj = j /\ t = T /\ last >= c
  BY <1>0, <1>d DEF IsAcker, durable
<1>g. \A v \in votes : v.voter = j => v.term \in Nat /\ v.term <= T
  <2> SUFFICES ASSUME NEW v \in votes, v.voter = j PROVE v.term \in Nat /\ v.term <= T
    OBVIOUS
  <2>1. v.term \in Nat /\ v.term <= voteTerm[j] /\ voteTerm[j] \in Nat /\ voteTerm[j] <= currentTerm[j]
    BY <1>a DEF TypeOK, VotesInv, TermInv
  <2> QED BY <2>1, <1>0, <1>b
<1> HIDE DEF T, last, ni, a
<1>1. TypeOK'
  <2>1. confirmed' \in [Server -> [term : Nat, index : Nat]] BY <1>0, <1>a, <1>b, <1>e DEF TypeOK
  <2> QED BY <2>1, <1>0, <1>a DEF TypeOK, durable
<1>2. AckInv'
  <2> SUFFICES ASSUME NEW x \in msgs', x.type = "ack"
               PROVE  /\ x.src \in Server /\ x.term \in DOMAIN ledLog /\ x.index \in Nat
                      /\ x.index <= Len(ledLog[x.term])
                      /\ x.term <= currentTerm[x.src]
    BY <1>0 DEF AckInv, durable
  <2>1. CASE x \in msgs BY <2>1, <1>a DEF AckInv
  <2>2. CASE x = a BY <2>2, <1>0, <1>b, <1>c, <1>d
  <2> QED BY <2>1, <2>2, <1>0
<1>3. ConfirmedInv'
  <2> SUFFICES ASSUME NEW jj \in Server
               PROVE  /\ confirmed'[jj].term <= currentTerm[jj]
                      /\ confirmed'[jj].index <= Len(log[jj])
                      /\ confirmed'[jj].index > 0 =>
                            /\ confirmed'[jj].term \in DOMAIN ledLog
                            /\ confirmed'[jj].index <= Len(ledLog[confirmed'[jj].term])
                            /\ \A q \in 1..confirmed'[jj].index : log[jj][q] = ledLog[confirmed'[jj].term][q]
    BY <1>0 DEF ConfirmedInv, durable
  <2>1. CASE jj # j
    <3>1. confirmed'[jj] = confirmed[jj] BY <2>1, <1>0, <1>a DEF TypeOK
    <3> QED BY <3>1, <1>a DEF ConfirmedInv
  <2>2. CASE jj = j
    <3>1. confirmed'[j].term = T /\ confirmed'[j].index = ni BY <1>0, <1>a DEF TypeOK
    <3>2. CASE ni = last BY <3>1, <3>2, <2>2, <1>0, <1>b, <1>c
    <3>3. CASE ni = confirmed[j].index /\ confirmed[j].term = T
      BY <3>1, <3>3, <2>2, <1>a DEF ConfirmedInv
    <3> QED BY <3>2, <3>3, <1>e
  <2> QED BY <2>1, <2>2
<1>4. AckerInv'
  <2> SUFFICES ASSUME NEW jj \in Server, NEW t \in DOMAIN ledLog, NEW c \in 1..Len(ledLog[t]),
                      ledLog[t][c].term = t, IsAcker(jj, t, c)',
                      \A w \in DOMAIN ledLog : t < w /\ w <= currentTerm[jj] => Has(ledLog[w], c, t)
               PROVE  Has(log[jj], c, t)
    BY <1>0 DEF AckerInv, Has, durable
  <2>1. CASE IsAcker(jj, t, c) BY <2>1, <1>a DEF AckerInv
  <2>2. CASE ~IsAcker(jj, t, c)
    <3>1. jj = j /\ t = T /\ last >= c BY <2>2, <1>f
    <3>2. c \in 1..last /\ c <= Len(log[j]) BY <3>1, <1>b, <1>c
    <3>3. log[j][c] = ledLog[T][c] BY <3>2, <1>c
    <3> QED BY <3>1, <3>2, <3>3 DEF Has
  <2> QED BY <2>1, <2>2
<1>5. VoterInv'
  <2> SUFFICES ASSUME NEW v \in votes, NEW t \in DOMAIN ledLog, NEW c \in 1..Len(ledLog[t]),
                      t < v.term, v.term \notin DOMAIN ledLog, ledLog[t][c].term = t,
                      IsAcker(v.voter, t, c)', Between(t, c, v.term)
               PROVE  \E x \in msgs' : /\ x.type = "vote" /\ x.src = v.cand /\ x.term = v.term
                                       /\ \/ x.lastLogTerm > t
                                          \/ x.lastLogTerm = t /\ x.lastLogIndex >= c
    BY <1>0 DEF VoterInv, Between, Has, durable
  <2>1. CASE IsAcker(v.voter, t, c)
    <3>1. \E x \in msgs : /\ x.type = "vote" /\ x.src = v.cand /\ x.term = v.term
                          /\ \/ x.lastLogTerm > t
                             \/ x.lastLogTerm = t /\ x.lastLogIndex >= c
      BY <2>1, <1>a DEF VoterInv
    <3> QED BY <3>1, <1>0
  <2>2. CASE ~IsAcker(v.voter, t, c)
    <3>1. v.voter = j /\ t = T BY <2>2, <1>f
    <3>2. v.term \in Nat /\ v.term <= T BY <3>1, <1>g
    <3> QED BY <3>1, <3>2, <1>b
  <2> QED BY <2>1, <2>2
<1>6. QuorumInv'
  <2> SUFFICES ASSUME NEW l \in leaders
               PROVE  \E Q \in SUBSET Server :
                         /\ IsQuorum(Q)
                         /\ \A jj \in Q : /\ [voter |-> jj, term |-> l.term, cand |-> l.server] \in votes
                                          /\ Good(jj, l.term)'
    BY <1>0 DEF QuorumInv, durable
  <2>1. PICK Q \in SUBSET Server :
           /\ IsQuorum(Q)
           /\ \A jj \in Q : /\ [voter |-> jj, term |-> l.term, cand |-> l.server] \in votes
                            /\ Good(jj, l.term)
    BY <1>a DEF QuorumInv
  <2>2. ASSUME NEW jj \in Q PROVE Good(jj, l.term)'
    <3> DEFINE u == l.term
    <3> SUFFICES ASSUME NEW t \in DOMAIN ledLog, NEW c \in 1..Len(ledLog[t]),
                        t < u, ledLog[t][c].term = t, IsAcker(jj, t, c)', Between(t, c, u)
                 PROVE  Has(ledLog[u], c, t)
      BY <1>0 DEF Good, Between, Has, durable
    <3>1. CASE IsAcker(jj, t, c) BY <3>1, <2>1 DEF Good
    <3>2. CASE ~IsAcker(jj, t, c)
      <4>1. jj = j /\ t = T BY <3>2, <1>f
      <4>2. [voter |-> jj, term |-> u, cand |-> l.server] \in votes BY <2>1
      <4>3. u \in Nat /\ u <= T BY <4>1, <4>2, <1>g
      <4> QED BY <4>1, <4>3, <1>b
    <3> QED BY <3>1, <3>2
  <2> QED BY <2>1, <2>2
<1>7. /\ msgs \subseteq msgs' /\ a.type # "vote" /\ a.type # "append"
      /\ \A x \in msgs' \ msgs : x.type # "grant"
      /\ votes \subseteq votes'
  BY <1>0, <1>d DEF a, durable
<1> QED
  BY <1>0, <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, TermInvUnch, VotesInvUnch, OneVoteUnch,
     VoteReqInvMsg, GrantInvMono, LeadersInvUnch, ElectionSafetyUnch, LogsInvUnch, AppendInvMsg,
     CommitsInvMono, CommitIndexInvUnch, AppliedInvUnch DEF Inv, durable
====
