---- MODULE RaftElect ----
\* BecomeLeader.
EXTENDS RaftAppend

LEMMA BecomeLeaderInv ==
    ASSUME IsFiniteSet(Server), Inv, NEW i \in Server, BecomeLeader(i)
    PROVE  Inv'
<1> DEFINE u == currentTerm[i]
<1> DEFINE nlr == [server |-> i, term |-> u]
<1>0. /\ role[i] = Candidate /\ IsQuorum(Granted(i))
      /\ role' = [role EXCEPT ![i] = Leader]
      /\ leaders' = leaders \cup {nlr}
      /\ ledLog' = WithLed(u, log[i])
      /\ UNCHANGED <<durable, commitIndex, lastApplied, confirmed, msgs, votes, commits, applied>>
  BY DEF BecomeLeader
<1>a. /\ TypeOK /\ TermInv /\ VotesInv /\ OneVotePerTerm /\ VoteReqInv /\ GrantInv /\ LeadersInv
      /\ ElectionSafety /\ LogsInv /\ AckInv /\ AckerInv /\ VoterInv /\ QuorumInv
  BY DEF Inv
<1>b. /\ Granted(i) \in SUBSET Server
      /\ \A jj \in Granted(i) : [voter |-> jj, term |-> u, cand |-> i] \in votes
  <2>1. Granted(i) \in SUBSET Server BY DEF Granted
  <2>2. ASSUME NEW jj \in Granted(i) PROVE [voter |-> jj, term |-> u, cand |-> i] \in votes
    <3>1. CASE jj \in Server \ {i} /\ [type |-> "grant", src |-> jj, dst |-> i, term |-> u] \in msgs
      <4> DEFINE g == [type |-> "grant", src |-> jj, dst |-> i, term |-> u]
      <4>1. g \in msgs /\ g.type = "grant" /\ g.src = jj /\ g.dst = i /\ g.term = u BY <3>1
      <4> HIDE DEF g
      <4> QED BY <4>1, <1>a DEF GrantInv
    <3>2. CASE jj = i /\ [voter |-> i, term |-> u, cand |-> i] \in votes BY <3>2
    <3> QED BY <3>1, <3>2 DEF Granted
  <2> QED BY <2>1, <2>2
<1>c. u \in Nat /\ u >= 2 /\ log[i] \in Seq(EntryT) /\ nlr.server = i /\ nlr.term = u
  <2>1. PICK jj \in Granted(i) : TRUE BY <1>0, <1>b, QuorumNonEmpty
  <2>2. [voter |-> jj, term |-> u, cand |-> i] \in votes BY <1>b
  <2>3. [voter |-> jj, term |-> u, cand |-> i].term >= 2 BY <2>2, <1>a DEF VotesInv
  <2> QED BY <2>3, <1>a DEF TypeOK
<1>d. /\ DOMAIN ledLog' = DOMAIN ledLog \cup {u} /\ ledLog'[u] = log[i]
      /\ \A w \in DOMAIN ledLog : w # u => ledLog'[w] = ledLog[w]
      /\ ledLog' = [t \in DOMAIN ledLog' |-> ledLog'[t]]
  BY <1>0 DEF WithLed
<1>1. CASE u \in DOMAIN ledLog
  <2>1. PICK l \in leaders : l.term = u BY <1>1, <1>a DEF LeadersInv
  <2>2. PICK Q \in SUBSET Server :
           /\ IsQuorum(Q)
           /\ \A jj \in Q : [voter |-> jj, term |-> u, cand |-> l.server] \in votes
    BY <2>1, <1>a DEF QuorumInv
  <2>3. PICK jj \in Q : jj \in Granted(i) BY <2>2, <1>0, <1>b, QuorumIntersect
  <2>4. l.server = i
    <3> DEFINE v1 == [voter |-> jj, term |-> u, cand |-> l.server]
    <3> DEFINE v2 == [voter |-> jj, term |-> u, cand |-> i]
    <3>1. v1 \in votes /\ v2 \in votes /\ v1.voter = v2.voter /\ v1.term = v2.term
      BY <2>2, <2>3, <1>b
    <3>2. v1.cand = v2.cand BY <3>1, <1>a DEF OneVotePerTerm
    <3> QED BY <3>2
  <2>5. l = nlr BY <2>1, <2>4, <1>a DEF TypeOK
  <2>6. leaders' = leaders BY <2>5, <1>0
  <2>7. log[i] = ledLog[u] BY <2>1, <2>4, <1>a DEF LeadersInv
  <2>8. ledLog' = ledLog
    <3>1. ledLog = [t \in DOMAIN ledLog |-> ledLog[t]] BY <1>a DEF TypeOK
    <3>2. DOMAIN ledLog' = DOMAIN ledLog BY <1>1, <1>d
    <3>3. \A t \in DOMAIN ledLog : ledLog'[t] = ledLog[t] BY <2>7, <1>d
    <3> QED BY <3>1, <3>2, <3>3, <1>d
  <2>9. TypeOK' BY <2>6, <2>8, <1>0, <1>a DEF TypeOK, Leader, durable
  <2>10. LeadersInv'
    <3>1. \A j \in Server : role'[j] = Leader => [server |-> j, term |-> currentTerm[j]] \in leaders
      <4> SUFFICES ASSUME NEW j \in Server, role'[j] = Leader
                   PROVE  [server |-> j, term |-> currentTerm[j]] \in leaders
        OBVIOUS
      <4>1. CASE j = i BY <4>1, <2>5
      <4>2. CASE j # i
        <5>1. role[j] = Leader BY <4>2, <1>0, <1>a DEF TypeOK
        <5> QED BY <5>1, <1>a DEF LeadersInv
      <4> QED BY <4>1, <4>2
    <3> QED BY <3>1, <2>6, <2>8, <1>0, <1>a DEF LeadersInv, durable
  <2> QED BY <2>6, <2>8, <2>9, <2>10, <1>0, InvLocal DEF durable
<1>2. CASE u \notin DOMAIN ledLog
  <2>a. \A w \in DOMAIN ledLog : w # u /\ ledLog'[w] = ledLog[w] /\ w \in DOMAIN ledLog'
    BY <1>2, <1>d
  <2>b. \A l \in leaders : l.term # u BY <1>2, <1>a DEF LeadersInv
  <2>c. \A k \in 1..Len(log[i]) : log[i][k].term \in Nat /\ log[i][k].term < u
    <3> SUFFICES ASSUME NEW k \in 1..Len(log[i]) PROVE log[i][k].term \in Nat /\ log[i][k].term < u
      OBVIOUS
    <3>1. log[i][k] \in EntryT BY <1>c, ElementOfSeq
    <3>2. log[i][k].term <= u /\ LMc(ledLog, log[i]) BY <1>a DEF LogsInv, LMlog
    <3>3. log[i][k].term # u
      <4> SUFFICES ASSUME log[i][k].term = u PROVE FALSE OBVIOUS
      <4>1. log[i][k].term # 1 BY <1>c
      <4>2. log[i][k].term \in DOMAIN ledLog BY <4>1, <3>2, TermHasLeader
      <4> QED BY <4>2, <1>2
    <3> QED BY <3>1, <3>2, <3>3, <1>c DEF EntryT
  <2>d. LedExt /\ LogExt
    <3>1. \A w \in DOMAIN ledLog : ledLog[w] \in Seq(EntryT) BY <1>a DEF TypeOK
    <3>2. \A jj \in Server : log[jj] \in Seq(EntryT) /\ log'[jj] = log[jj]
      BY <1>0, <1>a DEF TypeOK, durable
    <3> QED BY <3>1, <3>2, <2>a DEF LedExt, LogExt
  <2>e. \A jj, t, c : t # u => (IsAcker(jj, t, c)' <=> IsAcker(jj, t, c))
    BY <1>0, <1>c DEF IsAcker
  <2>f. \A t \in DOMAIN ledLog' : \A c \in 1..Len(ledLog'[t]) :
           ledLog'[t][c].term = t => t \in DOMAIN ledLog /\ t # u /\ ledLog'[t] = ledLog[t]
    <3> SUFFICES ASSUME NEW t \in DOMAIN ledLog', NEW c \in 1..Len(ledLog'[t]),
                        ledLog'[t][c].term = t, t = u
                 PROVE  FALSE
      BY <1>d, <2>a
    <3>1. c \in 1..Len(log[i]) /\ log[i][c].term = u BY <1>d
    <3> QED BY <3>1, <2>c
  <2>1. TypeOK'
    <3>1. role' \in [Server -> {Follower, Candidate, Leader}] BY <1>0, <1>a DEF TypeOK
    <3>2. leaders' \subseteq [server : Server, term : Nat] BY <1>0, <1>a, <1>c DEF TypeOK
    <3>3. DOMAIN ledLog' \subseteq Nat BY <1>d, <1>c, <1>a DEF TypeOK
    <3>4. \A t \in DOMAIN ledLog' : ledLog'[t] \in Seq(EntryT)
      BY <1>d, <1>c, <2>a, <1>a DEF TypeOK
    <3> QED BY <3>1, <3>2, <3>3, <3>4, <1>d, <1>0, <1>a DEF TypeOK, durable
  <2>2. VoteReqInv'
    <3> SUFFICES ASSUME NEW a \in msgs, a.type = "vote",
                        a.term = currentTerm[a.src], a.term \notin DOMAIN ledLog'
                 PROVE  a.lastLogIndex = Len(log[a.src]) /\ a.lastLogTerm = LastTerm(a.src)
      BY <1>0, <1>a DEF VoteReqInv, LastTerm, TermAt, durable
    <3>1. a.term \notin DOMAIN ledLog BY <1>d
    <3> QED BY <3>1, <1>a DEF VoteReqInv
  <2>3. LeadersInv'
    <3>1. ASSUME NEW l \in leaders'
          PROVE  /\ l.term <= currentTerm[l.server]
                 /\ l.term \in DOMAIN ledLog'
                 /\ currentTerm[l.server] = l.term => log[l.server] = ledLog'[l.term]
      <4>1. CASE l \in leaders
        <5>1. /\ l.term <= currentTerm[l.server]
              /\ l.term \in DOMAIN ledLog
              /\ currentTerm[l.server] = l.term => log[l.server] = ledLog[l.term]
          BY <4>1, <1>a DEF LeadersInv
        <5> QED BY <5>1, <2>a
      <4>2. CASE l = nlr BY <4>2, <1>c, <1>d
      <4> QED BY <4>1, <4>2, <1>0
    <3>2. ASSUME NEW t \in DOMAIN ledLog' PROVE t >= 2 /\ \E l \in leaders' : l.term = t
      <4>1. CASE t \in DOMAIN ledLog BY <4>1, <1>0, <1>a DEF LeadersInv
      <4>2. CASE t = u
        <5>1. nlr \in leaders' /\ nlr.term = t BY <4>2, <1>0, <1>c
        <5> QED BY <5>1, <4>2, <1>c
      <4> QED BY <4>1, <4>2, <1>d
    <3>3. ASSUME NEW j \in Server, role'[j] = Leader
          PROVE  [server |-> j, term |-> currentTerm[j]] \in leaders'
      <4>1. CASE j = i BY <4>1, <1>0
      <4>2. CASE j # i
        <5>1. role[j] = Leader BY <4>2, <3>3, <1>0, <1>a DEF TypeOK
        <5> QED BY <5>1, <1>0, <1>a DEF LeadersInv
      <4> QED BY <4>1, <4>2
    <3> QED BY <3>1, <3>2, <3>3, <1>0 DEF LeadersInv, durable
  <2>4. ElectionSafety'
    <3> SUFFICES ASSUME NEW a \in leaders', NEW b \in leaders', a.term = b.term
                 PROVE  a.server = b.server
      BY DEF ElectionSafety
    <3>1. CASE a \in leaders /\ b \in leaders BY <3>1, <1>a DEF ElectionSafety
    <3>2. CASE a = nlr /\ b = nlr BY <3>2
    <3>3. CASE a = nlr /\ b \in leaders BY <3>3, <2>b, <1>c
    <3>4. CASE b = nlr /\ a \in leaders BY <3>4, <2>b, <1>c
    <3> QED BY <3>1, <3>2, <3>3, <3>4, <1>0
  <2>5. LogsInv'
    <3>0. 1 \notin DOMAIN ledLog' BY <1>d, <1>c, <1>a DEF LeadersInv
    <3>1. \A w \in DOMAIN ledLog : /\ ledLog[w] \in Seq(EntryT) /\ ledLog'[w] \in Seq(EntryT)
                                   /\ Len(ledLog[w]) <= Len(ledLog'[w])
                                   /\ \A q \in 1..Len(ledLog[w]) : ledLog'[w][q] = ledLog[w][q]
      BY <2>a, <1>a DEF TypeOK
    <3>2. ASSUME NEW X \in Seq(EntryT), LMc(ledLog, X) PROVE LMc(ledLog', X)
      BY <3>0, <3>1, <3>2, <1>d, LMExt
    <3>3. ASSUME NEW j \in Server
          PROVE  /\ LMc(ledLog', log[j]) /\ Mono(log[j])
                 /\ \A k \in 1..Len(log[j]) : log[j][k].term <= currentTerm[j]
      <4>1. log[j] \in Seq(EntryT) BY <1>a DEF TypeOK
      <4>2. LMc(ledLog, log[j]) /\ Mono(log[j])
            /\ \A k \in 1..Len(log[j]) : log[j][k].term <= currentTerm[j]
        BY <1>a DEF LogsInv, LMlog
      <4> QED BY <4>1, <4>2, <3>2
    <3>4. ASSUME NEW t \in DOMAIN ledLog'
          PROVE  /\ LMc(ledLog', ledLog'[t]) /\ Mono(ledLog'[t])
                 /\ \A k \in 1..Len(ledLog'[t]) : ledLog'[t][k].term <= t
      <4>1. CASE t = u
        <5>1. ledLog'[t] = log[i] BY <4>1, <1>d
        <5> QED BY <5>1, <4>1, <3>3
      <4>2. CASE t \in DOMAIN ledLog
        <5>1. ledLog'[t] = ledLog[t] /\ ledLog[t] \in Seq(EntryT) BY <4>2, <2>a, <1>a DEF TypeOK
        <5>2. LMc(ledLog, ledLog[t]) /\ Mono(ledLog[t])
              /\ \A k \in 1..Len(ledLog[t]) : ledLog[t][k].term <= t
          BY <4>2, <1>a DEF LogsInv, LMlog
        <5> QED BY <5>1, <5>2, <3>2
      <4> QED BY <4>1, <4>2, <1>d
    <3> QED BY <3>3, <3>4, <1>0 DEF LogsInv, LMlog, durable
  <2>6. AckerInv'
    <3> SUFFICES ASSUME NEW jj \in Server, NEW t \in DOMAIN ledLog', NEW c \in 1..Len(ledLog'[t]),
                        ledLog'[t][c].term = t, IsAcker(jj, t, c)',
                        \A w \in DOMAIN ledLog' : t < w /\ w <= currentTerm[jj] => Has(ledLog'[w], c, t)
                 PROVE  Has(log[jj], c, t)
      BY <1>0 DEF AckerInv, Has, durable
    <3>1. t \in DOMAIN ledLog /\ t # u /\ ledLog'[t] = ledLog[t] BY <2>f
    <3>2. IsAcker(jj, t, c) BY <3>1, <2>e
    <3>3. \A w \in DOMAIN ledLog : t < w /\ w <= currentTerm[jj] => Has(ledLog[w], c, t)
      BY <2>a
    <3> QED BY <3>1, <3>2, <3>3, <1>a DEF AckerInv
  <2>7. VoterInv'
    <3> SUFFICES ASSUME NEW v \in votes, NEW t \in DOMAIN ledLog', NEW c \in 1..Len(ledLog'[t]),
                        t < v.term, v.term \notin DOMAIN ledLog', ledLog'[t][c].term = t,
                        IsAcker(v.voter, t, c)', Between(t, c, v.term)'
                 PROVE  \E x \in msgs : /\ x.type = "vote" /\ x.src = v.cand /\ x.term = v.term
                                        /\ \/ x.lastLogTerm > t
                                           \/ x.lastLogTerm = t /\ x.lastLogIndex >= c
      BY <1>0 DEF VoterInv, durable
    <3>1. t \in DOMAIN ledLog /\ t # u /\ ledLog'[t] = ledLog[t] BY <2>f
    <3>2. IsAcker(v.voter, t, c) BY <3>1, <2>e
    <3>3. Between(t, c, v.term) BY <2>a DEF Between
    <3>4. v.term \notin DOMAIN ledLog BY <1>d
    <3> QED BY <3>1, <3>2, <3>3, <3>4, <1>a DEF VoterInv
  <2>8. QuorumInv'
    <3> SUFFICES ASSUME NEW l \in leaders'
                 PROVE  \E Q \in SUBSET Server :
                           /\ IsQuorum(Q)
                           /\ \A jj \in Q : /\ [voter |-> jj, term |-> l.term, cand |-> l.server] \in votes
                                            /\ Good(jj, l.term)'
      BY <1>0 DEF QuorumInv, durable
    <3>1. CASE l \in leaders
      <4>1. PICK Q \in SUBSET Server :
               /\ IsQuorum(Q)
               /\ \A jj \in Q : /\ [voter |-> jj, term |-> l.term, cand |-> l.server] \in votes
                                /\ Good(jj, l.term)
        BY <3>1, <1>a DEF QuorumInv
      <4>2. ASSUME NEW jj \in Q PROVE Good(jj, l.term)'
        <5> DEFINE lt == l.term
        <5> SUFFICES ASSUME NEW t \in DOMAIN ledLog', NEW c \in 1..Len(ledLog'[t]),
                            t < lt, ledLog'[t][c].term = t, IsAcker(jj, t, c)', Between(t, c, lt)'
                     PROVE  Has(ledLog'[lt], c, t)
          BY DEF Good
        <5>1. t \in DOMAIN ledLog /\ t # u /\ ledLog'[t] = ledLog[t] BY <2>f
        <5>2. IsAcker(jj, t, c) BY <5>1, <2>e
        <5>3. Between(t, c, lt) BY <2>a DEF Between
        <5>4. lt \in DOMAIN ledLog /\ ledLog'[lt] = ledLog[lt] BY <3>1, <2>a, <1>a DEF LeadersInv
        <5>5. Has(ledLog[lt], c, t) BY <5>1, <5>2, <5>3, <4>1 DEF Good
        <5> QED BY <5>4, <5>5
      <4> QED BY <4>1, <4>2
    <3>2. CASE l = nlr
      <4>1. ASSUME NEW jj \in Granted(i) PROVE Good(jj, u)'
        <5> SUFFICES ASSUME NEW t \in DOMAIN ledLog', NEW c \in 1..Len(ledLog'[t]),
                            t < u, ledLog'[t][c].term = t, IsAcker(jj, t, c)', Between(t, c, u)'
                     PROVE  Has(log[i], c, t)
          BY <1>d, <1>0 DEF Good, durable
        <5>1. t \in DOMAIN ledLog /\ t # u /\ ledLog'[t] = ledLog[t] BY <2>f
        <5>2. IsAcker(jj, t, c) BY <5>1, <2>e
        <5>3. Between(t, c, u) BY <2>a, <1>0 DEF Between, durable
        <5>4. t \in Nat /\ t >= 2 /\ ledLog[t] \in Seq(EntryT) /\ c \in Nat /\ c >= 1
              /\ c \in 1..Len(ledLog[t]) /\ ledLog[t][c].term = t
          BY <5>1, <1>a DEF TypeOK, LeadersInv
        <5> DEFINE v == [voter |-> jj, term |-> u, cand |-> i]
        <5>5. v \in votes /\ v.voter = jj /\ v.term = u /\ v.cand = i BY <1>b
        <5>6. PICK x \in msgs : /\ x.type = "vote" /\ x.src = i /\ x.term = u
                                /\ \/ x.lastLogTerm > t
                                   \/ x.lastLogTerm = t /\ x.lastLogIndex >= c
          <6> HIDE DEF v
          <6> QED BY <5>1, <5>2, <5>3, <5>4, <5>5, <1>2, <1>a DEF VoterInv
        <5> DEFINE L == Len(log[i])
        <5>7. x.lastLogIndex = L /\ x.lastLogTerm = LastTerm(i)
          BY <5>6, <1>2, <1>a DEF VoteReqInv
        <5>8. L \in Nat /\ L >= 1
          <6>1. L \in Nat BY <1>c
          <6>2. L = 0 => LastTerm(i) = 0 BY DEF LastTerm, TermAt
          <6> QED BY <6>1, <6>2, <5>4, <5>6, <5>7
        <5> DEFINE w == log[i][L].term
        <5>9. LastTerm(i) = w /\ L \in 1..L /\ w \in Nat /\ w < u
          <6>1. L \in 1..L BY <5>8
          <6>2. LastTerm(i) = w BY <5>8 DEF LastTerm, TermAt
          <6> QED BY <6>1, <6>2, <2>c
        <5>10. LMc(ledLog, log[i]) BY <1>a DEF LogsInv, LMlog
        <5>11. CASE w = t /\ L >= c
          <6>1. LLc(ledLog, w) = ledLog[t] BY <5>11, <5>1 DEF LLc
          <6>2. L <= Len(ledLog[t]) /\ \A q \in 1..L : log[i][q] = ledLog[t][q]
            BY <6>1, <5>9, <5>10 DEF LMc
          <6>3. c \in 1..L BY <5>11, <5>4, <5>8
          <6> QED BY <6>2, <6>3, <5>4, <5>8 DEF Has
        <5>12. CASE w > t
          <6>1. w # 1 BY <5>12, <5>4, <5>9
          <6>2. w \in DOMAIN ledLog BY <6>1, <5>9, <5>10, TermHasLeader
          <6>3. Has(ledLog[w], c, t) BY <6>2, <5>12, <5>9, <5>3 DEF Between
          <6>4. LLc(ledLog, w) = ledLog[w] BY <6>2 DEF LLc
          <6>5. L <= Len(ledLog[w]) /\ \A q \in 1..L : log[i][q] = ledLog[w][q]
            BY <6>4, <5>9, <5>10 DEF LMc
          <6>6. ledLog[w] \in Seq(EntryT) /\ Mono(ledLog[w]) BY <6>2, <1>a DEF TypeOK, LogsInv
          <6>7. c <= Len(ledLog[w]) /\ ledLog[w][c].term = t BY <6>3 DEF Has
          <6>8. ledLog[w][L].term = w BY <6>5, <5>9
          <6>9. c <= L
            <7> SUFFICES ASSUME L < c PROVE FALSE BY <5>4, <5>8
            <7>1. L \in 1..Len(ledLog[w]) /\ c \in 1..Len(ledLog[w]) /\ L <= c
              BY <6>5, <6>6, <6>7, <5>4, <5>8
            <7>2. ledLog[w][L].term <= ledLog[w][c].term BY <7>1, <6>6 DEF Mono
            <7> QED BY <7>2, <6>7, <6>8, <5>12, <5>4, <5>9
          <6>10. c \in 1..L BY <6>9, <5>4, <5>8
          <6> QED BY <6>5, <6>7, <6>10, <5>8 DEF Has
        <5> HIDE DEF w, L
        <5> QED BY <5>6, <5>7, <5>9, <5>11, <5>12, <5>4, <5>8
      <4>2. \A jj \in Granted(i) : [voter |-> jj, term |-> l.term, cand |-> l.server] \in votes
        BY <3>2, <1>b, <1>c
      <4>3. \A jj \in Granted(i) : Good(jj, l.term)' BY <4>1, <3>2, <1>c, <1>0 DEF durable
      <4> QED BY <4>2, <4>3, <1>0, <1>b
    <3> QED BY <3>1, <3>2, <1>0
  <2>9. /\ UNCHANGED <<msgs, commits, confirmed, currentTerm, commitIndex, log, votes, voteTerm, applied>>
        /\ leaders \subseteq leaders' /\ msgs \subseteq msgs'
    BY <1>0 DEF durable
  <2> QED
    BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9, <2>d, <1>a, TermInvUnch, VotesInvUnch,
       OneVoteUnch, GrantInvUnch, AppendInvExt, AckInvExt, ConfirmedInvExt,
       CommitsInvExt, CommitIndexInvUnch, AppliedInvUnch DEF Inv
<1> QED BY <1>1, <1>2
====
