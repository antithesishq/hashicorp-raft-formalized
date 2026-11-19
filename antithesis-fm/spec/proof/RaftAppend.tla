---- MODULE RaftAppend ----
\* LeaderAppend.
EXTENDS RaftLog2

LEMMA LeaderAppendInv ==
    ASSUME Inv, NEW i \in Server, NEW e \in EntryT, e.term = currentTerm[i],
           LeaderAppend(i, <<e>>)
    PROVE  Inv'
<1> DEFINE T == currentTerm[i]
<1> DEFINE L == Len(log[i])
<1> DEFINE nl == log[i] \o <<e>>
<1>0. /\ role[i] = Leader
      /\ log' = [log EXCEPT ![i] = nl]
      /\ ledLog' = WithLed(T, nl)
      /\ UNCHANGED <<transfer, currentTerm, voteTerm, voteFor, snap, base, role, commitIndex,
                     lastApplied, confirmed, msgs, votes, leaders, commits, applied>>
  BY DEF LeaderAppend
<1>a. /\ TypeOK /\ TermInv /\ VotesInv /\ VoteReqInv /\ LeadersInv /\ ElectionSafety /\ LogsInv
      /\ AckInv /\ AckerInv /\ VoterInv /\ QuorumInv
  BY DEF Inv
<1>b. /\ [server |-> i, term |-> T] \in leaders /\ T \in DOMAIN ledLog /\ T \in Nat /\ T >= 2
      /\ log[i] = ledLog[T] /\ log[i] \in Seq(EntryT) /\ L \in Nat /\ e.term = T
  <2>1. [server |-> i, term |-> T] \in leaders BY <1>0, <1>a DEF LeadersInv
  <2>2. T \in DOMAIN ledLog /\ log[i] = ledLog[T] BY <2>1, <1>a DEF LeadersInv
  <2> QED BY <2>1, <2>2, <1>a DEF TypeOK, LeadersInv
<1>c. /\ nl \in Seq(EntryT) /\ Len(nl) = L + 1
      /\ \A q \in 1..L : nl[q] = log[i][q]
      /\ nl[L + 1] = e
  <2>1. <<e>> \in Seq(EntryT) /\ Len(<<e>>) = 1 /\ <<e>>[1] = e OBVIOUS
  <2>2. L + 1 \in L+1..L+Len(<<e>>) BY <2>1, <1>b
  <2> QED BY <2>1, <2>2, <1>b, ConcatFacts
<1>d. /\ DOMAIN ledLog' = DOMAIN ledLog /\ ledLog'[T] = nl
      /\ \A w \in DOMAIN ledLog : w # T => ledLog'[w] = ledLog[w]
      /\ ledLog' = [t \in DOMAIN ledLog' |-> ledLog'[t]]
  BY <1>0, <1>b DEF WithLed
<1>e. log'[i] = nl /\ \A jj \in Server : jj # i => log'[jj] = log[jj]
  BY <1>0, <1>a DEF TypeOK
<1>f. LedExt /\ LogExt
  <2>1. LedExt
    <3> SUFFICES ASSUME NEW w \in DOMAIN ledLog
                 PROVE  /\ Len(ledLog[w]) <= Len(ledLog'[w])
                        /\ \A q \in 1..Len(ledLog[w]) : ledLog'[w][q] = ledLog[w][q]
      BY <1>d DEF LedExt
    <3>1. CASE w = T BY <3>1, <1>b, <1>c, <1>d
    <3>2. CASE w # T
      <4>1. ledLog[w] \in Seq(EntryT) BY <1>a DEF TypeOK
      <4> QED BY <3>2, <4>1, <1>d
    <3> QED BY <3>1, <3>2
  <2>2. LogExt
    <3> SUFFICES ASSUME NEW jj \in Server
                 PROVE  /\ Len(log[jj]) <= Len(log'[jj])
                        /\ \A q \in 1..Len(log[jj]) : log'[jj][q] = log[jj][q]
      BY DEF LogExt
    <3>1. CASE jj = i BY <3>1, <1>b, <1>c, <1>e
    <3>2. CASE jj # i
      <4>1. log[jj] \in Seq(EntryT) BY <1>a DEF TypeOK
      <4> QED BY <3>2, <4>1, <1>e
    <3> QED BY <3>1, <3>2
  <2> QED BY <2>1, <2>2
<1>g. \A l \in leaders : l.term = T => l.server = i
  BY <1>b, <1>a DEF ElectionSafety
<1>h. \A jj : IsAcker(jj, T, L + 1) => jj = i
  <2> SUFFICES ASSUME NEW jj, IsAcker(jj, T, L + 1) PROVE jj = i OBVIOUS
  <2>1. CASE [server |-> jj, term |-> T] \in leaders BY <2>1, <1>g
  <2>2. CASE \E a \in msgs : a.type = "ack" /\ a.src = jj /\ a.term = T /\ a.index >= L + 1
    <3>1. PICK a \in msgs : a.type = "ack" /\ a.term = T /\ a.index >= L + 1 BY <2>2
    <3>2. a.index \in Nat /\ a.index <= Len(ledLog[T]) BY <3>1, <1>a DEF AckInv
    <3> QED BY <3>1, <3>2, <1>b
  <2> QED BY <2>1, <2>2 DEF IsAcker
<1>i. \A w \in DOMAIN ledLog : \A c \in Nat : \A t :
         t # w /\ c >= 1 /\ Has(ledLog'[w], c, t) => Has(ledLog[w], c, t)
  <2> SUFFICES ASSUME NEW w \in DOMAIN ledLog, NEW c \in Nat, NEW t, t # w, c >= 1,
                      Has(ledLog'[w], c, t)
               PROVE  Has(ledLog[w], c, t)
    OBVIOUS
  <2>1. CASE w # T BY <2>1, <1>d
  <2>2. CASE w = T
    <3>1. c <= L + 1 /\ nl[c].term = t BY <2>2, <1>d, <1>c DEF Has
    <3>2. c # L + 1 BY <3>1, <2>2, <1>c, <1>b
    <3>3. c \in 1..L BY <3>1, <3>2, <1>b
    <3> QED BY <3>1, <3>3, <2>2, <1>b, <1>c DEF Has
  <2> QED BY <2>1, <2>2
<1>j. \A w \in DOMAIN ledLog : \A c \in Nat : \A t :
         c >= 1 /\ Has(ledLog[w], c, t) => Has(ledLog'[w], c, t)
  <2> SUFFICES ASSUME NEW w \in DOMAIN ledLog, NEW c \in Nat, NEW t, c >= 1,
                      Has(ledLog[w], c, t)
               PROVE  Has(ledLog'[w], c, t)
    OBVIOUS
  <2>1. ledLog[w] \in Seq(EntryT) /\ ledLog'[w] \in Seq(EntryT)
        /\ Len(ledLog[w]) <= Len(ledLog'[w])
        /\ \A q \in 1..Len(ledLog[w]) : ledLog'[w][q] = ledLog[w][q]
    <3>1. ledLog[w] \in Seq(EntryT) BY <1>a DEF TypeOK
    <3>2. ledLog'[w] \in Seq(EntryT) BY <3>1, <1>c, <1>d
    <3> QED BY <3>1, <3>2, <1>f DEF LedExt
  <2>2. c \in 1..Len(ledLog[w]) BY <2>1 DEF Has
  <2> QED BY <2>1, <2>2 DEF Has
<1>k. \A t \in DOMAIN ledLog : \A c \in 1..Len(ledLog'[t]) :
         ledLog'[t][c].term = t /\ ~(t = T /\ c = L + 1) =>
            c \in 1..Len(ledLog[t]) /\ ledLog[t][c].term = t
  <2> SUFFICES ASSUME NEW t \in DOMAIN ledLog, NEW c \in 1..Len(ledLog'[t]),
                      ledLog'[t][c].term = t, ~(t = T /\ c = L + 1)
               PROVE  c \in 1..Len(ledLog[t]) /\ ledLog[t][c].term = t
    OBVIOUS
  <2>1. CASE t # T BY <2>1, <1>d
  <2>2. CASE t = T
    <3>1. c \in 1..L BY <2>2, <1>b, <1>c, <1>d
    <3> QED BY <3>1, <2>2, <1>b, <1>c, <1>d
  <2> QED BY <2>1, <2>2
<1>l. \A v \in votes : v.voter = i => v.term \in Nat /\ v.term <= T
  <2> SUFFICES ASSUME NEW v \in votes, v.voter = i PROVE v.term \in Nat /\ v.term <= T
    OBVIOUS
  <2>1. v.term \in Nat /\ v.term <= voteTerm[i] /\ voteTerm[i] \in Nat /\ voteTerm[i] <= currentTerm[i]
    BY <1>a DEF TypeOK, VotesInv, TermInv
  <2> QED BY <2>1, <1>b
<1> HIDE DEF T, L, nl
<1>1. TypeOK'
  <2>1. log' \in [Server -> Seq(EntryT)] BY <1>0, <1>c, <1>a DEF TypeOK
  <2>2. \A t \in DOMAIN ledLog' : ledLog'[t] \in Seq(EntryT)
    BY <1>c, <1>d, <1>a DEF TypeOK
  <2>3. DOMAIN ledLog' \subseteq Nat BY <1>d, <1>a DEF TypeOK
  <2> QED BY <2>1, <2>2, <2>3, <1>d, <1>0, <1>a DEF TypeOK
<1>2. VoteReqInv'
  <2> SUFFICES ASSUME NEW a \in msgs, a.type = "vote",
                      a.term = currentTerm[a.src], a.term \notin DOMAIN ledLog
               PROVE  a.lastLogIndex = Len(log'[a.src]) /\ a.lastLogTerm = LastTerm(a.src)'
    BY <1>0, <1>d, <1>a DEF VoteReqInv
  <2>1. a.src \in Server /\ a.lastLogIndex = Len(log[a.src]) /\ a.lastLogTerm = LastTerm(a.src)
    BY <1>a DEF VoteReqInv
  <2>2. a.src # i BY <1>b DEF T
  <2>3. log'[a.src] = log[a.src] BY <2>1, <2>2, <1>e
  <2> QED BY <2>1, <2>3 DEF LastTerm, TermAt
<1>3. LeadersInv'
  <2>1. ASSUME NEW l \in leaders, currentTerm[l.server] = l.term
        PROVE  log'[l.server] = ledLog'[l.term]
    <3>0. l.server \in Server /\ l.term \in DOMAIN ledLog /\ log[l.server] = ledLog[l.term]
      BY <2>1, <1>a DEF TypeOK, LeadersInv
    <3>1. CASE l.server = i BY <3>1, <2>1, <1>d, <1>e DEF T
    <3>2. CASE l.server # i
      <4>1. l.term # T BY <3>2, <1>g
      <4> QED BY <4>1, <3>0, <3>2, <1>d, <1>e
    <3> QED BY <3>1, <3>2
  <2> QED BY <2>1, <1>0, <1>d, <1>a DEF LeadersInv
<1>4. LogsInv'
  <2>0. 1 \notin DOMAIN ledLog' BY <1>d, <1>a DEF LeadersInv
  <2>1. \A w \in DOMAIN ledLog : /\ ledLog[w] \in Seq(EntryT) /\ ledLog'[w] \in Seq(EntryT)
                                 /\ Len(ledLog[w]) <= Len(ledLog'[w])
                                 /\ \A q \in 1..Len(ledLog[w]) : ledLog'[w][q] = ledLog[w][q]
    <3>1. \A w \in DOMAIN ledLog : ledLog[w] \in Seq(EntryT) /\ ledLog'[w] \in Seq(EntryT)
      BY <1>1, <1>d, <1>a DEF TypeOK
    <3> QED BY <3>1, <1>f DEF LedExt
  <2>2. ASSUME NEW X \in Seq(EntryT), LMc(ledLog, X) PROVE LMc(ledLog', X)
    BY <2>0, <2>1, <2>2, <1>d, LMExt
  <2>3. /\ LMc(ledLog', nl) /\ Mono(nl) /\ \A k \in 1..Len(nl) : nl[k].term <= T
    <3>1. LMc(ledLog, log[i]) /\ Mono(log[i]) /\ \A k \in 1..L : log[i][k].term <= T
      BY <1>a DEF LogsInv, LMlog, T, L
    <3>2. LMc(ledLog', log[i]) BY <3>1, <2>2, <1>b
    <3>3. LMc(ledLog', nl)
      <4> SUFFICES ASSUME NEW k \in 1..Len(nl)
                   PROVE  /\ k <= Len(LLc(ledLog', nl[k].term))
                          /\ \A q \in 1..k : nl[q] = LLc(ledLog', nl[k].term)[q]
        BY DEF LMc
      <4>1. CASE k = L + 1
        <5>1. LLc(ledLog', nl[k].term) = nl BY <4>1, <1>b, <1>c, <1>d DEF LLc
        <5> QED BY <5>1
      <4>2. CASE k # L + 1
        <5>1. k \in 1..L BY <4>2, <1>b, <1>c
        <5>2. nl[k] = log[i][k] /\ \A q \in 1..k : nl[q] = log[i][q] BY <5>1, <1>b, <1>c
        <5>3. /\ k <= Len(LLc(ledLog', log[i][k].term))
              /\ \A q \in 1..k : log[i][q] = LLc(ledLog', log[i][k].term)[q]
          BY <5>1, <3>2 DEF LMc, L
        <5> QED BY <5>2, <5>3
      <4> QED BY <4>1, <4>2
    <3>4. \A k \in 1..Len(nl) : nl[k].term \in Nat /\ nl[k].term <= T
      <4> SUFFICES ASSUME NEW k \in 1..Len(nl) PROVE nl[k].term \in Nat /\ nl[k].term <= T
        OBVIOUS
      <4>1. nl[k] \in EntryT BY <1>c, ElementOfSeq
      <4>2. CASE k = L + 1 BY <4>1, <4>2, <1>b, <1>c DEF EntryT
      <4>3. CASE k # L + 1
        <5>1. k \in 1..L BY <4>3, <1>b, <1>c
        <5> QED BY <5>1, <4>1, <3>1, <1>c DEF EntryT
      <4> QED BY <4>2, <4>3
    <3>5. Mono(nl)
      <4> SUFFICES ASSUME NEW a \in 1..Len(nl), NEW b \in 1..Len(nl), a <= b
                   PROVE  nl[a].term <= nl[b].term
        BY DEF Mono
      <4>1. CASE b = L + 1 BY <4>1, <3>4, <1>b, <1>c
      <4>2. CASE b # L + 1
        <5>1. a \in 1..L /\ b \in 1..L BY <4>2, <1>b, <1>c
        <5> QED BY <5>1, <3>1, <1>c DEF Mono, L
      <4> QED BY <4>1, <4>2
    <3> QED BY <3>3, <3>4, <3>5
  <2>4. ASSUME NEW j \in Server
        PROVE  /\ LMc(ledLog', log'[j]) /\ Mono(log'[j])
               /\ \A k \in 1..Len(log'[j]) : log'[j][k].term <= currentTerm[j]
    <3>1. CASE j = i BY <3>1, <2>3, <1>e DEF T
    <3>2. CASE j # i
      <4>1. log'[j] = log[j] /\ log[j] \in Seq(EntryT) BY <3>2, <1>e, <1>a DEF TypeOK
      <4>2. LMc(ledLog, log[j]) /\ Mono(log[j])
            /\ \A k \in 1..Len(log[j]) : log[j][k].term <= currentTerm[j]
        BY <1>a DEF LogsInv, LMlog
      <4> QED BY <4>1, <4>2, <2>2
    <3> QED BY <3>1, <3>2
  <2>5. ASSUME NEW t \in DOMAIN ledLog
        PROVE  /\ LMc(ledLog', ledLog'[t]) /\ Mono(ledLog'[t])
               /\ \A k \in 1..Len(ledLog'[t]) : ledLog'[t][k].term <= t
    <3>1. CASE t = T BY <3>1, <2>3, <1>d
    <3>2. CASE t # T
      <4>1. ledLog'[t] = ledLog[t] /\ ledLog[t] \in Seq(EntryT) BY <3>2, <1>d, <1>a DEF TypeOK
      <4>2. LMc(ledLog, ledLog[t]) /\ Mono(ledLog[t])
            /\ \A k \in 1..Len(ledLog[t]) : ledLog[t][k].term <= t
        BY <1>a DEF LogsInv, LMlog
      <4> QED BY <4>1, <4>2, <2>2
    <3> QED BY <3>1, <3>2
  <2> QED BY <2>4, <2>5, <1>0, <1>d DEF LogsInv, LMlog
<1>5. AckerInv'
  <2> SUFFICES ASSUME NEW jj \in Server, NEW t \in DOMAIN ledLog, NEW c \in 1..Len(ledLog'[t]),
                      ledLog'[t][c].term = t, IsAcker(jj, t, c),
                      \A w \in DOMAIN ledLog : t < w /\ w <= currentTerm[jj] => Has(ledLog'[w], c, t)
               PROVE  Has(log'[jj], c, t)
    BY <1>0, <1>d DEF AckerInv, IsAcker, Has
  <2>0. t \in Nat /\ ledLog'[t] \in Seq(EntryT) /\ c \in Nat /\ c >= 1
    BY <1>1, <1>d DEF TypeOK
  <2>1. CASE t = T /\ c = L + 1
    <3>1. jj = i BY <2>1, <1>h
    <3> QED BY <3>1, <2>1, <1>b, <1>c, <1>e DEF Has
  <2>2. CASE ~(t = T /\ c = L + 1)
    <3>1. c \in 1..Len(ledLog[t]) /\ ledLog[t][c].term = t BY <2>2, <1>k
    <3>2. \A w \in DOMAIN ledLog : t < w /\ w <= currentTerm[jj] => Has(ledLog[w], c, t)
      <4> SUFFICES ASSUME NEW w \in DOMAIN ledLog, t < w, w <= currentTerm[jj]
                   PROVE  Has(ledLog[w], c, t)
        OBVIOUS
      <4>1. w \in Nat /\ t # w BY <2>0, <1>a DEF TypeOK
      <4>2. Has(ledLog'[w], c, t) OBVIOUS
      <4> QED BY <4>1, <4>2, <2>0, <1>i
    <3>3. Has(log[jj], c, t) BY <3>1, <3>2, <1>a DEF AckerInv
    <3>4. log[jj] \in Seq(EntryT) /\ Len(log[jj]) <= Len(log'[jj])
          /\ \A q \in 1..Len(log[jj]) : log'[jj][q] = log[jj][q]
      BY <1>f, <1>a DEF LogExt, TypeOK
    <3>5. log'[jj] \in Seq(EntryT) BY <1>1 DEF TypeOK
    <3>6. c \in 1..Len(log[jj]) BY <3>3, <3>4, <2>0 DEF Has
    <3> QED BY <3>3, <3>4, <3>5, <3>6 DEF Has
  <2> QED BY <2>1, <2>2
<1>6. VoterInv'
  <2> SUFFICES ASSUME NEW v \in votes, NEW t \in DOMAIN ledLog, NEW c \in 1..Len(ledLog'[t]),
                      t < v.term, v.term \notin DOMAIN ledLog, ledLog'[t][c].term = t,
                      IsAcker(v.voter, t, c), Between(t, c, v.term)'
               PROVE  \E x \in msgs : /\ x.type = "vote" /\ x.src = v.cand /\ x.term = v.term
                                      /\ \/ x.lastLogTerm > t
                                         \/ x.lastLogTerm = t /\ x.lastLogIndex >= c
    BY <1>0, <1>d DEF VoterInv, IsAcker
  <2>0. t \in Nat /\ ledLog'[t] \in Seq(EntryT) /\ c \in Nat /\ c >= 1
    BY <1>1, <1>d DEF TypeOK
  <2>1. CASE t = T /\ c = L + 1
    <3>1. v.voter = i BY <2>1, <1>h
    <3>2. v.term \in Nat /\ v.term <= T BY <3>1, <1>l
    <3> QED BY <3>2, <2>1, <1>b
  <2>2. CASE ~(t = T /\ c = L + 1)
    <3>1. c \in 1..Len(ledLog[t]) /\ ledLog[t][c].term = t BY <2>2, <1>k
    <3>2. Between(t, c, v.term)
      <4> SUFFICES ASSUME NEW w \in DOMAIN ledLog, t < w, w < v.term
                   PROVE  Has(ledLog[w], c, t)
        BY DEF Between
      <4>1. w \in Nat /\ t # w BY <2>0, <1>a DEF TypeOK
      <4>2. Has(ledLog'[w], c, t) BY <1>d DEF Between
      <4> QED BY <4>1, <4>2, <2>0, <1>i
    <3> QED BY <3>1, <3>2, <1>a DEF VoterInv
  <2> QED BY <2>1, <2>2
<1>7. QuorumInv'
  <2> SUFFICES ASSUME NEW l \in leaders
               PROVE  \E Q \in SUBSET Server :
                         /\ IsQuorum(Q)
                         /\ \A jj \in Q : /\ [voter |-> jj, term |-> l.term, cand |-> l.server] \in votes
                                          /\ Good(jj, l.term)'
    BY <1>0 DEF QuorumInv
  <2>1. PICK Q \in SUBSET Server :
           /\ IsQuorum(Q)
           /\ \A jj \in Q : /\ [voter |-> jj, term |-> l.term, cand |-> l.server] \in votes
                            /\ Good(jj, l.term)
    BY <1>a DEF QuorumInv
  <2>2. ASSUME NEW jj \in Q PROVE Good(jj, l.term)'
    <3> DEFINE u == l.term
    <3> SUFFICES ASSUME NEW t \in DOMAIN ledLog, NEW c \in 1..Len(ledLog'[t]),
                        t < u, ledLog'[t][c].term = t, IsAcker(jj, t, c), Between(t, c, u)'
                 PROVE  Has(ledLog'[u], c, t)
      BY <1>0, <1>d DEF Good, IsAcker
    <3>0. t \in Nat /\ ledLog'[t] \in Seq(EntryT) /\ c \in Nat /\ c >= 1 /\ u \in DOMAIN ledLog
      BY <1>1, <1>d, <1>a DEF TypeOK, LeadersInv
    <3>1. CASE t = T /\ c = L + 1
      <4>1. jj = i BY <3>1, <1>h
      <4>2. [voter |-> jj, term |-> u, cand |-> l.server] \in votes BY <2>1
      <4>3. u \in Nat /\ u <= T BY <4>1, <4>2, <1>l
      <4> QED BY <4>3, <3>1, <1>b
    <3>2. CASE ~(t = T /\ c = L + 1)
      <4>1. c \in 1..Len(ledLog[t]) /\ ledLog[t][c].term = t BY <3>2, <1>k
      <4>2. Between(t, c, u)
        <5> SUFFICES ASSUME NEW w \in DOMAIN ledLog, t < w, w < u
                     PROVE  Has(ledLog[w], c, t)
          BY DEF Between
        <5>1. w \in Nat /\ t # w BY <3>0, <1>a DEF TypeOK
        <5>2. Has(ledLog'[w], c, t) BY <1>d DEF Between
        <5> QED BY <5>1, <5>2, <3>0, <1>i
      <4>3. Has(ledLog[u], c, t) BY <4>1, <4>2, <2>1 DEF Good
      <4> QED BY <4>3, <3>0, <1>j
    <3> QED BY <3>1, <3>2
  <2> QED BY <2>1, <2>2
<1>8. /\ UNCHANGED <<msgs, commits, confirmed, currentTerm, commitIndex>>
      /\ leaders \subseteq leaders' /\ msgs \subseteq msgs'
  BY <1>0
<1> QED
  BY <1>0, <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>f, <1>a, TermInvUnch, VotesInvUnch,
     OneVoteUnch, GrantInvUnch, ElectionSafetyUnch, AppendInvExt, AckInvExt, ConfirmedInvExt,
     CommitsInvExt, CommitIndexInvExt, AppliedInvUnch DEF Inv
====
