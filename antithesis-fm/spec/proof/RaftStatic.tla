---- MODULE RaftStatic ----
\* Consequences of the invariant in a single state: every later leader has
\* what a quorum stored (leader completeness in terms of leader logs).
EXTENDS RaftCommit, NaturalsInduction

LEMMA LeaderHas ==
    ASSUME IsFiniteSet(Server), Inv,
           NEW t \in DOMAIN ledLog, NEW c \in 1..Len(ledLog[t]), QC(t, c)
    PROVE  \A u \in Nat : (u \in DOMAIN ledLog /\ t < u) => Has(ledLog[u], c, t)
<1> DEFINE P(u) == (u \in DOMAIN ledLog /\ t < u) => Has(ledLog[u], c, t)
<1>a. TypeOK /\ LeadersInv /\ QuorumInv BY DEF Inv
<1>1. ASSUME NEW u \in Nat, \A w \in 0..(u-1) : P(w) PROVE P(u)
  <2> SUFFICES ASSUME u \in DOMAIN ledLog, t < u PROVE Has(ledLog[u], c, t) OBVIOUS
  <2>1. Between(t, c, u)
    <3> SUFFICES ASSUME NEW w \in DOMAIN ledLog, t < w, w < u PROVE Has(ledLog[w], c, t)
      BY DEF Between
    <3>1. w \in Nat BY <1>a DEF TypeOK
    <3>2. w \in 0..(u-1) BY <3>1
    <3> QED BY <3>2, <1>1
  <2>2. PICK l \in leaders : l.term = u BY <1>a DEF LeadersInv
  <2>3. PICK Q \in SUBSET Server :
          /\ IsQuorum(Q)
          /\ \A j \in Q : Good(j, u)
    BY <2>2, <1>a DEF QuorumInv
  <2>4. PICK QA \in SUBSET Server : IsQuorum(QA) /\ \A j \in QA : IsAcker(j, t, c)
    BY DEF QC
  <2>5. PICK j \in Q : j \in QA BY <2>3, <2>4, QuorumIntersect
  <2>6. Good(j, u) /\ IsAcker(j, t, c) /\ ledLog[t][c].term = t BY <2>3, <2>4, <2>5 DEF QC
  <2> QED BY <2>1, <2>6 DEF Good
<1> HIDE DEF P
<1>2. \A u \in Nat : P(u) BY <1>1, GeneralNatInduction, IsaM("blast")
<1> QED BY <1>2 DEF P

\* A committed prefix is in the leader log of its term and of every later term.
LEMMA CommitLed ==
    ASSUME IsFiniteSet(Server), Inv, NEW k \in commits, NEW u \in DOMAIN ledLog, k.term <= u
    PROVE  /\ Len(k.entries) <= Len(ledLog[u])
           /\ \A q \in 1..Len(k.entries) : k.entries[q] = ledLog[u][q]
<1>a. TypeOK /\ CommitsInv /\ LogsInv BY DEF Inv
<1>b. /\ k.term \in DOMAIN ledLog
      /\ Len(k.entries) <= Len(ledLog[k.term])
      /\ \A q \in 1..Len(k.entries) : k.entries[q] = ledLog[k.term][q]
  BY <1>a DEF CommitsInv
<1>c. PICK t \in DOMAIN ledLog : \E c \in 1..Len(ledLog[t]) :
              t <= k.term /\ Len(k.entries) <= c /\ QC(t, c)
  BY <1>a DEF CommitsInv
<1>d. PICK c \in 1..Len(ledLog[t]) : t <= k.term /\ Len(k.entries) <= c /\ QC(t, c)
  BY <1>c
<1>e. /\ k.term \in Nat /\ u \in Nat /\ t \in Nat /\ k.entries \in Seq(EntryT)
      /\ ledLog[u] \in Seq(EntryT) /\ ledLog[k.term] \in Seq(EntryT) /\ ledLog[t] \in Seq(EntryT)
  BY <1>a, <1>b DEF TypeOK
<1>1. CASE u = k.term BY <1>1, <1>b
<1>2. CASE u # k.term
  <2>1. t < u BY <1>2, <1>d, <1>e
  <2>2. Has(ledLog[u], c, t) BY <2>1, <1>d, <1>e, LeaderHas
  <2>3. Has(ledLog[k.term], c, t)
    <3>1. CASE t = k.term BY <3>1, <1>d DEF QC, Has
    <3>2. CASE t # k.term
      <4>1. t < k.term BY <3>2, <1>d, <1>e
      <4> QED BY <4>1, <1>b, <1>d, <1>e, LeaderHas
    <3> QED BY <3>1, <3>2
  <2>4. LMc(ledLog, ledLog[u]) /\ LMc(ledLog, ledLog[k.term]) BY <1>a, <1>b DEF LogsInv, LMlog
  <2>5. c \in 1..Len(ledLog[u]) /\ c \in 1..Len(ledLog[k.term])
        /\ ledLog[u][c].term = ledLog[k.term][c].term
    BY <2>2, <2>3, <1>e DEF Has
  <2>6. \A q \in 1..c : ledLog[u][q] = ledLog[k.term][q] BY <2>4, <2>5, Match
  <2> QED BY <2>5, <2>6, <1>b, <1>d, <1>e
<1> QED BY <1>1, <1>2
====
