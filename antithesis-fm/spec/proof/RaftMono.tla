---- MODULE RaftMono ----
\* Each conjunct is preserved when the facts it reads only grow in ways
\* that do not concern it.
EXTENDS RaftFrame

LEMMA VoteReqInvMsg ==
    ASSUME VoteReqInv, NEW m, m.type # "vote", msgs' = msgs \cup {m},
           UNCHANGED <<currentTerm, ledLog, log>>
    PROVE  VoteReqInv'
BY DEF VoteReqInv, LastTerm, TermAt

LEMMA GrantInvMono ==
    ASSUME GrantInv, msgs \subseteq msgs', \A a \in msgs' \ msgs : a.type # "grant",
           votes \subseteq votes'
    PROVE  GrantInv'
BY DEF GrantInv

LEMMA AppendInvMsg ==
    ASSUME AppendInv, NEW m, m.type # "append", msgs' = msgs \cup {m},
           UNCHANGED <<leaders, ledLog, commits>>
    PROVE  AppendInv'
BY DEF AppendInv, TermAt

LEMMA AckInvMono ==
    ASSUME AckInv, TypeOK, TypeOK', msgs \subseteq msgs',
           \A a \in msgs' \ msgs : a.type # "ack",
           \A j \in Server : currentTerm'[j] >= currentTerm[j],
           UNCHANGED ledLog
    PROVE  AckInv'
BY DEF AckInv, TypeOK

LEMMA LogsInvTerm ==
    ASSUME LogsInv, TypeOK, TypeOK',
           \A j \in Server : currentTerm'[j] >= currentTerm[j],
           UNCHANGED <<log, ledLog>>
    PROVE  LogsInv'
<1>1. ASSUME NEW i \in Server, NEW k \in 1..Len(log[i]) PROVE log[i][k].term <= currentTerm'[i]
  <2>1. log[i][k].term <= currentTerm[i] BY DEF LogsInv
  <2>2. log[i][k] \in EntryT BY DEF TypeOK
  <2> QED BY <2>1, <2>2 DEF TypeOK, EntryT
<1> QED BY <1>1 DEF LogsInv, LMlog, LMc, LLc, Mono

LEMMA ConfirmedInvTerm ==
    ASSUME ConfirmedInv, TypeOK, TypeOK',
           \A j \in Server : currentTerm'[j] >= currentTerm[j],
           UNCHANGED <<confirmed, log, ledLog>>
    PROVE  ConfirmedInv'
BY DEF ConfirmedInv, TypeOK

LEMMA CommitIndexInvTerm ==
    ASSUME CommitIndexInv, TypeOK, TypeOK',
           \A j \in Server : currentTerm'[j] >= currentTerm[j],
           UNCHANGED <<commitIndex, commits, log>>
    PROVE  CommitIndexInv'
<1> SUFFICES ASSUME NEW i \in Server, commitIndex[i] # 0
             PROVE  \E k \in commits :
                      /\ k.term <= currentTerm'[i]
                      /\ commitIndex[i] <= Len(k.entries)
                      /\ commitIndex[i] <= Len(log[i])
                      /\ \A q \in 1..commitIndex[i] : log[i][q] = k.entries[q]
  BY DEF CommitIndexInv
<1>1. PICK k \in commits :
                      /\ k.term <= currentTerm[i]
                      /\ commitIndex[i] <= Len(k.entries)
                      /\ commitIndex[i] <= Len(log[i])
                      /\ \A q \in 1..commitIndex[i] : log[i][q] = k.entries[q]
  BY DEF CommitIndexInv
<1>2. k.term \in Nat /\ currentTerm[i] \in Nat /\ currentTerm'[i] \in Nat BY DEF TypeOK
<1> QED BY <1>1, <1>2

LEMMA IsAckerSame ==
    ASSUME msgs \subseteq msgs', \A a \in msgs' \ msgs : a.type # "ack", UNCHANGED leaders
    PROVE  \A j, t, c : IsAcker(j, t, c)' <=> IsAcker(j, t, c)
BY DEF IsAcker

LEMMA AckerInvMono ==
    ASSUME AckerInv, TypeOK, TypeOK', msgs \subseteq msgs',
           \A a \in msgs' \ msgs : a.type # "ack",
           \A j \in Server : currentTerm'[j] >= currentTerm[j],
           UNCHANGED <<ledLog, leaders, log>>
    PROVE  AckerInv'
<1> SUFFICES ASSUME NEW j \in Server, NEW t \in DOMAIN ledLog, NEW c \in 1..Len(ledLog[t]),
                    ledLog[t][c].term = t, IsAcker(j, t, c)',
                    \A w \in DOMAIN ledLog : t < w /\ w <= currentTerm'[j] => Has(ledLog[w], c, t)
             PROVE  Has(log[j], c, t)
  BY DEF AckerInv, Has
<1>1. IsAcker(j, t, c) BY IsAckerSame
<1>2. \A w \in DOMAIN ledLog : t < w /\ w <= currentTerm[j] => Has(ledLog[w], c, t)
  BY DEF TypeOK
<1> QED BY <1>1, <1>2 DEF AckerInv

LEMMA VoterInvMono ==
    ASSUME VoterInv, msgs \subseteq msgs', \A a \in msgs' \ msgs : a.type # "ack",
           UNCHANGED <<votes, ledLog, leaders>>
    PROVE  VoterInv'
<1> SUFFICES ASSUME NEW v \in votes, NEW t \in DOMAIN ledLog, NEW c \in 1..Len(ledLog[t]),
                    t < v.term, v.term \notin DOMAIN ledLog, ledLog[t][c].term = t,
                    IsAcker(v.voter, t, c)', Between(t, c, v.term)
             PROVE  \E m \in msgs' : /\ m.type = "vote" /\ m.src = v.cand /\ m.term = v.term
                                     /\ \/ m.lastLogTerm > t
                                        \/ m.lastLogTerm = t /\ m.lastLogIndex >= c
  BY DEF VoterInv, Between, Has
<1>1. IsAcker(v.voter, t, c) BY IsAckerSame
<1> QED BY <1>1 DEF VoterInv

LEMMA GoodSame ==
    ASSUME msgs \subseteq msgs', \A a \in msgs' \ msgs : a.type # "ack",
           UNCHANGED <<ledLog, leaders>>
    PROVE  \A j, u : Good(j, u) => Good(j, u)'
<1> TAKE j, u
<1> SUFFICES ASSUME Good(j, u),
                    NEW t \in DOMAIN ledLog, NEW c \in 1..Len(ledLog[t]),
                    t < u, ledLog[t][c].term = t, IsAcker(j, t, c)', Between(t, c, u)
             PROVE  Has(ledLog[u], c, t)
  BY DEF Good, Between, Has
<1>1. IsAcker(j, t, c) BY IsAckerSame
<1> QED BY <1>1 DEF Good

LEMMA QuorumInvMono ==
    ASSUME QuorumInv, msgs \subseteq msgs', \A a \in msgs' \ msgs : a.type # "ack",
           votes \subseteq votes', UNCHANGED <<ledLog, leaders>>
    PROVE  QuorumInv'
<1> SUFFICES ASSUME NEW l \in leaders
             PROVE  \E Q \in SUBSET Server :
                       /\ IsQuorum(Q)
                       /\ \A j \in Q : /\ [voter |-> j, term |-> l.term, cand |-> l.server] \in votes'
                                       /\ Good(j, l.term)'
  BY DEF QuorumInv
<1>1. PICK Q \in SUBSET Server :
         /\ IsQuorum(Q)
         /\ \A j \in Q : /\ [voter |-> j, term |-> l.term, cand |-> l.server] \in votes
                         /\ Good(j, l.term)
  BY DEF QuorumInv
<1>2. \A j \in Q : Good(j, l.term)' BY <1>1, GoodSame
<1> QED BY <1>1, <1>2

LEMMA CommitsInvMono ==
    ASSUME CommitsInv, msgs \subseteq msgs', UNCHANGED <<commits, ledLog, leaders>>
    PROVE  CommitsInv'
<1>1. \A j, t, c : IsAcker(j, t, c) => IsAcker(j, t, c)' BY DEF IsAcker
<1>2. \A t, c : QC(t, c) => QC(t, c)' BY <1>1 DEF QC
<1> QED BY <1>2 DEF CommitsInv
====
