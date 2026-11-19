---- MODULE RaftFrame ----
\* The invariant holds initially; each conjunct is preserved when the
\* variables it reads do not change; helper lemmas on leader logs.
EXTENDS RaftBase

LEMMA InitInv == Init => Inv
<1> SUFFICES ASSUME Init PROVE Inv OBVIOUS
<1> USE DEF Init
<1>0. DOMAIN ledLog = {} OBVIOUS
<1>1. TypeOK BY <1>0 DEF TypeOK, EntryT, Entry, Follower, Candidate, Leader
<1>2. TermInv BY DEF TermInv
<1>3. VotesInv /\ OneVotePerTerm /\ VoteReqInv /\ GrantInv /\ ElectionSafety
      /\ AppendInv /\ AckInv /\ VoterInv /\ QuorumInv /\ CommitsInv /\ AppliedInv
  BY DEF VotesInv, OneVotePerTerm, VoteReqInv, GrantInv, ElectionSafety,
         AppendInv, AckInv, VoterInv, QuorumInv, CommitsInv, AppliedInv
<1>4. LeadersInv BY <1>0 DEF LeadersInv, Follower, Leader
<1>5. LogsInv
  <2>1. ASSUME NEW i \in Server PROVE LMlog(log[i]) /\ Mono(log[i]) /\ \A k \in 1..Len(log[i]) : log[i][k].term <= currentTerm[i]
    BY <1>0 DEF LMlog, LMc, LLc, InitLog, Mono, Entry
  <2> QED BY <2>1, <1>0 DEF LogsInv
<1>6. ConfirmedInv BY DEF ConfirmedInv
<1>7. AckerInv BY <1>0 DEF AckerInv
<1>8. CommitIndexInv BY DEF CommitIndexInv
<1> QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8 DEF Inv

----
LEMMA TypeOKUnch ==
    ASSUME TypeOK, UNCHANGED <<currentTerm, voteTerm, voteFor, log, snap, role, commitIndex,
                               lastApplied, confirmed, votes, leaders, ledLog, commits>>
    PROVE  TypeOK'
BY DEF TypeOK
LEMMA TermInvUnch == ASSUME TermInv, UNCHANGED <<currentTerm, voteTerm>> PROVE TermInv'
BY DEF TermInv
LEMMA VotesInvUnch == ASSUME VotesInv, UNCHANGED <<votes, voteTerm>> PROVE VotesInv'
BY DEF VotesInv
LEMMA OneVoteUnch == ASSUME OneVotePerTerm, UNCHANGED votes PROVE OneVotePerTerm'
BY DEF OneVotePerTerm
LEMMA VoteReqInvUnch ==
    ASSUME VoteReqInv, UNCHANGED <<msgs, currentTerm, ledLog, log>> PROVE VoteReqInv'
BY DEF VoteReqInv, LastTerm, TermAt
LEMMA GrantInvUnch == ASSUME GrantInv, UNCHANGED <<msgs, votes>> PROVE GrantInv'
BY DEF GrantInv
LEMMA LeadersInvUnch ==
    ASSUME LeadersInv, UNCHANGED <<leaders, currentTerm, ledLog, log, role>> PROVE LeadersInv'
BY DEF LeadersInv
LEMMA ElectionSafetyUnch == ASSUME ElectionSafety, UNCHANGED leaders PROVE ElectionSafety'
BY DEF ElectionSafety
LEMMA LogsInvUnch == ASSUME LogsInv, UNCHANGED <<log, ledLog, currentTerm>> PROVE LogsInv'
BY DEF LogsInv, LMlog, LMc, LLc, Mono
LEMMA AppendInvUnch ==
    ASSUME AppendInv, UNCHANGED <<msgs, leaders, ledLog, commits>> PROVE AppendInv'
BY DEF AppendInv, TermAt
LEMMA AckInvUnch == ASSUME AckInv, UNCHANGED <<msgs, ledLog, currentTerm>> PROVE AckInv'
BY DEF AckInv
LEMMA ConfirmedInvUnch ==
    ASSUME ConfirmedInv, UNCHANGED <<confirmed, currentTerm, log, ledLog>> PROVE ConfirmedInv'
BY DEF ConfirmedInv
LEMMA AckerInvUnch ==
    ASSUME AckerInv, UNCHANGED <<ledLog, leaders, msgs, currentTerm, log>> PROVE AckerInv'
BY DEF AckerInv, IsAcker, Has
LEMMA VoterInvUnch ==
    ASSUME VoterInv, UNCHANGED <<votes, ledLog, leaders, msgs>> PROVE VoterInv'
BY DEF VoterInv, IsAcker, Has, Between
LEMMA QuorumInvUnch ==
    ASSUME QuorumInv, UNCHANGED <<votes, ledLog, leaders, msgs>> PROVE QuorumInv'
BY DEF QuorumInv, Good, IsAcker, Has, Between
LEMMA CommitsInvUnch ==
    ASSUME CommitsInv, UNCHANGED <<commits, ledLog, leaders, msgs>> PROVE CommitsInv'
BY DEF CommitsInv, QC, IsAcker
LEMMA CommitIndexInvUnch ==
    ASSUME CommitIndexInv, UNCHANGED <<commitIndex, commits, currentTerm, log>>
    PROVE  CommitIndexInv'
BY DEF CommitIndexInv
LEMMA AppliedInvUnch == ASSUME AppliedInv, UNCHANGED <<applied, commits>> PROVE AppliedInv'
BY DEF AppliedInv

----
\* Leader logs.

LEMMA Match ==
    ASSUME NEW led, NEW X, NEW Y, LMc(led, X), LMc(led, Y),
           NEW k \in 1..Len(X), k <= Len(Y), k \in 1..Len(Y), X[k].term = Y[k].term
    PROVE  \A q \in 1..k : X[q] = Y[q]
BY DEF LMc

LEMMA TermHasLeader ==
    ASSUME NEW led, NEW X, LMc(led, X), NEW k \in 1..Len(X), X[k].term # 1
    PROVE  X[k].term \in DOMAIN led
<1> SUFFICES ASSUME X[k].term \notin DOMAIN led PROVE FALSE OBVIOUS
<1>1. LLc(led, X[k].term) = InitLog BY DEF LLc
<1>2. k <= Len(InitLog) /\ X[k] = InitLog[k] BY <1>1 DEF LMc
<1>3. k = 1 BY <1>2 DEF InitLog
<1> QED BY <1>2, <1>3 DEF InitLog, Entry
====
