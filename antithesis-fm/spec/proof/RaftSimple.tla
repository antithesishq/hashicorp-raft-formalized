---- MODULE RaftSimple ----
\* The actions that touch neither logs nor leader logs.
EXTENDS RaftMono

\* Only role, transfer, snap, base, lastApplied change.
LEMMA InvLocal ==
    ASSUME Inv, TypeOK', LeadersInv',
           UNCHANGED <<currentTerm, voteTerm, voteFor, log, commitIndex, confirmed, msgs,
                       votes, leaders, ledLog, commits, applied>>
    PROVE  Inv'
BY TermInvUnch, VotesInvUnch, OneVoteUnch, VoteReqInvUnch, GrantInvUnch, ElectionSafetyUnch,
   LogsInvUnch, AppendInvUnch, AckInvUnch, ConfirmedInvUnch, AckerInvUnch, VoterInvUnch,
   QuorumInvUnch, CommitsInvUnch, CommitIndexInvUnch, AppliedInvUnch DEF Inv

\* Only a message of a kind no invariant reads is added.
LEMMA InvMsg ==
    ASSUME Inv, NEW m, m.type \notin {"vote", "grant", "append", "ack"}, msgs' = msgs \cup {m},
           UNCHANGED <<currentTerm, voteTerm, voteFor, log, snap, role, commitIndex, lastApplied,
                       confirmed, votes, leaders, ledLog, commits, applied>>
    PROVE  Inv'
<1>0. msgs \subseteq msgs' /\ \A a \in msgs' \ msgs : a.type # "ack" /\ a.type # "grant" OBVIOUS
<1>1. TypeOK' BY TypeOKUnch DEF Inv
<1>2. \A j \in Server : currentTerm'[j] >= currentTerm[j] BY DEF Inv, TypeOK
<1> QED
  BY <1>0, <1>1, <1>2, TermInvUnch, VotesInvUnch, OneVoteUnch, VoteReqInvMsg, GrantInvMono,
     LeadersInvUnch, ElectionSafetyUnch,
     LogsInvUnch, AppendInvMsg, AckInvMono, ConfirmedInvUnch, AckerInvMono, VoterInvMono,
     QuorumInvMono, CommitsInvMono, CommitIndexInvUnch, AppliedInvUnch DEF Inv

LEMMA BecomeCandidateInv == ASSUME Inv, NEW i \in Server, BecomeCandidate(i) PROVE Inv'
<1> USE DEF BecomeCandidate, durable
<1>1. TypeOK' BY DEF Inv, TypeOK, Candidate
<1>2. LeadersInv' BY DEF Inv, TypeOK, LeadersInv, Candidate, Leader
<1> QED BY <1>1, <1>2, InvLocal

LEMMA BecomeFollowerInv == ASSUME Inv, NEW i \in Server, BecomeFollower(i) PROVE Inv'
<1> USE DEF BecomeFollower, durable
<1>1. TypeOK' BY DEF Inv, TypeOK, Follower
<1>2. LeadersInv' BY DEF Inv, TypeOK, LeadersInv, Follower, Leader
<1> QED BY <1>1, <1>2, InvLocal

LEMMA TimeoutNowInv == ASSUME Inv, NEW i \in Server, TimeoutNow(i) PROVE Inv'
<1> USE DEF TimeoutNow, durable
<1>1. TypeOK' BY DEF Inv, TypeOK, Candidate
<1>2. LeadersInv' BY DEF Inv, TypeOK, LeadersInv, Candidate, Leader
<1> QED BY <1>1, <1>2, InvLocal

LEMMA CompactLogInv == ASSUME Inv, NEW i \in Server, NEW b, CompactLog(i, b) PROVE Inv'
<1> USE DEF CompactLog
<1>1. TypeOK' BY TypeOKUnch DEF Inv
<1>2. LeadersInv' BY LeadersInvUnch DEF Inv
<1> QED BY <1>1, <1>2, InvLocal

LEMMA SendPreVoteInv == ASSUME Inv, NEW i \in Server, SendPreVote(i) PROVE Inv'
BY InvMsg DEF SendPreVote, PreVoteRequest, durable

LEMMA GrantPreVoteInv == ASSUME Inv, NEW i \in Server, NEW m, GrantPreVote(i, m) PROVE Inv'
BY InvMsg DEF GrantPreVote, durable

LEMMA SendTimeoutNowInv == ASSUME Inv, NEW i \in Server, NEW j, SendTimeoutNow(i, j) PROVE Inv'
BY InvMsg DEF SendTimeoutNow, durable

LEMMA SetVoteForInv == ASSUME Inv, NEW i \in Server, NEW c \in Server, SetVoteFor(i, c) PROVE Inv'
<1> USE DEF SetVoteFor
<1>1. TypeOK' BY DEF Inv, TypeOK
<1> QED
  BY <1>1, TermInvUnch, VotesInvUnch, OneVoteUnch, VoteReqInvUnch, GrantInvUnch, LeadersInvUnch,
     ElectionSafetyUnch, LogsInvUnch, AppendInvUnch, AckInvUnch, ConfirmedInvUnch, AckerInvUnch,
     VoterInvUnch, QuorumInvUnch, CommitsInvUnch, CommitIndexInvUnch, AppliedInvUnch DEF Inv

LEMMA GrantVoteInv ==
    ASSUME Inv, NEW i \in Server, NEW c, NEW t, GrantVote(i, c, t) PROVE Inv'
<1> USE DEF GrantVote, durable
<1> DEFINE m == [type |-> "grant", src |-> i, dst |-> c, term |-> t]
<1>0. msgs' = msgs \cup {m} /\ msgs \subseteq msgs' /\ \A a \in msgs' \ msgs : a.type # "ack"
  OBVIOUS
<1>1. TypeOK' BY TypeOKUnch DEF Inv
<1>2. \A j \in Server : currentTerm'[j] >= currentTerm[j] BY DEF Inv, TypeOK
<1>3. GrantInv'
  <2>1. [voter |-> i, term |-> t, cand |-> c] \in votes /\ votes' = votes OBVIOUS
  <2>2. GrantInv BY DEF Inv
  <2>3. m.type = "grant" /\ m.src = i /\ m.dst = c /\ m.term = t OBVIOUS
  <2> HIDE DEF m, GrantVote
  <2> QED BY <1>0, <2>1, <2>2, <2>3 DEF GrantInv
<1>4. VoteReqInv' BY <1>0, VoteReqInvMsg DEF Inv
<1>5. AppendInv' BY <1>0, AppendInvMsg DEF Inv
<1> HIDE DEF m
<1> QED
  BY <1>0, <1>1, <1>2, <1>3, <1>4, <1>5, TermInvUnch, VotesInvUnch, OneVoteUnch,
     LeadersInvUnch, ElectionSafetyUnch,
     LogsInvUnch, AckInvMono, ConfirmedInvUnch, AckerInvMono, VoterInvMono,
     QuorumInvMono, CommitsInvMono, CommitIndexInvUnch, AppliedInvUnch DEF Inv

LEMMA RestartInv == ASSUME Inv, NEW i \in Server, Restart(i) PROVE Inv'
<1> USE DEF Restart, durable
<1>1. TypeOK' BY DEF Inv, TypeOK, Follower
<1>2. LeadersInv' BY DEF Inv, TypeOK, LeadersInv, Follower, Leader
<1>3. CommitIndexInv'
  <2> SUFFICES ASSUME NEW j \in Server, commitIndex'[j] # 0
               PROVE  \E k \in commits' :
                         /\ k.term <= currentTerm'[j]
                         /\ commitIndex'[j] <= Len(k.entries)
                         /\ commitIndex'[j] <= Len(log'[j])
                         /\ \A q \in 1..commitIndex'[j] : log'[j][q] = k.entries[q]
    BY DEF CommitIndexInv
  <2>1. j # i /\ commitIndex'[j] = commitIndex[j] BY DEF Inv, TypeOK
  <2>2. CommitIndexInv BY DEF Inv
  <2> QED BY <2>1, <2>2 DEF CommitIndexInv
<1> QED
  BY <1>1, <1>2, <1>3, TermInvUnch, VotesInvUnch, OneVoteUnch, VoteReqInvUnch, GrantInvUnch,
     ElectionSafetyUnch, LogsInvUnch, AppendInvUnch, AckInvUnch, ConfirmedInvUnch, AckerInvUnch,
     VoterInvUnch, QuorumInvUnch, CommitsInvUnch, AppliedInvUnch DEF Inv

LEMMA ApplyInv == ASSUME Inv, NEW i \in Server, Apply(i) PROVE Inv'
<1> USE DEF Apply, durable
<1>1. TypeOK' BY DEF Inv, TypeOK
<1>2. AppliedInv'
  <2> DEFINE k == lastApplied[i] + 1
  <2>1. k \in Nat /\ k >= 1 /\ k <= commitIndex[i] /\ commitIndex[i] \in Nat BY DEF Inv, TypeOK
  <2>2. PICK kk \in commits : commitIndex[i] <= Len(kk.entries)
                              /\ \A q \in 1..commitIndex[i] : log[i][q] = kk.entries[q]
    BY <2>1 DEF Inv, CommitIndexInv
  <2>3. kk.entries \in Seq(EntryT) BY DEF Inv, TypeOK
  <2>4. k \in 1..Len(kk.entries) /\ kk.entries[k] = log[i][k] BY <2>1, <2>2, <2>3
  <2>5. applied' = applied \cup {[server |-> i, index |-> k, entry |-> log[i][k]]} /\ commits' = commits
    OBVIOUS
  <2> HIDE DEF k
  <2> QED BY <2>4, <2>5 DEF Inv, AppliedInv
<1> QED
  BY <1>1, <1>2, TermInvUnch, VotesInvUnch, OneVoteUnch, VoteReqInvUnch, GrantInvUnch,
     LeadersInvUnch, ElectionSafetyUnch, LogsInvUnch, AppendInvUnch, AckInvUnch,
     ConfirmedInvUnch, AckerInvUnch, VoterInvUnch, QuorumInvUnch, CommitsInvUnch,
     CommitIndexInvUnch DEF Inv

LEMMA TakeSnapshotInv == ASSUME Inv, NEW i \in Server, NEW k \in Nat, TakeSnapshot(i, k) PROVE Inv'
<1> USE DEF TakeSnapshot
<1>1. TypeOK'
  <2>1. snap[i] \in Seq(EntryT) /\ log[i] \in Seq(EntryT) /\ lastApplied[i] \in Nat
        /\ commitIndex[i] \in Nat
    BY DEF Inv, TypeOK
  <2>2. commitIndex[i] <= Len(log[i]) BY <2>1 DEF Inv, CommitIndexInv
  <2> DEFINE p == Len(snap[i])
  <2> DEFINE n == k - p
  <2>3. n \in Nat /\ k = p + n BY <2>1
  <2>4. p \in Nat /\ p + n <= Len(log[i]) BY <2>1, <2>2, <2>3
  <2>5. SubSeq(log[i], p + 1, p + n) \in Seq(EntryT) BY <2>1, <2>4, SubSeqSeg
  <2>6. Machine(i, k) \in Seq(EntryT) BY <2>1, <2>3, <2>5, ConcatFacts DEF Machine
  <2> HIDE DEF p, n
  <2> QED BY <2>6 DEF Inv, TypeOK
<1>2. LeadersInv' BY LeadersInvUnch DEF Inv
<1> QED BY <1>1, <1>2, InvLocal

LEMMA InstallSnapshotInv ==
    ASSUME Inv, NEW j \in Server, NEW m, InstallSnapshot(j, m) PROVE Inv'
<1> USE DEF InstallSnapshot
<1>1. TypeOK'
  <2>1. m.entries \in Seq(EntryT) BY DEF Inv, AppendInv, Installable
  <2> QED BY <2>1 DEF Inv, TypeOK
<1>2. LeadersInv' BY LeadersInvUnch DEF Inv
<1> QED BY <1>1, <1>2, InvLocal

LEMMA AdoptTermInv == ASSUME Inv, NEW i \in Server, NEW t \in Nat, AdoptTerm(i, t) PROVE Inv'
<1> USE DEF AdoptTerm
<1>1. TypeOK' BY DEF Inv, TypeOK, Follower
<1>2. \A j \in Server : currentTerm'[j] >= currentTerm[j] BY DEF Inv, TypeOK
<1>3. TermInv' BY DEF Inv, TypeOK, TermInv
<1>4. VoteReqInv'
  <2> SUFFICES ASSUME NEW m \in msgs, m.type = "vote"
               PROVE  /\ m.term <= currentTerm'[m.src]
                      /\ (m.term = currentTerm'[m.src] /\ m.term \notin DOMAIN ledLog) =>
                             m.lastLogIndex = Len(log[m.src]) /\ m.lastLogTerm = LastTerm(m.src)
    BY DEF Inv, VoteReqInv, LastTerm, TermAt
  <2>1. m.src \in Server /\ m.term \in Nat /\ m.term <= currentTerm[m.src]
        /\ ((m.term = currentTerm[m.src] /\ m.term \notin DOMAIN ledLog) =>
               m.lastLogIndex = Len(log[m.src]) /\ m.lastLogTerm = LastTerm(m.src))
    BY DEF Inv, VoteReqInv
  <2> QED BY <2>1, <1>2 DEF Inv, TypeOK
<1>5. LeadersInv' BY <1>2 DEF Inv, TypeOK, LeadersInv, Follower, Leader
<1>6. msgs \subseteq msgs' /\ \A a \in msgs' \ msgs : a.type # "ack" OBVIOUS
<1> QED
  BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, VotesInvUnch, OneVoteUnch, GrantInvUnch,
     ElectionSafetyUnch, LogsInvTerm, AppendInvUnch, AckInvMono, ConfirmedInvTerm,
     AckerInvMono, VoterInvUnch, QuorumInvUnch, CommitsInvUnch, CommitIndexInvTerm,
     AppliedInvUnch DEF Inv

LEMMA StartElectionInv == ASSUME Inv, NEW i \in Server, StartElection(i) PROVE Inv'
<1> USE DEF StartElection
<1> DEFINE m == VoteRequest(i, currentTerm[i] + 1)
<1>0. msgs' = msgs \cup {m} /\ m.type = "vote" /\ m.src = i /\ m.term = currentTerm[i] + 1
      /\ m.lastLogIndex = Len(log[i]) /\ m.lastLogTerm = LastTerm(i)
  BY DEF VoteRequest
<1>1. TypeOK' BY DEF Inv, TypeOK
<1>2. \A j \in Server : currentTerm'[j] >= currentTerm[j] BY DEF Inv, TypeOK
<1>3. TermInv' BY DEF Inv, TypeOK, TermInv
<1>4. VoteReqInv'
  <2>1. log[i] \in Seq(EntryT) /\ currentTerm[i] \in Nat /\ currentTerm[i] >= 1
        /\ currentTerm'[i] = currentTerm[i] + 1
    BY DEF Inv, TypeOK, TermInv
  <2>2. LastTerm(i) \in Nat
    <3>1. CASE Len(log[i]) > 0 /\ Len(log[i]) <= Len(log[i])
      <4>1. Len(log[i]) \in 1..Len(log[i]) BY <3>1, <2>1
      <4>2. log[i][Len(log[i])] \in EntryT BY <4>1, <2>1, ElementOfSeq
      <4> QED BY <3>1, <4>2 DEF LastTerm, TermAt, EntryT
    <3>2. CASE ~(Len(log[i]) > 0 /\ Len(log[i]) <= Len(log[i]))
      BY <3>2 DEF LastTerm, TermAt
    <3> QED BY <3>1, <3>2
  <2>3. /\ m.src \in Server /\ m.term \in Nat
        /\ m.lastLogIndex \in Nat /\ m.lastLogTerm \in Nat
        /\ m.term >= 2 /\ m.term <= currentTerm'[i]
        /\ m.lastLogIndex = Len(log'[i]) /\ m.lastLogTerm = LastTerm(i)'
    <3>1. log' = log OBVIOUS
    <3>2. LastTerm(i)' = LastTerm(i) BY <3>1 DEF LastTerm, TermAt
    <3> HIDE DEF m, StartElection
    <3> QED BY <1>0, <2>1, <2>2, <3>1, <3>2
  <2>4. ASSUME NEW a \in msgs, a.type = "vote"
        PROVE  /\ a.src \in Server /\ a.term \in Nat
               /\ a.lastLogIndex \in Nat /\ a.lastLogTerm \in Nat
               /\ a.term >= 2 /\ a.term <= currentTerm'[a.src]
               /\ (a.term = currentTerm'[a.src] /\ a.term \notin DOMAIN ledLog') =>
                     a.lastLogIndex = Len(log'[a.src]) /\ a.lastLogTerm = LastTerm(a.src)'
    <3>1. /\ a.src \in Server /\ a.term \in Nat
          /\ a.lastLogIndex \in Nat /\ a.lastLogTerm \in Nat
          /\ a.term >= 2 /\ a.term <= currentTerm[a.src]
          /\ ((a.term = currentTerm[a.src] /\ a.term \notin DOMAIN ledLog) =>
                 a.lastLogIndex = Len(log[a.src]) /\ a.lastLogTerm = LastTerm(a.src))
      BY <2>4 DEF Inv, VoteReqInv
    <3>2. log' = log /\ ledLog' = ledLog OBVIOUS
    <3>3. LastTerm(a.src)' = LastTerm(a.src) BY <3>2 DEF LastTerm, TermAt
    <3>4. currentTerm[a.src] \in Nat /\ currentTerm'[a.src] \in Nat
          /\ currentTerm'[a.src] >= currentTerm[a.src]
          /\ (a.src # i => currentTerm'[a.src] = currentTerm[a.src])
          /\ (a.src = i => currentTerm'[a.src] = currentTerm[a.src] + 1)
      BY <3>1 DEF Inv, TypeOK
    <3> HIDE DEF m, StartElection
    <3> QED BY <3>1, <3>2, <3>3, <3>4
  <2>5. \A a \in msgs' : a \in msgs \/ a = m BY <1>0
  <2>6. m.type = "vote" /\ m.src = i BY <1>0
  <2> HIDE DEF m, StartElection
  <2> QED BY <2>3, <2>4, <2>5, <2>6 DEF VoteReqInv
<1>5. LeadersInv' BY <1>2 DEF Inv, TypeOK, LeadersInv, Candidate, Leader
<1>6. msgs \subseteq msgs' /\ \A a \in msgs' \ msgs : a.type # "ack" /\ a.type # "grant" BY <1>0
<1>7. AppendInv' BY <1>0, AppendInvMsg DEF Inv
<1> HIDE DEF m
<1> QED
  BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, VotesInvUnch, OneVoteUnch, GrantInvMono,
     ElectionSafetyUnch, LogsInvTerm, AckInvMono, ConfirmedInvTerm,
     AckerInvMono, VoterInvMono, QuorumInvMono, CommitsInvMono, CommitIndexInvTerm,
     AppliedInvUnch DEF Inv
====
