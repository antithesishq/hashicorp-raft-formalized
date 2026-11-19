---- MODULE RaftSafety ----
\* The invariant is inductive; the safety properties of HashicorpRaft follow.
\* Lemmas assume IsFiniteSet(Server) (for Cardinality); the theorems
\* discharge it with ServerFinite.
EXTENDS RaftElect

THEOREM NextInv == ASSUME IsFiniteSet(Server), Inv, [Next]_vars PROVE Inv'
<1>a. TypeOK /\ LeadersInv /\ AppendInv BY DEF Inv
<1>1. CASE UNCHANGED vars
  <2>1. UNCHANGED <<currentTerm, voteTerm, voteFor, log, snap, role, commitIndex, lastApplied,
                    confirmed, msgs, votes, leaders, ledLog, commits, applied>>
    BY <1>1 DEF vars, protoVars
  <2>2. TypeOK' BY <2>1, <1>a, TypeOKUnch
  <2>3. LeadersInv' BY <2>1, <1>a, LeadersInvUnch
  <2> QED BY <2>1, <2>2, <2>3, InvLocal
<1>2. CASE Next
  <2>1. ASSUME NEW i \in Server,
               \/ BecomeCandidate(i) \/ BecomeFollower(i) \/ BecomeLeader(i)
               \/ StartElection(i) \/ SetVoteTerm(i) \/ Restart(i) \/ Apply(i)
        PROVE  Inv'
    BY <2>1, BecomeCandidateInv, BecomeFollowerInv, BecomeLeaderInv, StartElectionInv,
       SetVoteTermInv, RestartInv, ApplyInv
  <2>2. ASSUME NEW i \in Server, NEW k \in 1..lastApplied[i], TakeSnapshot(i, k) PROVE Inv'
    <3>1. k \in Nat BY <1>a DEF TypeOK
    <3> QED BY <3>1, <2>2, TakeSnapshotInv
  <2>3. ASSUME NEW i \in Server, NEW b \in 1..Len(snap[i]), CompactLog(i, b) PROVE Inv'
    BY <2>3, CompactLogInv
  <2>4. ASSUME NEW i \in Server, NEW t \in {currentTerm[k] : k \in Server}, AdoptTerm(i, t)
        PROVE  Inv'
    <3>1. t \in Nat BY <1>a DEF TypeOK
    <3> QED BY <3>1, <2>4, AdoptTermInv
  <2>5. ASSUME NEW i \in Server, NEW c \in Server, SetVoteFor(i, c) PROVE Inv'
    BY <2>5, SetVoteForInv
  <2>6. ASSUME NEW i \in Server, NEW v \in votes, v.voter = i /\ GrantVote(i, v.cand, v.term)
        PROVE  Inv'
    BY <2>6, GrantVoteInv
  <2>7. ASSUME NEW i \in Server, SendPreVote(i) \/ TimeoutNow(i) PROVE Inv'
    BY <2>7, SendPreVoteInv, TimeoutNowInv
  <2>8. ASSUME NEW i \in Server, NEW j \in Server, SendTimeoutNow(i, j) PROVE Inv'
    BY <2>8, SendTimeoutNowInv
  <2>9. ASSUME NEW i \in Server, NEW m \in msgs, m.type = "prevote" /\ GrantPreVote(i, m)
        PROVE  Inv'
    BY <2>9, GrantPreVoteInv
  <2>10. ASSUME NEW i \in Server, NEW ty \in {"noop", "barrier"},
                LeaderAppend(i, <<Entry(currentTerm[i], ty, Nil)>>)
         PROVE  Inv'
    <3> DEFINE e == Entry(currentTerm[i], ty, Nil)
    <3>1. e \in EntryT /\ e.term = currentTerm[i] BY <1>a DEF TypeOK, EntryT, Entry
    <3>2. LeaderAppend(i, <<e>>) BY <2>10
    <3> HIDE DEF e
    <3> QED BY <3>1, <3>2, LeaderAppendInv
  <2>11. ASSUME NEW i \in Server, NEW v \in Values,
                LeaderAppend(i, <<Entry(currentTerm[i], "command", v)>>)
         PROVE  Inv'
    <3> DEFINE e == Entry(currentTerm[i], "command", v)
    <3>1. e \in EntryT /\ e.term = currentTerm[i] BY <1>a DEF TypeOK, EntryT, Entry
    <3>2. LeaderAppend(i, <<e>>) BY <2>11
    <3> HIDE DEF e
    <3> QED BY <3>1, <3>2, LeaderAppendInv
  <2>12. ASSUME NEW i \in Server, NEW c \in 1..Len(log[i]), NEW l \in leaders,
                l.server = i /\ LeaderCommit(i, l.term, c)
         PROVE  Inv'
    <3>1. c \in Nat BY <1>a DEF TypeOK
    <3> QED BY <3>1, <2>12, LeaderCommitInv
  <2>13. ASSUME NEW i \in Server, NEW j \in Server, NEW l \in leaders, l.server = i,
                NEW p \in 0..Len(ledLog[l.term]), NEW n \in 0..Len(ledLog[l.term]),
                NEW c \in 0..Len(ledLog[l.term]), SendAppend(i, j, l.term, p, n, c)
         PROVE  Inv'
    <3>1. p \in Nat /\ n \in Nat /\ c \in Nat OBVIOUS
    <3> QED BY <3>1, <2>13, SendAppendInv
  <2>14. ASSUME NEW m \in msgs, m.type = "append", Ack(m.dst, m) PROVE Inv'
    <3>1. m.dst \in Server BY <2>14, <1>a DEF AppendInv
    <3> QED BY <3>1, <2>14, AckActInv
  <2>15. ASSUME NEW m \in msgs, m.type = "append", NEW k \in 1..Len(m.entries),
                DeleteSuffix(m.dst, m, k) \/ StoreEntries(m.dst, m, k)
         PROVE  Inv'
    <3>1. m.dst \in Server /\ m.entries \in Seq(EntryT) BY <2>15, <1>a DEF AppendInv
    <3>2. k \in Nat BY <3>1
    <3> QED BY <3>1, <3>2, <2>15, DeleteSuffixInv, StoreEntriesInv
  <2>16. ASSUME NEW m \in msgs, m.type = "append", NEW c \in 1..m.commit,
                FollowerCommit(m.dst, m, c)
         PROVE  Inv'
    <3>1. m.dst \in Server /\ m.commit \in Nat BY <2>16, <1>a DEF AppendInv
    <3>2. c \in Nat BY <3>1
    <3> QED BY <3>1, <3>2, <2>16, FollowerCommitInv
  <2>17. ASSUME NEW m \in msgs, m.type = "append", InstallSnapshot(m.dst, m) PROVE Inv'
    <3>1. m.dst \in Server BY <2>17, <1>a DEF AppendInv
    <3> QED BY <3>1, <2>17, InstallSnapshotInv
  <2> QED
    BY <1>2, <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9, <2>10, <2>11, <2>12, <2>13,
       <2>14, <2>15, <2>16, <2>17 DEF Next, ProtoNext
<1> QED BY <1>1, <1>2

\* ServerFinite is the spec's assumption IsFiniteSet(Server).
THEOREM InvInvariant == Spec => []Inv
<1>1. Init => Inv BY InitInv
<1>2. Inv /\ [Next]_vars => Inv' BY NextInv, ServerFinite
<1> QED BY <1>1, <1>2, PTL DEF Spec

----
\* The properties, in a state that satisfies the invariant.

LEMMA InvElectionSafety == Inv => ElectionSafety
BY DEF Inv

LEMMA InvLogMatching == Inv => LogMatching
<1> SUFFICES ASSUME Inv, NEW a \in Server, NEW b \in Server,
                    NEW k \in 1..Min(Len(log[a]), Len(log[b])),
                    log[a][k].term = log[b][k].term
             PROVE  SubSeq(log[a], 1, k) = SubSeq(log[b], 1, k)
  BY DEF LogMatching
<1>1. log[a] \in Seq(EntryT) /\ log[b] \in Seq(EntryT) /\ LMc(ledLog, log[a]) /\ LMc(ledLog, log[b])
  BY DEF Inv, TypeOK, LogsInv, LMlog
<1>2. k \in Nat /\ k \in 1..Len(log[a]) /\ k \in 1..Len(log[b]) /\ k <= Len(log[a]) /\ k <= Len(log[b])
  BY <1>1 DEF Min
<1>3. \A q \in 1..k : log[a][q] = log[b][q] BY <1>1, <1>2, Match
<1> DEFINE sa == SubSeq(log[a], 1, k)
<1> DEFINE sb == SubSeq(log[b], 1, k)
<1>4. sa \in Seq(EntryT) /\ Len(sa) = k /\ \A q \in 1..k : sa[q] = log[a][q]
  BY <1>1, <1>2, SubSeqPre
<1>5. sb \in Seq(EntryT) /\ Len(sb) = k /\ \A q \in 1..k : sb[q] = log[b][q]
  BY <1>1, <1>2, SubSeqPre
<1>6. sa = sb
  <2> HIDE DEF sa, sb
  <2>1. Len(sa) = Len(sb) /\ \A q \in 1..Len(sa) : sa[q] = sb[q] BY <1>3, <1>4, <1>5
  <2> QED BY <2>1, <1>4, <1>5, SeqPointwise
<1> QED BY <1>6

\* Two committed prefixes are both beginnings of one leader log.
LEMMA CommitsAgree ==
    ASSUME IsFiniteSet(Server), Inv, NEW a \in commits, NEW b \in commits
    PROVE  \E u \in DOMAIN ledLog :
              /\ ledLog[u] \in Seq(EntryT) /\ a.entries \in Seq(EntryT) /\ b.entries \in Seq(EntryT)
              /\ Len(a.entries) <= Len(ledLog[u])
              /\ \A q \in 1..Len(a.entries) : a.entries[q] = ledLog[u][q]
              /\ Len(b.entries) <= Len(ledLog[u])
              /\ \A q \in 1..Len(b.entries) : b.entries[q] = ledLog[u][q]
<1>1. /\ a.term \in Nat /\ b.term \in Nat /\ a.entries \in Seq(EntryT) /\ b.entries \in Seq(EntryT)
      /\ a.term \in DOMAIN ledLog /\ b.term \in DOMAIN ledLog
      /\ \A w \in DOMAIN ledLog : ledLog[w] \in Seq(EntryT)
  BY DEF Inv, TypeOK, CommitsInv
<1>2. CASE a.term <= b.term
  <2>1. /\ Len(a.entries) <= Len(ledLog[b.term])
        /\ \A q \in 1..Len(a.entries) : a.entries[q] = ledLog[b.term][q]
    BY <1>1, <1>2, CommitLed
  <2>2. /\ Len(b.entries) <= Len(ledLog[b.term])
        /\ \A q \in 1..Len(b.entries) : b.entries[q] = ledLog[b.term][q]
    BY <1>1, CommitLed
  <2> QED BY <1>1, <2>1, <2>2
<1>3. CASE b.term <= a.term
  <2>1. /\ Len(b.entries) <= Len(ledLog[a.term])
        /\ \A q \in 1..Len(b.entries) : b.entries[q] = ledLog[a.term][q]
    BY <1>1, <1>3, CommitLed
  <2>2. /\ Len(a.entries) <= Len(ledLog[a.term])
        /\ \A q \in 1..Len(a.entries) : a.entries[q] = ledLog[a.term][q]
    BY <1>1, CommitLed
  <2> QED BY <1>1, <2>1, <2>2
<1> QED BY <1>1, <1>2, <1>3

LEMMA InvCommitSafety == ASSUME IsFiniteSet(Server) PROVE Inv => CommitSafety
<1> SUFFICES ASSUME Inv, NEW a \in commits, NEW b \in commits
             PROVE  IsPrefix(a.entries, b.entries) \/ IsPrefix(b.entries, a.entries)
  BY DEF CommitSafety
<1> DEFINE ea == a.entries
<1> DEFINE eb == b.entries
<1>1. PICK u \in DOMAIN ledLog :
              /\ ledLog[u] \in Seq(EntryT) /\ ea \in Seq(EntryT) /\ eb \in Seq(EntryT)
              /\ Len(ea) <= Len(ledLog[u])
              /\ \A q \in 1..Len(ea) : ea[q] = ledLog[u][q]
              /\ Len(eb) <= Len(ledLog[u])
              /\ \A q \in 1..Len(eb) : eb[q] = ledLog[u][q]
  BY CommitsAgree
<1> HIDE DEF ea, eb
<1>2. CASE Len(ea) <= Len(eb)
  <2>1. \A q \in 1..Len(ea) : ea[q] = eb[q] BY <1>1, <1>2
  <2>2. IsPrefix(ea, eb) BY <1>1, <1>2, <2>1, PrefixPointwise
  <2> QED BY <2>2 DEF ea, eb
<1>3. CASE Len(eb) <= Len(ea)
  <2>1. \A q \in 1..Len(eb) : eb[q] = ea[q] BY <1>1, <1>3
  <2>2. IsPrefix(eb, ea) BY <1>1, <1>3, <2>1, PrefixPointwise
  <2> QED BY <2>2 DEF ea, eb
<1> QED BY <1>1, <1>2, <1>3

LEMMA InvStateMachineSafety == ASSUME IsFiniteSet(Server) PROVE Inv => StateMachineSafety
<1> SUFFICES ASSUME Inv, NEW a \in applied, NEW b \in applied, a.index = b.index
             PROVE  a.entry = b.entry
  BY DEF StateMachineSafety
<1>1. PICK ka \in commits : a.index \in 1..Len(ka.entries) /\ ka.entries[a.index] = a.entry
  BY DEF Inv, AppliedInv
<1>2. PICK kb \in commits : b.index \in 1..Len(kb.entries) /\ kb.entries[b.index] = b.entry
  BY DEF Inv, AppliedInv
<1>3. PICK u \in DOMAIN ledLog :
              /\ \A q \in 1..Len(ka.entries) : ka.entries[q] = ledLog[u][q]
              /\ \A q \in 1..Len(kb.entries) : kb.entries[q] = ledLog[u][q]
  BY CommitsAgree
<1> QED BY <1>1, <1>2, <1>3

LEMMA InvLeaderCompleteness == ASSUME IsFiniteSet(Server) PROVE Inv => LeaderCompleteness
<1> SUFFICES ASSUME Inv, NEW i \in Server, NEW c \in commits,
                    role[i] = Leader, c.term < currentTerm[i]
             PROVE  IsPrefix(c.entries, log[i])
  BY DEF LeaderCompleteness
<1> DEFINE T == currentTerm[i]
<1>1. TypeOK /\ LeadersInv BY DEF Inv
<1>2. [server |-> i, term |-> T] \in leaders BY <1>1 DEF LeadersInv
<1>3. T \in DOMAIN ledLog /\ log[i] = ledLog[T] BY <1>2, <1>1 DEF LeadersInv
<1>4. T \in Nat /\ c.term \in Nat /\ c.term <= T /\ c.entries \in Seq(EntryT)
      /\ log[i] \in Seq(EntryT)
  BY <1>1 DEF TypeOK
<1>5. /\ Len(c.entries) <= Len(ledLog[T])
      /\ \A q \in 1..Len(c.entries) : c.entries[q] = ledLog[T][q]
  BY <1>3, <1>4, CommitLed
<1> QED BY <1>3, <1>4, <1>5, PrefixPointwise

----
\* The safety properties of the spec.

THEOREM ElectionSafetyThm == Spec => []ElectionSafety
BY InvInvariant, InvElectionSafety, PTL

THEOREM LogMatchingThm == Spec => []LogMatching
BY InvInvariant, InvLogMatching, PTL

THEOREM CommitSafetyThm == Spec => []CommitSafety
<1>1. Inv => CommitSafety BY InvCommitSafety, ServerFinite
<1> QED BY <1>1, InvInvariant, PTL

THEOREM StateMachineSafetyThm == Spec => []StateMachineSafety
<1>1. Inv => StateMachineSafety BY InvStateMachineSafety, ServerFinite
<1> QED BY <1>1, InvInvariant, PTL

THEOREM LeaderCompletenessThm == Spec => []LeaderCompleteness
<1>1. Inv => LeaderCompleteness BY InvLeaderCompleteness, ServerFinite
<1> QED BY <1>1, InvInvariant, PTL
====
