---- MODULE RaftCommit ----
\* SetVoteTerm, SendAppend, LeaderCommit, FollowerCommit.
EXTENDS RaftSimple

LEMMA SetVoteTermInv == ASSUME Inv, NEW i \in Server, SetVoteTerm(i) PROVE Inv'
<1> DEFINE u == currentTerm[i]
<1> DEFINE nv == [voter |-> i, term |-> u, cand |-> voteFor[i]]
<1>0. /\ voteTerm[i] # u /\ voteFor[i] # Nil /\ MayVote(i, voteFor[i])
      /\ voteTerm' = [voteTerm EXCEPT ![i] = u]
      /\ votes' = votes \cup {nv}
      /\ UNCHANGED <<transfer, currentTerm, voteFor, log, snap, base, role, commitIndex,
                     lastApplied, confirmed, msgs, leaders, ledLog, commits, applied>>
  BY DEF SetVoteTerm
<1>a. TypeOK /\ TermInv /\ VotesInv /\ OneVotePerTerm /\ VoteReqInv /\ AckerInv /\ VoterInv /\ LogsInv
  BY DEF Inv
<1>b. u \in Nat /\ voteTerm[i] \in Nat /\ voteTerm[i] <= u /\ voteFor[i] \in Server
      /\ nv.voter = i /\ nv.term = u /\ nv.cand = voteFor[i]
  BY <1>0, <1>a DEF TypeOK, TermInv
<1>c. PICK vm \in msgs : /\ vm.type = "vote" /\ vm.src = voteFor[i] /\ vm.term = u
                         /\ UpToDate(vm, i)
  BY <1>0 DEF MayVote
<1>d. vm.term >= 2 /\ vm.lastLogIndex \in Nat /\ vm.lastLogTerm \in Nat
  BY <1>a, <1>c DEF VoteReqInv
<1> HIDE DEF u, nv
<1>1. TypeOK' BY <1>0, <1>a, <1>b DEF TypeOK, u, nv
<1>2. TermInv' BY <1>0, <1>a, <1>b DEF TermInv, TypeOK, u
<1>3. VotesInv'
  <2> SUFFICES ASSUME NEW v \in votes'
               PROVE  v.term <= voteTerm'[v.voter] /\ v.term >= 2
    BY DEF VotesInv
  <2>1. CASE v = nv BY <2>1, <1>0, <1>a, <1>b, <1>c, <1>d DEF TypeOK
  <2>2. CASE v \in votes
    <3>1. v.term <= voteTerm[v.voter] /\ v.term >= 2 /\ v.voter \in Server /\ v.term \in Nat
      BY <2>2, <1>a DEF VotesInv, TypeOK
    <3>2. voteTerm[v.voter] \in Nat /\ voteTerm'[v.voter] \in Nat
          /\ voteTerm'[v.voter] >= voteTerm[v.voter]
      BY <3>1, <1>0, <1>a, <1>b DEF TypeOK
    <3> QED BY <3>1, <3>2
  <2> QED BY <2>1, <2>2, <1>0
<1>4. OneVotePerTerm'
  <2> SUFFICES ASSUME NEW a \in votes', NEW b \in votes', a.voter = b.voter, a.term = b.term
               PROVE  a.cand = b.cand
    BY DEF OneVotePerTerm
  <2>1. \A v \in votes : v.voter = i => v.term # u
    <3> SUFFICES ASSUME NEW v \in votes, v.voter = i PROVE v.term # u OBVIOUS
    <3>1. v.term <= voteTerm[i] /\ v.term \in Nat BY <1>a DEF VotesInv, TypeOK
    <3> QED BY <3>1, <1>0, <1>b
  <2>2. CASE a \in votes /\ b \in votes BY <2>2, <1>a DEF OneVotePerTerm
  <2> QED BY <2>1, <2>2, <1>0, <1>b
<1>5. VoterInv'
  <2> SUFFICES ASSUME NEW v \in votes', NEW t \in DOMAIN ledLog, NEW c \in 1..Len(ledLog[t]),
                      t < v.term, v.term \notin DOMAIN ledLog, ledLog[t][c].term = t,
                      IsAcker(v.voter, t, c), Between(t, c, v.term)
               PROVE  \E m \in msgs : /\ m.type = "vote" /\ m.src = v.cand /\ m.term = v.term
                                      /\ \/ m.lastLogTerm > t
                                         \/ m.lastLogTerm = t /\ m.lastLogIndex >= c
    BY <1>0 DEF VoterInv, IsAcker, Between, Has
  <2>1. CASE v \in votes BY <2>1, <1>a DEF VoterInv
  <2>2. CASE v = nv
    <3>1. v.voter = i /\ v.term = u /\ v.cand = voteFor[i] BY <2>2, <1>b
    <3>2. t \in Nat /\ ledLog[t] \in Seq(EntryT) /\ log[i] \in Seq(EntryT) /\ c \in Nat
      BY <1>a DEF TypeOK
    <3>3. \A w \in DOMAIN ledLog : t < w /\ w <= currentTerm[i] => Has(ledLog[w], c, t)
      <4> SUFFICES ASSUME NEW w \in DOMAIN ledLog, t < w, w <= u PROVE Has(ledLog[w], c, t)
        BY DEF u
      <4>1. w \in Nat /\ w # u BY <3>1, <1>a DEF TypeOK
      <4>2. w < u BY <4>1, <1>b
      <4> QED BY <4>2, <3>1 DEF Between
    <3>4. Has(log[i], c, t) BY <3>1, <3>3, <1>a DEF AckerInv
    <3>5. c <= Len(log[i]) /\ log[i][c].term = t /\ Len(log[i]) \in 1..Len(log[i])
          /\ c \in 1..Len(log[i])
      BY <3>4, <3>2 DEF Has
    <3>6. log[i][c].term <= log[i][Len(log[i])].term BY <3>5, <1>a DEF LogsInv, Mono
    <3>7. LastTerm(i) = log[i][Len(log[i])].term BY <3>5, <3>2 DEF LastTerm, TermAt
    <3>8. log[i][Len(log[i])] \in EntryT BY <3>5, <3>2, ElementOfSeq
    <3>9. LastTerm(i) \in Nat /\ LastTerm(i) >= t BY <3>5, <3>6, <3>7, <3>8 DEF EntryT
    <3>10. \/ vm.lastLogTerm > t
           \/ vm.lastLogTerm = t /\ vm.lastLogIndex >= c
      BY <1>c, <1>d, <3>9, <3>5, <3>2 DEF UpToDate
    <3> QED BY <3>10, <1>c, <3>1
  <2> QED BY <2>1, <2>2, <1>0
<1>6. msgs \subseteq msgs' /\ (\A a \in msgs' \ msgs : a.type # "ack" /\ a.type # "grant")
      /\ votes \subseteq votes'
  BY <1>0
<1> QED
  BY <1>0, <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, VoteReqInvUnch, GrantInvMono, LeadersInvUnch,
     ElectionSafetyUnch, LogsInvUnch, AppendInvUnch, AckInvUnch, ConfirmedInvUnch, AckerInvUnch,
     QuorumInvMono, CommitsInvUnch, CommitIndexInvUnch, AppliedInvUnch DEF Inv

LEMMA SendAppendInv ==
    ASSUME Inv, NEW i \in Server, NEW j \in Server, NEW t, NEW p \in Nat, NEW n \in Nat,
           NEW c \in Nat, SendAppend(i, j, t, p, n, c)
    PROVE  Inv'
<1> DEFINE es == SubSeq(ledLog[t], p + 1, p + n)
<1> DEFINE m == [type |-> "append", src |-> i, dst |-> j, term |-> t,
                 prevLogIndex |-> p, prevLogTerm |-> TermAt(ledLog[t], p),
                 entries |-> es, commit |-> c]
<1>0. /\ [server |-> i, term |-> t] \in leaders /\ j # i /\ p + n <= Len(ledLog[t])
      /\ CommittedIn(ledLog[t], c, t)
      /\ msgs' = msgs \cup {m}
      /\ UNCHANGED <<transfer, durable, role, commitIndex, lastApplied, confirmed, votes,
                     leaders, ledLog, commits, applied>>
  BY DEF SendAppend
<1>a. TypeOK /\ LeadersInv /\ AppendInv BY DEF Inv
<1>b. t \in DOMAIN ledLog /\ ledLog[t] \in Seq(EntryT)
  BY <1>0, <1>a DEF LeadersInv, TypeOK
<1>c. es \in Seq(EntryT) /\ Len(es) = n /\ \A q \in 1..n : es[q] = ledLog[t][p + q]
  BY <1>0, <1>b, SubSeqSeg
<1>d. \/ c = 0
      \/ \E k \in commits : k.term <= t /\ c <= Len(k.entries)
  BY <1>0 DEF CommittedIn, KnownIn
<1>e. /\ m.type = "append" /\ m.src = i /\ m.dst = j /\ m.term = t /\ m.prevLogIndex = p
      /\ m.prevLogTerm = TermAt(ledLog[t], p) /\ m.entries = es /\ m.commit = c
  OBVIOUS
<1> HIDE DEF es, m
<1>1. TypeOK' BY <1>0, <1>a, TypeOKUnch DEF durable
<1>2. \A jj \in Server : currentTerm'[jj] >= currentTerm[jj] BY <1>0, <1>a DEF TypeOK, durable
<1>3. AppendInv'
  <2> SUFFICES ASSUME NEW a \in msgs', a.type = "append"
               PROVE  /\ a.src \in Server /\ a.dst \in Server /\ a.dst # a.src
                      /\ [server |-> a.src, term |-> a.term] \in leaders
                      /\ a.prevLogIndex \in Nat /\ a.commit \in Nat /\ a.entries \in Seq(EntryT)
                      /\ a.prevLogIndex + Len(a.entries) <= Len(ledLog[a.term])
                      /\ a.prevLogTerm = TermAt(ledLog[a.term], a.prevLogIndex)
                      /\ \A q \in 1..Len(a.entries) : a.entries[q] = ledLog[a.term][a.prevLogIndex + q]
                      /\ \/ a.commit = 0
                         \/ \E k \in commits : k.term <= a.term /\ a.commit <= Len(k.entries)
    BY <1>0 DEF AppendInv, TermAt
  <2>1. CASE a \in msgs BY <2>1, <1>a DEF AppendInv
  <2>2. CASE a = m BY <2>2, <1>0, <1>b, <1>c, <1>d, <1>e
  <2> QED BY <2>1, <2>2, <1>0
<1>4. msgs \subseteq msgs' /\ (\A a \in msgs' \ msgs : a.type # "ack" /\ a.type # "grant")
      /\ votes \subseteq votes' /\ m.type # "vote"
  BY <1>0, <1>e
<1> QED
  BY <1>0, <1>1, <1>2, <1>3, <1>4, TermInvUnch, VotesInvUnch, OneVoteUnch, VoteReqInvMsg,
     GrantInvMono, LeadersInvUnch, ElectionSafetyUnch, LogsInvUnch, AckInvMono,
     ConfirmedInvUnch, AckerInvMono, VoterInvMono, QuorumInvMono, CommitsInvMono,
     CommitIndexInvUnch, AppliedInvUnch DEF Inv, durable

----
\* A committed prefix is recorded: what LeaderCommit and FollowerCommit share.
LEMMA CommitRecordInv ==
    ASSUME Inv, NEW j \in Server, NEW T \in Nat, NEW c \in Nat, NEW ci \in Nat,
           c >= 1, c <= Len(log[j]),
           commits' = commits \cup {[server |-> j, term |-> T, entries |-> SubSeq(log[j], 1, c)]},
           commitIndex' = [commitIndex EXCEPT ![j] = ci],
           ci = c \/ ci = commitIndex[j],
           UNCHANGED <<transfer, durable, role, lastApplied, confirmed, msgs, votes, leaders,
                       ledLog, applied>>,
           T <= currentTerm[j],
           T \in DOMAIN ledLog,
           c <= Len(ledLog[T]),
           \A q \in 1..c : log[j][q] = ledLog[T][q],
           \E t \in DOMAIN ledLog : \E c0 \in 1..Len(ledLog[t]) : t <= T /\ c <= c0 /\ QC(t, c0)
    PROVE  Inv'
<1> DEFINE es == SubSeq(log[j], 1, c)
<1> DEFINE nk == [server |-> j, term |-> T, entries |-> es]
<1>a. TypeOK /\ CommitsInv /\ CommitIndexInv /\ AppendInv /\ AppliedInv BY DEF Inv
<1>b. log[j] \in Seq(EntryT) BY <1>a DEF TypeOK
<1>c. es \in Seq(EntryT) /\ Len(es) = c /\ \A q \in 1..c : es[q] = log[j][q]
  BY <1>b, SubSeqPre
<1>d. nk.server = j /\ nk.term = T /\ nk.entries = es /\ commits' = commits \cup {nk}
  OBVIOUS
<1> HIDE DEF es, nk
<1>1. TypeOK'
  <2>1. nk \in [server : Server, term : Nat, entries : Seq(EntryT)] BY <1>c DEF nk
  <2>2. commits' \subseteq [server : Server, term : Nat, entries : Seq(EntryT)]
    BY <2>1, <1>d, <1>a DEF TypeOK
  <2>3. commitIndex' \in [Server -> Nat] BY <1>a DEF TypeOK
  <2>4. UNCHANGED <<currentTerm, voteTerm, voteFor, log, snap, role, lastApplied, confirmed,
                    votes, leaders, ledLog>>
    BY DEF durable
  <2> QED BY <2>2, <2>3, <2>4, <1>a DEF TypeOK
<1>2. AppendInv'
  <2>1. \A a \in msgs : a.type = "append" =>
           \/ a.commit = 0
           \/ \E k \in commits' : k.term <= a.term /\ a.commit <= Len(k.entries)
    BY <1>a, <1>d DEF AppendInv
  <2> QED BY <2>1, <1>a DEF AppendInv, TermAt
<1>3. CommitsInv'
  <2> SUFFICES ASSUME NEW k \in commits'
               PROVE  /\ k.term \in DOMAIN ledLog
                      /\ Len(k.entries) <= Len(ledLog[k.term])
                      /\ \A q \in 1..Len(k.entries) : k.entries[q] = ledLog[k.term][q]
                      /\ \E t \in DOMAIN ledLog : \E c0 \in 1..Len(ledLog[t]) :
                            t <= k.term /\ Len(k.entries) <= c0 /\ QC(t, c0)
    BY DEF CommitsInv, QC, IsAcker
  <2>1. CASE k \in commits BY <2>1, <1>a DEF CommitsInv
  <2>2. CASE k = nk BY <2>2, <1>c, <1>d
  <2> QED BY <2>1, <2>2, <1>d
<1>4. CommitIndexInv'
  <2> SUFFICES ASSUME NEW i \in Server, commitIndex'[i] # 0
               PROVE  \E k \in commits' :
                         /\ k.term <= currentTerm[i]
                         /\ commitIndex'[i] <= Len(k.entries)
                         /\ commitIndex'[i] <= Len(log[i])
                         /\ \A q \in 1..commitIndex'[i] : log[i][q] = k.entries[q]
    BY DEF CommitIndexInv, durable
  <2>1. CASE commitIndex'[i] = commitIndex[i]
    <3>1. PICK k \in commits :
                         /\ k.term <= currentTerm[i]
                         /\ commitIndex[i] <= Len(k.entries)
                         /\ commitIndex[i] <= Len(log[i])
                         /\ \A q \in 1..commitIndex[i] : log[i][q] = k.entries[q]
      BY <2>1, <1>a DEF CommitIndexInv
    <3> QED BY <3>1, <2>1, <1>d
  <2>2. CASE commitIndex'[i] # commitIndex[i]
    <3>1. i = j /\ commitIndex'[i] = c BY <2>2, <1>a DEF TypeOK
    <3>2. nk \in commits' BY <1>d
    <3> QED BY <3>1, <3>2, <1>c, <1>d
  <2> QED BY <2>1, <2>2
<1>5. AppliedInv' BY <1>a, <1>d DEF AppliedInv
<1> QED
  BY <1>1, <1>2, <1>3, <1>4, <1>5, TermInvUnch, VotesInvUnch, OneVoteUnch, VoteReqInvUnch,
     GrantInvUnch, LeadersInvUnch, ElectionSafetyUnch, LogsInvUnch, AckInvUnch,
     ConfirmedInvUnch, AckerInvUnch, VoterInvUnch, QuorumInvUnch DEF Inv, durable

LEMMA LeaderCommitInv ==
    ASSUME Inv, NEW i \in Server, NEW t, NEW c \in Nat, LeaderCommit(i, t, c)
    PROVE  Inv'
<1>0. /\ [server |-> i, term |-> t] \in leaders /\ c >= 1 /\ c <= Len(log[i])
      /\ log[i][c].term = t /\ IsQuorum(Acked(i, t, c))
      /\ commitIndex' = [commitIndex EXCEPT ![i] = Max(@, c)]
      /\ commits' = commits \cup {Committed(i, t, c)}
      /\ UNCHANGED <<transfer, durable, role, lastApplied, confirmed, msgs, votes, leaders,
                     ledLog, applied>>
  BY DEF LeaderCommit
<1>a. TypeOK /\ LeadersInv /\ LogsInv BY DEF Inv
<1>b. t \in Nat /\ t \in DOMAIN ledLog /\ t <= currentTerm[i] /\ t >= 2
      /\ log[i] \in Seq(EntryT) /\ commitIndex[i] \in Nat
  BY <1>0, <1>a DEF TypeOK, LeadersInv
<1>c. c \in 1..Len(log[i]) /\ LMc(ledLog, log[i]) BY <1>0, <1>b, <1>a DEF LogsInv, LMlog
<1>d. c <= Len(ledLog[t]) /\ \A q \in 1..c : log[i][q] = ledLog[t][q]
  BY <1>0, <1>b, <1>c DEF LMc, LLc
<1>e. QC(t, c)
  <2>1. ledLog[t][c].term = t BY <1>0, <1>d
  <2>2. Acked(i, t, c) \in SUBSET Server BY DEF Acked
  <2>3. \A j \in Acked(i, t, c) : IsAcker(j, t, c) BY <1>0 DEF Acked, IsAcker
  <2> QED BY <2>1, <2>2, <2>3, <1>0 DEF QC
<1>f. Max(commitIndex[i], c) \in Nat
      /\ (Max(commitIndex[i], c) = c \/ Max(commitIndex[i], c) = commitIndex[i])
  BY <1>b DEF Max
<1>g. c \in 1..Len(ledLog[t]) BY <1>d, <1>0
<1>h. \E t0 \in DOMAIN ledLog : \E c0 \in 1..Len(ledLog[t0]) : t0 <= t /\ c <= c0 /\ QC(t0, c0)
  BY <1>b, <1>e, <1>g
<1> DEFINE ci == Max(commitIndex[i], c)
<1>i. /\ commits' = commits \cup {[server |-> i, term |-> t, entries |-> SubSeq(log[i], 1, c)]}
      /\ commitIndex' = [commitIndex EXCEPT ![i] = ci]
      /\ ci \in Nat /\ (ci = c \/ ci = commitIndex[i])
  BY <1>0, <1>f DEF Committed
<1>j. /\ c >= 1 /\ c <= Len(log[i])
      /\ UNCHANGED <<transfer, durable, role, lastApplied, confirmed, msgs, votes, leaders,
                     ledLog, applied>>
  BY <1>0
<1> HIDE DEF ci
<1> QED BY <1>b, <1>d, <1>h, <1>i, <1>j, CommitRecordInv

LEMMA FollowerCommitInv ==
    ASSUME Inv, NEW j \in Server, NEW m, NEW c \in Nat, FollowerCommit(j, m, c)
    PROVE  Inv'
<1> DEFINE T == confirmed[j].term
<1>0. /\ m \in msgs /\ m.type = "append" /\ m.dst = j /\ m.term = T
      /\ c > commitIndex[j] /\ c <= Min(m.commit, confirmed[j].index)
      /\ commitIndex' = [commitIndex EXCEPT ![j] = c]
      /\ commits' = commits \cup {Committed(j, T, c)}
      /\ UNCHANGED <<transfer, durable, role, lastApplied, confirmed, msgs, votes, leaders,
                     ledLog, applied>>
  BY DEF FollowerCommit
<1>a. TypeOK /\ ConfirmedInv /\ AppendInv /\ CommitsInv BY DEF Inv
<1>b. /\ T \in Nat /\ confirmed[j].index \in Nat /\ commitIndex[j] \in Nat /\ m.commit \in Nat
  BY <1>0, <1>a DEF TypeOK, AppendInv
<1>c. c >= 1 /\ c <= m.commit /\ c <= confirmed[j].index BY <1>0, <1>b DEF Min
<1>d. /\ T <= currentTerm[j] /\ confirmed[j].index <= Len(log[j]) /\ T \in DOMAIN ledLog
      /\ confirmed[j].index <= Len(ledLog[T])
      /\ \A q \in 1..confirmed[j].index : log[j][q] = ledLog[T][q]
  BY <1>a, <1>b, <1>c DEF ConfirmedInv
<1>e0. \/ m.commit = 0
       \/ \E k \in commits : k.term <= m.term /\ m.commit <= Len(k.entries)
  BY <1>0, <1>a DEF AppendInv
<1>e. PICK k0 \in commits : k0.term <= T /\ m.commit <= Len(k0.entries)
  BY <1>0, <1>e0, <1>b, <1>c
<1>f. PICK t \in DOMAIN ledLog : \E c0 \in 1..Len(ledLog[t]) :
            t <= k0.term /\ Len(k0.entries) <= c0 /\ QC(t, c0)
  BY <1>a DEF CommitsInv
<1>g. k0.term \in Nat /\ k0.entries \in Seq(EntryT) /\ t \in Nat /\ ledLog[t] \in Seq(EntryT)
      /\ log[j] \in Seq(EntryT) /\ ledLog[T] \in Seq(EntryT)
  BY <1>a, <1>d DEF TypeOK
<1>h. \E t0 \in DOMAIN ledLog : \E c0 \in 1..Len(ledLog[t0]) : t0 <= T /\ c <= c0 /\ QC(t0, c0)
  BY <1>b, <1>c, <1>e, <1>f, <1>g
<1>i. c <= Len(log[j]) /\ c <= Len(ledLog[T]) /\ \A q \in 1..c : log[j][q] = ledLog[T][q]
  BY <1>b, <1>c, <1>d, <1>g
<1>j. /\ commits' = commits \cup {[server |-> j, term |-> T, entries |-> SubSeq(log[j], 1, c)]}
      /\ commitIndex' = [commitIndex EXCEPT ![j] = c]
      /\ UNCHANGED <<transfer, durable, role, lastApplied, confirmed, msgs, votes, leaders,
                     ledLog, applied>>
  BY <1>0 DEF Committed
<1> HIDE DEF T
<1> QED BY <1>b, <1>c, <1>d, <1>h, <1>i, <1>j, CommitRecordInv
====
