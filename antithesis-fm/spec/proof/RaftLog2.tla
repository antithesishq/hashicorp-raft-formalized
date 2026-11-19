---- MODULE RaftLog2 ----
\* DeleteSuffix and StoreEntries.
EXTENDS RaftLog

\* What the two share: node j, in the term T of a request, changes its log
\* and has it confirmed up to r.  The new log has the leader log of T up to
\* r, and keeps whatever of the old log agreed with that leader log.
LEMMA FollowerLogInv ==
    ASSUME IsFiniteSet(Server), Inv, NEW j \in Server, NEW T \in DOMAIN ledLog, NEW r \in Nat,
           NEW nl \in Seq(EntryT),
           T = currentTerm[j],
           \E src \in Server : src # j /\ [server |-> src, term |-> T] \in leaders,
           log' = [log EXCEPT ![j] = nl],
           confirmed' = [confirmed EXCEPT ![j] = [term |-> T, index |-> r]],
           UNCHANGED <<transfer, currentTerm, voteTerm, voteFor, snap, base, role, commitIndex,
                       lastApplied, msgs, votes, leaders, ledLog, commits, applied>>,
           r <= Len(nl), r <= Len(ledLog[T]),
           \A q \in 1..r : nl[q] = ledLog[T][q],
           \* the new log is a beginning of the old one or of the leader log
           \/ Len(nl) <= Len(log[j]) /\ \A q \in 1..Len(nl) : nl[q] = log[j][q]
           \/ Len(nl) <= Len(ledLog[T]) /\ \A q \in 1..Len(nl) : nl[q] = ledLog[T][q],
           \* what agreed with the leader log is kept
           \A c \in 1..Len(log[j]) :
               c <= Len(ledLog[T]) /\ log[j][c].term = ledLog[T][c].term =>
                  c <= Len(nl) /\ nl[c] = log[j][c]
    PROVE  Inv'
<1>a. /\ TypeOK /\ TermInv /\ VoteReqInv /\ LeadersInv /\ ElectionSafety /\ LogsInv /\ AckInv
      /\ ConfirmedInv /\ AckerInv /\ CommitIndexInv
  BY DEF Inv
<1>b. /\ T \in Nat /\ ledLog[T] \in Seq(EntryT) /\ log[j] \in Seq(EntryT)
      /\ LMc(ledLog, ledLog[T]) /\ LMc(ledLog, log[j]) /\ Mono(ledLog[T]) /\ Mono(log[j])
      /\ \A k \in 1..Len(ledLog[T]) : ledLog[T][k].term <= T
      /\ \A k \in 1..Len(log[j]) : log[j][k].term <= T
  BY <1>a DEF TypeOK, LogsInv, LMlog
<1>c. log'[j] = nl /\ \A jj \in Server : jj # j => log'[jj] = log[jj]
  BY <1>a DEF TypeOK
<1>d. \A l \in leaders : ~(l.server = j /\ l.term = T)
  <2> SUFFICES ASSUME NEW l \in leaders, l.server = j, l.term = T PROVE FALSE OBVIOUS
  <2>1. PICK src \in Server : src # j /\ [server |-> src, term |-> T] \in leaders OBVIOUS
  <2> QED BY <2>1, <1>a DEF ElectionSafety
<1>1. TypeOK'
  <2>1. log' \in [Server -> Seq(EntryT)] BY <1>a DEF TypeOK
  <2>2. confirmed' \in [Server -> [term : Nat, index : Nat]] BY <1>a, <1>b DEF TypeOK
  <2> QED BY <2>1, <2>2, <1>a DEF TypeOK
<1>2. VoteReqInv'
  <2> SUFFICES ASSUME NEW a \in msgs, a.type = "vote",
                      a.term = currentTerm[a.src], a.term \notin DOMAIN ledLog
               PROVE  a.lastLogIndex = Len(log'[a.src]) /\ a.lastLogTerm = LastTerm(a.src)'
    BY <1>a DEF VoteReqInv
  <2>1. a.src \in Server /\ a.lastLogIndex = Len(log[a.src]) /\ a.lastLogTerm = LastTerm(a.src)
    BY <1>a DEF VoteReqInv
  <2>2. a.src # j OBVIOUS
  <2>3. log'[a.src] = log[a.src] BY <2>1, <2>2, <1>c
  <2> QED BY <2>1, <2>3 DEF LastTerm, TermAt
<1>3. LeadersInv'
  <2>1. ASSUME NEW l \in leaders, currentTerm[l.server] = l.term
        PROVE  log'[l.server] = ledLog[l.term]
    <3>1. l.server \in Server /\ l.server # j BY <2>1, <1>d, <1>a DEF TypeOK
    <3> QED BY <3>1, <2>1, <1>c, <1>a DEF LeadersInv
  <2> QED BY <2>1, <1>a DEF LeadersInv
<1>4. LogsInv'
  <2>1. ASSUME NEW i \in Server
        PROVE  /\ LMc(ledLog, log'[i]) /\ Mono(log'[i])
               /\ \A k \in 1..Len(log'[i]) : log'[i][k].term <= currentTerm[i]
    <3>1. CASE i # j BY <3>1, <1>c, <1>a DEF LogsInv, LMlog
    <3>2. CASE i = j
      <4>1. CASE Len(nl) <= Len(log[j]) /\ \A q \in 1..Len(nl) : nl[q] = log[j][q]
        <5>1. LMc(ledLog, nl) BY <4>1, <1>b, LMPrefix
        <5>2. Mono(nl) BY <4>1, <1>b, MonoPrefix
        <5>3. \A k \in 1..Len(nl) : nl[k].term <= T BY <4>1, <1>b
        <5> QED BY <5>1, <5>2, <5>3, <3>2, <1>c
      <4>2. CASE Len(nl) <= Len(ledLog[T]) /\ \A q \in 1..Len(nl) : nl[q] = ledLog[T][q]
        <5>1. LMc(ledLog, nl) BY <4>2, <1>b, LMPrefix
        <5>2. Mono(nl) BY <4>2, <1>b, MonoPrefix
        <5>3. \A k \in 1..Len(nl) : nl[k].term <= T BY <4>2, <1>b
        <5> QED BY <5>1, <5>2, <5>3, <3>2, <1>c
      <4> QED BY <4>1, <4>2
    <3> QED BY <3>1, <3>2
  <2> QED BY <2>1, <1>a DEF LogsInv, LMlog
<1>5. ConfirmedInv'
  <2> SUFFICES ASSUME NEW jj \in Server
               PROVE  /\ confirmed'[jj].term <= currentTerm[jj]
                      /\ confirmed'[jj].index <= Len(log'[jj])
                      /\ confirmed'[jj].index > 0 =>
                            /\ confirmed'[jj].term \in DOMAIN ledLog
                            /\ confirmed'[jj].index <= Len(ledLog[confirmed'[jj].term])
                            /\ \A q \in 1..confirmed'[jj].index : log'[jj][q] = ledLog[confirmed'[jj].term][q]
    BY DEF ConfirmedInv
  <2>1. CASE jj # j
    <3>1. confirmed'[jj] = confirmed[jj] /\ log'[jj] = log[jj] BY <2>1, <1>c, <1>a DEF TypeOK
    <3> QED BY <3>1, <1>a DEF ConfirmedInv
  <2>2. CASE jj = j
    <3>1. confirmed'[j].term = T /\ confirmed'[j].index = r BY <1>a DEF TypeOK
    <3> QED BY <3>1, <2>2, <1>b, <1>c
  <2> QED BY <2>1, <2>2
<1>6. AckerInv'
  <2> SUFFICES ASSUME NEW jj \in Server, NEW t \in DOMAIN ledLog, NEW c \in 1..Len(ledLog[t]),
                      ledLog[t][c].term = t, IsAcker(jj, t, c),
                      \A w \in DOMAIN ledLog : t < w /\ w <= currentTerm[jj] => Has(ledLog[w], c, t)
               PROVE  Has(log'[jj], c, t)
    BY DEF AckerInv, IsAcker, Has
  <2>1. Has(log[jj], c, t) BY <1>a DEF AckerInv
  <2>2. CASE jj # j BY <2>1, <2>2, <1>c
  <2>3. CASE jj = j
    <3>1. t \in Nat /\ t <= T
      <4>1. t \in Nat BY <1>a DEF TypeOK
      <4>2. CASE [server |-> j, term |-> t] \in leaders
        BY <4>1, <4>2, <1>a, <1>b DEF LeadersInv
      <4>3. CASE \E a \in msgs : a.type = "ack" /\ a.src = j /\ a.term = t /\ a.index >= c
        BY <4>1, <4>3, <1>a, <1>b DEF AckInv
      <4> QED BY <4>2, <4>3, <2>3 DEF IsAcker
    <3>2. Has(ledLog[T], c, t)
      <4>1. CASE t = T BY <4>1 DEF Has
      <4>2. CASE t # T
        <5>1. t < T /\ T <= currentTerm[jj] BY <4>2, <3>1, <1>b, <2>3
        <5> QED BY <5>1
      <4> QED BY <4>1, <4>2
    <3>3. c \in 1..Len(log[j]) /\ c <= Len(ledLog[T]) /\ log[j][c].term = ledLog[T][c].term
      BY <2>1, <2>3, <3>2, <1>b DEF Has
    <3>4. c <= Len(nl) /\ nl[c] = log[j][c] BY <3>3
    <3> QED BY <3>4, <2>1, <2>3, <1>c DEF Has
  <2> QED BY <2>2, <2>3
<1>7. CommitIndexInv'
  <2> SUFFICES ASSUME NEW i \in Server, commitIndex[i] # 0
               PROVE  \E k \in commits :
                        /\ k.term <= currentTerm[i]
                        /\ commitIndex[i] <= Len(k.entries)
                        /\ commitIndex[i] <= Len(log'[i])
                        /\ \A q \in 1..commitIndex[i] : log'[i][q] = k.entries[q]
    BY DEF CommitIndexInv
  <2>1. PICK k \in commits :
                        /\ k.term <= currentTerm[i]
                        /\ commitIndex[i] <= Len(k.entries)
                        /\ commitIndex[i] <= Len(log[i])
                        /\ \A q \in 1..commitIndex[i] : log[i][q] = k.entries[q]
    BY <1>a DEF CommitIndexInv
  <2>2. CASE i # j
    <3>1. log'[i] = log[i] BY <2>2, <1>c
    <3> QED BY <2>1, <3>1
  <2>3. CASE i = j
    <3> DEFINE ci == commitIndex[j]
    <3>1. ci \in Nat /\ ci >= 1 /\ k.entries \in Seq(EntryT)
      <4>1. ci \in Nat BY <1>a DEF TypeOK
      <4>2. ci # 0 BY <2>3
      <4>3. k.entries \in Seq(EntryT) BY <2>1, <1>a DEF TypeOK
      <4> QED BY <4>1, <4>2, <4>3
    <3>2. /\ Len(k.entries) <= Len(ledLog[T])
          /\ \A q \in 1..Len(k.entries) : k.entries[q] = ledLog[T][q]
      BY <2>1, <2>3, CommitLed
    <3>3. \A c \in 1..ci : c \in 1..Len(log[j]) /\ c <= Len(ledLog[T])
                           /\ log[j][c].term = ledLog[T][c].term
      BY <2>1, <2>3, <3>1, <3>2, <1>b
    <3>4. \A c \in 1..ci : c <= Len(nl) /\ nl[c] = log[j][c] BY <3>3
    <3>5. ci <= Len(nl) BY <3>1, <3>4
    <3>6. \A q \in 1..ci : log'[i][q] = k.entries[q] BY <3>4, <2>1, <2>3, <1>c
    <3>7. commitIndex[i] <= Len(log'[i]) BY <3>5, <2>3, <1>c
    <3>8. k.term <= currentTerm[i] /\ commitIndex[i] <= Len(k.entries) BY <2>1
    <3> QED BY <3>6, <3>7, <3>8, <2>3
  <2> QED BY <2>2, <2>3
<1> QED
  BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, TermInvUnch, VotesInvUnch, OneVoteUnch,
     GrantInvUnch, ElectionSafetyUnch, AppendInvUnch, AckInvUnch, VoterInvUnch, QuorumInvUnch,
     CommitsInvUnch, AppliedInvUnch DEF Inv

LEMMA DeleteSuffixInv ==
    ASSUME IsFiniteSet(Server), Inv, NEW j \in Server, NEW m, NEW k \in Nat, DeleteSuffix(j, m, k)
    PROVE  Inv'
<1> DEFINE T == m.term
<1> DEFINE p == m.prevLogIndex
<1> DEFINE r == m.prevLogIndex + k - 1
<1> DEFINE nl == SubSeq(log[j], 1, r)
<1>0. /\ m \in msgs /\ m.type = "append" /\ m.dst = j /\ T = currentTerm[j]
      /\ PrevOk(j, m) /\ k \in 1..Len(m.entries) /\ HasFirst(j, m, k - 1)
      /\ p + k <= Len(log[j])
      /\ log[j][p + k].term # m.entries[k].term
      /\ log' = [log EXCEPT ![j] = nl]
      /\ confirmed' = [confirmed EXCEPT ![j] = [term |-> T, index |-> r]]
      /\ UNCHANGED <<transfer, currentTerm, voteTerm, voteFor, snap, base, role, commitIndex,
                     lastApplied, msgs, votes, leaders, ledLog, commits, applied>>
  BY DEF DeleteSuffix, Confirm
<1>a. TypeOK /\ LeadersInv /\ AppendInv /\ LogsInv BY DEF Inv
<1>b. /\ m.src \in Server /\ m.src # j
      /\ [server |-> m.src, term |-> T] \in leaders
      /\ T \in DOMAIN ledLog /\ ledLog[T] \in Seq(EntryT) /\ LMc(ledLog, ledLog[T])
      /\ p \in Nat /\ m.entries \in Seq(EntryT)
      /\ p + Len(m.entries) <= Len(ledLog[T])
      /\ \A q \in 1..Len(m.entries) : m.entries[q] = ledLog[T][p + q]
  BY <1>0, <1>a, AppendFacts
<1>c. log[j] \in Seq(EntryT) /\ LMc(ledLog, log[j]) BY <1>a DEF TypeOK, LogsInv, LMlog
<1>d. /\ r \in Nat /\ r = p + (k - 1) /\ r + 1 = p + k /\ k - 1 \in Nat
      /\ k - 1 <= Len(m.entries) /\ r < Len(log[j]) /\ r + 1 <= Len(ledLog[T])
  <2> DEFINE n == Len(m.entries)
  <2> DEFINE L == Len(log[j])
  <2> DEFINE LT == Len(ledLog[T])
  <2>1. /\ p \in Nat /\ k \in Nat /\ n \in Nat /\ L \in Nat /\ LT \in Nat
        /\ k \in 1..n /\ p + k <= L /\ p + n <= LT /\ r = p + k - 1
    BY <1>0, <1>b, <1>c
  <2> HIDE DEF p, n, L, LT, r
  <2>2. /\ r \in Nat /\ r = p + (k - 1) /\ r + 1 = p + k /\ k - 1 \in Nat
        /\ k - 1 <= n /\ r < L /\ r + 1 <= LT
    BY <2>1
  <2> QED BY <2>2 DEF p, n, L, LT, r
<1>e. /\ r <= Len(log[j]) /\ r <= Len(ledLog[T])
      /\ \A q \in 1..r : log[j][q] = ledLog[T][q]
  BY <1>0, <1>a, <1>d, PrefixAgree
<1>f. log[j][r + 1].term # ledLog[T][r + 1].term
  <2>1. m.entries[k] = ledLog[T][p + k] BY <1>0, <1>b
  <2> QED BY <2>1, <1>0, <1>d
<1>g. nl \in Seq(EntryT) /\ Len(nl) = r /\ \A q \in 1..r : nl[q] = log[j][q]
  BY <1>c, <1>d, <1>e, SubSeqPre
<1>h. \A c \in 1..Len(log[j]) :
         c <= Len(ledLog[T]) /\ log[j][c].term = ledLog[T][c].term =>
            c <= Len(nl) /\ nl[c] = log[j][c]
  <2> SUFFICES ASSUME NEW c \in 1..Len(log[j]), c <= Len(ledLog[T]),
                      log[j][c].term = ledLog[T][c].term
               PROVE  c <= r
    BY <1>g, <1>d
  <2>1. c \in 1..Len(ledLog[T]) BY <1>b
  <2>2. \A q \in 1..c : log[j][q] = ledLog[T][q] BY <2>1, <1>b, <1>c, Match
  <2>3. ~(r + 1 \in 1..c) BY <2>2, <1>f
  <2> QED BY <2>3, <1>d
<1>i. /\ r <= Len(nl) /\ \A q \in 1..r : nl[q] = ledLog[T][q]
      /\ Len(nl) <= Len(log[j]) /\ \A q \in 1..Len(nl) : nl[q] = log[j][q]
  BY <1>d, <1>e, <1>g
<1>j. \E src \in Server : src # j /\ [server |-> src, term |-> T] \in leaders BY <1>b
<1>y. /\ T \in DOMAIN ledLog /\ r \in Nat /\ nl \in Seq(EntryT) /\ T = currentTerm[j]
      /\ log' = [log EXCEPT ![j] = nl]
      /\ confirmed' = [confirmed EXCEPT ![j] = [term |-> T, index |-> r]]
      /\ UNCHANGED <<transfer, currentTerm, voteTerm, voteFor, snap, base, role, commitIndex,
                     lastApplied, msgs, votes, leaders, ledLog, commits, applied>>
      /\ r <= Len(nl) /\ r <= Len(ledLog[T])
      /\ \A q \in 1..r : nl[q] = ledLog[T][q]
      /\ (\/ Len(nl) <= Len(log[j]) /\ \A q \in 1..Len(nl) : nl[q] = log[j][q]
          \/ Len(nl) <= Len(ledLog[T]) /\ \A q \in 1..Len(nl) : nl[q] = ledLog[T][q])
  BY <1>0, <1>b, <1>d, <1>e, <1>g, <1>i
<1> HIDE DEF T, p, r, nl
<1> QED BY <1>y, <1>h, <1>j, FollowerLogInv

LEMMA SubSeqFrom ==
    ASSUME NEW S, NEW s \in Seq(S), NEW k \in 1..Len(s)
    PROVE  /\ SubSeq(s, k, Len(s)) \in Seq(S)
           /\ Len(SubSeq(s, k, Len(s))) = Len(s) - k + 1
           /\ \A q \in 1..(Len(s) - k + 1) : SubSeq(s, k, Len(s))[q] = s[k + q - 1]
OBVIOUS

LEMMA StoreEntriesInv ==
    ASSUME IsFiniteSet(Server), Inv, NEW j \in Server, NEW m, NEW k \in Nat, StoreEntries(j, m, k)
    PROVE  Inv'
<1> DEFINE T == m.term
<1> DEFINE p == m.prevLogIndex
<1> DEFINE n == Len(m.entries)
<1> DEFINE L == Len(log[j])
<1> DEFINE suf == SubSeq(m.entries, k, Len(m.entries))
<1> DEFINE nl == log[j] \o suf
<1> DEFINE r == p + n
<1>0. /\ m \in msgs /\ m.type = "append" /\ m.dst = j /\ T = currentTerm[j]
      /\ PrevOk(j, m) /\ k \in 1..n /\ HasFirst(j, m, k - 1)
      /\ p + k = L + 1
      /\ log' = [log EXCEPT ![j] = nl]
      /\ confirmed' = [confirmed EXCEPT ![j] = [term |-> T, index |-> r]]
      /\ UNCHANGED <<transfer, currentTerm, voteTerm, voteFor, snap, base, role, commitIndex,
                     lastApplied, msgs, votes, leaders, ledLog, commits, applied>>
  BY DEF StoreEntries, Confirm
<1>a. TypeOK /\ LeadersInv /\ AppendInv /\ LogsInv BY DEF Inv
<1>b. /\ m.src \in Server /\ m.src # j
      /\ [server |-> m.src, term |-> T] \in leaders
      /\ T \in DOMAIN ledLog /\ ledLog[T] \in Seq(EntryT) /\ LMc(ledLog, ledLog[T])
      /\ p \in Nat /\ m.entries \in Seq(EntryT)
      /\ p + n <= Len(ledLog[T])
      /\ \A q \in 1..n : m.entries[q] = ledLog[T][p + q]
  BY <1>0, <1>a, AppendFacts
<1>c. log[j] \in Seq(EntryT) /\ L \in Nat /\ n \in Nat BY <1>a, <1>b DEF TypeOK
<1>d. /\ k - 1 \in Nat /\ k - 1 <= n /\ L = p + (k - 1) /\ r \in Nat /\ L <= r
      /\ r = L + (n - k + 1) /\ n - k + 1 \in Nat
  <2>1. p \in Nat /\ n \in Nat /\ L \in Nat /\ k \in 1..n /\ p + k = L + 1 /\ r = p + n
    BY <1>0, <1>b, <1>c
  <2> HIDE DEF p, n, L, r
  <2> QED BY <2>1
<1>e. /\ L <= Len(ledLog[T])
      /\ \A q \in 1..L : log[j][q] = ledLog[T][q]
  BY <1>0, <1>a, <1>c, <1>d, PrefixAgree
<1>f. /\ suf \in Seq(EntryT) /\ Len(suf) = n - k + 1
      /\ \A q \in 1..(n - k + 1) : suf[q] = m.entries[k + q - 1]
  BY <1>0, <1>b, SubSeqFrom
<1>g. /\ nl \in Seq(EntryT) /\ Len(nl) = r
      /\ \A q \in 1..L : nl[q] = log[j][q]
      /\ \A q \in L+1..r : nl[q] = suf[q - L]
  BY <1>c, <1>d, <1>f, ConcatFacts
<1>h. \A q \in 1..r : nl[q] = ledLog[T][q]
  <2> SUFFICES ASSUME NEW q \in 1..r PROVE nl[q] = ledLog[T][q] OBVIOUS
  <2>1. CASE q <= L BY <2>1, <1>c, <1>e, <1>g
  <2>2. CASE q > L
    <3> DEFINE q2 == q - L
    <3> DEFINE q3 == k + q2 - 1
    <3>1. q \in L+1..r /\ q2 \in 1..(n - k + 1) /\ q3 \in 1..n /\ p + q3 = q
      <4>1. /\ p \in Nat /\ n \in Nat /\ L \in Nat /\ k \in 1..n /\ p + k = L + 1 /\ r = p + n
            /\ q \in 1..r /\ q > L
        BY <2>2, <1>0, <1>b, <1>c
      <4> HIDE DEF p, n, L, r
      <4> QED BY <4>1
    <3>2. nl[q] = suf[q2] BY <3>1, <1>g
    <3>3. suf[q2] = m.entries[q3] BY <3>1, <1>f
    <3>4. m.entries[q3] = ledLog[T][p + q3] BY <3>1, <1>b
    <3> HIDE DEF q2, q3
    <3> QED BY <3>1, <3>2, <3>3, <3>4
  <2>3. q \in Nat /\ L \in Nat
    <3>1. r \in Nat /\ L \in Nat /\ q \in 1..r BY <1>c, <1>d
    <3> HIDE DEF r, L
    <3> QED BY <3>1
  <2>4. q <= L \/ q > L BY <2>3
  <2> HIDE DEF nl, L, T, suf
  <2> QED BY <2>1, <2>2, <2>4
<1>i. \A c \in 1..Len(log[j]) :
         c <= Len(ledLog[T]) /\ log[j][c].term = ledLog[T][c].term =>
            c <= Len(nl) /\ nl[c] = log[j][c]
  BY <1>c, <1>d, <1>g
<1>j. /\ r <= Len(nl) /\ r <= Len(ledLog[T])
      /\ Len(nl) <= Len(ledLog[T]) /\ \A q \in 1..Len(nl) : nl[q] = ledLog[T][q]
  <2>1. Len(nl) = r /\ r \in Nat BY <1>g, <1>d
  <2>2. r <= Len(ledLog[T]) BY <1>b DEF r
  <2> HIDE DEF T, p, n, L, suf, nl, r
  <2> QED BY <2>1, <2>2, <1>h
<1>k. \E src \in Server : src # j /\ [server |-> src, term |-> T] \in leaders BY <1>b
<1>y. /\ T \in DOMAIN ledLog /\ r \in Nat /\ nl \in Seq(EntryT) /\ T = currentTerm[j]
      /\ log' = [log EXCEPT ![j] = nl]
      /\ confirmed' = [confirmed EXCEPT ![j] = [term |-> T, index |-> r]]
      /\ UNCHANGED <<transfer, currentTerm, voteTerm, voteFor, snap, base, role, commitIndex,
                     lastApplied, msgs, votes, leaders, ledLog, commits, applied>>
      /\ r <= Len(nl) /\ r <= Len(ledLog[T])
      /\ \A q \in 1..r : nl[q] = ledLog[T][q]
      /\ (\/ Len(nl) <= Len(log[j]) /\ \A q \in 1..Len(nl) : nl[q] = log[j][q]
          \/ Len(nl) <= Len(ledLog[T]) /\ \A q \in 1..Len(nl) : nl[q] = ledLog[T][q])
  BY <1>0, <1>b, <1>d, <1>g, <1>h, <1>j
<1> HIDE DEF T, p, n, L, suf, nl, r
<1> QED BY <1>y, <1>i, <1>k, FollowerLogInv
====
