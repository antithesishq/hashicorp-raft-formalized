---- MODULE RaftExt ----
\* Logs and leader logs that only grow at the end.
EXTENDS RaftStatic

LogExt == \A jj \in Server : /\ Len(log[jj]) <= Len(log'[jj])
                             /\ \A q \in 1..Len(log[jj]) : log'[jj][q] = log[jj][q]

LedExt == /\ DOMAIN ledLog \subseteq DOMAIN ledLog'
          /\ \A w \in DOMAIN ledLog :
                /\ Len(ledLog[w]) <= Len(ledLog'[w])
                /\ \A q \in 1..Len(ledLog[w]) : ledLog'[w][q] = ledLog[w][q]

LEMMA LMPrefix ==
    ASSUME NEW led, NEW S, NEW X \in Seq(S), NEW Y \in Seq(S), LMc(led, X),
           Len(Y) <= Len(X), \A q \in 1..Len(Y) : Y[q] = X[q]
    PROVE  LMc(led, Y)
BY DEF LMc

LEMMA MonoPrefix ==
    ASSUME NEW S, NEW X \in Seq(S), NEW Y \in Seq(S), Mono(X),
           Len(Y) <= Len(X), \A q \in 1..Len(Y) : Y[q] = X[q]
    PROVE  Mono(Y)
BY DEF Mono

\* A log that fits the leader logs still fits them after they have grown
\* and terms have got their first leader.
LEMMA LMExt ==
    ASSUME NEW led, NEW led2, NEW S, NEW X \in Seq(S), LMc(led, X),
           DOMAIN led \subseteq DOMAIN led2, 1 \notin DOMAIN led2,
           \A w \in DOMAIN led : /\ led[w] \in Seq(S) /\ led2[w] \in Seq(S)
                                 /\ Len(led[w]) <= Len(led2[w])
                                 /\ \A q \in 1..Len(led[w]) : led2[w][q] = led[w][q]
    PROVE  LMc(led2, X)
<1> SUFFICES ASSUME NEW k \in 1..Len(X)
             PROVE  /\ k <= Len(LLc(led2, X[k].term))
                    /\ \A q \in 1..k : X[q] = LLc(led2, X[k].term)[q]
  BY DEF LMc
<1> DEFINE t == X[k].term
<1>1. k <= Len(LLc(led, t)) /\ \A q \in 1..k : X[q] = LLc(led, t)[q] BY DEF LMc
<1>2. CASE t \in DOMAIN led
  <2>1. LLc(led, t) = led[t] /\ LLc(led2, t) = led2[t] BY <1>2 DEF LLc
  <2>2. /\ led[t] \in Seq(S) /\ led2[t] \in Seq(S)
        /\ Len(led[t]) <= Len(led2[t])
        /\ \A q \in 1..Len(led[t]) : led2[t][q] = led[t][q]
    BY <1>2
  <2>3. k \in 1..Len(led[t]) /\ k <= Len(led2[t]) /\ \A q \in 1..k : q \in 1..Len(led[t])
    BY <1>1, <2>1, <2>2
  <2> QED BY <1>1, <2>1, <2>2, <2>3
<1>3. CASE t \notin DOMAIN led
  <2>1. LLc(led, t) = InitLog BY <1>3 DEF LLc
  <2>2. k = 1 /\ X[1] = InitLog[1] BY <1>1, <2>1 DEF InitLog
  <2>3. t = 1 BY <2>2 DEF InitLog, Entry
  <2>4. LLc(led2, t) = InitLog BY <2>3 DEF LLc
  <2> QED BY <1>1, <2>1, <2>4
<1> QED BY <1>2, <1>3

LEMMA AppendInvExt ==
    ASSUME AppendInv, TypeOK, TypeOK', LedExt, UNCHANGED <<msgs, commits>>,
           leaders \subseteq leaders', LeadersInv
    PROVE  AppendInv'
<1> SUFFICES ASSUME NEW m \in msgs, m.type = "append"
             PROVE  /\ m.prevLogIndex + Len(m.entries) <= Len(ledLog'[m.term])
                    /\ m.prevLogTerm = TermAt(ledLog'[m.term], m.prevLogIndex)
                    /\ \A q \in 1..Len(m.entries) : m.entries[q] = ledLog'[m.term][m.prevLogIndex + q]
  BY DEF AppendInv
<1> DEFINE T == m.term
<1> DEFINE p == m.prevLogIndex
<1> DEFINE n == Len(m.entries)
<1>1. /\ [server |-> m.src, term |-> T] \in leaders
      /\ p \in Nat /\ m.entries \in Seq(EntryT)
      /\ p + n <= Len(ledLog[T])
      /\ m.prevLogTerm = TermAt(ledLog[T], p)
      /\ \A q \in 1..n : m.entries[q] = ledLog[T][p + q]
  BY DEF AppendInv
<1>2. T \in DOMAIN ledLog /\ ledLog[T] \in Seq(EntryT) /\ ledLog'[T] \in Seq(EntryT)
  BY <1>1 DEF LeadersInv, TypeOK, LedExt
<1>3. /\ Len(ledLog[T]) <= Len(ledLog'[T])
      /\ \A q \in 1..Len(ledLog[T]) : ledLog'[T][q] = ledLog[T][q]
  BY <1>2 DEF LedExt
<1>4. n \in Nat BY <1>1
<1>5. TermAt(ledLog'[T], p) = TermAt(ledLog[T], p)
  BY <1>1, <1>2, <1>3, <1>4 DEF TermAt
<1>6. \A q \in 1..n : p + q \in 1..Len(ledLog[T]) BY <1>1, <1>2, <1>4
<1> HIDE DEF T, p, n
<1> QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6 DEF T, p, n

LEMMA AckInvExt ==
    ASSUME AckInv, TypeOK, TypeOK', LedExt, UNCHANGED <<msgs, currentTerm>>
    PROVE  AckInv'
<1> SUFFICES ASSUME NEW m \in msgs, m.type = "ack"
             PROVE  m.term \in DOMAIN ledLog' /\ m.index <= Len(ledLog'[m.term])
  BY DEF AckInv
<1>1. m.term \in DOMAIN ledLog /\ m.index \in Nat /\ m.index <= Len(ledLog[m.term])
  BY DEF AckInv
<1>2. ledLog[m.term] \in Seq(EntryT) /\ ledLog'[m.term] \in Seq(EntryT)
      /\ Len(ledLog[m.term]) <= Len(ledLog'[m.term]) /\ m.term \in DOMAIN ledLog'
  BY <1>1 DEF TypeOK, LedExt
<1> QED BY <1>1, <1>2

LEMMA ConfirmedInvExt ==
    ASSUME ConfirmedInv, TypeOK, TypeOK', LedExt, LogExt, UNCHANGED <<confirmed, currentTerm>>
    PROVE  ConfirmedInv'
<1> SUFFICES ASSUME NEW j \in Server
             PROVE  /\ confirmed[j].index <= Len(log'[j])
                    /\ confirmed[j].index > 0 =>
                          /\ confirmed[j].term \in DOMAIN ledLog'
                          /\ confirmed[j].index <= Len(ledLog'[confirmed[j].term])
                          /\ \A q \in 1..confirmed[j].index : log'[j][q] = ledLog'[confirmed[j].term][q]
  BY DEF ConfirmedInv
<1> DEFINE T == confirmed[j].term
<1> DEFINE n == confirmed[j].index
<1>1. n \in Nat /\ log[j] \in Seq(EntryT) /\ log'[j] \in Seq(EntryT) BY DEF TypeOK
<1>2. n <= Len(log[j]) BY DEF ConfirmedInv
<1>3. Len(log[j]) <= Len(log'[j]) /\ \A q \in 1..Len(log[j]) : log'[j][q] = log[j][q]
  BY DEF LogExt
<1>4. n <= Len(log'[j]) BY <1>1, <1>2, <1>3
<1>5. ASSUME n > 0
      PROVE  /\ T \in DOMAIN ledLog'
             /\ n <= Len(ledLog'[T])
             /\ \A q \in 1..n : log'[j][q] = ledLog'[T][q]
  <2>1. /\ T \in DOMAIN ledLog /\ n <= Len(ledLog[T])
        /\ \A q \in 1..n : log[j][q] = ledLog[T][q]
    BY <1>5 DEF ConfirmedInv
  <2>2. ledLog[T] \in Seq(EntryT) /\ ledLog'[T] \in Seq(EntryT) /\ T \in DOMAIN ledLog'
        /\ Len(ledLog[T]) <= Len(ledLog'[T])
        /\ \A q \in 1..Len(ledLog[T]) : ledLog'[T][q] = ledLog[T][q]
    BY <2>1 DEF TypeOK, LedExt
  <2> HIDE DEF T, n
  <2> QED BY <1>1, <1>2, <1>3, <2>1, <2>2
<1> QED BY <1>4, <1>5

LEMMA CommitIndexInvExt ==
    ASSUME CommitIndexInv, TypeOK, TypeOK', LogExt, UNCHANGED <<commitIndex, commits, currentTerm>>
    PROVE  CommitIndexInv'
<1> SUFFICES ASSUME NEW i \in Server, commitIndex[i] # 0
             PROVE  \E k \in commits :
                      /\ k.term <= currentTerm[i]
                      /\ commitIndex[i] <= Len(k.entries)
                      /\ commitIndex[i] <= Len(log'[i])
                      /\ \A q \in 1..commitIndex[i] : log'[i][q] = k.entries[q]
  BY DEF CommitIndexInv
<1>1. PICK k \in commits :
                      /\ k.term <= currentTerm[i]
                      /\ commitIndex[i] <= Len(k.entries)
                      /\ commitIndex[i] <= Len(log[i])
                      /\ \A q \in 1..commitIndex[i] : log[i][q] = k.entries[q]
  BY DEF CommitIndexInv
<1>2. commitIndex[i] \in Nat /\ log[i] \in Seq(EntryT) /\ log'[i] \in Seq(EntryT) BY DEF TypeOK
<1>3. Len(log[i]) <= Len(log'[i]) /\ \A q \in 1..Len(log[i]) : log'[i][q] = log[i][q]
  BY DEF LogExt
<1> QED BY <1>1, <1>2, <1>3

LEMMA CommitsInvExt ==
    ASSUME CommitsInv, TypeOK, TypeOK', LedExt, msgs \subseteq msgs', leaders \subseteq leaders',
           UNCHANGED commits
    PROVE  CommitsInv'
<1> SUFFICES ASSUME NEW k \in commits
             PROVE  /\ k.term \in DOMAIN ledLog'
                    /\ Len(k.entries) <= Len(ledLog'[k.term])
                    /\ \A q \in 1..Len(k.entries) : k.entries[q] = ledLog'[k.term][q]
                    /\ \E t \in DOMAIN ledLog' : \E c \in 1..Len(ledLog'[t]) :
                          t <= k.term /\ Len(k.entries) <= c /\ QC(t, c)'
  BY DEF CommitsInv
<1>1. /\ k.term \in DOMAIN ledLog
      /\ Len(k.entries) <= Len(ledLog[k.term])
      /\ \A q \in 1..Len(k.entries) : k.entries[q] = ledLog[k.term][q]
  BY DEF CommitsInv
<1>2. PICK t \in DOMAIN ledLog : \E c \in 1..Len(ledLog[t]) :
                          t <= k.term /\ Len(k.entries) <= c /\ QC(t, c)
  BY DEF CommitsInv
<1>3. PICK c \in 1..Len(ledLog[t]) : t <= k.term /\ Len(k.entries) <= c /\ QC(t, c)
  BY <1>2
<1>4. \A w \in DOMAIN ledLog :
         /\ w \in DOMAIN ledLog' /\ ledLog[w] \in Seq(EntryT) /\ ledLog'[w] \in Seq(EntryT)
         /\ Len(ledLog[w]) <= Len(ledLog'[w])
         /\ \A q \in 1..Len(ledLog[w]) : ledLog'[w][q] = ledLog[w][q]
  BY DEF TypeOK, LedExt
<1>5. k.entries \in Seq(EntryT) BY DEF TypeOK
<1>6. /\ k.term \in DOMAIN ledLog'
      /\ Len(k.entries) <= Len(ledLog'[k.term])
      /\ \A q \in 1..Len(k.entries) : k.entries[q] = ledLog'[k.term][q]
  BY <1>1, <1>4, <1>5
<1>7. t \in DOMAIN ledLog' /\ c \in 1..Len(ledLog'[t]) /\ ledLog'[t][c] = ledLog[t][c]
  BY <1>4
<1>8. QC(t, c)'
  <2>1. \A j : IsAcker(j, t, c) => IsAcker(j, t, c)' BY DEF IsAcker
  <2> QED BY <1>3, <1>7, <2>1 DEF QC
<1> QED BY <1>3, <1>6, <1>7, <1>8
====
