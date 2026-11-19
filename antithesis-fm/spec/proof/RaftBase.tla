---- MODULE RaftBase ----
\* Constant-level lemmas: quorums and sequences.
EXTENDS RaftDefs, TLAPS, FiniteSetTheorems, SequenceTheorems

LEMMA QArith ==
    ASSUME NEW c1 \in Nat, NEW c2 \in Nat, NEW c12 \in Nat, NEW cu \in Nat, NEW n \in Nat,
           cu + c12 = c1 + c2, cu <= n, c1 * 2 > n, c2 * 2 > n
    PROVE  c12 # 0
\* The SMT encoding needs the products by 2 as sums.
<1>1. c1 * 2 = c1 + c1 /\ c2 * 2 = c2 + c2 OBVIOUS
<1> QED BY <1>1

LEMMA QuorumIntersect ==
    ASSUME IsFiniteSet(Server),
           NEW S1 \in SUBSET Server, NEW S2 \in SUBSET Server,
           IsQuorum(S1), IsQuorum(S2)
    PROVE  \E j \in S1 : j \in S2
<1>1. IsFiniteSet(S1) /\ IsFiniteSet(S2) /\ Cardinality(S1) \in Nat /\ Cardinality(S2) \in Nat
      /\ Cardinality(Server) \in Nat
  BY FS_Subset, FS_CardinalityType
<1>2. IsFiniteSet(S1 \cup S2) /\ Cardinality(S1 \cup S2) = Cardinality(S1) + Cardinality(S2) - Cardinality(S1 \cap S2)
  BY <1>1, FS_Union
<1>3. Cardinality(S1 \cup S2) <= Cardinality(Server) /\ Cardinality(S1 \cup S2) \in Nat
  BY <1>2, FS_Subset, FS_CardinalityType
<1>4. IsFiniteSet(S1 \cap S2) /\ Cardinality(S1 \cap S2) \in Nat
  BY <1>1, FS_Intersection, FS_CardinalityType
<1>5. Cardinality(S1 \cap S2) # 0
  <2>1. Cardinality(S1 \cup S2) + Cardinality(S1 \cap S2) = Cardinality(S1) + Cardinality(S2)
    BY <1>1, <1>2, <1>3, <1>4
  <2> QED BY <1>1, <2>1, <1>3, <1>4, QArith DEF IsQuorum
<1>6. S1 \cap S2 # {}
  BY <1>5, FS_EmptySet
<1> QED BY <1>6

LEMMA QuorumNonEmpty ==
    ASSUME IsFiniteSet(Server), NEW S \in SUBSET Server, IsQuorum(S)
    PROVE  \E j \in S : TRUE
<1>1. Cardinality(Server) \in Nat BY FS_CardinalityType
<1>2. Cardinality(S) # 0 BY <1>1, FS_Subset, FS_CardinalityType DEF IsQuorum
<1> QED BY <1>2, FS_EmptySet

LEMMA SubSeqSeg ==
    ASSUME NEW S, NEW s \in Seq(S), NEW p \in Nat, NEW n \in Nat, p + n <= Len(s)
    PROVE  /\ SubSeq(s, p + 1, p + n) \in Seq(S)
           /\ Len(SubSeq(s, p + 1, p + n)) = n
           /\ \A q \in 1..n : SubSeq(s, p + 1, p + n)[q] = s[p + q]
OBVIOUS

LEMMA SubSeqPre ==
    ASSUME NEW S, NEW s \in Seq(S), NEW n \in Nat, n <= Len(s)
    PROVE  /\ SubSeq(s, 1, n) \in Seq(S)
           /\ Len(SubSeq(s, 1, n)) = n
           /\ \A q \in 1..n : SubSeq(s, 1, n)[q] = s[q]
OBVIOUS

LEMMA ConcatFacts ==
    ASSUME NEW S, NEW s \in Seq(S), NEW t \in Seq(S)
    PROVE  /\ s \o t \in Seq(S)
           /\ Len(s \o t) = Len(s) + Len(t)
           /\ \A q \in 1..Len(s) : (s \o t)[q] = s[q]
           /\ \A q \in Len(s)+1..Len(s)+Len(t) : (s \o t)[q] = t[q - Len(s)]
OBVIOUS

LEMMA SeqPointwise ==
    ASSUME NEW S, NEW s \in Seq(S), NEW t \in Seq(S), Len(s) = Len(t),
           \A q \in 1..Len(s) : s[q] = t[q]
    PROVE  s = t
OBVIOUS

LEMMA PrefixPointwise ==
    ASSUME NEW S, NEW a \in Seq(S), NEW b \in Seq(S), Len(a) <= Len(b),
           \A q \in 1..Len(a) : a[q] = b[q]
    PROVE  IsPrefix(a, b)
<1>1. Len(a) \in Nat OBVIOUS
<1> QED BY <1>1, SubSeqPre, SeqPointwise DEF IsPrefix
====
