---- MODULE RaftDefs ----
\* Definitions of the inductive invariant used to prove the safety
\* properties of HashicorpRaft.  No proofs here (so that TLC can load it).
EXTENDS HashicorpRaft

EntryT == [term : Nat, type : {"config", "noop", "barrier", "command"},
           value : Values \cup {Nil}]
InitLog == <<Entry(1, "config", Nil)>>

\* Leader log of term t; the bootstrap log for a term without a leader (so
\* the bootstrap entry fits). Parametrised by `led` so lemmas are constant-level.
LLc(led, t) == IF t \in DOMAIN led THEN led[t] ELSE InitLog

\* Every entry of X sits, with all that precedes it, in the leader log of
\* its term.
LMc(led, X) == \A k \in 1..Len(X) :
                  /\ k <= Len(LLc(led, X[k].term))
                  /\ \A q \in 1..k : X[q] = LLc(led, X[k].term)[q]
LMlog(X) == LMc(ledLog, X)
Mono(X) == \A a, b \in 1..Len(X) : a <= b => X[a].term <= X[b].term
Has(X, c, t) == c <= Len(X) /\ X[c].term = t

\* j has stored the first c entries of the leader log of t while in term t.
IsAcker(j, t, c) ==
    \/ [server |-> j, term |-> t] \in leaders
    \/ \E a \in msgs : a.type = "ack" /\ a.src = j /\ a.term = t /\ a.index >= c

\* Every leader of a term strictly between t and u has entry c of term t.
Between(t, c, u) == \A w \in DOMAIN ledLog : t < w /\ w < u => Has(ledLog[w], c, t)

TypeOK ==
    /\ currentTerm \in [Server -> Nat]
    /\ voteTerm \in [Server -> Nat]
    /\ voteFor \in [Server -> Server \cup {Nil}]
    /\ log \in [Server -> Seq(EntryT)]
    /\ snap \in [Server -> Seq(EntryT)]
    /\ role \in [Server -> {Follower, Candidate, Leader}]
    /\ commitIndex \in [Server -> Nat]
    /\ lastApplied \in [Server -> Nat]
    /\ confirmed \in [Server -> [term : Nat, index : Nat]]
    /\ votes \subseteq [voter : Server, term : Nat, cand : Server]
    /\ leaders \subseteq [server : Server, term : Nat]
    /\ DOMAIN ledLog \subseteq Nat
    /\ ledLog = [t \in DOMAIN ledLog |-> ledLog[t]]
    /\ \A t \in DOMAIN ledLog : ledLog[t] \in Seq(EntryT)
    /\ commits \subseteq [server : Server, term : Nat, entries : Seq(EntryT)]

TermInv == \A i \in Server : voteTerm[i] <= currentTerm[i] /\ currentTerm[i] >= 1

VotesInv == \A v \in votes : v.term <= voteTerm[v.voter] /\ v.term >= 2

VoteReqInv ==
    \A m \in msgs : m.type = "vote" =>
        /\ m.src \in Server /\ m.term \in Nat
        /\ m.lastLogIndex \in Nat /\ m.lastLogTerm \in Nat
        /\ m.term >= 2 /\ m.term <= currentTerm[m.src]
        /\ (m.term = currentTerm[m.src] /\ m.term \notin DOMAIN ledLog) =>
               m.lastLogIndex = Len(log[m.src]) /\ m.lastLogTerm = LastTerm(m.src)

GrantInv ==
    \A m \in msgs : m.type = "grant" =>
        [voter |-> m.src, term |-> m.term, cand |-> m.dst] \in votes

LeadersInv ==
    /\ \A l \in leaders :
          /\ l.term <= currentTerm[l.server]
          /\ l.term \in DOMAIN ledLog
          /\ currentTerm[l.server] = l.term => log[l.server] = ledLog[l.term]
    /\ \A t \in DOMAIN ledLog : t >= 2 /\ \E l \in leaders : l.term = t
    /\ \A i \in Server : role[i] = Leader =>
          [server |-> i, term |-> currentTerm[i]] \in leaders

LogsInv ==
    /\ \A i \in Server :
          /\ LMlog(log[i]) /\ Mono(log[i])
          /\ \A k \in 1..Len(log[i]) : log[i][k].term <= currentTerm[i]
    /\ \A t \in DOMAIN ledLog :
          /\ LMlog(ledLog[t]) /\ Mono(ledLog[t])
          /\ \A k \in 1..Len(ledLog[t]) : ledLog[t][k].term <= t

AppendInv ==
    \A m \in msgs : m.type = "append" =>
        /\ m.src \in Server /\ m.dst \in Server /\ m.dst # m.src
        /\ [server |-> m.src, term |-> m.term] \in leaders
        /\ m.prevLogIndex \in Nat /\ m.commit \in Nat /\ m.entries \in Seq(EntryT)
        /\ m.prevLogIndex + Len(m.entries) <= Len(ledLog[m.term])
        /\ m.prevLogTerm = TermAt(ledLog[m.term], m.prevLogIndex)
        /\ \A q \in 1..Len(m.entries) : m.entries[q] = ledLog[m.term][m.prevLogIndex + q]
        /\ \/ m.commit = 0
           \/ \E k \in commits : k.term <= m.term /\ m.commit <= Len(k.entries)

AckInv ==
    \A m \in msgs : m.type = "ack" =>
        /\ m.src \in Server /\ m.term \in DOMAIN ledLog /\ m.index \in Nat
        /\ m.index <= Len(ledLog[m.term])
        /\ m.term <= currentTerm[m.src]

ConfirmedInv ==
    \A j \in Server :
        /\ confirmed[j].term <= currentTerm[j]
        /\ confirmed[j].index <= Len(log[j])
        /\ confirmed[j].index > 0 =>
              /\ confirmed[j].term \in DOMAIN ledLog
              /\ confirmed[j].index <= Len(ledLog[confirmed[j].term])
              /\ \A q \in 1..confirmed[j].index : log[j][q] = ledLog[confirmed[j].term][q]

\* An acker of entry c of term t keeps it as long as every later leader up
\* to its own term has it.
AckerInv ==
    \A j \in Server : \A t \in DOMAIN ledLog : \A c \in 1..Len(ledLog[t]) :
        (/\ ledLog[t][c].term = t
         /\ IsAcker(j, t, c)
         /\ \A w \in DOMAIN ledLog : t < w /\ w <= currentTerm[j] => Has(ledLog[w], c, t))
        => Has(log[j], c, t)

\* A vote given in a term that has no leader yet, by an acker of entry c of
\* term t, was given to a candidate whose log is not behind that entry.
VoterInv ==
    \A v \in votes : \A t \in DOMAIN ledLog : \A c \in 1..Len(ledLog[t]) :
        (/\ t < v.term /\ v.term \notin DOMAIN ledLog
         /\ ledLog[t][c].term = t
         /\ IsAcker(v.voter, t, c)
         /\ Between(t, c, v.term))
        => \E m \in msgs : /\ m.type = "vote" /\ m.src = v.cand /\ m.term = v.term
                           /\ \/ m.lastLogTerm > t
                              \/ m.lastLogTerm = t /\ m.lastLogIndex >= c

Good(j, u) ==
    \A t \in DOMAIN ledLog : \A c \in 1..Len(ledLog[t]) :
        (/\ t < u
         /\ ledLog[t][c].term = t
         /\ IsAcker(j, t, c)
         /\ Between(t, c, u))
        => Has(ledLog[u], c, t)

\* Every leader was elected by a quorum of voters, each of which passes on
\* what it had acknowledged.
QuorumInv ==
    \A l \in leaders : \E Q \in SUBSET Server :
        /\ IsQuorum(Q)
        /\ \A j \in Q : /\ [voter |-> j, term |-> l.term, cand |-> l.server] \in votes
                        /\ Good(j, l.term)

\* Entry c of the leader log of t is of term t and stored by a quorum.
QC(t, c) ==
    /\ ledLog[t][c].term = t
    /\ \E Q \in SUBSET Server : IsQuorum(Q) /\ \A j \in Q : IsAcker(j, t, c)

CommitsInv ==
    \A k \in commits :
        /\ k.term \in DOMAIN ledLog
        /\ Len(k.entries) <= Len(ledLog[k.term])
        /\ \A q \in 1..Len(k.entries) : k.entries[q] = ledLog[k.term][q]
        /\ \E t \in DOMAIN ledLog : \E c \in 1..Len(ledLog[t]) :
              t <= k.term /\ Len(k.entries) <= c /\ QC(t, c)

CommitIndexInv ==
    \A i \in Server :
        \/ commitIndex[i] = 0
        \/ \E k \in commits :
              /\ k.term <= currentTerm[i]
              /\ commitIndex[i] <= Len(k.entries)
              /\ commitIndex[i] <= Len(log[i])
              /\ \A q \in 1..commitIndex[i] : log[i][q] = k.entries[q]

AppliedInv ==
    \A a \in applied : \E k \in commits :
        a.index \in 1..Len(k.entries) /\ k.entries[a.index] = a.entry

Inv ==
    /\ TypeOK /\ TermInv /\ VotesInv /\ OneVotePerTerm /\ VoteReqInv /\ GrantInv
    /\ LeadersInv /\ ElectionSafety /\ LogsInv /\ AppendInv /\ AckInv
    /\ ConfirmedInv /\ AckerInv /\ VoterInv /\ QuorumInv
    /\ CommitsInv /\ CommitIndexInv /\ AppliedInv
====
