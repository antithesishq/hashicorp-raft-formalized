---- MODULE MCRaft ----
\* Bounded instances of Raft for model checking. See ../scripts/mc.sh.
EXTENDS Raft, TLC

CONSTANTS MaxTerm, MaxLog, MaxBatch, MaxMsgs

Bounded ==
    /\ \A i \in Server : currentTerm[i] <= MaxTerm /\ Len(log[i]) <= MaxLog
    /\ \A m \in msgs : m.type = "append" => Len(m.entries) <= MaxBatch
    /\ Cardinality(msgs) <= MaxMsgs

Symmetry == Permutations(Server)

\* Requests always carry a full batch when there is one to send, and the
\* highest commit index allowed (a request with less adds nothing that one
\* with more does not).
MaxCommit(l) ==
    LET S == {c \in 0..Len(l) : CommittedIn(l, c)} IN CHOOSE c \in S : \A d \in S : d <= c

Sends(i) ==
    \E j \in Server, ld \in leaders :
        /\ ld.server = i
        /\ LET l == ledLog[ld.term] IN
           \E p \in 0..Len(l) :
              SendAppend(i, j, ld.term, p, Min(MaxBatch, Len(l) - p), MaxCommit(l))

Receives ==
    \E m \in msgs :
          /\ m.type = "append"
          /\ \/ Ack(m.dst, m)
             \/ \E k \in 1..Len(m.entries) : DeleteSuffix(m.dst, m, k) \/ StoreEntries(m.dst, m, k)
             \/ \E c \in 1..m.commit : FollowerCommit(m.dst, m, c)

\* Everything, with the restriction on requests above.
FullNext ==
    \/ \E i \in Server :
          \/ BecomeCandidate(i) \/ BecomeFollower(i) \/ BecomeLeader(i)
          \/ StartElection(i) \/ SetVoteTerm(i) \/ Restart(i)
          \/ \E t \in {currentTerm[k] : k \in Server} : AdoptTerm(i, t)
          \/ \E c \in Server : SetVoteFor(i, c)
          \/ \E v \in votes : v.voter = i /\ GrantVote(i, v.cand, v.term)
          \/ \E ty \in {"noop", "barrier"} : LeaderAppend(i, <<Entry(currentTerm[i], ty, Nil)>>)
          \/ \E v \in Values : LeaderAppend(i, <<Entry(currentTerm[i], "command", v)>>)
          \/ \E c \in 1..Len(log[i]), l \in leaders : l.server = i /\ LeaderCommit(i, l.term, c)
          \/ Sends(i)
    \/ Receives
FullSpec == Init /\ [][FullNext]_vars

\* Without restarts.
QuietNext ==
    \/ \E i \in Server :
          \/ BecomeCandidate(i) \/ BecomeFollower(i) \/ BecomeLeader(i)
          \/ StartElection(i) \/ SetVoteTerm(i)
          \/ \E t \in {currentTerm[k] : k \in Server} : AdoptTerm(i, t)
          \/ \E c \in Server : SetVoteFor(i, c)
          \/ \E v \in votes : v.voter = i /\ GrantVote(i, v.cand, v.term)
          \/ LeaderAppend(i, <<Entry(currentTerm[i], "noop", Nil)>>)
          \/ \E v \in Values : LeaderAppend(i, <<Entry(currentTerm[i], "command", v)>>)
          \/ \E c \in 1..Len(log[i]), l \in leaders : l.server = i /\ LeaderCommit(i, l.term, c)
          \/ Sends(i)
    \/ Receives
QuietSpec == Init /\ [][QuietNext]_vars

\* Seeded errors, substituted for Raft's definitions in the MCMut configs.
NoFreshnessCheck(m, i) == TRUE              \* for UpToDate
QuorumOfOne(S) == Cardinality(S) >= 1       \* for IsQuorum
NoPrevCheck(j, m) == TRUE                   \* for PrevOk
====
