---- MODULE MCRaft ----
\* Bounded instances of HashicorpRaft for TLC (scripts/mc.sh).
EXTENDS HashicorpRaft, TLC

CONSTANTS MaxTerm, MaxLog, MaxBatch, MaxMsgs

Bounded ==
    /\ \A i \in Server : currentTerm[i] <= MaxTerm /\ Len(log[i]) <= MaxLog
    /\ \A m \in msgs : m.type = "append" => Len(m.entries) <= MaxBatch \/ Installable(m)
    /\ Cardinality(msgs) <= MaxMsgs

Symmetry == Permutations(Server)

\* Requests carry a full batch and the highest allowed commit index (smaller
\* ones add no behaviour).
MaxCommit(l, t) ==
    LET S == {c \in 0..Len(l) : CommittedIn(l, c, t)} IN CHOOSE c \in S : \A d \in S : d <= c

Sends(i) ==
    \E j \in Server, ld \in leaders :
        /\ ld.server = i
        /\ LET l == ledLog[ld.term] IN
           \E p \in 0..Len(l) :
              SendAppend(i, j, ld.term, p, Min(MaxBatch, Len(l) - p), MaxCommit(l, ld.term))

Receives ==
    \E m \in msgs :
          /\ m.type = "append"
          /\ \/ Ack(m.dst, m)
             \/ \E k \in 1..Len(m.entries) : DeleteSuffix(m.dst, m, k) \/ StoreEntries(m.dst, m, k)
             \/ \E c \in 1..m.commit : FollowerCommit(m.dst, m, c)
             \/ InstallSnapshot(m.dst, m)

\* Take, compact, and send a snapshot (any committed prefix of the leader log).
Snaps(i) ==
    \/ \E k \in 1..lastApplied[i] : TakeSnapshot(i, k)
    \/ \E b \in 1..Len(snap[i]) : CompactLog(i, b)
    \/ /\ Snapshots
       /\ \E j \in Server, ld \in leaders :
            /\ ld.server = i
            /\ \E n \in 1..Len(ledLog[ld.term]) : SendAppend(i, j, ld.term, 0, n, n)

\* Pre-votes and leadership transfer.
Extra(i) ==
    \/ SendPreVote(i) \/ TimeoutNow(i)
    \/ \E j \in Server : SendTimeoutNow(i, j)
    \/ \E m \in msgs : m.type = "prevote" /\ GrantPreVote(i, m)

\* All actions, with the request restriction above.
FullNext ==
    \/ \E i \in Server :
          \/ BecomeCandidate(i) \/ BecomeFollower(i) \/ BecomeLeader(i)
          \/ StartElection(i) \/ SetVoteTerm(i) \/ Restart(i) \/ Apply(i)
          \/ \E t \in {currentTerm[k] : k \in Server} : AdoptTerm(i, t)
          \/ \E c \in Server : SetVoteFor(i, c)
          \/ \E v \in votes : v.voter = i /\ GrantVote(i, v.cand, v.term)
          \/ \E ty \in {"noop", "barrier"} : LeaderAppend(i, <<Entry(currentTerm[i], ty, Nil)>>)
          \/ \E v \in Values : LeaderAppend(i, <<Entry(currentTerm[i], "command", v)>>)
          \/ \E c \in 1..Len(log[i]), l \in leaders : l.server = i /\ LeaderCommit(i, l.term, c)
          \/ Sends(i) \/ Extra(i) \/ Snaps(i)
    \/ Receives
FullSpec == Init /\ [][FullNext]_vars

\* Without restarts, pre-votes or leadership transfer (PreVote FALSE).
QuietNext ==
    \/ \E i \in Server :
          \/ BecomeCandidate(i) \/ BecomeFollower(i) \/ BecomeLeader(i)
          \/ StartElection(i) \/ SetVoteTerm(i) \/ Apply(i)
          \/ \E t \in {currentTerm[k] : k \in Server} : AdoptTerm(i, t)
          \/ \E c \in Server : SetVoteFor(i, c)
          \/ \E v \in votes : v.voter = i /\ GrantVote(i, v.cand, v.term)
          \/ LeaderAppend(i, <<Entry(currentTerm[i], "noop", Nil)>>)
          \/ \E v \in Values : LeaderAppend(i, <<Entry(currentTerm[i], "command", v)>>)
          \/ \E c \in 1..Len(log[i]), l \in leaders : l.server = i /\ LeaderCommit(i, l.term, c)
          \/ Sends(i) \/ Snaps(i)
    \/ Receives
QuietSpec == Init /\ [][QuietNext]_vars

\* Without restarts, with pre-votes and leadership transfer.
QuietPVNext == QuietNext \/ \E i \in Server : Extra(i)
QuietPVSpec == Init /\ [][QuietPVNext]_vars
====
