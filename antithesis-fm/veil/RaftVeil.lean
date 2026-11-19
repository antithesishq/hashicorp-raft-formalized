module

public import Veil

/-!
`../spec/HashicorpRaft.tla` in Veil: the same variables, actions, parameters and properties,
each TLA+ definition quoted above its translation.

Encoding: `Server` is `server`; `Cardinality` of a set of servers given by a condition is
`Card` over `Servers.all`; `Nil` is `none`; a log is a `List` (entry `k` is element `k - 1`);
`confirmed[i]` is `confirmedTerm i` and `confirmedIndex i`; message kinds are the constructors
of `Msg`; `ledLog` is `Nat → Option log` (`none` outside its domain); the constants `PreVote`
and `Snapshots` are immutable individuals (the proofs hold for either value); the sets are
TSets. Actions read message fields through accessors (`m.dst`), since Veil generates no proof
goals for a `match` inside an action.

Layout: the model; its invariants (every state invariant of HashicorpRaft.tla, plus the
supporting ones the proofs need); lemmas; and the proofs, one section per action.
-/


veil module RaftVeil

@[veil_decl]
inductive EntryType where
  | config
  | noop
  | barrier
  | command

deriving instance Veil.Enumeration for EntryType

-- Entry(t, ty, v) == [term |-> t, type |-> ty, value |-> v]
@[veil_decl]
structure Entry (value : Type) where
  term : Nat
  kind : EntryType
  value : Option value

@[veil_decl]
inductive Msg (server value : Type) where
  -- [type |-> "vote", src, term, lastLogIndex, lastLogTerm]
  | vote (src : server) (term : Nat) (lastLogIndex : Nat) (lastLogTerm : Nat)
  -- [type |-> "grant", src, dst, term]
  | grant (src : server) (dst : server) (term : Nat)
  -- [type |-> "append", src, dst, term, prevLogIndex, prevLogTerm, entries, commit]
  | append (src : server) (dst : server) (term : Nat) (prevLogIndex : Nat) (prevLogTerm : Nat)
      (entries : List (Entry value)) (commit : Nat)
  -- [type |-> "ack", src, dst, term, index]
  | ack (src : server) (dst : server) (term : Nat) (index : Nat)
  -- [type |-> "prevote", src, term, lastLogIndex, lastLogTerm]
  | prevote (src : server) (term : Nat) (lastLogIndex : Nat) (lastLogTerm : Nat)
  -- [type |-> "pregrant", src, dst, term]
  | pregrant (src : server) (dst : server) (term : Nat)
  -- [type |-> "timeoutnow", src, dst]
  | timeoutnow (src : server) (dst : server)

-- Fields of a message, as the source's `m.dst`, `m.entries`. Actions read them only on a
-- message of a kind they require; the values for other kinds are never read.
def Msg.isAppend {server value : Type} (m : Msg server value) : Bool :=
  match m with | .append .. => true | _ => false
def Msg.src {server value : Type} (m : Msg server value) : server :=
  match m with
  | .vote s .. => s | .grant s .. => s | .append s .. => s | .ack s .. => s
  | .prevote s .. => s | .pregrant s .. => s | .timeoutnow s _ => s
def Msg.dst {server value : Type} (m : Msg server value) : server :=
  match m with
  | .vote s .. => s | .grant _ d _ => d | .append _ d .. => d | .ack _ d .. => d
  | .prevote s .. => s | .pregrant _ d _ => d | .timeoutnow _ d => d
def Msg.term {server value : Type} (m : Msg server value) : Nat :=
  match m with
  | .vote _ t .. => t | .grant _ _ t => t | .append _ _ t .. => t | .ack _ _ t _ => t
  | .prevote _ t .. => t | .pregrant _ _ t => t | .timeoutnow .. => 0
def Msg.prevLogIndex {server value : Type} (m : Msg server value) : Nat :=
  match m with | .append _ _ _ p .. => p | _ => 0
def Msg.prevLogTerm {server value : Type} (m : Msg server value) : Nat :=
  match m with | .append _ _ _ _ pt .. => pt | _ => 0
def Msg.entries {server value : Type} (m : Msg server value) : List (Entry value) :=
  match m with | .append _ _ _ _ _ es _ => es | _ => []
def Msg.commit {server value : Type} (m : Msg server value) : Nat :=
  match m with | .append _ _ _ _ _ _ c => c | _ => 0

-- The fields of a pre-vote request, read the same way by GrantPreVote.
def Msg.isPreVote {server value : Type} (m : Msg server value) : Bool :=
  match m with | .prevote .. => true | _ => false
def Msg.lastLogIndex {server value : Type} (m : Msg server value) : Nat :=
  match m with | .vote _ _ li _ => li | .prevote _ _ li _ => li | _ => 0
def Msg.lastLogTerm {server value : Type} (m : Msg server value) : Nat :=
  match m with | .vote _ _ _ lt => lt | .prevote _ _ _ lt => lt | _ => 0

-- An element of `votes`: [voter, term, cand].
@[veil_decl]
structure Vote (server : Type) where
  voter : server
  term : Nat
  cand : server

-- An element of `leaders`: [server, term].
@[veil_decl]
structure Elected (server : Type) where
  server : server
  term : Nat

-- An element of `commits`: [server, term, entries].
@[veil_decl]
structure Commit (server value : Type) where
  server : server
  term : Nat
  entries : List (Entry value)

-- An element of `applied`: [server, index, entry].
@[veil_decl]
structure Applied (server value : Type) where
  server : server
  index : Nat
  entry : Entry value

-- TermAt(l, k) == IF k > 0 /\ k <= Len(l) THEN l[k].term ELSE 0
def TermAt {value : Type} (l : List (Entry value)) (k : Nat) : Nat :=
  match k with
  | 0 => 0
  | k + 1 => match l[k]? with
    | some e => e.term
    | none => 0

-- Stands for `l[k]` where k is outside the log; never read (see Apply).
def noEntry {value : Type} : Entry value := { term := 0, kind := .config, value := none }

-- SubSeq(l, m, n)
def SubSeq {α : Type} (l : List α) (m n : Nat) : List α := (l.drop (m - 1)).take (n + 1 - m)

-- IsPrefix(a, b) == Len(a) <= Len(b) /\ a = SubSeq(b, 1, Len(a))
def IsPrefix {α : Type} [DecidableEq α] (a b : List α) : Bool :=
  decide (a.length ≤ b.length ∧ a = SubSeq b 1 a.length)

/-- The servers are finitely many: a list of all of them, without repeats. -/
class Servers (server : Type) where
  all : List server
  complete : ∀ s, s ∈ all
  nodup : all.Nodup

instance (n : Nat) : Servers (Fin n) where
  all := List.finRange n
  complete := by simp
  nodup := List.nodup_finRange n

-- Cardinality({s \in Server : p(s)})
def Card {server : Type} [Servers server] (p : server → Bool) : Nat :=
  ((Servers.all (server := server)).filter p).length

-- IsQuorum(S) == Cardinality(S) * 2 > Cardinality(Server)
def IsQuorum {server : Type} [Servers server] (p : server → Bool) : Bool :=
  decide (Card p * 2 > Card (fun _ : server => true))

type server
type value
type MsgSet
type VoteSet
type LeaderSet
type CommitSet
type AppliedSet
instantiate srv : Servers server
instantiate msgSet : TSet (Msg server value) MsgSet
instantiate vSet : TSet (Vote server) VoteSet
instantiate lSet : TSet (Elected server) LeaderSet
instantiate cSet : TSet (Commit server value) CommitSet
instantiate aSet : TSet (Applied server value) AppliedSet

-- The bounds of MCRaft.tla's `Bounded`.
immutable individual MaxTerm : Nat
immutable individual MaxLog : Nat
immutable individual MaxBatch : Nat
immutable individual MaxMsgs : Nat

-- The constant PreVote.
immutable individual PreVote : Bool

-- The constant Snapshots.
immutable individual Snapshots : Bool

enum Role = {Follower, Candidate, Leader}

function currentTerm : server → Nat
function voteTerm : server → Nat
function voteFor : server → Option server
function log : server → List (Entry value)
function role : server → Role
function commitIndex : server → Nat
function confirmedTerm : server → Nat
function confirmedIndex : server → Nat
individual msgs : MsgSet
individual votes : VoteSet
individual leaders : LeaderSet
function ledLog : Nat → Option (List (Entry value))
individual commits : CommitSet
function lastApplied : server → Nat
individual applied : AppliedSet
-- Declared last, so that earlier fields keep their positions in the proofs.
function transfer : server → Bool
-- snap[i]: node i's newest snapshot, as its entries; base[i]: entries deleted from the front
-- of its log store. Declared after `transfer` for the same reason.
function snap : server → List (Entry value)
function base : server → Nat

set_option veil.warnHybridFields false
set_option veil.deferVCGeneration true
#gen_state

after_init {
  currentTerm S := 1
  voteTerm S := 0
  voteFor S := none
  log S := [{ term := 1, kind := .config, value := none }]
  role S := Follower
  commitIndex S := 0
  confirmedTerm S := 0
  confirmedIndex S := 0
  msgs := msgSet.empty
  votes := vSet.empty
  leaders := lSet.empty
  ledLog T := none
  commits := cSet.empty
  lastApplied S := 0
  applied := aSet.empty
  transfer S := false
  snap S := []
  base S := 0
}

-- BecomeCandidate(i) == role' = [role EXCEPT ![i] = Candidate]
action BecomeCandidate (i : server) {
  role i := Candidate
}

-- BecomeFollower(i) ==
--     /\ role' = [role EXCEPT ![i] = Follower]
--     /\ transfer' = [transfer EXCEPT ![i] = FALSE]
action BecomeFollower (i : server) {
  role i := Follower
  transfer i := false
}

-- PreGranted(i) ==
--     {i} \cup {j \in Server \ {i} :
--               [type |-> "pregrant", src |-> j, dst |-> i, term |-> currentTerm[i] + 1] \in msgs}
-- MayStartElection(i) == ~PreVote \/ transfer[i] \/ IsQuorum(PreGranted(i))
-- StartElection(i) ==
--     /\ role[i] = Candidate
--     /\ MayStartElection(i)
--     /\ currentTerm' = [currentTerm EXCEPT ![i] = @ + 1]
--     /\ msgs' = msgs \cup {VoteRequest(i, currentTerm[i] + 1)}
--     /\ transfer' = [transfer EXCEPT ![i] = FALSE]
action StartElection (i : server) {
  require role i = Candidate
  let t := currentTerm i + 1
  let l := log i
  let ms := msgs
  require PreVote = false ∨ transfer i = true ∨
    IsQuorum (fun j => if j = i then true else msgSet.contains (.pregrant j i t) ms) = true
  currentTerm i := t
  msgs := msgSet.insert (.vote i t l.length (TermAt l l.length)) msgs
  transfer i := false
}

-- AdoptTerm(i, t) ==
--     /\ t > currentTerm[i]
--     /\ \E k \in Server \ {i} : currentTerm[k] >= t
--     /\ currentTerm' = [currentTerm EXCEPT ![i] = t]
--     /\ role' = [role EXCEPT ![i] = Follower]
--     /\ transfer' = [transfer EXCEPT ![i] = FALSE]
-- Next: \E t \in {currentTerm[k] : k \in Server} : AdoptTerm(i, t)
action AdoptTerm (i : server) {
  let k ← pick server
  let t := currentTerm k
  require t > currentTerm i
  require ∃ k', k' ≠ i ∧ currentTerm k' ≥ t
  currentTerm i := t
  role i := Follower
  transfer i := false
}

-- UpToDate(m, i) ==
--     \/ m.lastLogTerm > LastTerm(i)
--     \/ m.lastLogTerm = LastTerm(i) /\ m.lastLogIndex >= Len(log[i])
-- MayVote(i, c) ==
--     \E m \in msgs : m.type = "vote" /\ m.src = c /\ m.term = currentTerm[i] /\ UpToDate(m, i)
-- SetVoteFor(i, c) ==
--     /\ voteTerm[i] # currentTerm[i]
--     /\ MayVote(i, c)
--     /\ voteFor' = [voteFor EXCEPT ![i] = c]
action SetVoteFor (i : server) (c : server) {
  require voteTerm i ≠ currentTerm i
  let l := log i
  let lastTerm := TermAt l l.length
  let cur := currentTerm i
  require ∃ m : { m // m ∈ msgs },
    (match m.val with
      | .vote src term lastLogIndex lastLogTerm =>
        decide (src = c ∧ term = cur ∧
          (lastLogTerm > lastTerm ∨ (lastLogTerm = lastTerm ∧ lastLogIndex ≥ l.length)))
      | _ => false) = true
  voteFor i := some c
}

-- SetVoteTerm(i) ==
--     /\ voteTerm[i] # currentTerm[i]
--     /\ voteFor[i] # Nil
--     /\ MayVote(i, voteFor[i])
--     /\ voteTerm' = [voteTerm EXCEPT ![i] = currentTerm[i]]
--     /\ votes' = votes \cup {[voter |-> i, term |-> currentTerm[i], cand |-> voteFor[i]]}
-- `c` is voteFor[i]: the first requirement says so.
action SetVoteTerm (i : server) (c : server) {
  require voteFor i = some c
  require voteTerm i ≠ currentTerm i
  let l := log i
  let lastTerm := TermAt l l.length
  let cur := currentTerm i
  require ∃ m : { m // m ∈ msgs },
    (match m.val with
      | .vote src term lastLogIndex lastLogTerm =>
        decide (src = c ∧ term = cur ∧
          (lastLogTerm > lastTerm ∨ (lastLogTerm = lastTerm ∧ lastLogIndex ≥ l.length)))
      | _ => false) = true
  voteTerm i := cur
  votes := vSet.insert { voter := i, term := cur, cand := c } votes
}

-- GrantVote(i, c, t) ==
--     /\ c # i
--     /\ [voter |-> i, term |-> t, cand |-> c] \in votes
--     /\ msgs' = msgs \cup {[type |-> "grant", src |-> i, dst |-> c, term |-> t]}
-- Next: \E v \in votes : v.voter = i /\ GrantVote(i, v.cand, v.term)
action GrantVote (i : server) {
  let v : { v // v ∈ votes } :| v.val.voter = i ∧ v.val.cand ≠ i
  msgs := msgSet.insert (.grant i v.val.cand v.val.term) msgs
}

-- IsQuorum(S) == Cardinality(S) * 2 > Cardinality(Server)
-- Granted(i) ==
--     {j \in Server \ {i} : [type |-> "grant", src |-> j, dst |-> i, term |-> currentTerm[i]] \in msgs}
--     \cup (IF [voter |-> i, term |-> currentTerm[i], cand |-> i] \in votes THEN {i} ELSE {})
-- BecomeLeader(i) ==
--     /\ role[i] = Candidate
--     /\ IsQuorum(Granted(i))
--     /\ role' = [role EXCEPT ![i] = Leader]
--     /\ leaders' = leaders \cup {[server |-> i, term |-> currentTerm[i]]}
--     /\ ledLog' = WithLed(currentTerm[i], log[i])
--     /\ transfer' = [transfer EXCEPT ![i] = FALSE]
action BecomeLeader (i : server) {
  require role i = Candidate
  let cur := currentTerm i
  let vs := votes
  let ms := msgs
  require IsQuorum (fun j =>
    if j = i then vSet.contains { voter := i, term := cur, cand := i } vs
    else msgSet.contains (.grant j i cur) ms)
  role i := Leader
  leaders := lSet.insert { server := i, term := cur } leaders
  ledLog cur := some (log i)
  transfer i := false
}

-- LeaderAppend(i, es) ==
--     /\ role[i] = Leader
--     /\ Len(es) > 0
--     /\ \A k \in 1..Len(es) : es[k].term = currentTerm[i]
--     /\ log' = [log EXCEPT ![i] = @ \o es]
--     /\ ledLog' = WithLed(currentTerm[i], log[i] \o es)
-- Next: \E ty \in {"noop", "barrier"} : LeaderAppend(i, <<Entry(currentTerm[i], ty, Nil)>>)
--       \E v \in Values : LeaderAppend(i, <<Entry(currentTerm[i], "command", v)>>)
-- `ty` and `v` cover both disjuncts of Next: a marker entry (`v` unused) or command `v`.
action LeaderAppend (i : server) (ty : EntryType) (v : value) {
  require ty ≠ .config
  require role i = Leader
  let cur := currentTerm i
  let l := log i ++ [{ term := cur, kind := ty, value := if ty = .command then some v else none }]
  log i := l
  ledLog cur := some l
}

-- KnownIn(k, t) == k.term <= t
-- CommittedIn(l, c, t) ==
--     \/ c = 0
--     \/ /\ c <= Len(l)
--        /\ \E k \in commits : /\ KnownIn(k, t)
--                              /\ c <= Len(k.entries)
--                              /\ SubSeq(k.entries, 1, c) = SubSeq(l, 1, c)
-- SendAppend(i, j, t, p, n, c) ==
--     /\ [server |-> i, term |-> t] \in leaders
--     /\ j # i
--     /\ p + n <= Len(ledLog[t])
--     /\ CommittedIn(ledLog[t], c, t)
--     /\ msgs' = msgs \cup {[type |-> "append", src |-> i, dst |-> j, term |-> t,
--                            prevLogIndex |-> p, prevLogTerm |-> TermAt(ledLog[t], p),
--                            entries |-> SubSeq(ledLog[t], p + 1, p + n), commit |-> c]}
-- Next: \E j \in Server, l \in leaders : l.server = i /\
--          \E p, n, c \in 0..Len(ledLog[l.term]) : SendAppend(i, j, l.term, p, n, c)
action SendAppend (i : server) (j : server) {
  require j ≠ i
  let ld : { ld // ld ∈ leaders } :| ld.val.server = i
  let t := ld.val.term
  let l := (ledLog t).getD []
  let (p, n, c) : { p // p ∈ List.range (l.length + 1) } × { n // n ∈ List.range (l.length + 1) }
      × { c // c ∈ List.range (l.length + 1) } :|
    p.val + n.val ≤ l.length ∧
    (c.val = 0 ∨ ∃ k : { k // k ∈ commits },
      k.val.term ≤ t ∧ c.val ≤ k.val.entries.length ∧ SubSeq k.val.entries 1 c.val = SubSeq l 1 c.val)
  msgs := msgSet.insert
    (.append i j t p.val (TermAt l p.val) (SubSeq l (p.val + 1) (p.val + n.val)) c.val) msgs
}

-- Acked(i, t, c) ==
--     {i} \cup {j \in Server \ {i} :
--                  \E a \in msgs : a.type = "ack" /\ a.src = j /\ a.dst = i /\ a.term = t /\ a.index >= c}
-- Committed(s, t, c) == [server |-> s, term |-> t, entries |-> SubSeq(log[s], 1, c)]
-- LeaderCommit(i, t, c) ==
--     /\ [server |-> i, term |-> t] \in leaders
--     /\ c >= 1
--     /\ c <= Len(log[i])
--     /\ log[i][c].term = t
--     /\ IsQuorum(Acked(i, t, c))
--     /\ commitIndex' = [commitIndex EXCEPT ![i] = Max(@, c)]
--     /\ commits' = commits \cup {Committed(i, t, c)}
-- Next: \E c \in 1..Len(log[i]), l \in leaders : l.server = i /\ LeaderCommit(i, l.term, c)
action LeaderCommit (i : server) {
  let ld : { ld // ld ∈ leaders } :| ld.val.server = i
  let t := ld.val.term
  let l := log i
  let c : { c // c ∈ List.range' 1 l.length } :| TermAt l c.val = t
  let ms := msgs
  require IsQuorum (fun j =>
    if j = i then true
    else decide (∃ a : { a // a ∈ ms },
      (match a.val with
        | .ack src dst term index => decide (src = j ∧ dst = i ∧ term = t ∧ index ≥ c.val)
        | _ => false) = true))
  commitIndex i := max (commitIndex i) c.val
  commits := cSet.insert { server := i, term := t, entries := SubSeq l 1 c.val } commits
}

-- PrevOk(j, m) ==
--     IF m.prevLogIndex = 0 THEN TRUE
--     ELSE /\ m.prevLogIndex <= Len(log[j])
--          /\ log[j][m.prevLogIndex].term = m.prevLogTerm
def PrevOk {value : Type} (l : List (Entry value)) (prevLogIndex prevLogTerm : Nat) : Bool :=
  match prevLogIndex with
  | 0 => true
  | p + 1 => match l[p]? with
    | some e => e.term == prevLogTerm
    | none => false

-- HasFirst(j, m, k) ==
--     \A q \in 1..k :
--         /\ m.prevLogIndex + q <= Len(log[j])
--         /\ log[j][m.prevLogIndex + q].term = m.entries[q].term
def HasFirst {value : Type} (l : List (Entry value)) (prevLogIndex : Nat) (entries : List (Entry value))
    (k : Nat) : Bool :=
  (List.range k).all fun q =>
    match l[prevLogIndex + q]?, entries[q]? with
    | some a, some b => a.term == b.term
    | _, _ => false

-- DeleteSuffix(j, m, k) ==
--     /\ m \in msgs /\ m.type = "append" /\ m.dst = j
--     /\ m.term = currentTerm[j]
--     /\ PrevOk(j, m)
--     /\ k \in 1..Len(m.entries)
--     /\ HasFirst(j, m, k - 1)
--     /\ m.prevLogIndex + k <= Len(log[j])
--     /\ log[j][m.prevLogIndex + k].term # m.entries[k].term
--     /\ m.prevLogIndex + k > Len(snap[j])
--     /\ log' = [log EXCEPT ![j] = SubSeq(@, 1, m.prevLogIndex + k - 1)]
--     /\ confirmed' = Confirm(j, m.term, m.prevLogIndex + k - 1)
-- Next: \E m \in msgs : m.type = "append" /\ \E k \in 1..Len(m.entries) : DeleteSuffix(m.dst, m, k)
action DeleteSuffix {
  let m : { m // m ∈ msgs } :| m.val.isAppend = true
  let m := m.val
  let j := m.dst
  let l := log j
  require m.term = currentTerm j
  require PrevOk l m.prevLogIndex m.prevLogTerm
  let k : { k // k ∈ List.range' 1 m.entries.length } :|
    HasFirst l m.prevLogIndex m.entries (k.val - 1) ∧
    m.prevLogIndex + k.val ≤ l.length ∧
    TermAt l (m.prevLogIndex + k.val) ≠ TermAt m.entries k.val
  require m.prevLogIndex + k.val > (snap j).length
  log j := SubSeq l 1 (m.prevLogIndex + k.val - 1)
  confirmedTerm j := m.term
  confirmedIndex j := m.prevLogIndex + k.val - 1
}

-- StoreEntries(j, m, k) ==
--     /\ m \in msgs /\ m.type = "append" /\ m.dst = j
--     /\ m.term = currentTerm[j]
--     /\ PrevOk(j, m)
--     /\ k \in 1..Len(m.entries)
--     /\ HasFirst(j, m, k - 1)
--     /\ m.prevLogIndex + k = Len(log[j]) + 1
--     /\ log' = [log EXCEPT ![j] = @ \o SubSeq(m.entries, k, Len(m.entries))]
--     /\ confirmed' = Confirm(j, m.term, m.prevLogIndex + Len(m.entries))
action StoreEntries {
  let m : { m // m ∈ msgs } :| m.val.isAppend = true
  let m := m.val
  let j := m.dst
  let l := log j
  require m.term = currentTerm j
  require PrevOk l m.prevLogIndex m.prevLogTerm
  let k : { k // k ∈ List.range' 1 m.entries.length } :|
    HasFirst l m.prevLogIndex m.entries (k.val - 1) ∧
    m.prevLogIndex + k.val = l.length + 1
  log j := l ++ SubSeq m.entries k.val m.entries.length
  confirmedTerm j := m.term
  confirmedIndex j := m.prevLogIndex + m.entries.length
}

-- Ack(j, m) ==
--     /\ m \in msgs /\ m.type = "append" /\ m.dst = j
--     /\ currentTerm[j] = m.term
--     /\ PrevOk(j, m)
--     /\ HasFirst(j, m, Len(m.entries))
--     /\ LET last == m.prevLogIndex + Len(m.entries)
--        IN /\ msgs' = msgs \cup {[type |-> "ack", src |-> j, dst |-> m.src, term |-> m.term, index |-> last]}
--           /\ confirmed' = Confirm(j, m.term,
--                 IF confirmed[j].term = m.term THEN Max(confirmed[j].index, last) ELSE last)
action Ack {
  let m : { m // m ∈ msgs } :| m.val.isAppend = true
  let m := m.val
  let j := m.dst
  let l := log j
  require currentTerm j = m.term
  require PrevOk l m.prevLogIndex m.prevLogTerm
  require HasFirst l m.prevLogIndex m.entries m.entries.length
  let last := m.prevLogIndex + m.entries.length
  let idx := if confirmedTerm j = m.term then max (confirmedIndex j) last else last
  msgs := msgSet.insert (.ack j m.src m.term last) msgs
  confirmedTerm j := m.term
  confirmedIndex j := idx
}

-- FollowerCommit(j, m, c) ==
--     /\ m \in msgs /\ m.type = "append" /\ m.dst = j
--     /\ m.term = confirmed[j].term
--     /\ c > commitIndex[j]
--     /\ c <= Min(m.commit, confirmed[j].index)
--     /\ commitIndex' = [commitIndex EXCEPT ![j] = c]
--     /\ commits' = commits \cup {Committed(j, m.term, c)}
-- Next: \E c \in 1..m.commit : FollowerCommit(m.dst, m, c)
action FollowerCommit {
  let m : { m // m ∈ msgs } :| m.val.isAppend = true
  let m := m.val
  let j := m.dst
  require m.term = confirmedTerm j
  let ci := commitIndex j
  let cf := confirmedIndex j
  let c : { c // c ∈ List.range' 1 m.commit } :| c.val > ci ∧ c.val ≤ min m.commit cf
  commitIndex j := c.val
  commits := cSet.insert { server := j, term := m.term, entries := SubSeq (log j) 1 c.val } commits
}

-- Apply(i) ==
--     LET k == lastApplied[i] + 1 IN
--     /\ k <= commitIndex[i]
--     /\ k <= Len(log[i])
--     /\ lastApplied' = [lastApplied EXCEPT ![i] = k]
--     /\ applied' = applied \cup {[server |-> i, index |-> k, entry |-> log[i][k]]}
-- `log[i][k]` is read with a default that the second requirement makes unreachable.
action Apply (i : server) {
  let k := lastApplied i + 1
  let l := log i
  require k ≤ commitIndex i
  require k ≤ l.length
  lastApplied i := k
  applied := aSet.insert { server := i, index := k, entry := (l[k - 1]?).getD noEntry } applied
}

-- Restart(i) ==
--     /\ role' = [role EXCEPT ![i] = Follower]
--     /\ commitIndex' = [commitIndex EXCEPT ![i] = 0]
--     /\ lastApplied' = [lastApplied EXCEPT ![i] = Len(snap[i])]
--     /\ transfer' = [transfer EXCEPT ![i] = FALSE]
action Restart (i : server) {
  role i := Follower
  commitIndex i := 0
  lastApplied i := (snap i).length
  transfer i := false
}

-- PreVoteRequest(i, t) ==
--     [type |-> "prevote", src |-> i, term |-> t,
--      lastLogIndex |-> Len(log[i]), lastLogTerm |-> LastTerm(i)]
-- SendPreVote(i) ==
--     /\ PreVote
--     /\ role[i] = Candidate
--     /\ msgs' = msgs \cup {PreVoteRequest(i, currentTerm[i] + 1)}
action SendPreVote (i : server) {
  require PreVote = true
  require role i = Candidate
  let l := log i
  msgs := msgSet.insert (.prevote i (currentTerm i + 1) l.length (TermAt l l.length)) msgs
}

-- GrantPreVote(j, m) ==
--     /\ m \in msgs /\ m.type = "prevote" /\ m.src # j
--     /\ m.term >= currentTerm[j]
--     /\ UpToDate(m, j)
--     /\ msgs' = msgs \cup {[type |-> "pregrant", src |-> j, dst |-> m.src, term |-> m.term]}
-- Next: \E m \in msgs : m.type = "prevote" /\ GrantPreVote(i, m)
action GrantPreVote (j : server) {
  let m : { m // m ∈ msgs } :| m.val.isPreVote = true
  let m := m.val
  let l := log j
  let lastTerm := TermAt l l.length
  require m.src ≠ j
  require m.term ≥ currentTerm j
  require m.lastLogTerm > lastTerm ∨ (m.lastLogTerm = lastTerm ∧ m.lastLogIndex ≥ l.length)
  msgs := msgSet.insert (.pregrant j m.src m.term) msgs
}

-- SendTimeoutNow(i, j) ==
--     /\ \E l \in leaders : l.server = i
--     /\ j # i
--     /\ msgs' = msgs \cup {[type |-> "timeoutnow", src |-> i, dst |-> j]}
action SendTimeoutNow (i : server) (j : server) {
  require ∃ ld : { ld // ld ∈ leaders }, ld.val.server = i
  require j ≠ i
  msgs := msgSet.insert (.timeoutnow i j) msgs
}

-- TimeoutNow(j) ==
--     /\ \E m \in msgs : m.type = "timeoutnow" /\ m.dst = j
--     /\ role' = [role EXCEPT ![j] = Candidate]
--     /\ transfer' = [transfer EXCEPT ![j] = TRUE]
action TimeoutNow (j : server) {
  require ∃ m : { m // m ∈ msgs },
    (match m.val with
      | .timeoutnow _ dst => decide (dst = j)
      | _ => false) = true
  role j := Candidate
  transfer j := true
}

-- Snapshots.

-- Machine(i, k) == snap[i] \o SubSeq(log[i], Len(snap[i]) + 1, k)
-- TakeSnapshot(i, k) ==
--     /\ Snapshots
--     /\ k > Len(snap[i])
--     /\ k <= lastApplied[i]
--     /\ lastApplied[i] <= commitIndex[i]
--     /\ snap' = [snap EXCEPT ![i] = Machine(i, k)]
-- Next: \E k \in 1..lastApplied[i] : TakeSnapshot(i, k)
action TakeSnapshot (i : server) {
  require Snapshots = true
  let s := snap i
  let k : { k // k ∈ List.range' 1 (lastApplied i) } :| k.val > s.length
  require lastApplied i ≤ commitIndex i
  snap i := s ++ SubSeq (log i) (s.length + 1) k.val
}

-- CompactLog(i, b) ==
--     /\ b > base[i]
--     /\ b <= Len(snap[i])
--     /\ base' = [base EXCEPT ![i] = b]
-- Next: \E b \in 1..Len(snap[i]) : CompactLog(i, b)
action CompactLog (i : server) {
  let b : { b // b ∈ List.range' 1 (snap i).length } :| b.val > base i
  base i := b.val
}

-- Installable(m) ==
--     m.type = "append" /\ m.prevLogIndex = 0 /\ Len(m.entries) >= 1 /\ m.commit >= Len(m.entries)
-- InstallSnapshot(j, m) ==
--     /\ Snapshots
--     /\ m \in msgs /\ Installable(m) /\ m.dst = j
--     /\ m.term = currentTerm[j]
--     /\ Len(m.entries) > Len(snap[j])
--     /\ Len(m.entries) > lastApplied[j]
--     /\ HasFirst(j, m, Len(m.entries))
--     /\ snap' = [snap EXCEPT ![j] = m.entries]
--     /\ lastApplied' = [lastApplied EXCEPT ![j] = Len(m.entries)]
-- Next: \E m \in msgs : m.type = "append" /\ InstallSnapshot(m.dst, m)
action InstallSnapshot {
  require Snapshots = true
  let m : { m // m ∈ msgs } :| m.val.isAppend = true
  let m := m.val
  let j := m.dst
  require m.prevLogIndex = 0 ∧ m.entries.length ≥ 1 ∧ m.commit ≥ m.entries.length
  require m.term = currentTerm j
  require m.entries.length > (snap j).length
  require m.entries.length > lastApplied j
  require HasFirst (log j) m.prevLogIndex m.entries m.entries.length
  snap j := m.entries
  lastApplied j := m.entries.length
}

-- Definitions that the invariants below use, besides those of the model.

-- The entry that bootstrap writes at index 1 of every log.
def Boot {value : Type} : Entry value := { term := 1, kind := .config, value := none }

-- Every entry of `l` after the first is, with all entries before it, in the leader log of its term.
def FromLed {value : Type} [DecidableEq value] (led : Nat → Option (List (Entry value)))
    (l : List (Entry value)) : Prop :=
  ∀ q ∈ List.range l.length, q = 0 ∨
    ((led (TermAt l (q + 1))).any fun L => decide (l.take (q + 1) = L.take (q + 1))) = true

instance {value : Type} [DecidableEq value] (led : Nat → Option (List (Entry value)))
    (l : List (Entry value)) : Decidable (FromLed led l) := by
  unfold FromLed; infer_instance

section LogDefs
set_option linter.unusedSectionVars false
variable {value : Type} [DecidableEq value]

-- Facts about logs for the proof of StateMachineSafety.

-- Terms in `l` never decrease along the log and are at most `t`.
def Sorted (l : List (Entry value)) (t : Nat) : Prop :=
  (∀ a b, 1 ≤ a → a ≤ b → b ≤ l.length → TermAt l a ≤ TermAt l b) ∧ ∀ a, TermAt l a ≤ t

-- The leader log of term w does not have the first c entries of `a`.
def Lacks {value : Type} (led : Nat → Option (List (Entry value))) (a : List (Entry value)) (c w : Nat) : Prop :=
  ∃ B, led w = some B ∧ ¬ a.take c <+: B

-- Some leader log of a term in (lo, hi] does not have them.
def LostIn {value : Type} (led : Nat → Option (List (Entry value))) (a : List (Entry value))
    (c lo hi : Nat) : Prop :=
  ∃ w, lo < w ∧ w ≤ hi ∧ Lacks led a c w

-- A log of li entries, the last of term lt, has them.
def Covers {value : Type} (led : Nat → Option (List (Entry value))) (a : List (Entry value))
    (c li lt : Nat) : Prop :=
  c ≤ li ∧ ∃ B, led lt = some B ∧ a.take c = B.take c

-- A vote request of term u for a log of li entries, the last of term lt, describes a log that
-- exists: a prefix of the leader log of term lt.
def ReqOk {value : Type} (led : Nat → Option (List (Entry value))) (u li lt : Nat) : Prop :=
  lt < u ∧ ((li = 1 ∧ lt = 1) ∨ ∃ B, led lt = some B ∧ li ≤ B.length ∧ TermAt B li = lt)
-- Leader logs only grow, each by entries of its own term.
def LedGrows (led led' : Nat → Option (List (Entry value))) : Prop :=
  ∀ w B, led w = some B → ∃ es, led' w = some (B ++ es) ∧ ∀ e ∈ es, e.term = w

end LogDefs

-- Acknowledgements, elections and commits, for the proof of StateMachineSafety.
section QuorumDefs
set_option linter.unusedSectionVars false
variable {server value MS VS LS CS : Type} [DecidableEq value] [Servers server] [TSet (Msg server value) MS]
  [TSet (Vote server) VS] [TSet (Elected server) LS] [TSet (Commit server value) CS]

-- Node n has acknowledged the first c entries of `A`, the leader log of term t, the c-th of
-- them an entry of term t: by a reply, or as the leader of t, for its own log.
def Acked (msgs : MS) (leaders : LS) (led : Nat → Option (List (Entry value))) (n : server) (t : Nat)
    (A : List (Entry value)) (c : Nat) : Prop :=
  led t = some A ∧ 2 ≤ c ∧ TermAt A c = t ∧
  ((∃ i x, Msg.ack (value := value) n i t x ∈ msgs ∧ c ≤ x) ∨
   (({ server := n, term := t } : Elected server) ∈ leaders ∧ c ≤ A.length))

-- Node n's vote for `cand` in term u is early: whatever n acknowledged in an earlier term,
-- the candidate's log has it, or a leader log strictly between does not.
def Early (msgs : MS) (leaders : LS) (led : Nat → Option (List (Entry value))) (n cand : server)
    (u : Nat) : Prop :=
  ∀ t A c, Acked msgs leaders led n t A c → t < u →
    ∀ li lt, Msg.vote (value := value) cand u li lt ∈ msgs →
      Covers led A c li lt ∨ LostIn led A c t (u - 1)

-- A quorum has acknowledged the first c entries to i, the leader of term t.
def QC (msgs : MS) (i : server) (t c : Nat) : Prop :=
  IsQuorum (fun j => @decide (j = i ∨ ∃ x, Msg.ack (value := value) j i t x ∈ msgs ∧ c ≤ x)
    (Classical.propDecidable _)) = true

-- A committed prefix that the leader of its term committed.
def Root (msgs : MS) (leaders : LS) (led : Nat → Option (List (Entry value)))
    (r : Commit server value) : Prop :=
  ({ server := r.server, term := r.term } : Elected server) ∈ leaders ∧
  (∃ A, led r.term = some A ∧ r.entries <+: A ∧ TermAt A r.entries.length = r.term) ∧
  QC msgs r.server r.term r.entries.length

end QuorumDefs

-- ElectionSafety == \A a, b \in leaders : a.term = b.term => a.server = b.server
invariant [ElectionSafety]
  ∀ a b : { x // x ∈ leaders }, a.val.term = b.val.term → a.val.server = b.val.server

-- OneVotePerTerm ==
--     \A a, b \in votes : a.voter = b.voter /\ a.term = b.term => a.cand = b.cand
invariant [OneVotePerTerm]
  ∀ a b : { x // x ∈ votes }, a.val.voter = b.val.voter ∧ a.val.term = b.val.term → a.val.cand = b.val.cand

-- Supporting invariants (not in HashicorpRaft.tla) for ElectionSafety and OneVotePerTerm.

-- A node's vote record is never ahead of its term.
invariant [VoteTermBound] ∀ i : server, voteTerm i ≤ currentTerm i

-- Every vote a node has given is at or before its vote record's term.
invariant [VotesBound] ∀ v : { v // v ∈ votes }, v.val.term ≤ voteTerm v.val.voter

-- A granted reply states a vote that exists.
invariant [GrantsAreVotes]
  ∀ m : { m // m ∈ msgs }, (match m.val with
    | .grant src dst term => vSet.contains { voter := src, term := term, cand := dst } votes
    | _ => true) = true

-- Every leader was voted for by a quorum in its term.
invariant [LeadersHaveQuorum]
  ∀ ld : { x // x ∈ leaders },
    IsQuorum (fun j => vSet.contains { voter := j, term := ld.val.term, cand := ld.val.server } votes) = true

-- Supporting invariants for LogMatching.

-- A node in the leader role was elected in its term.
invariant [LeaderIsElected]
  ∀ i : server, role i = Leader → lSet.contains { server := i, term := currentTerm i } leaders = true

-- No node was elected in a term it has not reached.
invariant [LeadersTermBound] ∀ ld : { x // x ∈ leaders }, ld.val.term ≤ currentTerm ld.val.server

-- While the node elected in a term is still in that term, the term's leader log is its log.
invariant [LedOwner]
  ∀ ld : { x // x ∈ leaders },
    ld.val.term = currentTerm ld.val.server → ledLog ld.val.term = some (log ld.val.server)

-- The terms that have a leader log are the terms that had a leader.
invariant [LeadersHaveLed] ∀ ld : { x // x ∈ leaders }, ledLog ld.val.term ≠ none
invariant [LedHasLeader]
  ∀ t : Nat, ledLog t ≠ none → ∃ ld : { x // x ∈ leaders }, ld.val.term = t

-- An append request is from the node elected in its term, to another node.
invariant [AppendFromLeader]
  ∀ m : { m // m ∈ msgs }, (match m.val with
    | .append src dst term _ _ _ _ =>
      decide (dst ≠ src) && lSet.contains { server := src, term := term } leaders
    | _ => true) = true

-- LeaderLogIsLed ==
--     \A i \in Server : role[i] = Leader =>
--         /\ currentTerm[i] \in DOMAIN ledLog
--         /\ log[i] = ledLog[currentTerm[i]]
invariant [LeaderLogIsLed]
  ∀ i : server, role i = Leader → ledLog (currentTerm i) = some (log i)

-- RequestsFromLed ==
--     \A m \in msgs : m.type = "append" =>
--         /\ m.term \in DOMAIN ledLog
--         /\ m.prevLogIndex + Len(m.entries) <= Len(ledLog[m.term])
--         /\ m.prevLogTerm = TermAt(ledLog[m.term], m.prevLogIndex)
--         /\ m.entries = SubSeq(ledLog[m.term], m.prevLogIndex + 1, m.prevLogIndex + Len(m.entries))
--         /\ CommittedIn(ledLog[m.term], m.commit, m.term)
invariant [RequestsFromLed]
  ∀ m : { m // m ∈ msgs }, (match m.val with
    | .append _ _ term prevLogIndex prevLogTerm entries commit =>
      (match ledLog term with
        | none => false
        | some l => decide (
            prevLogIndex + entries.length ≤ l.length ∧
            prevLogTerm = TermAt l prevLogIndex ∧
            entries = SubSeq l (prevLogIndex + 1) (prevLogIndex + entries.length) ∧
            (commit = 0 ∨ (commit ≤ l.length ∧ ∃ k : { k // k ∈ commits },
              k.val.term ≤ term ∧ commit ≤ k.val.entries.length ∧
              SubSeq k.val.entries 1 commit = SubSeq l 1 commit))))
    | _ => true) = true

-- Every log, and every leader log, starts with the bootstrap entry.
invariant [BootEntry] ∀ i : server, (log i).head? = some Boot
invariant [LedBoot] ∀ t : Nat, ((ledLog t).all fun L => decide (L.head? = some Boot)) = true

-- Every entry after the first, in a log or in a leader log, is with all entries before it in
-- the leader log of its term.
invariant [LogFromLed] ∀ i : server, FromLed ledLog (log i)
invariant [LedFromLed] ∀ t : Nat, ((ledLog t).all fun L => decide (FromLed ledLog L)) = true

-- LogMatching ==
--     \A a, b \in Server :
--         \A k \in 1..Min(Len(log[a]), Len(log[b])) :
--             log[a][k].term = log[b][k].term => SubSeq(log[a], 1, k) = SubSeq(log[b], 1, k)
invariant [LogMatching]
  ∀ a b : server, ∀ k ∈ List.range' 1 (min (log a).length (log b).length),
    TermAt (log a) k = TermAt (log b) k → SubSeq (log a) 1 k = SubSeq (log b) 1 k

-- PROOF-ONLY BEGIN
-- Supporting invariants for StateMachineSafety. They quantify over all indexes and terms,
-- which the model checker cannot evaluate; `../scripts/veil-count.sh` drops them.

invariant [TermsPositive] ∀ i : server, 1 ≤ currentTerm i

-- A log has no entry of a term its node has not reached.
invariant [LogTermsBound] ∀ i : server, ∀ k : Nat, TermAt (log i) k ≤ currentTerm i

-- Terms never decrease along a leader log and do not exceed its term.
invariant [LedSorted] ∀ t : Nat, ∀ L : List (Entry value), ledLog t = some L → Sorted L t

-- A vote request is of a term its sender has reached, and describes a log that exists.
invariant [ReqFacts]
  ∀ m : { m // m ∈ msgs }, ∀ c : server, ∀ u li lt : Nat, m.val = Msg.vote c u li lt →
    u ≤ currentTerm c ∧ ReqOk ledLog u li lt

-- A node asks once per term.
invariant [ReqUnique]
  ∀ m m' : { m // m ∈ msgs }, ∀ c : server, ∀ u li lt li' lt' : Nat,
    m.val = Msg.vote c u li lt → m'.val = Msg.vote c u li' lt' → li = li' ∧ lt = lt'

-- Every vote answers a request.
invariant [VoteHasReq]
  ∀ v : { v // v ∈ votes }, ∃ m : { m // m ∈ msgs }, ∃ li lt : Nat,
    m.val = Msg.vote v.val.cand v.val.term li lt

-- Until its term has a leader, a candidate's log is the one its request describes.
invariant [CandLog]
  ∀ m : { m // m ∈ msgs }, ∀ c : server, ∀ u li lt : Nat, m.val = Msg.vote c u li lt →
    currentTerm c = u → ledLog u = none → (log c).length = li ∧ TermAt (log c) li = lt

-- A leader log starts with the log its leader asked for votes with.
invariant [LedExtendsReq]
  ∀ ld : { x // x ∈ leaders }, ∀ m : { m // m ∈ msgs }, ∀ li lt : Nat,
    m.val = Msg.vote ld.val.server ld.val.term li lt →
    ∀ L : List (Entry value), ledLog ld.val.term = some L → li ≤ L.length ∧ TermAt L li = lt

-- An acknowledgement is to the leader of its term, from a node that has reached the term,
-- for entries the leader log has.
invariant [AckFacts]
  ∀ m : { m // m ∈ msgs }, ∀ j i : server, ∀ t x : Nat, m.val = Msg.ack j i t x →
    lSet.contains { server := i, term := t } leaders = true ∧ t ≤ currentTerm j ∧
    ∃ L : List (Entry value), ledLog t = some L ∧ x ≤ L.length

-- A node still holds what it acknowledged, unless a later leader log up to its term lacks it.
invariant [AckedHeld]
  ∀ n : server, ∀ t : Nat, ∀ A : List (Entry value), ∀ c : Nat, Acked msgs leaders ledLog n t A c →
    A.take c <+: log n ∨ LostIn ledLog A c t (currentTerm n)

-- A node that acknowledged entries and later voted: the candidate's log has them, unless a
-- leader log between the two terms (the vote's included) lacks them.
invariant [AckVote]
  ∀ n : server, ∀ t : Nat, ∀ A : List (Entry value), ∀ c : Nat, Acked msgs leaders ledLog n t A c →
    ∀ v : { v // v ∈ votes }, v.val.voter = n → t < v.val.term →
    ∀ li lt : Nat, msgSet.contains (Msg.vote v.val.cand v.val.term li lt) msgs = true →
      Covers ledLog A c li lt ∨ LostIn ledLog A c t v.val.term

-- Every leader was elected by a quorum of early votes.
invariant [EarlyQuorum]
  ∀ ld : { x // x ∈ leaders },
    IsQuorum (fun n => @decide (
      vSet.contains { voter := n, term := ld.val.term, cand := ld.val.server } votes = true ∧
      Early msgs leaders ledLog n ld.val.server ld.val.term) (Classical.propDecidable _)) = true

-- What a leader has confirmed of a node's log is a prefix of that leader's log.
invariant [ConfirmedIsLed]
  ∀ j : server, confirmedIndex j = 0 ∨ ∃ L : List (Entry value),
    ledLog (confirmedTerm j) = some L ∧ confirmedIndex j ≤ (log j).length ∧
    (log j).take (confirmedIndex j) = L.take (confirmedIndex j)

-- Every committed prefix is part of a `Root`: one committed by the leader of a term no later
-- than the one it is recorded under.
invariant [CommitRoot]
  ∀ k : { x // x ∈ commits }, k.val.entries ≠ [] ∧ ∃ r : { x // x ∈ commits },
    k.val.entries <+: r.val.entries ∧ Root msgs leaders ledLog r.val ∧ r.val.term ≤ k.val.term
-- PROOF-ONLY END

-- CommitSafety ==
--     \A a, b \in commits : IsPrefix(a.entries, b.entries) \/ IsPrefix(b.entries, a.entries)
invariant [CommitSafety]
  ∀ a b : { x // x ∈ commits },
    IsPrefix a.val.entries b.val.entries ∨ IsPrefix b.val.entries a.val.entries

-- Supporting invariants for the four properties below.

-- What a node has had confirmed is from a leader of a term it has reached.
invariant [ConfirmedTermBound] ∀ i : server, confirmedTerm i ≤ currentTerm i

-- A committed prefix is recorded under a term its server has reached.
invariant [CommitTermBound] ∀ c : { x // x ∈ commits }, c.val.term ≤ currentTerm c.val.server

-- CommittedEntriesPreserved == \A c \in commits : IsPrefix(c.entries, log[c.server])
invariant [CommittedEntriesPreserved]
  ∀ c : { x // x ∈ commits }, IsPrefix c.val.entries (log c.val.server)

-- A node's commit index is the length of a prefix it committed.
invariant [CommitIndexCommitted]
  ∀ i : server, commitIndex i = 0 ∨ ∃ k : { x // x ∈ commits },
    k.val.server = i ∧ k.val.entries.length = commitIndex i

-- Every entry handed to a state machine is, at its index, in a committed prefix.
invariant [AppliedCommitted]
  ∀ a : { x // x ∈ applied }, ∃ k : { x // x ∈ commits },
    1 ≤ a.val.index ∧ k.val.entries[a.val.index - 1]? = some a.val.entry

-- StateMachineSafety == \A a, b \in applied : a.index = b.index => a.entry = b.entry
invariant [StateMachineSafety]
  ∀ a b : { x // x ∈ applied }, a.val.index = b.val.index → a.val.entry = b.val.entry

-- LeaderCompleteness ==
--     \A i \in Server, c \in commits :
--         role[i] = Leader /\ c.term < currentTerm[i] => IsPrefix(c.entries, log[i])
invariant [LeaderCompleteness]
  ∀ i : server, ∀ c : { x // x ∈ commits },
    role i = Leader ∧ c.val.term < currentTerm i → IsPrefix c.val.entries (log i)

-- ConfirmedWithinLog == \A i \in Server : confirmed[i].index <= Len(log[i])
invariant [ConfirmedWithinLog]
  ∀ i : server, confirmedIndex i ≤ (log i).length

-- Pre-vote and leadership-transfer invariants; no property above depends on them. Declared
-- last so that earlier invariants keep their positions in the proofs.

-- PreVoteRequestsBounded ==
--     \A m \in msgs : m.type = "prevote" => m.term <= currentTerm[m.src] + 1
invariant [PreVoteRequestsBounded]
  ∀ m : { m // m ∈ msgs }, (match m.val with
    | .prevote src term _ _ => decide (term ≤ currentTerm src + 1)
    | _ => true) = true

-- PreGrantsAnswer ==
--     \A a \in msgs : a.type = "pregrant" =>
--         \E m \in msgs : m.type = "prevote" /\ m.src = a.dst /\ m.term = a.term
invariant [PreGrantsAnswer]
  ∀ a : { m // m ∈ msgs }, (match a.val with
    | .pregrant _ dst term => decide (∃ m : { m // m ∈ msgs },
        (match m.val with
          | .prevote src term' _ _ => decide (src = dst ∧ term' = term)
          | _ => false) = true)
    | _ => true) = true

-- TimeoutNowFromLeader ==
--     \A m \in msgs : m.type = "timeoutnow" => \E l \in leaders : l.server = m.src
invariant [TimeoutNowFromLeader]
  ∀ m : { m // m ∈ msgs }, (match m.val with
    | .timeoutnow src _ => decide (∃ ld : { ld // ld ∈ leaders }, ld.val.server = src)
    | _ => true) = true

-- TransferIsCandidate == \A i \in Server : transfer[i] => role[i] = Candidate
invariant [TransferIsCandidate]
  ∀ i : server, transfer i = true → role i = Candidate

-- The four invariants about snapshots, declared last for the same reason.

-- SnapshotWithinLog == \A i \in Server : IsPrefix(snap[i], log[i])
invariant [SnapshotWithinLog]
  ∀ i : server, IsPrefix (snap i) (log i)

-- BaseWithinSnapshot == \A i \in Server : base[i] <= Len(snap[i])
invariant [BaseWithinSnapshot]
  ∀ i : server, base i ≤ (snap i).length

-- SnapshotCommitted ==
--     \A i \in Server : snap[i] = <<>> \/ \E k \in commits : IsPrefix(snap[i], k.entries)
invariant [SnapshotCommitted]
  ∀ i : server, snap i = [] ∨ ∃ k : { x // x ∈ commits }, IsPrefix (snap i) k.val.entries

-- SnapshotApplied == \A i \in Server : Len(snap[i]) <= lastApplied[i]
invariant [SnapshotApplied]
  ∀ i : server, (snap i).length ≤ lastApplied i

-- Bounded (MCRaft.tla) ==
--     /\ \A i \in Server : currentTerm[i] <= MaxTerm /\ Len(log[i]) <= MaxLog
--     /\ \A m \in msgs : m.type = "append" => Len(m.entries) <= MaxBatch \/ Installable(m)
--     /\ Cardinality(msgs) <= MaxMsgs
state_constraint [Bounded]
  (∀ i, currentTerm i ≤ MaxTerm ∧ (log i).length ≤ MaxLog) ∧
  (∀ m : { m // m ∈ msgs }, (match m.val with
    | .append _ _ _ prevLogIndex _ entries commit =>
        decide (entries.length ≤ MaxBatch ∨ (prevLogIndex = 0 ∧ entries.length ≥ 1 ∧ commit ≥ entries.length))
    | _ => true) = true) ∧
  msgSet.count msgs ≤ MaxMsgs

-- With this many invariants, Veil needs more than the default budget to state each goal
-- over the fields an action changes.
set_option synthInstance.maxHeartbeats 400000
#gen_spec
set_option synthInstance.maxHeartbeats 20000
#gen_executable


-- State counts agree with TLC on `Spec` without symmetry: 6,488, 30,880 and 202,840 at
-- `../spec/MCCount{2,3,4}.cfg` (PreVote FALSE), 17,704 and 113,968 at `MCCountPV{4,5}.cfg`.
-- `../scripts/veil-count.sh` enables this check; it is commented out so that a build skips it.
-- #model_check compiled
--   { server := Fin 3, value := Fin 1, Role := Role_IndT, MsgSet := OrdList _,
--     VoteSet := OrdList _, LeaderSet := OrdList _, CommitSet := OrdList _, AppliedSet := OrdList _ }
--   { MaxTerm := 2, MaxLog := 2, MaxBatch := 1, MaxMsgs := 2, PreVote := false, Snapshots := false }

-- ---------------------------------------------------------------------------------------
-- Lemmas. Facts about sets, quorums and logs used by the proofs below.

-- Facts about TSets, without decidable equality on elements (goals give none for `server`).
namespace Lemmas

theorem ifPos {c : Prop} {h : Decidable c} {α : Sort _} {a b : α} (hc : c) : @ite α c h a b = a := by
  simp [hc]

theorem ifNeg {c : Prop} {h : Decidable c} {α : Sort _} {a b : α} (hc : ¬ c) : @ite α c h a b = b := by
  simp [hc]

theorem mem_iff {α κ : Type} [TSet α κ] (a : α) (s : κ) : a ∈ s ↔ TSet.contains a s = true := Iff.rfl

theorem contains_insert_iff {α κ : Type} [TSet α κ] (a b : α) (s : κ) :
    TSet.contains a (TSet.insert b s) = true ↔ a = b ∨ TSet.contains a s = true := by
  rcases Classical.em (a = b) with h | h
  · subst h; simp [TSet.contains_insert_self]
  · simp [TSet.contains_insert_other _ _ _ h, h]

theorem mem_insert {α κ : Type} [TSet α κ] (a b : α) (s : κ) :
    a ∈ TSet.insert b s ↔ a = b ∨ a ∈ s := contains_insert_iff a b s

theorem not_mem_empty {α κ : Type} [TSet α κ] (a : α) : ¬ a ∈ (TSet.empty : κ) := by
  simp [mem_iff, TSet.empty_contains]

theorem sub_empty {α κ : Type} [TSet α κ] (a : { x : α // x ∈ (TSet.empty : κ) }) : False :=
  not_mem_empty _ a.property

end Lemmas

-- Facts about quorums.

theorem filter_len_le_of_imp {α : Type} (l : List α) (p q : α → Bool) (h : ∀ a, p a = true → q a = true) :
    (l.filter p).length ≤ (l.filter q).length := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.filter_cons]
    cases hp : p x <;> cases hq : q x <;> simp <;> first | omega | (have := h x hp; simp_all)

theorem filter_len_add {α : Type} (l : List α) (p q : α → Bool) :
    (l.filter p).length + (l.filter q).length ≤ l.length + (l.filter (fun a => p a && q a)).length := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.filter_cons, List.length_cons]
    cases hp : p x <;> cases hq : q x <;> simp <;> omega

theorem filter_true_len {α : Type} (l : List α) : (l.filter (fun _ => true)).length = l.length := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp

theorem IsQuorum.iff {server : Type} [Servers server] (p : server → Bool) :
    IsQuorum p = true ↔
      ((Servers.all (server := server)).filter p).length * 2 > (Servers.all (server := server)).length := by
  unfold IsQuorum Card
  rw [filter_true_len]
  exact decide_eq_true_iff

theorem IsQuorum.mono {server : Type} [Servers server] (p q : server → Bool)
    (h : ∀ a, p a = true → q a = true) (hp : IsQuorum p = true) : IsQuorum q = true := by
  rw [IsQuorum.iff] at *
  have := filter_len_le_of_imp (Servers.all (server := server)) p q h
  omega

theorem IsQuorum.inter {server : Type} [Servers server] (p q : server → Bool)
    (hp : IsQuorum p = true) (hq : IsQuorum q = true) : ∃ a, p a = true ∧ q a = true := by
  rw [IsQuorum.iff] at *
  have h := filter_len_add (Servers.all (server := server)) p q
  have hpos : 0 < ((Servers.all (server := server)).filter (fun a => p a && q a)).length := by omega
  obtain ⟨a, ha⟩ := List.exists_mem_of_length_pos hpos
  simp only [List.mem_filter, Bool.and_eq_true] at ha
  exact ⟨a, ha.2⟩

-- Facts about logs.
section LogLemmas
set_option linter.unusedSectionVars false
variable {value : Type} [DecidableEq value]

theorem termAt_succ (l : List (Entry value)) (q : Nat) (h : q < l.length) :
    TermAt l (q + 1) = l[q].term := by
  simp [TermAt, List.getElem?_eq_getElem h]

theorem subSeq_one {α : Type} (l : List α) (k : Nat) : SubSeq l 1 k = l.take k := by
  simp [SubSeq]

theorem subSeq_length {α : Type} (l : List α) (p n : Nat) (h : p + n ≤ l.length) :
    (SubSeq l (p + 1) (p + n)).length = n := by
  simp [SubSeq]; omega

theorem termAt_take (l : List (Entry value)) (c k : Nat) (h : k ≤ c) :
    TermAt (l.take c) k = TermAt l k := by
  cases k with
  | zero => rfl
  | succ q => simp [TermAt, show q < c by omega]

theorem termAt_append_left (l es : List (Entry value)) (k : Nat) (h : k ≤ l.length) :
    TermAt (l ++ es) k = TermAt l k := by
  cases k with
  | zero => rfl
  | succ q => simp [TermAt, List.getElem?_append_left (show q < l.length by omega)]

theorem subSeq_append_left {α : Type} (l es : List α) (a b : Nat) (ha : 1 ≤ a) (h : b ≤ l.length) :
    SubSeq (l ++ es) a b = SubSeq l a b := by
  unfold SubSeq
  by_cases hab : a ≤ b
  · rw [List.drop_append_of_le_length (by omega), List.take_append_of_le_length (by simp; omega)]
  · simp [show b + 1 - a = 0 by omega]

theorem FromLed.iff (led : Nat → Option (List (Entry value))) (l : List (Entry value)) :
    FromLed led l ↔ ∀ q, 1 ≤ q → q < l.length →
      ∃ L, led (TermAt l (q + 1)) = some L ∧ l.take (q + 1) = L.take (q + 1) := by
  unfold FromLed
  constructor
  · intro h q h1 h2
    rcases h q (List.mem_range.2 h2) with h0 | h'
    · omega
    · cases hl : led (TermAt l (q + 1)) with
      | none => simp [hl] at h'
      | some L => exact ⟨L, rfl, by simpa [hl] using h'⟩
  · intro h q hq
    rcases Nat.eq_zero_or_pos q with h0 | h1
    · exact Or.inl h0
    · obtain ⟨L, hL, he⟩ := h q h1 (List.mem_range.1 hq)
      exact Or.inr (by simp [hL, he])

theorem FromLed.take (led : Nat → Option (List (Entry value))) (l : List (Entry value)) (c : Nat)
    (h : FromLed led l) : FromLed led (l.take c) := by
  rw [FromLed.iff] at *
  intro q h1 h2
  have hq : q < c ∧ q < l.length := by simp at h2; omega
  obtain ⟨L, hL, he⟩ := h q h1 hq.2
  refine ⟨L, by rw [termAt_take _ _ _ (by omega)]; exact hL, ?_⟩
  rw [List.take_take, Nat.min_eq_left (by omega)]; exact he

theorem FromLed.mono (led led' : Nat → Option (List (Entry value))) (l : List (Entry value))
    (hm : ∀ t L, led t = some L → ∃ L', led' t = some L' ∧ L <+: L')
    (h : FromLed led l) : FromLed led' l := by
  rw [FromLed.iff] at *
  intro q h1 h2
  obtain ⟨L, hL, he⟩ := h q h1 h2
  obtain ⟨L', hL', hp⟩ := hm _ _ hL
  refine ⟨L', hL', ?_⟩
  have hlen : q + 1 ≤ L.length := by
    have := congrArg List.length he
    simp at this; omega
  obtain ⟨s, rfl⟩ := hp
  rw [he, List.take_append_of_le_length hlen]

theorem FromLed.append_own (led : Nat → Option (List (Entry value))) (l es : List (Entry value))
    (t : Nat) (hled : led t = some (l ++ es)) (hes : ∀ e ∈ es, e.term = t)
    (h : FromLed led l) : FromLed led (l ++ es) := by
  rw [FromLed.iff] at *
  intro q h1 h2
  by_cases hq : q < l.length
  · obtain ⟨L, hL, he⟩ := h q h1 hq
    refine ⟨L, by rw [termAt_append_left _ _ _ (by omega)]; exact hL, ?_⟩
    rw [List.take_append_of_le_length (by omega)]; exact he
  · refine ⟨l ++ es, ?_, rfl⟩
    rw [termAt_succ _ _ h2]
    have : (l ++ es)[q] ∈ es := by
      rw [List.getElem_append_right (by omega)]
      exact List.getElem_mem _
    rw [hes _ this]; exact hled

-- Two logs that are both from leader logs, and both start with the bootstrap entry, match.
theorem FromLed.matching (led : Nat → Option (List (Entry value))) (a b : List (Entry value))
    (ha : FromLed led a) (hb : FromLed led b)
    (ha0 : a.head? = some Boot) (hb0 : b.head? = some Boot) :
    ∀ k ∈ List.range' 1 (min a.length b.length),
      TermAt a k = TermAt b k → SubSeq a 1 k = SubSeq b 1 k := by
  rw [FromLed.iff] at *
  intro k hk ht
  rw [subSeq_one, subSeq_one]
  have hk' : 1 ≤ k ∧ k ≤ a.length ∧ k ≤ b.length := by
    simp [List.mem_range'] at hk; omega
  obtain ⟨q, rfl⟩ : ∃ q, k = q + 1 := ⟨k - 1, by omega⟩
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · cases a with
    | nil => simp at ha0
    | cons x xs => cases b with
      | nil => simp at hb0
      | cons y ys => simp at ha0 hb0; simp [ha0, hb0]
  · obtain ⟨L, hL, he⟩ := ha q hq (by omega)
    obtain ⟨L', hL', he'⟩ := hb q hq (by omega)
    rw [ht, hL'] at hL
    cases hL
    rw [he, he']

theorem FromLed.prefix_of_term (led : Nat → Option (List (Entry value))) (l L : List (Entry value))
    (hl : FromLed led l) (hL : FromLed led L)
    (hl0 : l.head? = some Boot) (hL0 : L.head? = some Boot)
    (c : Nat) (hc1 : 1 ≤ c) (hcl : c ≤ l.length) (hcL : c ≤ L.length)
    (ht : TermAt l c = TermAt L c) : l.take c = L.take c := by
  have := FromLed.matching led l L hl hL hl0 hL0 c (List.mem_range'_1.2 ⟨hc1, by omega⟩) ht
  simpa [subSeq_one] using this

theorem hasFirst_get (l es : List (Entry value)) (p k q : Nat) (h : HasFirst l p es k = true)
    (hq : q < k) : ∃ a b, l[p + q]? = some a ∧ es[q]? = some b ∧ a.term = b.term := by
  unfold HasFirst at h
  rw [List.all_eq_true] at h
  have := h q (List.mem_range.2 hq)
  split at this
  · next a b ha hb => exact ⟨a, b, ha, hb, by simpa using this⟩
  · simp at this

-- What a node acknowledges is within its log.
theorem ack_within (l es : List (Entry value)) (p pt : Nat) (hp : PrevOk l p pt = true)
    (h : HasFirst l p es es.length = true) : p + es.length ≤ l.length := by
  rcases Nat.eq_zero_or_pos es.length with h0 | hpos
  · rw [h0]
    cases p with
    | zero => exact Nat.zero_le _
    | succ q =>
      unfold PrevOk at hp
      cases hq : l[q]? with
      | none => simp [hq] at hp
      | some e =>
        obtain ⟨hlt, _⟩ := List.getElem?_eq_some_iff.1 hq
        omega
  · obtain ⟨a, b, ha, _, _⟩ := hasFirst_get l es p es.length (es.length - 1) h (by omega)
    obtain ⟨hlt, _⟩ := List.getElem?_eq_some_iff.1 ha
    omega

-- StoreEntries: a follower whose log passes the checks of a request ends with the first
-- p + n entries of the leader log the request was taken from.
theorem store_eq (led : Nat → Option (List (Entry value))) (l L : List (Entry value)) (p k : Nat)
    (es : List (Entry value))
    (hl : FromLed led l) (hL : FromLed led L)
    (hl0 : l.head? = some Boot) (hL0 : L.head? = some Boot)
    (hpn : p + es.length ≤ L.length)
    (hes : es = SubSeq L (p + 1) (p + es.length))
    (hprev : PrevOk l p (TermAt L p) = true)
    (hk : k ∈ List.range' 1 es.length)
    (hfirst : HasFirst l p es (k - 1) = true)
    (hlen : p + k = l.length + 1) :
    l ++ SubSeq es k es.length = L.take (p + es.length) := by
  have hk' : 1 ≤ k ∧ k ≤ es.length := by simp [List.mem_range'] at hk; omega
  have hlpos : 1 ≤ l.length := by cases l <;> simp at hl0 ⊢
  -- the last entry of l has the term of the entry of L at the same index
  have hterm : TermAt l l.length = TermAt L l.length := by
    rcases Nat.lt_or_ge 1 k with h2 | h1
    · obtain ⟨a, b, ha, hb, hab⟩ := hasFirst_get l es p (k - 1) (k - 2) hfirst (by omega)
      have hidx : p + (k - 2) = l.length - 1 := by omega
      have hb' : L[l.length - 1]? = some b := by
        rw [hes] at hb
        simp only [SubSeq, List.getElem?_take, List.getElem?_drop] at hb
        split at hb
        · rw [show p + 1 - 1 + (k - 2) = l.length - 1 by omega] at hb; exact hb
        · simp at hb
      rw [hidx] at ha
      obtain ⟨c, hc⟩ : ∃ c, l.length = c + 1 := ⟨l.length - 1, by omega⟩
      simp only [hc, Nat.add_sub_cancel] at ha hb' ⊢
      simp [TermAt, ha, hb', hab]
    · have hk1 : k = 1 := by omega
      subst hk1
      have hp : p = l.length := by omega
      subst hp
      obtain ⟨c, hc⟩ : ∃ c, l.length = c + 1 := ⟨l.length - 1, by omega⟩
      rw [hc] at hprev ⊢
      simp only [PrevOk] at hprev
      split at hprev
      · next e he =>
        have : e.term = TermAt L (c + 1) := by simpa using hprev
        rw [← this]; simp [TermAt, he]
      · simp at hprev
  have hpre : l = L.take l.length := by
    have := FromLed.prefix_of_term led l L hl hL hl0 hL0 l.length hlpos (Nat.le_refl _) (by omega) hterm
    simpa using this
  have hdrop : SubSeq es k es.length = (L.drop l.length).take (p + es.length - l.length) := by
    rw [hes]
    simp only [SubSeq, List.length_take, List.length_drop, List.drop_take, List.drop_drop, List.take_take]
    rw [show p + 1 - 1 + (k - 1) = l.length by omega]
    congr 1
    omega
  rw [hdrop]
  conv => lhs; lhs; rw [hpre]
  rw [← List.take_add]
  congr 1; omega

-- DeleteSuffix: a conflict is never at the first entry, so truncation keeps the bootstrap entry.
theorem delete_keeps_boot (l L : List (Entry value)) (p k : Nat) (es : List (Entry value))
    (hl0 : l.head? = some Boot) (hL0 : L.head? = some Boot)
    (hes : es = SubSeq L (p + 1) (p + es.length))
    (hk : k ∈ List.range' 1 es.length)
    (hne : TermAt l (p + k) ≠ TermAt es k) :
    (SubSeq l 1 (p + k - 1)).head? = some Boot := by
  have hk' : 1 ≤ k ∧ k ≤ es.length := by simp [List.mem_range'] at hk; omega
  rw [subSeq_one]
  rcases Nat.lt_or_ge 1 (p + k) with h | h
  · cases l with
    | nil => simp at hl0
    | cons x xs =>
      obtain ⟨c, hc⟩ : ∃ c, p + k - 1 = c + 1 := ⟨p + k - 2, by omega⟩
      rw [hc]; simpa using hl0
  · exfalso
    have hp : p = 0 := by omega
    have hk1 : k = 1 := by omega
    subst hp hk1
    apply hne
    cases l with
    | nil => simp at hl0
    | cons x xs => cases L with
      | nil => simp at hL0
      | cons y ys =>
        simp at hl0 hL0
        subst hl0 hL0
        rw [hes]
        obtain ⟨c, hc⟩ : ∃ c, es.length = c + 1 := ⟨es.length - 1, by omega⟩
        simp [TermAt, SubSeq, hc]

theorem optAll_iff {α : Type} (o : Option α) (P : α → Prop) {d : DecidablePred P} :
    (o.all fun L => @decide (P L) (d L)) = true ↔ ∀ L, o = some L → P L := by
  cases o <;> simp

theorem termAt_le_of_gt (l : List (Entry value)) (k : Nat) (h : l.length < k) : TermAt l k = 0 := by
  cases k with
  | zero => rfl
  | succ q => simp [TermAt, List.getElem?_eq_none (show l.length ≤ q by omega)]

theorem termAt_append_right (l es : List (Entry value)) (k : Nat) (h1 : l.length < k)
    (h2 : k ≤ l.length + es.length) : ∃ e ∈ es, TermAt (l ++ es) k = e.term := by
  obtain ⟨q, rfl⟩ : ∃ q, k = q + 1 := ⟨k - 1, by omega⟩
  have hq : q < (l ++ es).length := by simp; omega
  refine ⟨(l ++ es)[q], ?_, termAt_succ _ _ hq⟩
  rw [List.getElem_append_right (by omega)]
  exact List.getElem_mem _

theorem termAt_of_prefix (a l : List (Entry value)) (k : Nat) (h : a <+: l) (hk : k ≤ a.length) :
    TermAt l k = TermAt a k := by
  obtain ⟨s, rfl⟩ := h
  exact termAt_append_left _ _ _ hk

theorem take_prefix_iff (a l : List (Entry value)) (c : Nat) (hc : c ≤ a.length) :
    a.take c <+: l ↔ c ≤ l.length ∧ a.take c = l.take c := by
  constructor
  · intro h
    have hl := h.length_le
    simp at hl
    refine ⟨by omega, ?_⟩
    obtain ⟨s, hs⟩ := h
    rw [← hs, List.take_append_of_le_length (by simp; omega)]
    simp [List.take_take]
  · rintro ⟨_, h⟩
    rw [h]; exact List.take_prefix _ _

-- Sortedness is kept by appending entries of a term at least as high as every term so far.
theorem Sorted.append (l es : List (Entry value)) (t : Nat) (h : Sorted l t)
    (hes : ∀ e ∈ es, e.term = t) : Sorted (l ++ es) t := by
  obtain ⟨h1, h2⟩ := h
  have hb : ∀ a, TermAt (l ++ es) a ≤ t := by
    intro a
    rcases Nat.lt_or_ge l.length a with ha | ha
    · rcases Nat.lt_or_ge (l.length + es.length) a with hb | hb
      · rw [termAt_le_of_gt _ _ (by simp; omega)]; omega
      · obtain ⟨e, he, heq⟩ := termAt_append_right l es a ha hb
        rw [heq, hes e he]; omega
    · rw [termAt_append_left _ _ _ ha]; exact h2 a
  refine ⟨?_, hb⟩
  intro a b ha hab hbl
  simp at hbl
  rcases Nat.lt_or_ge l.length b with hb' | hb'
  · obtain ⟨e, he, heq⟩ := termAt_append_right l es b hb' hbl
    rw [heq, hes e he]; exact hb a
  · rw [termAt_append_left _ _ _ hb', termAt_append_left _ _ _ (by omega)]
    exact h1 a b ha hab hb'

theorem Sorted.take (l : List (Entry value)) (t c : Nat) (h : Sorted l t) : Sorted (l.take c) t := by
  obtain ⟨h1, h2⟩ := h
  constructor
  · intro a b ha hab hb
    simp at hb
    rw [termAt_take _ _ _ (by omega), termAt_take _ _ _ (by omega)]
    exact h1 a b ha hab (by omega)
  · intro a
    rcases Nat.lt_or_ge c a with hc | hc
    · rw [termAt_le_of_gt _ _ (by simp; omega)]; omega
    · rw [termAt_take _ _ _ hc]; exact h2 a

-- A leader log that lacks the first c entries of `a` keeps lacking them when it grows by
-- entries of its own, higher, term.
theorem lacks_append (a l es : List (Entry value)) (c w : Nat) (hc : c ≤ a.length)
    (ha : ∀ x, TermAt a x < w) (hes : ∀ e ∈ es, e.term = w)
    (h : ¬ a.take c <+: l) : ¬ a.take c <+: l ++ es := by
  intro hp
  rw [take_prefix_iff _ _ _ hc] at hp h
  obtain ⟨hlen, heq⟩ := hp
  simp at hlen
  rcases Nat.lt_or_ge l.length c with hlc | hlc
  · -- position l.length + 1 of `a` has a term below w, of l ++ es the term w
    obtain ⟨e, he, hterm⟩ := termAt_append_right l es (l.length + 1) (by omega) (by omega)
    have h1 : TermAt (a.take c) (l.length + 1) = TermAt ((l ++ es).take c) (l.length + 1) := by rw [heq]
    rw [termAt_take _ _ _ (by omega), termAt_take _ _ _ (by omega), hterm, hes e he] at h1
    have := ha (l.length + 1)
    omega
  · apply h
    refine ⟨hlc, ?_⟩
    rw [heq, List.take_append_of_le_length hlc]

-- At a vote: a voter holding the first c entries of the leader log of term t (the c-th of
-- term t) compares with the candidate's (li, lt). The candidate's log holds them too, or the
-- leader log of its last term, above t, lacks them.
theorem vote_cover (led : Nat → Option (List (Entry value))) (ln A : List (Entry value))
    (t c li lt : Nat)
    (hA : led t = some A) (hc2 : 2 ≤ c) (hcA : c ≤ A.length) (hct : TermAt A c = t)
    (hheld : A.take c <+: ln)
    (hln : FromLed led ln) (hboot : ln.head? = some Boot)
    (hsorted : ∀ w B, led w = some B → Sorted B w)
    (hreq : li = 1 ∧ lt = 1 ∨ ∃ B, led lt = some B ∧ li ≤ B.length ∧ TermAt B li = lt)
    (hup : lt > TermAt ln ln.length ∨ (lt = TermAt ln ln.length ∧ li ≥ ln.length)) :
    (c ≤ li ∧ ∃ B, led lt = some B ∧ A.take c = B.take c) ∨
    (t < lt ∧ ∃ B, led lt = some B ∧ ¬ A.take c <+: B) := by
  rw [take_prefix_iff _ _ _ hcA] at hheld
  obtain ⟨hcl, heq⟩ := hheld
  -- the voter's log is a prefix of the leader log of its last term, s
  rw [FromLed.iff] at hln
  obtain ⟨S, hS, hSeq⟩ := hln (ln.length - 1) (by omega) (by omega)
  rw [show ln.length - 1 + 1 = ln.length by omega] at hS hSeq
  have hlS : ln.length ≤ S.length := by
    have := congrArg List.length hSeq; simp at this; omega
  have hlnS : ln = S.take ln.length := by simpa using hSeq
  have hterm : ∀ k, k ≤ ln.length → TermAt ln k = TermAt S k := by
    intro k hk; rw [hlnS, termAt_take _ _ _ hk]
  have hAS : A.take c = S.take c := by
    rw [heq, hlnS, List.take_take, Nat.min_eq_left hcl]
  have hSc : TermAt S c = t := by
    rw [← hterm c hcl, ← hct]
    have : TermAt (ln.take c) c = TermAt (A.take c) c := by rw [heq]
    rw [termAt_take _ _ _ (Nat.le_refl c), termAt_take _ _ _ (Nat.le_refl c)] at this
    exact this
  have hSs := hsorted _ S hS
  have hts : t ≤ TermAt ln ln.length := by
    rw [hterm _ (Nat.le_refl _), ← hSc]
    exact hSs.1 c ln.length (by omega) hcl hlS
  rcases hup with hgt | ⟨heqt, hli⟩
  · -- the candidate's last term is above the voter's
    rcases hreq with ⟨_, h1⟩ | ⟨B, hB, hliB, hBt⟩
    · -- a log of one entry has last term 1, which is not above the voter's
      have hb1 : TermAt ln 1 = 1 := by
        cases ln with
        | nil => simp at hboot
        | cons x xs => simp at hboot; simp [TermAt, hboot, Boot]
      have := hSs.1 1 ln.length (Nat.le_refl 1) (by omega) hlS
      rw [← hterm _ (Nat.le_refl _), ← hterm 1 (by omega), hb1] at this
      omega
    · by_cases hpre : A.take c <+: B
      · left
        rw [take_prefix_iff _ _ _ hcA] at hpre
        refine ⟨?_, B, hB, hpre.2⟩
        -- entry li of B has term lt > t, entries up to c have terms at most t
        have hBs := hsorted _ B hB
        have hBc : TermAt B c = t := by
          have : TermAt (A.take c) c = TermAt (B.take c) c := by rw [hpre.2]
          rw [termAt_take _ _ _ (Nat.le_refl c), termAt_take _ _ _ (Nat.le_refl c)] at this
          rw [← this]; exact hct
        rcases Nat.lt_or_ge li c with hlt | hge
        · rcases Nat.eq_zero_or_pos li with h0 | hpos
          · subst h0; simp [TermAt] at hBt; omega
          · have := hBs.1 li c hpos (by omega) hpre.1
            omega
        · exact hge
      · right
        exact ⟨by omega, B, hB, hpre⟩
  · -- same last term: the candidate's log is at least as long, on the same leader log
    left
    refine ⟨by omega, ?_⟩
    rcases hreq with ⟨h1, _⟩ | ⟨B, hB, _, _⟩
    · omega
    · rw [heqt, hS] at hB
      cases hB
      exact ⟨S, by rw [heqt]; exact hS, hAS⟩

theorem termAt_subSeq (L : List (Entry value)) (p n k : Nat) (hk1 : 1 ≤ k) (hk : k ≤ n)
    (h : p + n ≤ L.length) : TermAt (SubSeq L (p + 1) (p + n)) k = TermAt L (p + k) := by
  obtain ⟨q, rfl⟩ : ∃ q, k = q + 1 := ⟨k - 1, by omega⟩
  simp only [TermAt, SubSeq, List.getElem?_take, List.getElem?_drop]
  rw [show p + 1 - 1 + q = p + q by omega]
  simp [show q < n by omega, show p + (q + 1) = p + q + 1 by omega]

-- A log that passes a request's checks up to its k-th entry agrees with the leader log the
-- request was taken from on the first p + k entries.
theorem checked_prefix (led : Nat → Option (List (Entry value))) (l L : List (Entry value)) (p k : Nat)
    (es : List (Entry value))
    (hl : FromLed led l) (hL : FromLed led L)
    (hl0 : l.head? = some Boot) (hL0 : L.head? = some Boot)
    (hpn : p + es.length ≤ L.length)
    (hes : es = SubSeq L (p + 1) (p + es.length))
    (hprev : PrevOk l p (TermAt L p) = true)
    (hk : k ≤ es.length)
    (hfirst : HasFirst l p es k = true) :
    p + k ≤ l.length ∧ l.take (p + k) = L.take (p + k) := by
  rcases Nat.eq_zero_or_pos (p + k) with h0 | hpos
  · simp [h0]
  · -- the entry of l at p + k has the term of L's
    have hboth : p + k ≤ l.length ∧ TermAt l (p + k) = TermAt L (p + k) := by
      rcases Nat.eq_zero_or_pos k with hk0 | hkpos
      · subst hk0
        obtain ⟨c, hc⟩ : ∃ c, p = c + 1 := ⟨p - 1, by omega⟩
        subst hc
        simp only [PrevOk] at hprev
        split at hprev
        · next e he =>
          have hlt : c < l.length := by
            rcases Nat.lt_or_ge c l.length with h | h
            · exact h
            · rw [List.getElem?_eq_none h] at he; cases he
          have : e.term = TermAt L (c + 1) := by simpa using hprev
          exact ⟨by omega, by rw [← this]; simp [TermAt, he]⟩
        · simp at hprev
      · obtain ⟨a, b, ha, hb, hab⟩ := hasFirst_get l es p k (k - 1) hfirst (by omega)
        have hlt : p + (k - 1) < l.length := by
          rcases Nat.lt_or_ge (p + (k - 1)) l.length with h | h
          · exact h
          · rw [List.getElem?_eq_none h] at ha; cases ha
        refine ⟨by omega, ?_⟩
        have h1 : TermAt l (p + k) = a.term := by
          rw [show p + k = p + (k - 1) + 1 by omega]; simp [TermAt, ha]
        have h2 : TermAt es k = b.term := by
          rw [show k = (k - 1) + 1 by omega]; simp [TermAt, hb]
        rw [h1, hab, ← h2, hes, termAt_subSeq L p es.length k hkpos hk hpn]
    refine ⟨hboth.1, ?_⟩
    exact FromLed.prefix_of_term led l L hl hL hl0 hL0 (p + k) hpos hboth.1 (by omega) hboth.2

-- DeleteSuffix: a prefix of another leader log that the node held is still held after the
-- truncation, or the leader log the request was taken from does not have it.
theorem delete_held (a l B : List (Entry value)) (c p k : Nat) (es : List (Entry value))
    (hc : c ≤ a.length) (hheld : a.take c <+: l)
    (hpn : p + es.length ≤ B.length) (hes : es = SubSeq B (p + 1) (p + es.length))
    (hk1 : 1 ≤ k) (hk : k ≤ es.length) (hkl : p + k ≤ l.length)
    (hne : TermAt l (p + k) ≠ TermAt es k) :
    a.take c <+: SubSeq l 1 (p + k - 1) ∨ ¬ a.take c <+: B := by
  rw [subSeq_one]
  rcases Nat.lt_or_ge c (p + k) with hlt | hge
  · left
    rw [take_prefix_iff _ _ _ hc] at hheld ⊢
    refine ⟨by simp; omega, ?_⟩
    rw [List.take_take, Nat.min_eq_left (by omega)]; exact hheld.2
  · right
    intro hB
    apply hne
    rw [take_prefix_iff _ _ _ hc] at hheld hB
    have h1 : TermAt (l.take c) (p + k) = TermAt (B.take c) (p + k) := by rw [← hheld.2, hB.2]
    rw [termAt_take _ _ _ hge, termAt_take _ _ _ hge] at h1
    rw [h1, hes, termAt_subSeq B p es.length k hk1 hk hpn]

-- A log from leader logs whose terms are bounded is sorted, given that leader logs are.
theorem sorted_of_fromLed (led : Nat → Option (List (Entry value))) (l : List (Entry value)) (u : Nat)
    (hl : FromLed led l) (hsorted : ∀ w B, led w = some B → Sorted B w)
    (hb : ∀ k, TermAt l k ≤ u) : Sorted l u := by
  refine ⟨?_, hb⟩
  intro a b ha hab hbl
  rcases Nat.lt_or_ge 1 b with h2 | h1
  · rw [FromLed.iff] at hl
    obtain ⟨S, hS, heq⟩ := hl (b - 1) (by omega) (by omega)
    rw [show b - 1 + 1 = b by omega] at hS heq
    have hbS : b ≤ S.length := by have := congrArg List.length heq; simp at this; omega
    have e1 : TermAt l a = TermAt S a := by
      have : TermAt (l.take b) a = TermAt (S.take b) a := by rw [heq]
      rwa [termAt_take _ _ _ hab, termAt_take _ _ _ hab] at this
    have e2 : TermAt l b = TermAt S b := by
      have : TermAt (l.take b) b = TermAt (S.take b) b := by rw [heq]
      rwa [termAt_take _ _ _ (Nat.le_refl b), termAt_take _ _ _ (Nat.le_refl b)] at this
    rw [e1, e2]; exact (hsorted _ S hS).1 a b ha hab hbS
  · have : a = b := by omega
    subst this; exact Nat.le_refl _

theorem LedGrows.refl (led : Nat → Option (List (Entry value))) : LedGrows led led :=
  fun _ B h => ⟨[], by simpa using h, by simp⟩

theorem LostIn.mono_hi (led : Nat → Option (List (Entry value))) (a : List (Entry value))
    (c lo hi hi' : Nat) (h : LostIn led a c lo hi) (hh : hi ≤ hi') : LostIn led a c lo hi' := by
  obtain ⟨w, h1, h2, h3⟩ := h
  exact ⟨w, h1, by omega, h3⟩

theorem LostIn.grows (led led' : Nat → Option (List (Entry value))) (a : List (Entry value))
    (c lo hi : Nat) (hg : LedGrows led led') (hc : c ≤ a.length) (ha : ∀ x, TermAt a x ≤ lo)
    (h : LostIn led a c lo hi) : LostIn led' a c lo hi := by
  obtain ⟨w, h1, h2, B, hB, hl⟩ := h
  obtain ⟨es, hB', hes⟩ := hg w B hB
  exact ⟨w, h1, h2, B ++ es, hB', lacks_append a B es c w hc (fun x => by have := ha x; omega) hes hl⟩

theorem Covers.grows (led led' : Nat → Option (List (Entry value))) (a : List (Entry value))
    (c li lt : Nat) (hg : LedGrows led led') (hc : c ≤ a.length)
    (h : Covers led a c li lt) : Covers led' a c li lt := by
  obtain ⟨h1, B, hB, heq⟩ := h
  obtain ⟨es, hB', _⟩ := hg lt B hB
  refine ⟨h1, B ++ es, hB', ?_⟩
  have hlen : c ≤ B.length := by
    have := congrArg List.length heq; simp at this; omega
  rw [List.take_append_of_le_length hlen]; exact heq

-- Both depend on `a` only through its first c entries.
theorem LostIn.congr (led : Nat → Option (List (Entry value))) (a a' : List (Entry value))
    (c lo hi : Nat) (heq : a.take c = a'.take c) (h : LostIn led a c lo hi) : LostIn led a' c lo hi := by
  unfold LostIn Lacks at *; rw [← heq]; exact h

theorem Covers.congr (led : Nat → Option (List (Entry value))) (a a' : List (Entry value))
    (c li lt : Nat) (heq : a.take c = a'.take c) (h : Covers led a c li lt) : Covers led a' c li lt := by
  unfold Covers at *; rw [← heq]; exact h

theorem ReqOk.grows (led led' : Nat → Option (List (Entry value))) (u li lt : Nat)
    (hg : LedGrows led led') (h : ReqOk led u li lt) : ReqOk led' u li lt := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨h1, ?_⟩
  rcases h2 with h2 | ⟨B, hB, hli, ht⟩
  · exact Or.inl h2
  · obtain ⟨es, hB', _⟩ := hg lt B hB
    exact Or.inr ⟨B ++ es, hB', by simp; omega, by rw [termAt_append_left _ _ _ hli]; exact ht⟩

theorem prefix_cmp_of_prefix {α : Type} (a b c : List α) (ha : a <+: c) (hb : b <+: c) :
    a <+: b ∨ b <+: a := by
  rcases Nat.le_total a.length b.length with h | h
  · exact Or.inl (List.prefix_of_prefix_length_le ha hb h)
  · exact Or.inr (List.prefix_of_prefix_length_le hb ha h)

-- Prefixes of two comparable lists are comparable.
theorem prefix_cmp_of_roots {α : Type} (k1 k2 r1 r2 : List α) (h1 : k1 <+: r1) (h2 : k2 <+: r2)
    (h : r1 <+: r2 ∨ r2 <+: r1) : k1 <+: k2 ∨ k2 <+: k1 := by
  rcases h with h | h
  · exact prefix_cmp_of_prefix k1 k2 r2 (h1.trans h) h2
  · exact prefix_cmp_of_prefix k1 k2 r1 h1 (h2.trans h)

-- An index within a prefix reads the same entry in the whole list.
theorem prefix_getD {α : Type} (a l : List α) (d : α) (q : Nat) (h : a <+: l) (hq : q < a.length) :
    a[q]? = some (l[q]?.getD d) := by
  obtain ⟨t, rfl⟩ := h
  rw [List.getElem?_append_left hq, List.getElem?_eq_getElem hq]; rfl

-- Two comparable lists have the same element at an index both have.
theorem prefix_get_eq {α : Type} (a b : List α) (q : Nat) (x y : α) (h : a <+: b ∨ b <+: a)
    (ha : a[q]? = some x) (hb : b[q]? = some y) : x = y := by
  rcases h with ⟨t, rfl⟩ | ⟨t, rfl⟩
  · have hq := (List.getElem?_eq_some_iff.1 ha).1
    rw [List.getElem?_append_left hq, ha] at hb; exact Option.some.inj hb
  · have hq := (List.getElem?_eq_some_iff.1 hb).1
    rw [List.getElem?_append_left hq, hb] at ha; exact (Option.some.inj ha).symm

theorem isPrefix_iff {α : Type} [DecidableEq α] (a b : List α) : IsPrefix a b = true ↔ a <+: b := by
  unfold IsPrefix
  rw [decide_eq_true_iff, subSeq_one]
  constructor
  · rintro ⟨_, h⟩; rw [h]; exact List.take_prefix _ _
  · intro h
    refine ⟨h.length_le, ?_⟩
    obtain ⟨t, rfl⟩ := h
    simp

-- The two ways a step changes leader logs.
theorem ledGrows_set (led : Nat → Option (List (Entry value))) (cur : Nat) {d : ∀ x : Nat, Decidable (cur = x)} (l : List (Entry value))
    (hsame : ∀ L, led cur = some L → L = l) :
    LedGrows led (fun x => @ite _ (cur = x) (d _) (some l) (led x)) := by
  intro w B hB
  by_cases hc : cur = w
  · subst hc
    refine ⟨[], ?_, by simp⟩
    show (@ite _ (cur = cur) (d _) (some l) (led cur)) = some (B ++ [])
    rw [RaftVeil.Lemmas.ifPos rfl, hsame B hB]; simp
  · refine ⟨[], ?_, by simp⟩
    show (@ite _ (cur = w) (d _) (some l) (led w)) = some (B ++ [])
    rw [RaftVeil.Lemmas.ifNeg hc, hB]; simp

theorem ledGrows_append (led : Nat → Option (List (Entry value))) (cur : Nat) {d : ∀ x : Nat, Decidable (cur = x)} (l : List (Entry value))
    (e : Entry value) (hl : led cur = some l) (he : e.term = cur) :
    LedGrows led (fun x => @ite _ (cur = x) (d _) (some (l ++ [e])) (led x)) := by
  intro w B hB
  by_cases hc : cur = w
  · subst hc
    rw [hl] at hB; cases hB
    refine ⟨[e], ?_, by simp [he]⟩
    show (@ite _ (cur = cur) (d _) (some (l ++ [e])) (led cur)) = some (l ++ [e])
    rw [RaftVeil.Lemmas.ifPos rfl]
  · refine ⟨[], ?_, by simp⟩
    show (@ite _ (cur = w) (d _) (some (l ++ [e])) (led w)) = some (B ++ [])
    rw [RaftVeil.Lemmas.ifNeg hc, hB]; simp

-- A node's log is one that a vote request can describe.
theorem reqOk_of_log (led : Nat → Option (List (Entry value))) (l : List (Entry value)) (u : Nat)
    (hl : FromLed led l) (h0 : l.head? = some Boot) (hb : TermAt l l.length < u) :
    ReqOk led u l.length (TermAt l l.length) := by
  refine ⟨hb, ?_⟩
  rcases Nat.lt_or_ge 1 l.length with h2 | h1
  · right
    rw [FromLed.iff] at hl
    obtain ⟨L, hL, heq⟩ := hl (l.length - 1) (by omega) (by omega)
    rw [show l.length - 1 + 1 = l.length by omega] at hL heq
    have hlen : l.length ≤ L.length := by have := congrArg List.length heq; simp at this; omega
    refine ⟨L, hL, hlen, ?_⟩
    have : TermAt (l.take l.length) l.length = TermAt (L.take l.length) l.length := by rw [heq]
    rw [termAt_take _ _ _ (Nat.le_refl _), termAt_take _ _ _ (Nat.le_refl _)] at this
    exact this.symm
  · left
    cases l with
    | nil => simp at h0
    | cons x xs =>
      simp at h0 h1
      subst h0
      have : xs = [] := by cases xs <;> simp_all
      subst this
      simp [TermAt, Boot]

-- The step of voting: what the voter holds or has lost, the candidate covers or it is lost.
theorem vote_step (led : Nat → Option (List (Entry value))) (ln A : List (Entry value))
    (t c li lt u : Nat)
    (hA : led t = some A) (hc2 : 2 ≤ c) (hcA : c ≤ A.length) (hct : TermAt A c = t)
    (hheld : A.take c <+: ln ∨ LostIn led A c t u)
    (hln : FromLed led ln) (hboot : ln.head? = some Boot)
    (hsorted : ∀ w B, led w = some B → Sorted B w)
    (hreq : ReqOk led u li lt)
    (hup : lt > TermAt ln ln.length ∨ (lt = TermAt ln ln.length ∧ li ≥ ln.length)) :
    Covers led A c li lt ∨ LostIn led A c t u := by
  rcases hheld with hheld | hlost
  · rcases vote_cover led ln A t c li lt hA hc2 hcA hct hheld hln hboot hsorted hreq.2 hup with h | ⟨h1, B, hB, hl⟩
    · exact Or.inl h
    · exact Or.inr ⟨lt, h1, Nat.le_of_lt hreq.1, B, hB, hl⟩
  · exact Or.inr hlost

-- A prefix of a log that ends in an entry of term t is a prefix of the leader log of t.
theorem take_prefix_led (led : Nat → Option (List (Entry value))) (l A : List (Entry value)) (t c : Nat)
    (hl : FromLed led l) (hl0 : l.head? = some Boot) (hA : led t = some A)
    (hA0 : A.head? = some Boot) (hc1 : 1 ≤ c) (hcl : c ≤ l.length) (ht : TermAt l c = t) :
    l.take c <+: A ∧ TermAt A c = t := by
  rcases Nat.lt_or_ge 1 c with h2 | h1
  · rw [FromLed.iff] at hl
    obtain ⟨L, hL, heq⟩ := hl (c - 1) (by omega) (by omega)
    rw [show c - 1 + 1 = c by omega, ht, hA] at hL; cases hL
    rw [show c - 1 + 1 = c by omega] at heq
    refine ⟨by rw [heq]; exact List.take_prefix _ _, ?_⟩
    have : TermAt (l.take c) c = TermAt (A.take c) c := by rw [heq]
    rw [termAt_take _ _ _ (Nat.le_refl c), termAt_take _ _ _ (Nat.le_refl c)] at this
    rw [← this]; exact ht
  · have hc : c = 1 := by omega
    subst hc
    cases l with
    | nil => simp at hl0
    | cons x xs => cases A with
      | nil => simp at hA0
      | cons y ys =>
        simp at hl0 hA0; subst hl0 hA0
        refine ⟨by simp, ?_⟩
        simpa [TermAt] using ht

end LogLemmas

-- Facts about what is acknowledged and committed.
section Quorums
set_option linter.unusedSectionVars false
variable {server value MS VS LS CS : Type} [DecidableEq value] [Servers server] [TSet (Msg server value) MS]
  [TSet (Vote server) VS] [TSet (Elected server) LS] [TSet (Commit server value) CS]

theorem QC.mono (msgs msgs' : MS) (i : server) (t c : Nat)
    (h : ∀ a : Msg server value, a ∈ msgs → a ∈ msgs') (hq : QC msgs i t c) : QC msgs' i t c := by
  unfold QC at *
  refine IsQuorum.mono _ _ ?_ hq
  intro j hj
  simp only [decide_eq_true_eq] at hj ⊢
  rcases hj with hj | ⟨x, hx, hc⟩
  · exact Or.inl hj
  · exact Or.inr ⟨x, h _ hx, hc⟩

theorem Root.mono (msgs msgs' : MS) (leaders leaders' : LS) (led led' : Nat → Option (List (Entry value)))
    (r : Commit server value) (hm : ∀ a : Msg server value, a ∈ msgs → a ∈ msgs')
    (hl : ∀ a : Elected server, a ∈ leaders → a ∈ leaders') (hg : LedGrows led led')
    (h : Root msgs leaders led r) : Root msgs' leaders' led' r := by
  obtain ⟨h1, ⟨A, hA, hp, ht⟩, h3⟩ := h
  obtain ⟨es, hA', _⟩ := hg _ A hA
  refine ⟨hl _ h1, ⟨A ++ es, hA', hp.trans (List.prefix_append _ _), ?_⟩, QC.mono _ _ _ _ _ hm h3⟩
  rw [termAt_append_left _ _ _ hp.length_le]; exact ht

-- A fact that is not an acknowledgement changes nothing about what is acknowledged.
theorem Acked.of_insert (msgs : MS) (leaders : LS) (led : Nat → Option (List (Entry value)))
    (m : Msg server value) (n : server) (t : Nat) (A : List (Entry value)) (c : Nat)
    (hm : ∀ j i t x, m ≠ Msg.ack j i t x)
    (h : Acked (TSet.insert m msgs) leaders led n t A c) : Acked msgs leaders led n t A c := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨h1, h2, h3, ?_⟩
  rcases h4 with ⟨i, x, hx, hc⟩ | h4
  · rw [RaftVeil.Lemmas.mem_insert] at hx
    rcases hx with hx | hx
    · exact absurd hx.symm (hm _ _ _ _)
    · exact Or.inl ⟨i, x, hx, hc⟩
  · exact Or.inr h4

-- A new acknowledgement adds what it says, for its sender.
theorem Acked.of_insert_ack (msgs : MS) (leaders : LS) (led : Nat → Option (List (Entry value)))
    (j i0 : server) (t0 x0 : Nat) (n : server) (t : Nat) (A : List (Entry value)) (c : Nat)
    (h : Acked (TSet.insert (Msg.ack j i0 t0 x0) msgs) leaders led n t A c) :
    Acked msgs leaders led n t A c ∨ (n = j ∧ t = t0 ∧ c ≤ x0 ∧ led t = some A ∧ 2 ≤ c ∧ TermAt A c = t) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  rcases h4 with ⟨i, x, hx, hc⟩ | h4
  · rw [RaftVeil.Lemmas.mem_insert] at hx
    rcases hx with hx | hx
    · cases hx; exact Or.inr ⟨rfl, rfl, hc, h1, h2, h3⟩
    · exact Or.inl ⟨h1, h2, h3, Or.inl ⟨i, x, hx, hc⟩⟩
  · exact Or.inl ⟨h1, h2, h3, Or.inr h4⟩

theorem Early.of_insert (msgs : MS) (leaders : LS) (led : Nat → Option (List (Entry value)))
    (m : Msg server value) (n cand : server) (u : Nat)
    (hm : ∀ j i t x, m ≠ Msg.ack j i t x) (hv : ∀ li lt, m ≠ Msg.vote cand u li lt)
    (h : Early msgs leaders led n cand u) : Early (TSet.insert m msgs) leaders led n cand u := by
  intro t A c ha htu li lt hr
  rw [RaftVeil.Lemmas.mem_insert] at hr
  rcases hr with hr | hr
  · exact absurd hr.symm (hv _ _)
  · exact h t A c (Acked.of_insert _ _ _ _ _ _ _ _ hm ha) htu li lt hr

-- Entries a quorum acknowledged to the leader of their term are in every later leader log.
theorem leader_complete (msgs : MS) (leaders : LS) (votes : VS)
    (led : Nat → Option (List (Entry value)))
    (hEQ : ∀ ld : Elected server, ld ∈ leaders →
      IsQuorum (fun n => @decide (
        TSet.contains ({ voter := n, term := ld.term, cand := ld.server } : Vote server) votes = true ∧
        Early msgs leaders led n ld.server ld.term) (Classical.propDecidable _)) = true)
    (hLHas : ∀ t : Nat, ¬ led t = none → ∃ a : Elected server, a ∈ leaders ∧ a.term = t)
    (hVHR : ∀ v : Vote server, v ∈ votes →
      ∃ m : Msg server value, m ∈ msgs ∧ ∃ li lt, m = Msg.vote v.cand v.term li lt)
    (hLER : ∀ ld : Elected server, ld ∈ leaders → ∀ m : Msg server value, m ∈ msgs → ∀ li lt : Nat,
      m = Msg.vote ld.server ld.term li lt → ∀ L : List (Entry value), led ld.term = some L →
        li ≤ L.length ∧ TermAt L li = lt)
    (hLedFL : ∀ t L, led t = some L → FromLed led L)
    (i : server) (t c : Nat) (A : List (Entry value))
    (hl : ({ server := i, term := t } : Elected server) ∈ leaders) (hA : led t = some A)
    (hc2 : 2 ≤ c) (hcA : c ≤ A.length) (hct : TermAt A c = t) (hq : QC msgs i t c) :
    ∀ u, t < u → ∀ B, led u = some B → A.take c <+: B := by
  intro u
  induction u using Nat.strongRecOn with
  | ind u ih =>
    intro htu B hB
    obtain ⟨ld, hld, hldt⟩ := hLHas u (by rw [hB]; exact Option.some_ne_none B)
    obtain ⟨n, hn1, hn2⟩ := IsQuorum.inter _ _ hq (hEQ ld hld)
    simp only [decide_eq_true_eq] at hn1 hn2
    obtain ⟨hvote, hearly⟩ := hn2
    have hack : Acked msgs leaders led n t A c := by
      refine ⟨hA, hc2, hct, ?_⟩
      rcases hn1 with rfl | ⟨x, hx, hcx⟩
      · exact Or.inr ⟨hl, hcA⟩
      · exact Or.inl ⟨i, x, hx, hcx⟩
    obtain ⟨m, hm, li, lt, rfl⟩ := hVHR _ hvote
    rcases hearly t A c hack (by omega) li lt hm with ⟨hcli, B', hB', heq⟩ | ⟨w, htw, hwu, B2, hB2, hlack⟩
    · obtain ⟨hliB, hBt⟩ := hLER ld hld _ hm li lt rfl B (by rw [hldt]; exact hB)
      have hfl := hLedFL u B hB
      rw [FromLed.iff] at hfl
      obtain ⟨L2, hL2, hBL2⟩ := hfl (li - 1) (by omega) (by omega)
      rw [show li - 1 + 1 = li by omega, hBt, hB'] at hL2
      cases hL2
      rw [show li - 1 + 1 = li by omega] at hBL2
      rw [take_prefix_iff _ _ _ hcA]
      refine ⟨by omega, ?_⟩
      have : (B.take li).take c = (B'.take li).take c := by rw [hBL2]
      rw [List.take_take, List.take_take, Nat.min_eq_left hcli] at this
      rw [heq, this]
    · exact absurd (ih w (by omega) htw B2 hB2) hlack

-- Two committed prefixes that leaders committed are comparable.
theorem roots_cmp (msgs : MS) (leaders : LS) (votes : VS)
    (led : Nat → Option (List (Entry value)))
    (hEQ : ∀ ld : Elected server, ld ∈ leaders →
      IsQuorum (fun n => @decide (
        TSet.contains ({ voter := n, term := ld.term, cand := ld.server } : Vote server) votes = true ∧
        Early msgs leaders led n ld.server ld.term) (Classical.propDecidable _)) = true)
    (hLHas : ∀ t : Nat, ¬ led t = none → ∃ a : Elected server, a ∈ leaders ∧ a.term = t)
    (hVHR : ∀ v : Vote server, v ∈ votes →
      ∃ m : Msg server value, m ∈ msgs ∧ ∃ li lt, m = Msg.vote v.cand v.term li lt)
    (hLER : ∀ ld : Elected server, ld ∈ leaders → ∀ m : Msg server value, m ∈ msgs → ∀ li lt : Nat,
      m = Msg.vote ld.server ld.term li lt → ∀ L : List (Entry value), led ld.term = some L →
        li ≤ L.length ∧ TermAt L li = lt)
    (hLedFL : ∀ t L, led t = some L → FromLed led L)
    (hLBoot : ∀ t L, led t = some L → L.head? = some Boot)
    (r1 r2 : Commit server value) (h1 : Root msgs leaders led r1) (h2 : Root msgs leaders led r2) :
    r1.entries <+: r2.entries ∨ r2.entries <+: r1.entries := by
  -- it is enough to look at the one of the earlier term, or either if the terms are equal
  have key : ∀ a b : Commit server value, Root msgs leaders led a → Root msgs leaders led b →
      a.term ≤ b.term → a.entries <+: b.entries ∨ b.entries <+: a.entries := by
    intro a b ⟨ha1, ⟨A, hA, hpa, hta⟩, ha3⟩ ⟨hb1, ⟨B, hB, hpb, htb⟩, hb3⟩ hle
    have haA : a.entries = A.take a.entries.length := by
      obtain ⟨s, rfl⟩ := hpa; simp
    suffices h : a.entries <+: B from prefix_cmp_of_prefix _ _ B h hpb
    rcases Nat.eq_or_lt_of_le hle with heq | hlt
    · rw [heq, hB] at hA; cases hA; exact hpa
    · rcases Nat.lt_or_ge a.entries.length 2 with hsmall | hbig
      · -- at most the bootstrap entry, which every leader log starts with
        have hA0 := hLBoot _ A hA
        have hB0 := hLBoot _ B hB
        rw [haA]
        cases A with
        | nil => simp
        | cons x xs => cases B with
          | nil => simp at hB0
          | cons y ys =>
            simp at hA0 hB0; subst hA0 hB0
            rcases Nat.lt_or_ge a.entries.length 1 with h0 | h1
            · simp [show a.entries.length = 0 by omega]
            · rw [show a.entries.length = 1 by omega]; simp
      · rw [haA]
        exact leader_complete msgs leaders votes led hEQ hLHas hVHR hLER hLedFL a.server a.term
          a.entries.length A ha1 hA hbig hpa.length_le hta ha3 b.term hlt B hB
  rcases Nat.le_total r1.term r2.term with h | h
  · exact key r1 r2 h1 h2 h
  · exact (key r2 r1 h2 h1 h).symm

-- At most the bootstrap entry: every log that starts with it has it.
theorem boot_prefix (A B : List (Entry value)) (c : Nat) (hA0 : A.head? = some Boot)
    (hB0 : B.head? = some Boot) (hc : c < 2) : A.take c <+: B := by
  cases A with
  | nil => simp
  | cons x xs => cases B with
    | nil => simp at hB0
    | cons y ys =>
      simp at hA0 hB0; subst hA0 hB0
      rcases Nat.lt_or_ge c 1 with h0 | h1
      · simp [show c = 0 by omega]
      · rw [show c = 1 by omega]; simp

-- A committed prefix that a leader committed is in the leader log of its term and of every
-- later term.
theorem root_in_later (msgs : MS) (leaders : LS) (votes : VS)
    (led : Nat → Option (List (Entry value)))
    (hEQ : ∀ ld : Elected server, ld ∈ leaders →
      IsQuorum (fun n => @decide (
        TSet.contains ({ voter := n, term := ld.term, cand := ld.server } : Vote server) votes = true ∧
        Early msgs leaders led n ld.server ld.term) (Classical.propDecidable _)) = true)
    (hLHas : ∀ t : Nat, ¬ led t = none → ∃ a : Elected server, a ∈ leaders ∧ a.term = t)
    (hVHR : ∀ v : Vote server, v ∈ votes →
      ∃ m : Msg server value, m ∈ msgs ∧ ∃ li lt, m = Msg.vote v.cand v.term li lt)
    (hLER : ∀ ld : Elected server, ld ∈ leaders → ∀ m : Msg server value, m ∈ msgs → ∀ li lt : Nat,
      m = Msg.vote ld.server ld.term li lt → ∀ L : List (Entry value), led ld.term = some L →
        li ≤ L.length ∧ TermAt L li = lt)
    (hLedFL : ∀ t L, led t = some L → FromLed led L)
    (hLBoot : ∀ t L, led t = some L → L.head? = some Boot)
    (r : Commit server value) (hr : Root msgs leaders led r) (u : Nat) (hu : r.term ≤ u)
    (B : List (Entry value)) (hB : led u = some B) : r.entries <+: B := by
  obtain ⟨hr1, ⟨A, hA, hpa, hta⟩, hr3⟩ := hr
  have haA : r.entries = A.take r.entries.length := by
    obtain ⟨s, rfl⟩ := hpa; simp
  rcases Nat.eq_or_lt_of_le hu with heq | hlt
  · rw [heq, hB] at hA; cases hA; exact hpa
  · rcases Nat.lt_or_ge r.entries.length 2 with hsmall | hbig
    · rw [haA]; exact boot_prefix A B _ (hLBoot _ A hA) (hLBoot _ B hB) hsmall
    · rw [haA]
      exact leader_complete msgs leaders votes led hEQ hLHas hVHR hLER hLedFL r.server r.term
        r.entries.length A hr1 hA hbig hpa.length_le hta hr3 u hlt B hB

-- The same for a candidate a quorum voted for, before its term has a leader log.
theorem cand_complete (msgs : MS) (leaders : LS) (votes : VS)
    (led : Nat → Option (List (Entry value)))
    (hEQ : ∀ ld : Elected server, ld ∈ leaders →
      IsQuorum (fun n => @decide (
        TSet.contains ({ voter := n, term := ld.term, cand := ld.server } : Vote server) votes = true ∧
        Early msgs leaders led n ld.server ld.term) (Classical.propDecidable _)) = true)
    (hLHas : ∀ t : Nat, ¬ led t = none → ∃ a : Elected server, a ∈ leaders ∧ a.term = t)
    (hVHR : ∀ v : Vote server, v ∈ votes →
      ∃ m : Msg server value, m ∈ msgs ∧ ∃ li lt, m = Msg.vote v.cand v.term li lt)
    (hLER : ∀ ld : Elected server, ld ∈ leaders → ∀ m : Msg server value, m ∈ msgs → ∀ li lt : Nat,
      m = Msg.vote ld.server ld.term li lt → ∀ L : List (Entry value), led ld.term = some L →
        li ≤ L.length ∧ TermAt L li = lt)
    (hLedFL : ∀ t L, led t = some L → FromLed led L)
    (hLBoot : ∀ t L, led t = some L → L.head? = some Boot)
    (i : server) (cur : Nat) (l : List (Entry value))
    (hAV : ∀ n t A c, Acked msgs leaders led n t A c →
      TSet.contains ({ voter := n, term := cur, cand := i } : Vote server) votes = true → t < cur →
      ∀ li lt, Msg.vote (value := value) i cur li lt ∈ msgs →
        Covers led A c li lt ∨ LostIn led A c t cur)
    (hnone : led cur = none)
    (hq : IsQuorum (fun n => TSet.contains ({ voter := n, term := cur, cand := i } : Vote server) votes) = true)
    (hCL : ∀ li lt, Msg.vote (value := value) i cur li lt ∈ msgs → l.length = li ∧ TermAt l li = lt)
    (hl : FromLed led l) (hl0 : l.head? = some Boot)
    (r : Commit server value) (hr : Root msgs leaders led r) (hlt : r.term < cur) :
    r.entries <+: l := by
  obtain ⟨hr1, ⟨A, hA, hpa, hta⟩, hr3⟩ := hr
  have haA : r.entries = A.take r.entries.length := by
    obtain ⟨s, rfl⟩ := hpa; simp
  rcases Nat.lt_or_ge r.entries.length 2 with hsmall | hbig
  · rw [haA]; exact boot_prefix A l _ (hLBoot _ A hA) hl0 hsmall
  · obtain ⟨n, hn1, hn2⟩ := IsQuorum.inter _ _ hr3 hq
    simp only [decide_eq_true_eq] at hn1
    have hack : Acked msgs leaders led n r.term A r.entries.length := by
      refine ⟨hA, hbig, hta, ?_⟩
      rcases hn1 with rfl | ⟨x, hx, hcx⟩
      · exact Or.inr ⟨hr1, hpa.length_le⟩
      · exact Or.inl ⟨r.server, x, hx, hcx⟩
    obtain ⟨m, hm, li, lt, rfl⟩ := hVHR _ hn2
    rcases hAV n r.term A _ hack hn2 hlt li lt hm with ⟨hcli, B', hB', heq⟩ | ⟨w, htw, hwu, B2, hB2, hlack⟩
    · obtain ⟨hlen, hlast⟩ := hCL li lt hm
      obtain ⟨hpre, -⟩ := take_prefix_led led l B' lt li hl hl0 hB' (hLBoot _ B' hB') (by omega)
        (by omega) hlast
      rw [take_prefix_iff _ _ _ (by omega)] at hpre
      have h2 : (l.take li).take r.entries.length = (B'.take li).take r.entries.length := by rw [hpre.2]
      rw [List.take_take, List.take_take, Nat.min_eq_left hcli] at h2
      rw [haA, heq, ← h2]; exact List.take_prefix _ _
    · rcases Nat.eq_or_lt_of_le hwu with hw | hw
      · rw [hw, hnone] at hB2; cases hB2
      · exact absurd (leader_complete msgs leaders votes led hEQ hLHas hVHR hLER hLedFL r.server r.term
          r.entries.length A hr1 hA hbig hpa.length_le hta hr3 w htw B2 hB2) hlack

-- BecomeLeader adds nothing to what is acknowledged: the new leader has no entry of its term.
theorem Acked.of_becomeLeader (msgs : MS) (leaders : LS) (led : Nat → Option (List (Entry value)))
    (i : server) (cur : Nat) {d : ∀ x : Nat, Decidable (cur = x)} (l : List (Entry value)) (n : server) (t : Nat) (A : List (Entry value)) (c : Nat)
    (hsame : ∀ L, led cur = some L → L = l)
    (hmem : ¬ led cur = none → ({ server := i, term := cur } : Elected server) ∈ leaders)
    (hfresh : led cur = none → ∀ c, 2 ≤ c → TermAt l c ≠ cur)
    (h : Acked msgs (TSet.insert ({ server := i, term := cur } : Elected server) leaders)
      (fun x => @ite _ (cur = x) (d _) (some l) (led x)) n t A c) :
    Acked msgs leaders led n t A c := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have h1' : (@ite _ (cur = t) (d _) (some l) (led t)) = some A := h1
  by_cases hc : cur = t
  · subst hc
    rw [RaftVeil.Lemmas.ifPos rfl] at h1'; cases h1'
    cases hL : led cur with
    | none => exact absurd h3 (hfresh hL c h2)
    | some L =>
      have hLl := hsame L hL
      subst hLl
      refine ⟨hL, h2, h3, ?_⟩
      rcases h4 with h4 | ⟨h4, h5⟩
      · exact Or.inl h4
      · rw [RaftVeil.Lemmas.mem_insert] at h4
        rcases h4 with h4 | h4
        · cases h4; exact Or.inr ⟨hmem (by rw [hL]; exact Option.some_ne_none _), h5⟩
        · exact Or.inr ⟨h4, h5⟩
  · rw [RaftVeil.Lemmas.ifNeg hc] at h1'
    refine ⟨h1', h2, h3, ?_⟩
    rcases h4 with h4 | ⟨h4, h5⟩
    · exact Or.inl h4
    · rw [RaftVeil.Lemmas.mem_insert] at h4
      rcases h4 with h4 | h4
      · cases h4; exact absurd rfl hc
      · exact Or.inr ⟨h4, h5⟩

-- LeaderAppend: what is acknowledged afterwards was acknowledged before, except the new
-- entry, which only the leader has.
theorem Acked.of_leaderAppend (msgs : MS) (leaders : LS) (led : Nat → Option (List (Entry value)))
    (cur : Nat) {d : ∀ x : Nat, Decidable (cur = x)} (l : List (Entry value)) (e : Entry value) (n : server) (t : Nat)
    (A : List (Entry value)) (c : Nat)
    (hl : led cur = some l)
    (hAF : ∀ i x, Msg.ack (value := value) n i cur x ∈ msgs → x ≤ l.length)
    (h : Acked msgs leaders
      (fun x => @ite _ (cur = x) (d _) (some (l ++ [e])) (led x)) n t A c) :
    (t ≠ cur ∧ Acked msgs leaders led n t A c) ∨
    (t = cur ∧ A = l ++ [e] ∧
      ((c ≤ l.length ∧ Acked msgs leaders led n cur l c) ∨
       (c = l.length + 1 ∧ ({ server := n, term := cur } : Elected server) ∈ leaders))) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have h1' : (@ite _ (cur = t) (d _) (some (l ++ [e])) (led t)) = some A := h1
  by_cases hc : cur = t
  · subst hc
    rw [RaftVeil.Lemmas.ifPos rfl] at h1'; cases h1'
    refine Or.inr ⟨rfl, rfl, ?_⟩
    rcases h4 with ⟨i, x, hx, hcx⟩ | ⟨h4, h5⟩
    · have := hAF i x hx
      refine Or.inl ⟨by omega, hl, h2, ?_, Or.inl ⟨i, x, hx, hcx⟩⟩
      rw [← termAt_append_left l [e] c (by omega)]; exact h3
    · simp at h5
      rcases Nat.lt_or_ge l.length c with hlt | hge
      · exact Or.inr ⟨by omega, h4⟩
      · refine Or.inl ⟨hge, hl, h2, ?_, Or.inr ⟨h4, hge⟩⟩
        rw [← termAt_append_left l [e] c hge]; exact h3
  · rw [RaftVeil.Lemmas.ifNeg hc] at h1'
    exact Or.inl ⟨fun h => hc h.symm, h1', h2, h3, h4⟩

theorem Acked.le_length (msgs : MS) (leaders : LS) (led : Nat → Option (List (Entry value)))
    (n : server) (t : Nat) (A : List (Entry value)) (c : Nat)
    (hAF : ∀ i x, Msg.ack (value := value) n i t x ∈ msgs → ∃ L, led t = some L ∧ x ≤ L.length)
    (h : Acked msgs leaders led n t A c) : c ≤ A.length := by
  obtain ⟨h1, _, _, h4⟩ := h
  rcases h4 with ⟨i, x, hx, hc⟩ | ⟨_, h5⟩
  · obtain ⟨L, hL, hxL⟩ := hAF i x hx
    rw [h1] at hL; cases hL; omega
  · exact h5

end Quorums

-- BecomeLeader: a candidate with a quorum of votes is the only node elected in its term, so
-- an existing leader log of the term is its log.
theorem winner_unique {server value MsgSet VoteSet LeaderSet : Type} [Servers server]
    [TSet (Msg server value) MsgSet] [TSet (Vote server) VoteSet] [TSet (Elected server) LeaderSet]
    (msgs : MsgSet) (votes : VoteSet) (leaders : LeaderSet) (i : server) (cur : Nat)
    (hOV : ∀ a b : Vote server, a ∈ votes → b ∈ votes → a.voter = b.voter → a.term = b.term → a.cand = b.cand)
    (hGV : ∀ j, TSet.contains (Msg.grant (value := value) j i cur) msgs = true →
      TSet.contains ({ voter := j, term := cur, cand := i } : Vote server) votes = true)
    (hLQ : ∀ a : Elected server, a ∈ leaders →
      (IsQuorum fun j => TSet.contains ({ voter := j, term := a.term, cand := a.server } : Vote server) votes) = true)
    (hq : (IsQuorum fun j =>
      @ite Bool (j = i) (Classical.propDecidable _) (TSet.contains ({ voter := i, term := cur, cand := i } : Vote server) votes)
        (TSet.contains (Msg.grant (value := value) j i cur) msgs)) = true) :
    ∀ x : Elected server, x ∈ leaders → x.term = cur → x.server = i := by
  have hq' : IsQuorum (fun j => TSet.contains ({ voter := j, term := cur, cand := i } : Vote server) votes) = true := by
    refine IsQuorum.mono _ _ ?_ hq
    intro j hj
    by_cases hji : j = i
    · subst hji; simpa using hj
    · simp only [hji, ite_false] at hj
      exact hGV _ hj
  intro x hx hxt
  obtain ⟨j, h1, h2⟩ := IsQuorum.inter _ _ (hLQ x hx) hq'
  have := hOV _ _ h1 h2 rfl (by simpa using hxt)
  simpa using this

theorem winner_led {server value LeaderSet : Type} [TSet (Elected server) LeaderSet]
    (leaders : LeaderSet) (currentTerm : server → Nat) (log : server → List (Entry value))
    (ledLog : Nat → Option (List (Entry value))) (i : server)
    (key : ∀ x : Elected server, x ∈ leaders → x.term = currentTerm i → x.server = i)
    (hLO : ∀ a : Elected server, a ∈ leaders → a.term = currentTerm a.server → ledLog a.term = some (log a.server))
    (hLHas : ∀ t : Nat, ¬ ledLog t = none → ∃ a, a ∈ leaders ∧ a.term = t) :
    ∀ L, ledLog (currentTerm i) = some L → L = log i := by
  intro L hL
  obtain ⟨x, hx, hxt⟩ := hLHas (currentTerm i) (by rw [hL]; exact Option.some_ne_none L)
  have hxi := key x hx hxt
  have := hLO x hx (by rw [hxt, hxi])
  rw [hxt, hL, hxi] at this
  exact Option.some.inj this

-- Setting a term's leader log for the first time, or to its value, keeps every leader log
-- (for FromLed.mono).
theorem led_ext_set {value : Type} (ledLog : Nat → Option (List (Entry value))) (cur : Nat)
    (l : List (Entry value)) (hsame : ∀ L, ledLog cur = some L → L <+: l) :
    ∀ t L, ledLog t = some L →
      ∃ L', (fun x => @ite _ (cur = x) (Classical.propDecidable _) (some l) (ledLog x)) t = some L' ∧ L <+: L' := by
  intro t L hL
  by_cases hc : cur = t
  · subst hc
    refine ⟨l, ?_, hsame L hL⟩
    show (@ite _ (cur = cur) (Classical.propDecidable _) (some l) (ledLog cur)) = some l
    rw [RaftVeil.Lemmas.ifPos rfl]
  · refine ⟨L, ?_, List.prefix_refl _⟩
    show (@ite _ (cur = t) (Classical.propDecidable _) (some l) (ledLog t)) = some L
    rw [RaftVeil.Lemmas.ifNeg hc]; exact hL

-- What RequestsFromLed says of an append request (`X` stands for the part about its commit
-- index), in terms of the fields actions read.
theorem req_facts {server value : Type} [DecidableEq value]
    (ledLog : Nat → Option (List (Entry value))) (X : Nat → List (Entry value) → Nat → Bool)
    (m : Msg server value)
    (h : (match m with
      | .append _ _ term prevLogIndex prevLogTerm entries commit =>
        (match ledLog term with
          | none => false
          | some l =>
            decide (prevLogIndex + entries.length ≤ l.length) &&
              (decide (prevLogTerm = TermAt l prevLogIndex) &&
                (decide (entries = SubSeq l (prevLogIndex + 1) (prevLogIndex + entries.length)) &&
                  X term l commit)))
      | _ => true) = true)
    (ha : m.isAppend = true) :
    ∃ L, ledLog m.term = some L ∧ m.prevLogIndex + m.entries.length ≤ L.length ∧
      m.prevLogTerm = TermAt L m.prevLogIndex ∧
      m.entries = SubSeq L (m.prevLogIndex + 1) (m.prevLogIndex + m.entries.length) ∧
      X m.term L m.commit = true := by
  cases m with
  | append src dst term p pt es c =>
    dsimp only [Msg.term, Msg.prevLogIndex, Msg.prevLogTerm, Msg.entries, Msg.commit] at h ⊢
    cases hL : ledLog term with
    | none => rw [hL] at h; exact Bool.noConfusion h
    | some L =>
      rw [hL] at h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      exact ⟨L, rfl, h.1, h.2.1, h.2.2.1, h.2.2.2⟩
  | _ => simp [Msg.isAppend] at ha

-- LeaderAppend: what appending an entry of its term to the leader's log, and to the term's
-- leader log with it, does to FromLed.
theorem leaderAppend_fromLed {value : Type} [DecidableEq value]
    (led : Nat → Option (List (Entry value))) (l : List (Entry value)) (e : Entry value) (t : Nat)
    (het : e.term = t) (hled : led t = some l) :
    (∀ l', FromLed led l' →
      FromLed (fun x => @ite _ (t = x) (Classical.propDecidable _) (some (l ++ [e])) (led x)) l') ∧
    (FromLed led l →
      FromLed (fun x => @ite _ (t = x) (Classical.propDecidable _) (some (l ++ [e])) (led x)) (l ++ [e])) := by
  subst het
  have hext := led_ext_set led e.term (l ++ [e])
    (fun L hL => by rw [hled] at hL; cases hL; exact List.prefix_append _ _)
  refine ⟨fun l' h => FromLed.mono _ _ _ hext h, fun h => ?_⟩
  refine FromLed.append_own _ l [e] e.term ?_ ?_ (FromLed.mono _ _ _ hext h)
  · show (@ite _ (e.term = e.term) (Classical.propDecidable _) (some (l ++ [e])) (led e.term)) = some (l ++ [e])
    rw [RaftVeil.Lemmas.ifPos rfl]
  · intro e' he'; simp at he'; rw [he']

-- StoreEntries: the follower's new log is from leader logs and keeps the bootstrap entry.
theorem store_fromLed {value : Type} [DecidableEq value]
    (led : Nat → Option (List (Entry value))) (l L : List (Entry value)) (p k : Nat)
    (es : List (Entry value))
    (hl : FromLed led l) (hL : FromLed led L)
    (hl0 : l.head? = some Boot) (hL0 : L.head? = some Boot)
    (hpn : p + es.length ≤ L.length)
    (hes : es = SubSeq L (p + 1) (p + es.length))
    (hprev : PrevOk l p (TermAt L p) = true)
    (hk : k ∈ List.range' 1 es.length)
    (hfirst : HasFirst l p es (k - 1) = true)
    (hlen : p + k = l.length + 1) :
    FromLed led (l ++ SubSeq es k es.length) ∧ (l ++ SubSeq es k es.length).head? = some Boot := by
  constructor
  · rw [store_eq led l L p k es hl hL hl0 hL0 hpn hes hprev hk hfirst hlen]
    exact FromLed.take led L _ hL
  · cases l with
    | nil => simp at hl0
    | cons x xs => simpa using hl0

-- RequestsFromLed is kept when leader logs only grow and the commit part (`X`, `X'`) is kept.
theorem req_mono {server value : Type} [DecidableEq value]
    (led led' : Nat → Option (List (Entry value))) (X X' : Nat → List (Entry value) → Nat → Bool)
    (m : Msg server value)
    (h : (match m with
      | .append _ _ term prevLogIndex prevLogTerm entries commit =>
        (match led term with
          | none => false
          | some l =>
            decide (prevLogIndex + entries.length ≤ l.length) &&
              (decide (prevLogTerm = TermAt l prevLogIndex) &&
                (decide (entries = SubSeq l (prevLogIndex + 1) (prevLogIndex + entries.length)) &&
                  X term l commit)))
      | _ => true) = true)
    (hled : ∀ t l, led t = some l → ∃ l', led' t = some l' ∧ l <+: l')
    (hX : ∀ t l l' c, l <+: l' → X t l c = true → X' t l' c = true) :
    (match (generalizing := false) m with
      | .append _ _ term prevLogIndex prevLogTerm entries commit =>
        (match led' term with
          | none => false
          | some l =>
            decide (prevLogIndex + entries.length ≤ l.length) &&
              (decide (prevLogTerm = TermAt l prevLogIndex) &&
                (decide (entries = SubSeq l (prevLogIndex + 1) (prevLogIndex + entries.length)) &&
                  X' term l commit)))
      | _ => true) = true := by
  cases m with
  | append src dst term p pt es c =>
    dsimp only at h ⊢
    cases hL : led term with
    | none => rw [hL] at h; exact Bool.noConfusion h
    | some l =>
      obtain ⟨l', hl', hp⟩ := hled term l hL
      rw [hL] at h; rw [hl']
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h ⊢
      obtain ⟨h1, h2, h3, h4⟩ := h
      obtain ⟨s, rfl⟩ := hp
      refine ⟨by simp; omega, ?_, ?_, hX term l (l ++ s) c ⟨s, rfl⟩ h4⟩
      · rw [termAt_append_left _ _ _ (by omega)]; exact h2
      · rw [subSeq_append_left _ _ _ _ (by omega) h1]; exact h3
  | _ => rfl

-- The commit part of RequestsFromLed is kept when the leader log and the set of commits grow.
theorem commitPart_mono {server value S S' : Type} [TSet (Commit server value) S]
    [TSet (Commit server value) S'] (cs : S) (cs' : S') (hS : ∀ k, k ∈ cs → k ∈ cs')
    (l l' : List (Entry value)) (c t : Nat) (hp : l <+: l')
    (h : c = 0 ∨ (c ≤ l.length ∧ ∃ k : { k // k ∈ cs },
      k.val.term ≤ t ∧ c ≤ k.val.entries.length ∧ SubSeq k.val.entries 1 c = SubSeq l 1 c)) :
    c = 0 ∨ (c ≤ l'.length ∧ ∃ k : { k // k ∈ cs' },
      k.val.term ≤ t ∧ c ≤ k.val.entries.length ∧ SubSeq k.val.entries 1 c = SubSeq l' 1 c) := by
  rcases h with h0 | ⟨hc, ⟨k, hk⟩, ht, h1, h2⟩
  · exact Or.inl h0
  · obtain ⟨s, rfl⟩ := hp
    refine Or.inr ⟨by simp; omega, ⟨k, hS k hk⟩, ht, h1, ?_⟩
    rw [subSeq_append_left _ _ _ _ (Nat.le_refl 1) hc]; exact h2

-- LeaderAppend keeps LogMatching.
theorem leaderAppend_matching {server value : Type} [DecidableEq value]
    (led : Nat → Option (List (Entry value))) (log : server → List (Entry value)) (i : server)
    (e : Entry value) (hled : led e.term = some (log i))
    (hF : ∀ j, FromLed led (log j)) (hB : ∀ j, (log j).head? = some Boot) :
    ∀ (a b : server) (k : Nat), 1 ≤ k →
      k < 1 + min (@ite _ (i = a) (Classical.propDecidable _) (log i ++ [e]) (log a)).length
        (@ite _ (i = b) (Classical.propDecidable _) (log i ++ [e]) (log b)).length →
      TermAt (@ite _ (i = a) (Classical.propDecidable _) (log i ++ [e]) (log a)) k =
        TermAt (@ite _ (i = b) (Classical.propDecidable _) (log i ++ [e]) (log b)) k →
      SubSeq (@ite _ (i = a) (Classical.propDecidable _) (log i ++ [e]) (log a)) 1 k =
        SubSeq (@ite _ (i = b) (Classical.propDecidable _) (log i ++ [e]) (log b)) 1 k := by
  have hLA := leaderAppend_fromLed led (log i) e e.term rfl hled
  have hF' : ∀ j, FromLed (fun x => @ite _ (e.term = x) (Classical.propDecidable _) (some (log i ++ [e])) (led x))
      (@ite _ (i = j) (Classical.propDecidable _) (log i ++ [e]) (log j)) := by
    intro j
    by_cases hj : i = j
    · rw [RaftVeil.Lemmas.ifPos hj]; exact hLA.2 (hF i)
    · rw [RaftVeil.Lemmas.ifNeg hj]; exact hLA.1 _ (hF j)
  have hB' : ∀ j, (@ite _ (i = j) (Classical.propDecidable _) (log i ++ [e]) (log j)).head? = some Boot := by
    intro j
    by_cases hj : i = j
    · rw [RaftVeil.Lemmas.ifPos hj]
      have := hB i
      cases hl : log i with
      | nil => rw [hl] at this; simp at this
      | cons x xs => rw [hl] at this; exact this
    · rw [RaftVeil.Lemmas.ifNeg hj]; exact hB j
  intro a b k hk1 hk2
  exact FromLed.matching _ _ _ (hF' a) (hF' b) (hB' a) (hB' b) k (List.mem_range'_1.2 ⟨hk1, hk2⟩)

-- PreGrantsAnswer and TimeoutNowFromLeader are kept when messages and leaders are only added
-- (`X`, `X'` the part asking for a request or a leader).
theorem pregrants_mono {server value : Type} (X X' : server → Nat → Bool) (a : Msg server value)
    (h : (match a with
      | .pregrant _ dst term => X dst term
      | _ => true) = true)
    (hX : ∀ d t, X d t = true → X' d t = true) :
    (match (generalizing := false) a with
      | .pregrant _ dst term => X' dst term
      | _ => true) = true := by
  cases a with
  | pregrant s d t => exact hX d t h
  | _ => rfl

theorem timeoutnow_mono {server value : Type} (X X' : server → Bool) (a : Msg server value)
    (h : (match a with
      | .timeoutnow src _ => X src
      | _ => true) = true)
    (hX : ∀ s, X s = true → X' s = true) :
    (match (generalizing := false) a with
      | .timeoutnow src _ => X' src
      | _ => true) = true := by
  cases a with
  | timeoutnow s d => exact hX s h
  | _ => rfl

-- Snapshots. If a snapshot is a prefix of the log, so is it extended by the entries applied since.
theorem snap_extend {α : Type} (s l : List α) (a : Nat) (h : s <+: l) (ha : s.length ≤ a) :
    s ++ SubSeq l (s.length + 1) a = l.take a := by
  obtain ⟨t, rfl⟩ := h
  have e : a + 1 - (s.length + 1) = a - s.length := by omega
  unfold SubSeq
  rw [e, Nat.add_sub_cancel, List.drop_left, List.take_append, List.take_of_length_le ha]

-- It is no shorter than the snapshot and no longer than the index it is extended to.
theorem snap_extend_length {α : Type} (s l : List α) (a : Nat) (ha : s.length ≤ a) :
    s.length ≤ (s ++ SubSeq l (s.length + 1) a).length ∧ (s ++ SubSeq l (s.length + 1) a).length ≤ a := by
  unfold SubSeq
  rw [List.length_append, List.length_take]
  omega

-- The beginning of a list, no longer than a prefix of the list, is a prefix of that prefix.
theorem take_prefix_of_prefix {α : Type} (e l : List α) (a : Nat) (h : e <+: l) (ha : a ≤ e.length) :
    l.take a <+: e := by
  obtain ⟨t, rfl⟩ := h
  rw [List.take_append_of_le_length ha]
  exact List.take_prefix _ _

-- ---------------------------------------------------------------------------------------
-- Proofs. Every invariant holds initially and is preserved by every action: one goal per
-- action and invariant. Proofs name the facts they use (`grind only`, `simp only`, the lemmas
-- above), so checking does not search a lemma library.
--
-- In a goal, `hinv` is the conjunction of the invariants before the step, in declaration
-- order. A proof takes the ones it uses by position (`have hX := hinv.2.….1`) and clears the
-- rest. Hand-written proofs name them
-- hES hOV hVT hVB hGV hLQ hLE hLTB hLO hLHL hLHas hAFL hLLL hRFL hBoot hLBoot hLFL hLedFL hLM
-- hTP hLogTB hLS hRF hRU hVHR hCL hLER hAF hAH hAV hEQ hCIL hCR hSMS
-- hCfT hCmT hCEP hCIC hAC hSM hLC hCWL
-- (hSMS is CommitSafety, hSM is StateMachineSafety), then hPGA, hTN and the rest by their own
-- names. New invariants and state fields go at the end, or the positions change.
--
-- Later actions name a goal's hypotheses at once (`intros; rename_i ...`) in goal order: the
-- action's choices and the invariant's first variable, the action's requirements, the rest.
--
-- Check with `../scripts/veil-check.sh`, or `lake build`.

-- initializer

prove_veil_invariant_goal initializer ElectionSafety using tr by
  obtain ⟨-, -, -, -, -, -, -, -, hm, hv, hl, -, hc, -, happ, htransfer, hsnap, hbase⟩ := htr
  subst hm hv hl hc
  intros
  exact (RaftVeil.Lemmas.sub_empty a).elim

prove_veil_invariant_goal initializer OneVotePerTerm using tr by
  obtain ⟨-, -, -, -, -, -, -, -, hm, hv, hl, -, hc, -, happ, htransfer, hsnap, hbase⟩ := htr
  subst hm hv hl hc
  intros
  exact (RaftVeil.Lemmas.sub_empty a).elim

prove_veil_invariant_goal initializer VoteTermBound using tr by
  obtain ⟨h1, h2, -, hsnap, hbase⟩ := htr
  rw [← h1 i, ← h2 i]
  exact Nat.zero_le 1

prove_veil_invariant_goal initializer VotesBound using tr by
  obtain ⟨-, -, -, -, -, -, -, -, hm, hv, hl, -, hc, -, happ, htransfer, hsnap, hbase⟩ := htr
  subst hm hv hl hc
  intros
  exact (RaftVeil.Lemmas.sub_empty v).elim

prove_veil_invariant_goal initializer GrantsAreVotes using tr by
  obtain ⟨-, -, -, -, -, -, -, -, hm, hv, hl, -, hc, -, happ, htransfer, hsnap, hbase⟩ := htr
  subst hm hv hl hc
  intros
  exact (RaftVeil.Lemmas.sub_empty m).elim

prove_veil_invariant_goal initializer LeadersHaveQuorum using tr by
  obtain ⟨-, -, -, -, -, -, -, -, hm, hv, hl, -, hc, -, happ, htransfer, hsnap, hbase⟩ := htr
  subst hm hv hl hc
  intros
  exact (RaftVeil.Lemmas.sub_empty ld).elim

prove_veil_invariant_goal initializer LeaderIsElected using tr by
  obtain ⟨hct, hvt, hvf, hlog, hrole, hci, hcft, hcfi, hm, hv, hl, hled, hc, hla, happ, htransfer, hsnap, hbase⟩ := htr
  intro h
  rw [← hrole i] at h
  have hR := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hR
  exact absurd h hR.2.1

prove_veil_invariant_goal initializer LeadersTermBound using tr by
  obtain ⟨hct, hvt, hvf, hlog, hrole, hci, hcft, hcfi, hm, hv, hl, hled, hc, hla, happ, htransfer, hsnap, hbase⟩ := htr
  subst hl
  exact (RaftVeil.Lemmas.sub_empty ld).elim

prove_veil_invariant_goal initializer LedOwner using tr by
  obtain ⟨hct, hvt, hvf, hlog, hrole, hci, hcft, hcfi, hm, hv, hl, hled, hc, hla, happ, htransfer, hsnap, hbase⟩ := htr
  subst hl
  exact (RaftVeil.Lemmas.sub_empty ld).elim

prove_veil_invariant_goal initializer LeadersHaveLed using tr by
  obtain ⟨hct, hvt, hvf, hlog, hrole, hci, hcft, hcfi, hm, hv, hl, hled, hc, hla, happ, htransfer, hsnap, hbase⟩ := htr
  subst hl
  exact (RaftVeil.Lemmas.sub_empty ld).elim

prove_veil_invariant_goal initializer LedHasLeader using tr by
  obtain ⟨hct, hvt, hvf, hlog, hrole, hci, hcft, hcfi, hm, hv, hl, hled, hc, hla, happ, htransfer, hsnap, hbase⟩ := htr
  intro h
  exact absurd (hled t).symm h

prove_veil_invariant_goal initializer AppendFromLeader using tr by
  obtain ⟨hct, hvt, hvf, hlog, hrole, hci, hcft, hcfi, hm, hv, hl, hled, hc, hla, happ, htransfer, hsnap, hbase⟩ := htr
  subst hm
  exact (RaftVeil.Lemmas.sub_empty m).elim

prove_veil_invariant_goal initializer LeaderLogIsLed using tr by
  obtain ⟨hct, hvt, hvf, hlog, hrole, hci, hcft, hcfi, hm, hv, hl, hled, hc, hla, happ, htransfer, hsnap, hbase⟩ := htr
  intro h
  rw [← hrole i] at h
  have hR := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hR
  exact absurd h hR.2.1

prove_veil_invariant_goal initializer RequestsFromLed using tr by
  obtain ⟨hct, hvt, hvf, hlog, hrole, hci, hcft, hcfi, hm, hv, hl, hled, hc, hla, happ, htransfer, hsnap, hbase⟩ := htr
  subst hm
  exact (RaftVeil.Lemmas.sub_empty m).elim

prove_veil_invariant_goal initializer BootEntry using tr by
  obtain ⟨hct, hvt, hvf, hlog, hrole, hci, hcft, hcfi, hm, hv, hl, hled, hc, hla, happ, htransfer, hsnap, hbase⟩ := htr
  rw [← hlog i]
  rfl

prove_veil_invariant_goal initializer LedBoot using tr by
  obtain ⟨hct, hvt, hvf, hlog, hrole, hci, hcft, hcfi, hm, hv, hl, hled, hc, hla, happ, htransfer, hsnap, hbase⟩ := htr
  rw [← hled t]
  rfl

prove_veil_invariant_goal initializer LogFromLed using tr by
  obtain ⟨hct, hvt, hvf, hlog, hrole, hci, hcft, hcfi, hm, hv, hl, hled, hc, hla, happ, htransfer, hsnap, hbase⟩ := htr
  rw [← hlog i, FromLed.iff]
  intro q h1 h2
  simp at h2
  omega

prove_veil_invariant_goal initializer LedFromLed using tr by
  obtain ⟨hct, hvt, hvf, hlog, hrole, hci, hcft, hcfi, hm, hv, hl, hled, hc, hla, happ, htransfer, hsnap, hbase⟩ := htr
  rw [← hled t]
  rfl

prove_veil_invariant_goal initializer LogMatching using tr by
  obtain ⟨hct, hvt, hvf, hlog, hrole, hci, hcft, hcfi, hm, hv, hl, hled, hc, hla, happ, htransfer, hsnap, hbase⟩ := htr
  intro _ _ _
  rw [← hlog a, ← hlog b]

prove_veil_invariant_goal initializer TermsPositive using tr by
  obtain ⟨hct, hvt, hvf, hlog, hrole, hci, hcft, hcfi, hm, hv, hl, hled, hc, hla, happ, htransfer, hsnap, hbase⟩ := htr
  rw [← hct i]
  exact Nat.le_refl 1

prove_veil_invariant_goal initializer LogTermsBound using tr by
  obtain ⟨hct, hvt, hvf, hlog, hrole, hci, hcft, hcfi, hm, hv, hl, hled, hc, hla, happ, htransfer, hsnap, hbase⟩ := htr
  rw [← hlog i, ← hct i]
  cases k with
  | zero => simp [TermAt]
  | succ q => cases q <;> simp [TermAt]

prove_veil_invariant_goal initializer LedSorted using tr by
  obtain ⟨hct, hvt, hvf, hlog, hrole, hci, hcft, hcfi, hm, hv, hl, hled, hc, hla, happ, htransfer, hsnap, hbase⟩ := htr
  intro hL
  rw [← hled t] at hL
  cases hL

prove_veil_invariant_goal initializer ReqFacts using tr by
  obtain ⟨hct, hvt, hvf, hlog, hrole, hci, hcft, hcfi, hm, hv, hl, hled, hc, hla, happ, htransfer, hsnap, hbase⟩ := htr
  subst hm
  exact (RaftVeil.Lemmas.sub_empty m).elim

prove_veil_invariant_goal initializer ReqUnique using tr by
  obtain ⟨hct, hvt, hvf, hlog, hrole, hci, hcft, hcfi, hm, hv, hl, hled, hc, hla, happ, htransfer, hsnap, hbase⟩ := htr
  subst hm
  exact (RaftVeil.Lemmas.sub_empty m).elim

prove_veil_invariant_goal initializer VoteHasReq using tr by
  obtain ⟨hct, hvt, hvf, hlog, hrole, hci, hcft, hcfi, hm, hv, hl, hled, hc, hla, happ, htransfer, hsnap, hbase⟩ := htr
  subst hv
  exact (RaftVeil.Lemmas.sub_empty v).elim

prove_veil_invariant_goal initializer CandLog using tr by
  obtain ⟨hct, hvt, hvf, hlog, hrole, hci, hcft, hcfi, hm, hv, hl, hled, hc, hla, happ, htransfer, hsnap, hbase⟩ := htr
  subst hm
  exact (RaftVeil.Lemmas.sub_empty m).elim

prove_veil_invariant_goal initializer LedExtendsReq using tr by
  obtain ⟨hct, hvt, hvf, hlog, hrole, hci, hcft, hcfi, hm, hv, hl, hled, hc, hla, happ, htransfer, hsnap, hbase⟩ := htr
  subst hl
  exact (RaftVeil.Lemmas.sub_empty ld).elim

prove_veil_invariant_goal initializer AckFacts using tr by
  obtain ⟨hct, hvt, hvf, hlog, hrole, hci, hcft, hcfi, hm, hv, hl, hled, hc, hla, happ, htransfer, hsnap, hbase⟩ := htr
  subst hm
  exact (RaftVeil.Lemmas.sub_empty m).elim

prove_veil_invariant_goal initializer AckedHeld using tr by
  obtain ⟨hct, hvt, hvf, hlog, hrole, hci, hcft, hcfi, hm, hv, hl, hled, hc, hla, happ, htransfer, hsnap, hbase⟩ := htr
  intro h
  have h1 := h.1
  rw [← hled t] at h1
  cases h1

prove_veil_invariant_goal initializer AckVote using tr by
  obtain ⟨hct, hvt, hvf, hlog, hrole, hci, hcft, hcfi, hm, hv, hl, hled, hc, hla, happ, htransfer, hsnap, hbase⟩ := htr
  intro v h
  have h1 := h.1
  rw [← hled t] at h1
  cases h1

prove_veil_invariant_goal initializer EarlyQuorum using tr by
  obtain ⟨hct, hvt, hvf, hlog, hrole, hci, hcft, hcfi, hm, hv, hl, hled, hc, hla, happ, htransfer, hsnap, hbase⟩ := htr
  subst hl
  exact (RaftVeil.Lemmas.sub_empty ld).elim

prove_veil_invariant_goal initializer ConfirmedIsLed using tr by
  obtain ⟨hct, hvt, hvf, hlog, hrole, hci, hcft, hcfi, hm, hv, hl, hled, hc, hla, happ, htransfer, hsnap, hbase⟩ := htr
  exact Or.inl (hcfi j).symm

prove_veil_invariant_goal initializer CommitRoot using tr by
  obtain ⟨hct, hvt, hvf, hlog, hrole, hci, hcft, hcfi, hm, hv, hl, hled, hc, hla, happ, htransfer, hsnap, hbase⟩ := htr
  subst hc
  exact (RaftVeil.Lemmas.sub_empty k).elim

prove_veil_invariant_goal initializer CommitSafety using tr by
  obtain ⟨hct, hvt, hvf, hlog, hrole, hci, hcft, hcfi, hm, hv, hl, hled, hc, hla, happ, htransfer, hsnap, hbase⟩ := htr
  subst hc
  exact (RaftVeil.Lemmas.sub_empty a).elim

prove_veil_invariant_goal initializer ConfirmedTermBound using tr by
  obtain ⟨hct, hvt, hvf, hlog, hrole, hci, hcft, hcfi, hm, hv, hl, hled, hc, hla, happ, htransfer, hsnap, hbase⟩ := htr
  rw [← hct i, ← hcft i]
  exact Nat.zero_le 1

prove_veil_invariant_goal initializer CommitTermBound using tr by
  obtain ⟨hct, hvt, hvf, hlog, hrole, hci, hcft, hcfi, hm, hv, hl, hled, hc, hla, happ, htransfer, hsnap, hbase⟩ := htr
  subst hc
  exact (RaftVeil.Lemmas.sub_empty c).elim

prove_veil_invariant_goal initializer CommittedEntriesPreserved using tr by
  obtain ⟨hct, hvt, hvf, hlog, hrole, hci, hcft, hcfi, hm, hv, hl, hled, hc, hla, happ, htransfer, hsnap, hbase⟩ := htr
  subst hc
  exact (RaftVeil.Lemmas.sub_empty c).elim

prove_veil_invariant_goal initializer CommitIndexCommitted using tr by
  obtain ⟨hct, hvt, hvf, hlog, hrole, hci, hcft, hcfi, hm, hv, hl, hled, hc, hla, happ, htransfer, hsnap, hbase⟩ := htr
  exact Or.inl (hci i).symm

prove_veil_invariant_goal initializer AppliedCommitted using tr by
  obtain ⟨hct, hvt, hvf, hlog, hrole, hci, hcft, hcfi, hm, hv, hl, hled, hc, hla, happ, htransfer, hsnap, hbase⟩ := htr
  subst happ
  exact (RaftVeil.Lemmas.sub_empty a).elim

prove_veil_invariant_goal initializer StateMachineSafety using tr by
  obtain ⟨hct, hvt, hvf, hlog, hrole, hci, hcft, hcfi, hm, hv, hl, hled, hc, hla, happ, htransfer, hsnap, hbase⟩ := htr
  subst happ
  exact (RaftVeil.Lemmas.sub_empty a).elim

prove_veil_invariant_goal initializer LeaderCompleteness using tr by
  obtain ⟨hct, hvt, hvf, hlog, hrole, hci, hcft, hcfi, hm, hv, hl, hled, hc, hla, happ, htransfer, hsnap, hbase⟩ := htr
  subst hc
  exact (RaftVeil.Lemmas.sub_empty c).elim

prove_veil_invariant_goal initializer ConfirmedWithinLog using tr by
  obtain ⟨hct, hvt, hvf, hlog, hrole, hci, hcft, hcfi, hm, hv, hl, hled, hc, hla, happ, htransfer, hsnap, hbase⟩ := htr
  rw [← hcfi i]
  exact Nat.zero_le _

prove_veil_invariant_goal initializer PreVoteRequestsBounded using tr by
  obtain ⟨hct, hvt, hvf, hlog, hrole, hci, hcft, hcfi, hm, hv, hl, hled, hc, hla, happ, htransfer, hsnap, hbase⟩ := htr
  subst hm
  intros
  exact (RaftVeil.Lemmas.sub_empty m).elim

prove_veil_invariant_goal initializer PreGrantsAnswer using tr by
  obtain ⟨hct, hvt, hvf, hlog, hrole, hci, hcft, hcfi, hm, hv, hl, hled, hc, hla, happ, htransfer, hsnap, hbase⟩ := htr
  subst hm
  intros
  exact (RaftVeil.Lemmas.sub_empty a).elim

prove_veil_invariant_goal initializer TimeoutNowFromLeader using tr by
  obtain ⟨hct, hvt, hvf, hlog, hrole, hci, hcft, hcfi, hm, hv, hl, hled, hc, hla, happ, htransfer, hsnap, hbase⟩ := htr
  subst hm
  intros
  exact (RaftVeil.Lemmas.sub_empty m).elim

prove_veil_invariant_goal initializer TransferIsCandidate using tr by
  obtain ⟨hct, hvt, hvf, hlog, hrole, hci, hcft, hcfi, hm, hv, hl, hled, hc, hla, happ, htransfer, hsnap, hbase⟩ := htr
  intro h
  rw [htransfer i] at h
  cases h

prove_veil_invariant_goal initializer SnapshotWithinLog using tr by
  obtain ⟨hct, hvt, hvf, hlog, hrole, hci, hcft, hcfi, hm, hv, hl, hled, hc, hla, happ, htransfer, hsnap, hbase⟩ := htr
  intros
  simp only [hsnap, hbase, hlog, hla, IsPrefix, List.length_nil, List.take_zero, SubSeq] at *
  first | rfl | omega | simp | grind

prove_veil_invariant_goal initializer BaseWithinSnapshot using tr by
  obtain ⟨hct, hvt, hvf, hlog, hrole, hci, hcft, hcfi, hm, hv, hl, hled, hc, hla, happ, htransfer, hsnap, hbase⟩ := htr
  rw [← hbase i]
  exact Nat.zero_le _

prove_veil_invariant_goal initializer SnapshotCommitted using tr by
  obtain ⟨hct, hvt, hvf, hlog, hrole, hci, hcft, hcfi, hm, hv, hl, hled, hc, hla, happ, htransfer, hsnap, hbase⟩ := htr
  intros
  simp only [hsnap, hbase, hlog, hla, IsPrefix, List.length_nil, List.take_zero, SubSeq] at *
  first | rfl | omega | simp | grind

prove_veil_invariant_goal initializer SnapshotApplied using tr by
  obtain ⟨hct, hvt, hvf, hlog, hrole, hci, hcft, hcfi, hm, hv, hl, hled, hc, hla, happ, htransfer, hsnap, hbase⟩ := htr
  intros
  simp only [hsnap, hbase, hlog, hla, IsPrefix, List.length_nil, List.take_zero, SubSeq] at *
  first | rfl | omega | simp | grind

-- BecomeCandidate

prove_veil_invariant_goal BecomeCandidate ElectionSafety using wp by
  have hElectionSafety := hinv.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeCandidate OneVotePerTerm using wp by
  have hOneVotePerTerm := hinv.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeCandidate VoteTermBound using wp by
  have hVoteTermBound := hinv.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeCandidate VotesBound using wp by
  have hVotesBound := hinv.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeCandidate GrantsAreVotes using wp by
  have hGrantsAreVotes := hinv.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeCandidate LeadersHaveQuorum using wp by
  have hLeadersHaveQuorum := hinv.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeCandidate LeaderIsElected using wp by
  have hLeaderIsElected := hinv.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeCandidate LeadersTermBound using wp by
  have hLeadersTermBound := hinv.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeCandidate LedOwner using wp by
  have hLedOwner := hinv.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeCandidate LeadersHaveLed using wp by
  have hLeadersHaveLed := hinv.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeCandidate LedHasLeader using wp by
  have hLedHasLeader := hinv.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeCandidate AppendFromLeader using wp by
  have hAppendFromLeader := hinv.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeCandidate LeaderLogIsLed using wp by
  have hLeaderLogIsLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeCandidate RequestsFromLed using wp by
  have hRequestsFromLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeCandidate BootEntry using wp by
  have hBootEntry := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeCandidate LedBoot using wp by
  have hLedBoot := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeCandidate LogFromLed using wp by
  have hLogFromLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeCandidate LedFromLed using wp by
  have hLedFromLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeCandidate LogMatching using wp by
  have hLogMatching := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeCandidate TermsPositive using wp by
  have hTermsPositive := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeCandidate LogTermsBound using wp by
  have hLogTermsBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeCandidate LedSorted using wp by
  have hLedSorted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeCandidate ReqFacts using wp by
  have hReqFacts := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeCandidate ReqUnique using wp by
  have hReqUnique := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeCandidate VoteHasReq using wp by
  have hVoteHasReq := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeCandidate CandLog using wp by
  have hCandLog := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeCandidate LedExtendsReq using wp by
  have hLedExtendsReq := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeCandidate AckFacts using wp by
  have hAckFacts := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeCandidate AckedHeld using wp by
  have hAckedHeld := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeCandidate AckVote using wp by
  have hAckVote := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeCandidate EarlyQuorum using wp by
  have hEarlyQuorum := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeCandidate ConfirmedIsLed using wp by
  have hConfirmedIsLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeCandidate CommitRoot using wp by
  have hCommitRoot := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeCandidate CommitSafety using wp by
  have hCommitSafety := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeCandidate ConfirmedTermBound using wp by
  have hConfirmedTermBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeCandidate CommitTermBound using wp by
  have hCommitTermBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeCandidate CommittedEntriesPreserved using wp by
  have hCommittedEntriesPreserved := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeCandidate CommitIndexCommitted using wp by
  have hCommitIndexCommitted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeCandidate AppliedCommitted using wp by
  have hAppliedCommitted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeCandidate StateMachineSafety using wp by
  have hStateMachineSafety := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeCandidate LeaderCompleteness using wp by
  have hLeaderCompleteness := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeCandidate ConfirmedWithinLog using wp by
  have hConfirmedWithinLog := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeCandidate PreVoteRequestsBounded using wp by
  have hPreVoteRequestsBounded := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeCandidate PreGrantsAnswer using wp by
  have hPreGrantsAnswer := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeCandidate TimeoutNowFromLeader using wp by
  have hTimeoutNowFromLeader := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeCandidate TransferIsCandidate using wp by
  have hTransferIsCandidate := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeCandidate SnapshotWithinLog using wp by
  have hSnapshotWithinLog := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeCandidate BaseWithinSnapshot using wp by
  have hBaseWithinSnapshot := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeCandidate SnapshotCommitted using wp by
  have hSnapshotCommitted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeCandidate SnapshotApplied using wp by
  have hSnapshotApplied := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

-- BecomeFollower

prove_veil_invariant_goal BecomeFollower ElectionSafety using wp by
  have hElectionSafety := hinv.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeFollower OneVotePerTerm using wp by
  have hOneVotePerTerm := hinv.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeFollower VoteTermBound using wp by
  have hVoteTermBound := hinv.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeFollower VotesBound using wp by
  have hVotesBound := hinv.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeFollower GrantsAreVotes using wp by
  have hGrantsAreVotes := hinv.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeFollower LeadersHaveQuorum using wp by
  have hLeadersHaveQuorum := hinv.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeFollower LeaderIsElected using wp by
  have hLeaderIsElected := hinv.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeFollower LeadersTermBound using wp by
  have hLeadersTermBound := hinv.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeFollower LedOwner using wp by
  have hLedOwner := hinv.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeFollower LeadersHaveLed using wp by
  have hLeadersHaveLed := hinv.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeFollower LedHasLeader using wp by
  have hLedHasLeader := hinv.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeFollower AppendFromLeader using wp by
  have hAppendFromLeader := hinv.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeFollower LeaderLogIsLed using wp by
  have hLeaderLogIsLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeFollower RequestsFromLed using wp by
  have hRequestsFromLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeFollower BootEntry using wp by
  have hBootEntry := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeFollower LedBoot using wp by
  have hLedBoot := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeFollower LogFromLed using wp by
  have hLogFromLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeFollower LedFromLed using wp by
  have hLedFromLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeFollower LogMatching using wp by
  have hLogMatching := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeFollower TermsPositive using wp by
  have hTermsPositive := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeFollower LogTermsBound using wp by
  have hLogTermsBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeFollower LedSorted using wp by
  have hLedSorted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeFollower ReqFacts using wp by
  have hReqFacts := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeFollower ReqUnique using wp by
  have hReqUnique := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeFollower VoteHasReq using wp by
  have hVoteHasReq := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeFollower CandLog using wp by
  have hCandLog := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeFollower LedExtendsReq using wp by
  have hLedExtendsReq := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeFollower AckFacts using wp by
  have hAckFacts := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeFollower AckedHeld using wp by
  have hAckedHeld := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeFollower AckVote using wp by
  have hAckVote := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeFollower EarlyQuorum using wp by
  have hEarlyQuorum := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeFollower ConfirmedIsLed using wp by
  have hConfirmedIsLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeFollower CommitRoot using wp by
  have hCommitRoot := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeFollower CommitSafety using wp by
  have hCommitSafety := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeFollower ConfirmedTermBound using wp by
  have hConfirmedTermBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeFollower CommitTermBound using wp by
  have hCommitTermBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeFollower CommittedEntriesPreserved using wp by
  have hCommittedEntriesPreserved := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeFollower CommitIndexCommitted using wp by
  have hCommitIndexCommitted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeFollower AppliedCommitted using wp by
  have hAppliedCommitted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeFollower StateMachineSafety using wp by
  have hStateMachineSafety := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeFollower LeaderCompleteness using wp by
  have hLeaderCompleteness := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeFollower ConfirmedWithinLog using wp by
  have hConfirmedWithinLog := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeFollower PreVoteRequestsBounded using wp by
  have hPreVoteRequestsBounded := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeFollower PreGrantsAnswer using wp by
  have hPreGrantsAnswer := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeFollower TimeoutNowFromLeader using wp by
  have hTimeoutNowFromLeader := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeFollower TransferIsCandidate using wp by
  have hTransferIsCandidate := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeFollower SnapshotWithinLog using wp by
  have hSnapshotWithinLog := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeFollower BaseWithinSnapshot using wp by
  have hBaseWithinSnapshot := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeFollower SnapshotCommitted using wp by
  have hSnapshotCommitted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeFollower SnapshotApplied using wp by
  have hSnapshotApplied := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

-- StartElection

prove_veil_invariant_goal StartElection ElectionSafety using wp by
  have hElectionSafety := hinv.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StartElection OneVotePerTerm using wp by
  have hOneVotePerTerm := hinv.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StartElection VoteTermBound using wp by
  have hVoteTermBound := hinv.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StartElection VotesBound using wp by
  have hVotesBound := hinv.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StartElection GrantsAreVotes using wp by
  have hGV := hinv.2.2.2.2.1
  clear hinv
  intros
  simp only [RaftVeil.Lemmas.mem_iff, RaftVeil.Lemmas.contains_insert_iff] at *
  repeat' split
  all_goals grind only

prove_veil_invariant_goal StartElection LeadersHaveQuorum using wp by
  have hLeadersHaveQuorum := hinv.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StartElection LeaderIsElected using wp by
  have hLeaderIsElected := hinv.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StartElection LeadersTermBound using wp by
  have hLeadersTermBound := hinv.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StartElection LedOwner using wp by
  have hLeadersTermBound := hinv.2.2.2.2.2.2.2.1
  have hLedOwner := hinv.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StartElection LeadersHaveLed using wp by
  have hLeadersHaveLed := hinv.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StartElection LedHasLeader using wp by
  have hLedHasLeader := hinv.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StartElection AppendFromLeader using wp by
  have hAppendFromLeader := hinv.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StartElection LeaderLogIsLed using wp by
  have hLeaderLogIsLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StartElection RequestsFromLed using wp by
  have hRequestsFromLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StartElection BootEntry using wp by
  have hBootEntry := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StartElection LedBoot using wp by
  have hLedBoot := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StartElection LogFromLed using wp by
  have hLogFromLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StartElection LedFromLed using wp by
  have hLedFromLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StartElection LogMatching using wp by
  have hLogMatching := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StartElection TermsPositive using wp by
  have hTermsPositive := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StartElection LogTermsBound using wp by
  have hLogTermsBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StartElection LedSorted using wp by
  have hLedSorted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StartElection ReqFacts using wp by
  have hBoot := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLFL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLogTB := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hRF := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro hrole hmay a ha c u li lt heq
  rw [RaftVeil.Lemmas.mem_insert] at ha
  rcases ha with rfl | ha
  · injection heq with h1 h2 h3 h4
    subst h1 h2 h3 h4
    rw [RaftVeil.Lemmas.ifPos rfl]
    exact ⟨Nat.le_refl _, reqOk_of_log _ _ _ (hLFL i) (hBoot i) (Nat.lt_succ_of_le (hLogTB i _))⟩
  · obtain ⟨h1, h2⟩ := hRF a ha c u li lt heq
    refine ⟨?_, h2⟩
    by_cases hic : i = c
    · subst hic; rw [RaftVeil.Lemmas.ifPos rfl]; omega
    · rw [RaftVeil.Lemmas.ifNeg hic]; exact h1

prove_veil_invariant_goal StartElection ReqUnique using wp by
  have hReqFacts := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hReqUnique := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StartElection VoteHasReq using wp by
  have hVoteHasReq := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StartElection CandLog using wp by
  have hReqFacts := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hCandLog := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StartElection LedExtendsReq using wp by
  have hLeadersTermBound := hinv.2.2.2.2.2.2.2.1
  have hLedExtendsReq := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StartElection AckFacts using wp by
  have hAckFacts := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StartElection AckedHeld using wp by
  have hAH := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro hrole hmay n t A c hack
  have hack' := Acked.of_insert _ _ _ _ _ _ _ _ (fun _ _ _ _ h => by cases h) hack
  rcases hAH n t A c hack' with h | h
  · exact Or.inl h
  · right
    by_cases hin : i = n
    · subst hin; rw [RaftVeil.Lemmas.ifPos rfl]; exact LostIn.mono_hi _ _ _ _ _ _ h (by omega)
    · rw [RaftVeil.Lemmas.ifNeg hin]; exact h

prove_veil_invariant_goal StartElection AckVote using wp by
  have hRF := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hVHR := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hAV := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro v hrole hmay n t A c hack hv hvn htv li lt hreq
  rcases (RaftVeil.Lemmas.contains_insert_iff _ _ _).1 hreq with h | h
  · exfalso
    injection h with h1 h2
    obtain ⟨m, hm, li', lt', rfl⟩ := hVHR v hv
    have := (hRF _ hm v.cand v.term li' lt' rfl).1
    rw [h1, h2] at this
    omega
  · exact hAV v n t A c (Acked.of_insert _ _ _ _ _ _ _ _ (fun _ _ _ _ h => by cases h) hack) hv hvn htv li lt h

prove_veil_invariant_goal StartElection EarlyQuorum using wp by
  have hLTB := hinv.2.2.2.2.2.2.2.1
  have hEQ := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro ld hrole hmay hld
  refine IsQuorum.mono _ _ ?_ (hEQ ld hld)
  intro n hn
  simp only [decide_eq_true_eq] at hn ⊢
  refine ⟨hn.1, Early.of_insert _ _ _ _ _ _ _ (fun _ _ _ _ h => by cases h) ?_ hn.2⟩
  intro li lt h
  injection h with h1 h2
  have := hLTB ld hld
  rw [← h2, ← h1] at this
  omega

prove_veil_invariant_goal StartElection ConfirmedIsLed using wp by
  have hConfirmedIsLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StartElection CommitRoot using wp by
  have hCR := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro k
  intros
  rename_i hk
  obtain ⟨h1, r, h2, h3, h4, h5⟩ := hCR k hk
  exact ⟨h1, r, h2, Root.mono _ _ _ _ _ _ _ (fun a ha => (RaftVeil.Lemmas.mem_insert _ _ _).2 (Or.inr ha))
    (fun a ha => ha) (LedGrows.refl _) h3, h4, h5⟩

prove_veil_invariant_goal StartElection CommitSafety using wp by
  have hCommitSafety := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StartElection ConfirmedTermBound using wp by
  have hConfirmedTermBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StartElection CommitTermBound using wp by
  have hCommitTermBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StartElection CommittedEntriesPreserved using wp by
  have hCommittedEntriesPreserved := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StartElection CommitIndexCommitted using wp by
  have hCommitIndexCommitted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StartElection AppliedCommitted using wp by
  have hAppliedCommitted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StartElection StateMachineSafety using wp by
  have hStateMachineSafety := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StartElection LeaderCompleteness using wp by
  have hLeaderCompleteness := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StartElection ConfirmedWithinLog using wp by
  have hConfirmedWithinLog := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StartElection PreVoteRequestsBounded using wp by
  have hPreVoteRequestsBounded := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StartElection PreGrantsAnswer using wp by
  have hPGA := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  rename_i a ha
  rw [RaftVeil.Lemmas.mem_insert] at ha
  rcases ha with rfl | ha
  · rfl
  · refine pregrants_mono _ _ a (hPGA a ha) ?_
    intro d t hx
    simp only [decide_eq_true_eq] at hx ⊢
    obtain ⟨⟨m, hm⟩, hm2⟩ := hx
    exact ⟨⟨m, (RaftVeil.Lemmas.mem_insert _ _ _).2 (Or.inr hm)⟩, hm2⟩

prove_veil_invariant_goal StartElection TimeoutNowFromLeader using wp by
  have hTimeoutNowFromLeader := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StartElection TransferIsCandidate using wp by
  have hTransferIsCandidate := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StartElection SnapshotWithinLog using wp by
  have hSnapshotWithinLog := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StartElection BaseWithinSnapshot using wp by
  have hBaseWithinSnapshot := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StartElection SnapshotCommitted using wp by
  have hSnapshotCommitted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StartElection SnapshotApplied using wp by
  have hSnapshotApplied := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

-- AdoptTerm

prove_veil_invariant_goal AdoptTerm ElectionSafety using wp by
  have hElectionSafety := hinv.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal AdoptTerm OneVotePerTerm using wp by
  have hOneVotePerTerm := hinv.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal AdoptTerm VoteTermBound using wp by
  have hVoteTermBound := hinv.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal AdoptTerm VotesBound using wp by
  have hVotesBound := hinv.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal AdoptTerm GrantsAreVotes using wp by
  have hGrantsAreVotes := hinv.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal AdoptTerm LeadersHaveQuorum using wp by
  have hLeadersHaveQuorum := hinv.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal AdoptTerm LeaderIsElected using wp by
  have hLeaderIsElected := hinv.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal AdoptTerm LeadersTermBound using wp by
  have hLeadersTermBound := hinv.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal AdoptTerm LedOwner using wp by
  have hLeadersTermBound := hinv.2.2.2.2.2.2.2.1
  have hLedOwner := hinv.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal AdoptTerm LeadersHaveLed using wp by
  have hLeadersHaveLed := hinv.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal AdoptTerm LedHasLeader using wp by
  have hLedHasLeader := hinv.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal AdoptTerm AppendFromLeader using wp by
  have hAppendFromLeader := hinv.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal AdoptTerm LeaderLogIsLed using wp by
  have hLeaderLogIsLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal AdoptTerm RequestsFromLed using wp by
  have hRequestsFromLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal AdoptTerm BootEntry using wp by
  have hBootEntry := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal AdoptTerm LedBoot using wp by
  have hLedBoot := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal AdoptTerm LogFromLed using wp by
  have hLogFromLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal AdoptTerm LedFromLed using wp by
  have hLedFromLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal AdoptTerm LogMatching using wp by
  have hLogMatching := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal AdoptTerm TermsPositive using wp by
  have hTermsPositive := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal AdoptTerm LogTermsBound using wp by
  have hLogTermsBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal AdoptTerm LedSorted using wp by
  have hLedSorted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal AdoptTerm ReqFacts using wp by
  have hReqFacts := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal AdoptTerm ReqUnique using wp by
  have hReqUnique := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal AdoptTerm VoteHasReq using wp by
  have hVoteHasReq := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal AdoptTerm CandLog using wp by
  have hReqFacts := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hCandLog := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal AdoptTerm LedExtendsReq using wp by
  have hLedExtendsReq := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal AdoptTerm AckFacts using wp by
  have hAckFacts := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal AdoptTerm AckedHeld using wp by
  have hAH := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro hlt k' hk' hge n t A c hack'
  rcases hAH n t A c hack' with h | h
  · exact Or.inl h
  · right
    by_cases hin : i = n
    · subst hin; rw [RaftVeil.Lemmas.ifPos rfl]; exact LostIn.mono_hi _ _ _ _ _ _ h (by omega)
    · rw [RaftVeil.Lemmas.ifNeg hin]; exact h

prove_veil_invariant_goal AdoptTerm AckVote using wp by
  have hAckVote := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal AdoptTerm EarlyQuorum using wp by
  have hEarlyQuorum := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal AdoptTerm ConfirmedIsLed using wp by
  have hConfirmedIsLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal AdoptTerm CommitRoot using wp by
  have hCommitRoot := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal AdoptTerm CommitSafety using wp by
  have hCommitSafety := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal AdoptTerm ConfirmedTermBound using wp by
  have hConfirmedTermBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal AdoptTerm CommitTermBound using wp by
  have hCommitTermBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal AdoptTerm CommittedEntriesPreserved using wp by
  have hCommittedEntriesPreserved := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal AdoptTerm CommitIndexCommitted using wp by
  have hCommitIndexCommitted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal AdoptTerm AppliedCommitted using wp by
  have hAppliedCommitted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal AdoptTerm StateMachineSafety using wp by
  have hStateMachineSafety := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal AdoptTerm LeaderCompleteness using wp by
  have hLeaderCompleteness := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal AdoptTerm ConfirmedWithinLog using wp by
  have hConfirmedWithinLog := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal AdoptTerm PreVoteRequestsBounded using wp by
  have hPreVoteRequestsBounded := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal AdoptTerm PreGrantsAnswer using wp by
  have hPreGrantsAnswer := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal AdoptTerm TimeoutNowFromLeader using wp by
  have hTimeoutNowFromLeader := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal AdoptTerm TransferIsCandidate using wp by
  have hTransferIsCandidate := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal AdoptTerm SnapshotWithinLog using wp by
  have hSnapshotWithinLog := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal AdoptTerm BaseWithinSnapshot using wp by
  have hBaseWithinSnapshot := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal AdoptTerm SnapshotCommitted using wp by
  have hSnapshotCommitted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal AdoptTerm SnapshotApplied using wp by
  have hSnapshotApplied := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

-- SetVoteFor

prove_veil_invariant_goal SetVoteFor ElectionSafety using wp by
  have hElectionSafety := hinv.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SetVoteFor OneVotePerTerm using wp by
  have hOneVotePerTerm := hinv.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SetVoteFor VoteTermBound using wp by
  have hVoteTermBound := hinv.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SetVoteFor VotesBound using wp by
  have hVotesBound := hinv.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SetVoteFor GrantsAreVotes using wp by
  have hGrantsAreVotes := hinv.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SetVoteFor LeadersHaveQuorum using wp by
  have hLeadersHaveQuorum := hinv.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SetVoteFor LeaderIsElected using wp by
  have hLeaderIsElected := hinv.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SetVoteFor LeadersTermBound using wp by
  have hLeadersTermBound := hinv.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SetVoteFor LedOwner using wp by
  have hLedOwner := hinv.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SetVoteFor LeadersHaveLed using wp by
  have hLeadersHaveLed := hinv.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SetVoteFor LedHasLeader using wp by
  have hLedHasLeader := hinv.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SetVoteFor AppendFromLeader using wp by
  have hAppendFromLeader := hinv.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SetVoteFor LeaderLogIsLed using wp by
  have hLeaderLogIsLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SetVoteFor RequestsFromLed using wp by
  have hRequestsFromLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SetVoteFor BootEntry using wp by
  have hBootEntry := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SetVoteFor LedBoot using wp by
  have hLedBoot := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SetVoteFor LogFromLed using wp by
  have hLogFromLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SetVoteFor LedFromLed using wp by
  have hLedFromLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SetVoteFor LogMatching using wp by
  have hLogMatching := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SetVoteFor TermsPositive using wp by
  have hTermsPositive := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SetVoteFor LogTermsBound using wp by
  have hLogTermsBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SetVoteFor LedSorted using wp by
  have hLedSorted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SetVoteFor ReqFacts using wp by
  have hReqFacts := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SetVoteFor ReqUnique using wp by
  have hReqUnique := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SetVoteFor VoteHasReq using wp by
  have hVoteHasReq := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SetVoteFor CandLog using wp by
  have hCandLog := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SetVoteFor LedExtendsReq using wp by
  have hLedExtendsReq := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SetVoteFor AckFacts using wp by
  have hAckFacts := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SetVoteFor AckedHeld using wp by
  have hAckedHeld := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SetVoteFor AckVote using wp by
  have hAckVote := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SetVoteFor EarlyQuorum using wp by
  have hEarlyQuorum := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SetVoteFor ConfirmedIsLed using wp by
  have hConfirmedIsLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SetVoteFor CommitRoot using wp by
  have hCommitRoot := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SetVoteFor CommitSafety using wp by
  have hCommitSafety := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SetVoteFor ConfirmedTermBound using wp by
  have hConfirmedTermBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SetVoteFor CommitTermBound using wp by
  have hCommitTermBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SetVoteFor CommittedEntriesPreserved using wp by
  have hCommittedEntriesPreserved := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SetVoteFor CommitIndexCommitted using wp by
  have hCommitIndexCommitted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SetVoteFor AppliedCommitted using wp by
  have hAppliedCommitted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SetVoteFor StateMachineSafety using wp by
  have hStateMachineSafety := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SetVoteFor LeaderCompleteness using wp by
  have hLeaderCompleteness := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SetVoteFor ConfirmedWithinLog using wp by
  have hConfirmedWithinLog := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SetVoteFor PreVoteRequestsBounded using wp by
  have hPreVoteRequestsBounded := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SetVoteFor PreGrantsAnswer using wp by
  have hPreGrantsAnswer := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SetVoteFor TimeoutNowFromLeader using wp by
  have hTimeoutNowFromLeader := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SetVoteFor TransferIsCandidate using wp by
  have hTransferIsCandidate := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SetVoteFor SnapshotWithinLog using wp by
  have hSnapshotWithinLog := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SetVoteFor BaseWithinSnapshot using wp by
  have hBaseWithinSnapshot := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SetVoteFor SnapshotCommitted using wp by
  have hSnapshotCommitted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SetVoteFor SnapshotApplied using wp by
  have hSnapshotApplied := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

-- SetVoteTerm

prove_veil_invariant_goal SetVoteTerm ElectionSafety using wp by
  have hElectionSafety := hinv.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SetVoteTerm OneVotePerTerm using wp by
  have hOneVotePerTerm := hinv.2.1
  have hVoteTermBound := hinv.2.2.1
  have hVotesBound := hinv.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SetVoteTerm VoteTermBound using wp by
  have hVoteTermBound := hinv.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SetVoteTerm VotesBound using wp by
  have hVT := hinv.2.2.1
  have hVB := hinv.2.2.2.1
  clear hinv
  intro a hvf hne x hx hmay hb
  rw [RaftVeil.Lemmas.mem_insert] at hb
  rcases hb with rfl | hb
  · simp
  · have h1 := hVB a hb
    have h2 := hVT a.voter
    by_cases h : i = a.voter
    · subst h; simp; omega
    · simp [h]; exact h1

prove_veil_invariant_goal SetVoteTerm GrantsAreVotes using wp by
  have hGrantsAreVotes := hinv.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SetVoteTerm LeadersHaveQuorum using wp by
  have hLQ := hinv.2.2.2.2.2.1
  clear hinv
  intros
  refine IsQuorum.mono _ _ ?_ (hLQ _ ‹_ ∈ st.leaders›)
  intro j hj
  simp only [RaftVeil.Lemmas.contains_insert_iff, hj, or_true]

prove_veil_invariant_goal SetVoteTerm LeaderIsElected using wp by
  have hLeaderIsElected := hinv.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SetVoteTerm LeadersTermBound using wp by
  have hLeadersTermBound := hinv.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SetVoteTerm LedOwner using wp by
  have hLedOwner := hinv.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SetVoteTerm LeadersHaveLed using wp by
  have hLeadersHaveLed := hinv.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SetVoteTerm LedHasLeader using wp by
  have hLedHasLeader := hinv.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SetVoteTerm AppendFromLeader using wp by
  have hAppendFromLeader := hinv.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SetVoteTerm LeaderLogIsLed using wp by
  have hLeaderLogIsLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SetVoteTerm RequestsFromLed using wp by
  have hRequestsFromLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SetVoteTerm BootEntry using wp by
  have hBootEntry := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SetVoteTerm LedBoot using wp by
  have hLedBoot := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SetVoteTerm LogFromLed using wp by
  have hLogFromLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SetVoteTerm LedFromLed using wp by
  have hLedFromLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SetVoteTerm LogMatching using wp by
  have hLogMatching := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SetVoteTerm TermsPositive using wp by
  have hTermsPositive := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SetVoteTerm LogTermsBound using wp by
  have hLogTermsBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SetVoteTerm LedSorted using wp by
  have hLedSorted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SetVoteTerm ReqFacts using wp by
  have hReqFacts := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SetVoteTerm ReqUnique using wp by
  have hReqUnique := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SetVoteTerm VoteHasReq using wp by
  have hVoteHasReq := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SetVoteTerm CandLog using wp by
  have hCandLog := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SetVoteTerm LedExtendsReq using wp by
  have hLedExtendsReq := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SetVoteTerm AckFacts using wp by
  have hAckFacts := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SetVoteTerm AckedHeld using wp by
  have hAckedHeld := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SetVoteTerm AckVote using wp by
  have hBoot := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLFL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLS := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hRF := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hRU := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hAF := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hAH := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hAV := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro v hvf hne x hx hmay n t A c1 hack hv hvn htv li lt hreq
  rw [RaftVeil.Lemmas.mem_insert] at hv
  rcases hv with rfl | hv
  · subst hvn
    cases x with
    | vote src term lli llt =>
      simp only [decide_eq_true_eq] at hmay
      obtain ⟨rfl, rfl, hup⟩ := hmay
      obtain ⟨rfl, rfl⟩ := hRU _ hx _ hreq src (st.currentTerm i) lli llt li lt rfl rfl
      have hcA := Acked.le_length _ _ _ _ _ _ _ (fun i' x' hx' => (hAF _ hx' i i' t x' rfl).2.2) hack
      refine vote_step st.ledLog (st.log i) A t c1 lli llt (st.currentTerm i) hack.1 hack.2.1 hcA
        hack.2.2.1 (hAH i t A c1 hack) (hLFL i) (hBoot i) hLS (hRF _ hx src _ lli llt rfl).2 ?_
      rcases hup with h | ⟨h1, h2⟩
      · exact Or.inl h
      · exact Or.inr ⟨h1, h2⟩
    | _ => simp at hmay
  · exact hAV v n t A c1 hack hv hvn htv li lt hreq

prove_veil_invariant_goal SetVoteTerm EarlyQuorum using wp by
  have hEQ := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro ld
  intros
  rename_i hld
  refine IsQuorum.mono _ _ ?_ (hEQ ld hld)
  intro n hn
  simp only [decide_eq_true_eq] at hn ⊢
  exact ⟨(RaftVeil.Lemmas.contains_insert_iff _ _ _).2 (Or.inr hn.1), hn.2⟩

prove_veil_invariant_goal SetVoteTerm ConfirmedIsLed using wp by
  have hConfirmedIsLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SetVoteTerm CommitRoot using wp by
  have hCommitRoot := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SetVoteTerm CommitSafety using wp by
  have hCommitSafety := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SetVoteTerm ConfirmedTermBound using wp by
  have hConfirmedTermBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SetVoteTerm CommitTermBound using wp by
  have hCommitTermBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SetVoteTerm CommittedEntriesPreserved using wp by
  have hCommittedEntriesPreserved := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SetVoteTerm CommitIndexCommitted using wp by
  have hCommitIndexCommitted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SetVoteTerm AppliedCommitted using wp by
  have hAppliedCommitted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SetVoteTerm StateMachineSafety using wp by
  have hStateMachineSafety := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SetVoteTerm LeaderCompleteness using wp by
  have hLeaderCompleteness := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SetVoteTerm ConfirmedWithinLog using wp by
  have hConfirmedWithinLog := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SetVoteTerm PreVoteRequestsBounded using wp by
  have hPreVoteRequestsBounded := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SetVoteTerm PreGrantsAnswer using wp by
  have hPreGrantsAnswer := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SetVoteTerm TimeoutNowFromLeader using wp by
  have hTimeoutNowFromLeader := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SetVoteTerm TransferIsCandidate using wp by
  have hTransferIsCandidate := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SetVoteTerm SnapshotWithinLog using wp by
  have hSnapshotWithinLog := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SetVoteTerm BaseWithinSnapshot using wp by
  have hBaseWithinSnapshot := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SetVoteTerm SnapshotCommitted using wp by
  have hSnapshotCommitted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SetVoteTerm SnapshotApplied using wp by
  have hSnapshotApplied := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

-- GrantVote

prove_veil_invariant_goal GrantVote ElectionSafety using wp by
  have hElectionSafety := hinv.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal GrantVote OneVotePerTerm using wp by
  have hOneVotePerTerm := hinv.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal GrantVote VoteTermBound using wp by
  have hVoteTermBound := hinv.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal GrantVote VotesBound using wp by
  have hVotesBound := hinv.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal GrantVote GrantsAreVotes using wp by
  have hGV := hinv.2.2.2.2.1
  clear hinv
  intro ha hv hc m hm
  rw [RaftVeil.Lemmas.mem_insert] at hm
  rcases hm with rfl | hm
  · subst hv
    cases a
    exact ha
  · exact hGV m hm

prove_veil_invariant_goal GrantVote LeadersHaveQuorum using wp by
  have hLeadersHaveQuorum := hinv.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal GrantVote LeaderIsElected using wp by
  have hLeaderIsElected := hinv.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal GrantVote LeadersTermBound using wp by
  have hLeadersTermBound := hinv.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal GrantVote LedOwner using wp by
  have hLedOwner := hinv.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal GrantVote LeadersHaveLed using wp by
  have hLeadersHaveLed := hinv.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal GrantVote LedHasLeader using wp by
  have hLedHasLeader := hinv.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal GrantVote AppendFromLeader using wp by
  have hAppendFromLeader := hinv.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal GrantVote LeaderLogIsLed using wp by
  have hLeaderLogIsLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal GrantVote RequestsFromLed using wp by
  have hRequestsFromLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal GrantVote BootEntry using wp by
  have hBootEntry := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal GrantVote LedBoot using wp by
  have hLedBoot := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal GrantVote LogFromLed using wp by
  have hLogFromLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal GrantVote LedFromLed using wp by
  have hLedFromLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal GrantVote LogMatching using wp by
  have hLogMatching := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal GrantVote TermsPositive using wp by
  have hTermsPositive := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal GrantVote LogTermsBound using wp by
  have hLogTermsBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal GrantVote LedSorted using wp by
  have hLedSorted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal GrantVote ReqFacts using wp by
  have hReqFacts := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal GrantVote ReqUnique using wp by
  have hReqUnique := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal GrantVote VoteHasReq using wp by
  have hVoteHasReq := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal GrantVote CandLog using wp by
  have hCandLog := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal GrantVote LedExtendsReq using wp by
  have hLedExtendsReq := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal GrantVote AckFacts using wp by
  have hAckFacts := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal GrantVote AckedHeld using wp by
  have hAH := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  rename_i n t A c hack
  exact hAH n t A c (Acked.of_insert _ _ _ _ _ _ _ _ (fun _ _ _ _ h => by cases h) hack)

prove_veil_invariant_goal GrantVote AckVote using wp by
  have hAV := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro v
  intros
  rename_i n t A c hack hv hvn htv li lt hreq
  rcases (RaftVeil.Lemmas.contains_insert_iff _ _ _).1 hreq with h | h
  · cases h
  · exact hAV v n t A c (Acked.of_insert _ _ _ _ _ _ _ _ (fun _ _ _ _ h => by cases h) hack) hv hvn htv li lt h

prove_veil_invariant_goal GrantVote EarlyQuorum using wp by
  have hEQ := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro ld
  intros
  rename_i hld
  refine IsQuorum.mono _ _ ?_ (hEQ ld hld)
  intro n hn
  simp only [decide_eq_true_eq] at hn ⊢
  exact ⟨hn.1, Early.of_insert _ _ _ _ _ _ _ (fun _ _ _ _ h => by cases h) (fun _ _ h => by cases h) hn.2⟩

prove_veil_invariant_goal GrantVote ConfirmedIsLed using wp by
  have hConfirmedIsLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal GrantVote CommitRoot using wp by
  have hCR := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro k
  intros
  rename_i hk
  obtain ⟨h1, r, h2, h3, h4, h5⟩ := hCR k hk
  exact ⟨h1, r, h2, Root.mono _ _ _ _ _ _ _ (fun a ha => (RaftVeil.Lemmas.mem_insert _ _ _).2 (Or.inr ha))
    (fun a ha => ha) (LedGrows.refl _) h3, h4, h5⟩

prove_veil_invariant_goal GrantVote CommitSafety using wp by
  have hCommitSafety := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal GrantVote ConfirmedTermBound using wp by
  have hConfirmedTermBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal GrantVote CommitTermBound using wp by
  have hCommitTermBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal GrantVote CommittedEntriesPreserved using wp by
  have hCommittedEntriesPreserved := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal GrantVote CommitIndexCommitted using wp by
  have hCommitIndexCommitted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal GrantVote AppliedCommitted using wp by
  have hAppliedCommitted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal GrantVote StateMachineSafety using wp by
  have hStateMachineSafety := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal GrantVote LeaderCompleteness using wp by
  have hLeaderCompleteness := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal GrantVote ConfirmedWithinLog using wp by
  have hConfirmedWithinLog := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal GrantVote PreVoteRequestsBounded using wp by
  have hPreVoteRequestsBounded := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal GrantVote PreGrantsAnswer using wp by
  have hPGA := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  rename_i a ha
  rw [RaftVeil.Lemmas.mem_insert] at ha
  rcases ha with rfl | ha
  · rfl
  · refine pregrants_mono _ _ a (hPGA a ha) ?_
    intro d t hx
    simp only [decide_eq_true_eq] at hx ⊢
    obtain ⟨⟨m, hm⟩, hm2⟩ := hx
    exact ⟨⟨m, (RaftVeil.Lemmas.mem_insert _ _ _).2 (Or.inr hm)⟩, hm2⟩

prove_veil_invariant_goal GrantVote TimeoutNowFromLeader using wp by
  have hTimeoutNowFromLeader := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal GrantVote TransferIsCandidate using wp by
  have hTransferIsCandidate := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal GrantVote SnapshotWithinLog using wp by
  have hSnapshotWithinLog := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal GrantVote BaseWithinSnapshot using wp by
  have hBaseWithinSnapshot := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal GrantVote SnapshotCommitted using wp by
  have hSnapshotCommitted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal GrantVote SnapshotApplied using wp by
  have hSnapshotApplied := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

-- BecomeLeader

prove_veil_invariant_goal BecomeLeader ElectionSafety using wp by
  have hES := hinv.1
  have hOV := hinv.2.1
  have hGV := hinv.2.2.2.2.1
  have hLQ := hinv.2.2.2.2.2.1
  clear hinv
  intro a b hrole hq ha hb hterm
  have hq' : IsQuorum (fun j => TSet.contains { voter := j, term := st.currentTerm i, cand := i } st.votes) = true := by
    refine IsQuorum.mono _ _ ?_ hq
    intro j hj
    by_cases hji : j = i
    · subst hji; simpa using hj
    · simp only [hji, ite_false] at hj
      simpa using hGV _ hj
  have key : ∀ x : Elected server, x ∈ st.leaders → x.term = st.currentTerm i → x.server = i := by
    intro x hx hxt
    obtain ⟨j, h1, h2⟩ := IsQuorum.inter _ _ (hLQ x hx) hq'
    have := hOV _ _ h1 h2 rfl (by simpa using hxt)
    simpa using this
  rw [RaftVeil.Lemmas.mem_insert] at ha hb
  rcases ha with rfl | ha <;> rcases hb with rfl | hb
  · rfl
  · exact (key b hb (by simpa using hterm.symm)).symm
  · exact key a ha (by simpa using hterm)
  · exact hES a b ha hb hterm

prove_veil_invariant_goal BecomeLeader OneVotePerTerm using wp by
  have hOneVotePerTerm := hinv.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeLeader VoteTermBound using wp by
  have hVoteTermBound := hinv.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeLeader VotesBound using wp by
  have hVotesBound := hinv.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeLeader GrantsAreVotes using wp by
  have hGrantsAreVotes := hinv.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeLeader LeadersHaveQuorum using wp by
  have hGV := hinv.2.2.2.2.1
  have hLQ := hinv.2.2.2.2.2.1
  clear hinv
  intro a hrole hq ha
  rw [RaftVeil.Lemmas.mem_insert] at ha
  rcases ha with rfl | ha
  · refine IsQuorum.mono _ _ ?_ hq
    intro j hj
    by_cases hji : j = i
    · subst hji; simpa using hj
    · simp only [hji, ite_false] at hj
      simpa using hGV _ hj
  · exact hLQ a ha

prove_veil_invariant_goal BecomeLeader LeaderIsElected using wp by
  have hLE := hinv.2.2.2.2.2.2.1
  clear hinv
  intro hrole hq j hj
  apply (RaftVeil.Lemmas.contains_insert_iff _ _ _).2
  by_cases h : i = j
  · subst h; exact Or.inl rfl
  · exact Or.inr (hLE j (hj h))

prove_veil_invariant_goal BecomeLeader LeadersTermBound using wp by
  have hLeadersTermBound := hinv.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeLeader LedOwner using wp by
  have hOV := hinv.2.1
  have hGV := hinv.2.2.2.2.1
  have hLQ := hinv.2.2.2.2.2.1
  have hLO := hinv.2.2.2.2.2.2.2.2.1
  clear hinv
  intro a hrole hq
  have key := winner_unique st.msgs st.votes st.leaders i (st.currentTerm i) hOV (fun j hj => by simpa using hGV _ hj) hLQ hq
  intro ha hterm
  rw [RaftVeil.Lemmas.mem_insert] at ha
  rcases ha with rfl | ha
  · simp
  · by_cases hc : st.currentTerm i = a.term
    · rw [RaftVeil.Lemmas.ifPos hc, key a ha hc.symm]
    · rw [RaftVeil.Lemmas.ifNeg hc]; exact hLO a ha hterm

prove_veil_invariant_goal BecomeLeader LeadersHaveLed using wp by
  have hLeadersHaveLed := hinv.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeLeader LedHasLeader using wp by
  have hLedHasLeader := hinv.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeLeader AppendFromLeader using wp by
  have hAppendFromLeader := hinv.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeLeader LeaderLogIsLed using wp by
  have hOV := hinv.2.1
  have hGV := hinv.2.2.2.2.1
  have hLQ := hinv.2.2.2.2.2.1
  have hLO := hinv.2.2.2.2.2.2.2.2.1
  have hLHas := hinv.2.2.2.2.2.2.2.2.2.2.1
  have hLLL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro hrole hq
  have key := winner_unique st.msgs st.votes st.leaders i (st.currentTerm i) hOV (fun j hj => by simpa using hGV _ hj) hLQ hq
  have hsame := winner_led st.leaders st.currentTerm st.log st.ledLog i key hLO hLHas
  have hext := led_ext_set st.ledLog (st.currentTerm i) (st.log i) (fun L hL => by rw [hsame L hL]; exact List.prefix_refl _)
  intro j hj
  by_cases hij : i = j
  · subst hij; simp
  · by_cases hc : st.currentTerm i = st.currentTerm j
    · rw [RaftVeil.Lemmas.ifPos hc, ← hsame _ (hc ▸ hLLL j (hj hij))]
    · rw [RaftVeil.Lemmas.ifNeg hc]; exact hLLL j (hj hij)

prove_veil_invariant_goal BecomeLeader RequestsFromLed using wp by
  have hOV := hinv.2.1
  have hGV := hinv.2.2.2.2.1
  have hLQ := hinv.2.2.2.2.2.1
  have hLO := hinv.2.2.2.2.2.2.2.2.1
  have hLHas := hinv.2.2.2.2.2.2.2.2.2.2.1
  have hRFL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro hrole hq
  have key := winner_unique st.msgs st.votes st.leaders i (st.currentTerm i) hOV (fun j hj => by simpa using hGV _ hj) hLQ hq
  have hsame := winner_led st.leaders st.currentTerm st.log st.ledLog i key hLO hLHas
  have hext := led_ext_set st.ledLog (st.currentTerm i) (st.log i) (fun L hL => by rw [hsame L hL]; exact List.prefix_refl _)
  intro a ha
  have h := hRFL a ha
  cases a with
  | append src dst term p pt es c =>
    dsimp only at h ⊢
    by_cases hc : st.currentTerm i = term
    · subst hc
      rw [RaftVeil.Lemmas.ifPos rfl]
      cases hL : st.ledLog (st.currentTerm i) with
      | none => simp [hL] at h
      | some l => rw [hL, hsame l hL] at h; exact h
    · rw [RaftVeil.Lemmas.ifNeg hc]; exact h
  | _ => rfl

prove_veil_invariant_goal BecomeLeader BootEntry using wp by
  have hBootEntry := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeLeader LedBoot using wp by
  have hBoot := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLBoot := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro hrole hq t
  by_cases hc : st.currentTerm i = t
  · rw [RaftVeil.Lemmas.ifPos hc]; simp [hBoot i]
  · rw [RaftVeil.Lemmas.ifNeg hc]; exact hLBoot t

prove_veil_invariant_goal BecomeLeader LogFromLed using wp by
  have hOV := hinv.2.1
  have hGV := hinv.2.2.2.2.1
  have hLQ := hinv.2.2.2.2.2.1
  have hLO := hinv.2.2.2.2.2.2.2.2.1
  have hLHas := hinv.2.2.2.2.2.2.2.2.2.2.1
  have hLFL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro hrole hq
  have key := winner_unique st.msgs st.votes st.leaders i (st.currentTerm i) hOV (fun j hj => by simpa using hGV _ hj) hLQ hq
  have hsame := winner_led st.leaders st.currentTerm st.log st.ledLog i key hLO hLHas
  have hext := led_ext_set st.ledLog (st.currentTerm i) (st.log i) (fun L hL => by rw [hsame L hL]; exact List.prefix_refl _)
  intro j
  exact FromLed.mono st.ledLog _ _ hext (hLFL j)

prove_veil_invariant_goal BecomeLeader LedFromLed using wp by
  have hOV := hinv.2.1
  have hGV := hinv.2.2.2.2.1
  have hLQ := hinv.2.2.2.2.2.1
  have hLO := hinv.2.2.2.2.2.2.2.2.1
  have hLHas := hinv.2.2.2.2.2.2.2.2.2.2.1
  have hLFL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLedFL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro hrole hq
  have key := winner_unique st.msgs st.votes st.leaders i (st.currentTerm i) hOV (fun j hj => by simpa using hGV _ hj) hLQ hq
  have hsame := winner_led st.leaders st.currentTerm st.log st.ledLog i key hLO hLHas
  have hext := led_ext_set st.ledLog (st.currentTerm i) (st.log i) (fun L hL => by rw [hsame L hL]; exact List.prefix_refl _)
  intro t
  refine (optAll_iff _ _).2 ?_
  intro L hL
  apply FromLed.mono st.ledLog _ _ hext
  by_cases hc : st.currentTerm i = t
  · rw [RaftVeil.Lemmas.ifPos hc] at hL; cases hL; exact hLFL i
  · rw [RaftVeil.Lemmas.ifNeg hc] at hL; exact (optAll_iff _ _).1 (hLedFL t) L hL

prove_veil_invariant_goal BecomeLeader LogMatching using wp by
  have hLogMatching := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeLeader TermsPositive using wp by
  have hTermsPositive := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeLeader LogTermsBound using wp by
  have hLogTermsBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeLeader LedSorted using wp by
  have hOV := hinv.2.1
  have hGV := hinv.2.2.2.2.1
  have hLQ := hinv.2.2.2.2.2.1
  have hLO := hinv.2.2.2.2.2.2.2.2.1
  have hLHas := hinv.2.2.2.2.2.2.2.2.2.2.1
  have hLFL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hTP := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLogTB := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLS := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hAF := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro hrole hq
  have key := winner_unique st.msgs st.votes st.leaders i (st.currentTerm i) hOV (fun j hj => by simpa using hGV _ hj) hLQ hq
  have hsame := winner_led st.leaders st.currentTerm st.log st.ledLog i key hLO hLHas
  have hg := ledGrows_set (d := fun _ => Classical.propDecidable _) st.ledLog (st.currentTerm i) (st.log i) hsame
  have hmem : ¬ st.ledLog (st.currentTerm i) = none →
      ({ server := i, term := st.currentTerm i } : Elected server) ∈ st.leaders := by
    intro h
    obtain ⟨x, hx, hxt⟩ := hLHas _ h
    have hxs := key x hx hxt
    cases x; simp only at hxs hxt; subst hxs hxt; exact hx
  have hfresh : st.ledLog (st.currentTerm i) = none → ∀ c, 2 ≤ c → TermAt (st.log i) c ≠ st.currentTerm i := by
    intro hnone c hc hct
    rcases Nat.lt_or_ge (st.log i).length c with h | h
    · have h0 := termAt_le_of_gt _ _ h; have := hTP i; omega
    · have hfl := hLFL i
      rw [FromLed.iff] at hfl
      obtain ⟨L, hL, _⟩ := hfl (c - 1) (by omega) (by omega)
      rw [show c - 1 + 1 = c by omega, hct, hnone] at hL; cases hL
  have hack : ∀ n t A c, Acked st.msgs (TSet.insert ({ server := i, term := st.currentTerm i } : Elected server) st.leaders)
      (fun x => @ite _ (st.currentTerm i = x) (Classical.propDecidable _) (some (st.log i)) (st.ledLog x)) n t A c →
      Acked st.msgs st.leaders st.ledLog n t A c :=
    fun n t A c h => Acked.of_becomeLeader _ _ _ i _ _ n t A c hsame hmem hfresh h
  have hlen : ∀ n t A c, Acked st.msgs st.leaders st.ledLog n t A c → c ≤ A.length :=
    fun n t A c h => Acked.le_length _ _ _ _ _ _ _ (fun i' x' hx' => (hAF _ hx' n i' t x' rfl).2.2) h
  have hE : ∀ n cand u, Early st.msgs st.leaders st.ledLog n cand u →
      Early st.msgs (TSet.insert ({ server := i, term := st.currentTerm i } : Elected server) st.leaders)
        (fun x => @ite _ (st.currentTerm i = x) (Classical.propDecidable _) (some (st.log i)) (st.ledLog x)) n cand u := by
    intro n cand u he t A c ha htu li lt hr
    have ha' := hack n t A c ha
    rcases he t A c ha' htu li lt hr with h1 | h1
    · exact Or.inl (Covers.grows _ _ _ _ _ _ hg (hlen n t A c ha') h1)
    · exact Or.inr (LostIn.grows _ _ _ _ _ _ hg (hlen n t A c ha') (hLS t A ha'.1).2 h1)
  intro t L hL
  by_cases hc : st.currentTerm i = t
  · rw [RaftVeil.Lemmas.ifPos hc] at hL; cases hL
    rw [← hc]; exact sorted_of_fromLed st.ledLog _ _ (hLFL i) hLS (hLogTB i)
  · rw [RaftVeil.Lemmas.ifNeg hc] at hL; exact hLS t L hL

prove_veil_invariant_goal BecomeLeader ReqFacts using wp by
  have hOV := hinv.2.1
  have hGV := hinv.2.2.2.2.1
  have hLQ := hinv.2.2.2.2.2.1
  have hLO := hinv.2.2.2.2.2.2.2.2.1
  have hLHas := hinv.2.2.2.2.2.2.2.2.2.2.1
  have hLFL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hTP := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLS := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hRF := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hAF := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  first | intro (a : Msg server value) hrole hq | intro hrole hq (a : Msg server value)
  have key := winner_unique st.msgs st.votes st.leaders i (st.currentTerm i) hOV (fun j hj => by simpa using hGV _ hj) hLQ hq
  have hsame := winner_led st.leaders st.currentTerm st.log st.ledLog i key hLO hLHas
  have hg := ledGrows_set (d := fun _ => Classical.propDecidable _) st.ledLog (st.currentTerm i) (st.log i) hsame
  have hmem : ¬ st.ledLog (st.currentTerm i) = none →
      ({ server := i, term := st.currentTerm i } : Elected server) ∈ st.leaders := by
    intro h
    obtain ⟨x, hx, hxt⟩ := hLHas _ h
    have hxs := key x hx hxt
    cases x; simp only at hxs hxt; subst hxs hxt; exact hx
  have hfresh : st.ledLog (st.currentTerm i) = none → ∀ c, 2 ≤ c → TermAt (st.log i) c ≠ st.currentTerm i := by
    intro hnone c hc hct
    rcases Nat.lt_or_ge (st.log i).length c with h | h
    · have h0 := termAt_le_of_gt _ _ h; have := hTP i; omega
    · have hfl := hLFL i
      rw [FromLed.iff] at hfl
      obtain ⟨L, hL, _⟩ := hfl (c - 1) (by omega) (by omega)
      rw [show c - 1 + 1 = c by omega, hct, hnone] at hL; cases hL
  have hack : ∀ n t A c, Acked st.msgs (TSet.insert ({ server := i, term := st.currentTerm i } : Elected server) st.leaders)
      (fun x => @ite _ (st.currentTerm i = x) (Classical.propDecidable _) (some (st.log i)) (st.ledLog x)) n t A c →
      Acked st.msgs st.leaders st.ledLog n t A c :=
    fun n t A c h => Acked.of_becomeLeader _ _ _ i _ _ n t A c hsame hmem hfresh h
  have hlen : ∀ n t A c, Acked st.msgs st.leaders st.ledLog n t A c → c ≤ A.length :=
    fun n t A c h => Acked.le_length _ _ _ _ _ _ _ (fun i' x' hx' => (hAF _ hx' n i' t x' rfl).2.2) h
  have hE : ∀ n cand u, Early st.msgs st.leaders st.ledLog n cand u →
      Early st.msgs (TSet.insert ({ server := i, term := st.currentTerm i } : Elected server) st.leaders)
        (fun x => @ite _ (st.currentTerm i = x) (Classical.propDecidable _) (some (st.log i)) (st.ledLog x)) n cand u := by
    intro n cand u he t A c ha htu li lt hr
    have ha' := hack n t A c ha
    rcases he t A c ha' htu li lt hr with h1 | h1
    · exact Or.inl (Covers.grows _ _ _ _ _ _ hg (hlen n t A c ha') h1)
    · exact Or.inr (LostIn.grows _ _ _ _ _ _ hg (hlen n t A c ha') (hLS t A ha'.1).2 h1)
  intro ha c u li lt heq
  obtain ⟨h1, h2⟩ := hRF a ha c u li lt heq
  exact ⟨h1, ReqOk.grows _ _ _ _ _ hg h2⟩

prove_veil_invariant_goal BecomeLeader ReqUnique using wp by
  have hReqUnique := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeLeader VoteHasReq using wp by
  have hVoteHasReq := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeLeader CandLog using wp by
  have hCandLog := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeLeader LedExtendsReq using wp by
  have hOV := hinv.2.1
  have hGV := hinv.2.2.2.2.1
  have hLQ := hinv.2.2.2.2.2.1
  have hLO := hinv.2.2.2.2.2.2.2.2.1
  have hLHas := hinv.2.2.2.2.2.2.2.2.2.2.1
  have hLFL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hTP := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLS := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hCL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLER := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hAF := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  first | intro (ld : Elected server) hrole hq | intro hrole hq (ld : Elected server)
  have key := winner_unique st.msgs st.votes st.leaders i (st.currentTerm i) hOV (fun j hj => by simpa using hGV _ hj) hLQ hq
  have hsame := winner_led st.leaders st.currentTerm st.log st.ledLog i key hLO hLHas
  have hg := ledGrows_set (d := fun _ => Classical.propDecidable _) st.ledLog (st.currentTerm i) (st.log i) hsame
  have hmem : ¬ st.ledLog (st.currentTerm i) = none →
      ({ server := i, term := st.currentTerm i } : Elected server) ∈ st.leaders := by
    intro h
    obtain ⟨x, hx, hxt⟩ := hLHas _ h
    have hxs := key x hx hxt
    cases x; simp only at hxs hxt; subst hxs hxt; exact hx
  have hfresh : st.ledLog (st.currentTerm i) = none → ∀ c, 2 ≤ c → TermAt (st.log i) c ≠ st.currentTerm i := by
    intro hnone c hc hct
    rcases Nat.lt_or_ge (st.log i).length c with h | h
    · have h0 := termAt_le_of_gt _ _ h; have := hTP i; omega
    · have hfl := hLFL i
      rw [FromLed.iff] at hfl
      obtain ⟨L, hL, _⟩ := hfl (c - 1) (by omega) (by omega)
      rw [show c - 1 + 1 = c by omega, hct, hnone] at hL; cases hL
  have hack : ∀ n t A c, Acked st.msgs (TSet.insert ({ server := i, term := st.currentTerm i } : Elected server) st.leaders)
      (fun x => @ite _ (st.currentTerm i = x) (Classical.propDecidable _) (some (st.log i)) (st.ledLog x)) n t A c →
      Acked st.msgs st.leaders st.ledLog n t A c :=
    fun n t A c h => Acked.of_becomeLeader _ _ _ i _ _ n t A c hsame hmem hfresh h
  have hlen : ∀ n t A c, Acked st.msgs st.leaders st.ledLog n t A c → c ≤ A.length :=
    fun n t A c h => Acked.le_length _ _ _ _ _ _ _ (fun i' x' hx' => (hAF _ hx' n i' t x' rfl).2.2) h
  have hE : ∀ n cand u, Early st.msgs st.leaders st.ledLog n cand u →
      Early st.msgs (TSet.insert ({ server := i, term := st.currentTerm i } : Elected server) st.leaders)
        (fun x => @ite _ (st.currentTerm i = x) (Classical.propDecidable _) (some (st.log i)) (st.ledLog x)) n cand u := by
    intro n cand u he t A c ha htu li lt hr
    have ha' := hack n t A c ha
    rcases he t A c ha' htu li lt hr with h1 | h1
    · exact Or.inl (Covers.grows _ _ _ _ _ _ hg (hlen n t A c ha') h1)
    · exact Or.inr (LostIn.grows _ _ _ _ _ _ hg (hlen n t A c ha') (hLS t A ha'.1).2 h1)
  intro hld m hm li lt heq L hL
  by_cases hc : st.currentTerm i = ld.term
  · rw [RaftVeil.Lemmas.ifPos hc] at hL; cases hL
    have hsrv : ld.server = i := by
      rw [RaftVeil.Lemmas.mem_insert] at hld
      rcases hld with rfl | hld
      · rfl
      · exact key ld hld hc.symm
    cases hL0 : st.ledLog (st.currentTerm i) with
    | none =>
      obtain ⟨h1, h2⟩ := hCL m hm i (st.currentTerm i) li lt (by rw [heq, hsrv, hc]) rfl hL0
      exact ⟨by omega, h2⟩
    | some L0 =>
      have hl0 := hsame L0 hL0
      subst hl0
      have hin := hmem (by rw [hL0]; exact Option.some_ne_none _)
      exact hLER _ hin m hm li lt (by rw [heq, hsrv, hc]) _ hL0
  · rw [RaftVeil.Lemmas.ifNeg hc] at hL
    rw [RaftVeil.Lemmas.mem_insert] at hld
    rcases hld with rfl | hld
    · exact absurd rfl hc
    · exact hLER ld hld m hm li lt heq L hL

prove_veil_invariant_goal BecomeLeader AckFacts using wp by
  have hOV := hinv.2.1
  have hGV := hinv.2.2.2.2.1
  have hLQ := hinv.2.2.2.2.2.1
  have hLO := hinv.2.2.2.2.2.2.2.2.1
  have hLHas := hinv.2.2.2.2.2.2.2.2.2.2.1
  have hLFL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hTP := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLS := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hAF := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  first | intro (a : Msg server value) hrole hq | intro hrole hq (a : Msg server value)
  have key := winner_unique st.msgs st.votes st.leaders i (st.currentTerm i) hOV (fun j hj => by simpa using hGV _ hj) hLQ hq
  have hsame := winner_led st.leaders st.currentTerm st.log st.ledLog i key hLO hLHas
  have hg := ledGrows_set (d := fun _ => Classical.propDecidable _) st.ledLog (st.currentTerm i) (st.log i) hsame
  have hmem : ¬ st.ledLog (st.currentTerm i) = none →
      ({ server := i, term := st.currentTerm i } : Elected server) ∈ st.leaders := by
    intro h
    obtain ⟨x, hx, hxt⟩ := hLHas _ h
    have hxs := key x hx hxt
    cases x; simp only at hxs hxt; subst hxs hxt; exact hx
  have hfresh : st.ledLog (st.currentTerm i) = none → ∀ c, 2 ≤ c → TermAt (st.log i) c ≠ st.currentTerm i := by
    intro hnone c hc hct
    rcases Nat.lt_or_ge (st.log i).length c with h | h
    · have h0 := termAt_le_of_gt _ _ h; have := hTP i; omega
    · have hfl := hLFL i
      rw [FromLed.iff] at hfl
      obtain ⟨L, hL, _⟩ := hfl (c - 1) (by omega) (by omega)
      rw [show c - 1 + 1 = c by omega, hct, hnone] at hL; cases hL
  have hack : ∀ n t A c, Acked st.msgs (TSet.insert ({ server := i, term := st.currentTerm i } : Elected server) st.leaders)
      (fun x => @ite _ (st.currentTerm i = x) (Classical.propDecidable _) (some (st.log i)) (st.ledLog x)) n t A c →
      Acked st.msgs st.leaders st.ledLog n t A c :=
    fun n t A c h => Acked.of_becomeLeader _ _ _ i _ _ n t A c hsame hmem hfresh h
  have hlen : ∀ n t A c, Acked st.msgs st.leaders st.ledLog n t A c → c ≤ A.length :=
    fun n t A c h => Acked.le_length _ _ _ _ _ _ _ (fun i' x' hx' => (hAF _ hx' n i' t x' rfl).2.2) h
  have hE : ∀ n cand u, Early st.msgs st.leaders st.ledLog n cand u →
      Early st.msgs (TSet.insert ({ server := i, term := st.currentTerm i } : Elected server) st.leaders)
        (fun x => @ite _ (st.currentTerm i = x) (Classical.propDecidable _) (some (st.log i)) (st.ledLog x)) n cand u := by
    intro n cand u he t A c ha htu li lt hr
    have ha' := hack n t A c ha
    rcases he t A c ha' htu li lt hr with h1 | h1
    · exact Or.inl (Covers.grows _ _ _ _ _ _ hg (hlen n t A c ha') h1)
    · exact Or.inr (LostIn.grows _ _ _ _ _ _ hg (hlen n t A c ha') (hLS t A ha'.1).2 h1)
  intro ha j i' t x heq
  obtain ⟨h1, h2, L, hL, hx⟩ := hAF a ha j i' t x heq
  obtain ⟨es, hL', _⟩ := hg t L hL
  exact ⟨(RaftVeil.Lemmas.contains_insert_iff _ _ _).2 (Or.inr h1), h2, L ++ es, hL', by simp; omega⟩

prove_veil_invariant_goal BecomeLeader AckedHeld using wp by
  have hOV := hinv.2.1
  have hGV := hinv.2.2.2.2.1
  have hLQ := hinv.2.2.2.2.2.1
  have hLO := hinv.2.2.2.2.2.2.2.2.1
  have hLHas := hinv.2.2.2.2.2.2.2.2.2.2.1
  have hLFL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hTP := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLS := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hAF := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hAH := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro hrole hq
  have key := winner_unique st.msgs st.votes st.leaders i (st.currentTerm i) hOV (fun j hj => by simpa using hGV _ hj) hLQ hq
  have hsame := winner_led st.leaders st.currentTerm st.log st.ledLog i key hLO hLHas
  have hg := ledGrows_set (d := fun _ => Classical.propDecidable _) st.ledLog (st.currentTerm i) (st.log i) hsame
  have hmem : ¬ st.ledLog (st.currentTerm i) = none →
      ({ server := i, term := st.currentTerm i } : Elected server) ∈ st.leaders := by
    intro h
    obtain ⟨x, hx, hxt⟩ := hLHas _ h
    have hxs := key x hx hxt
    cases x; simp only at hxs hxt; subst hxs hxt; exact hx
  have hfresh : st.ledLog (st.currentTerm i) = none → ∀ c, 2 ≤ c → TermAt (st.log i) c ≠ st.currentTerm i := by
    intro hnone c hc hct
    rcases Nat.lt_or_ge (st.log i).length c with h | h
    · have h0 := termAt_le_of_gt _ _ h; have := hTP i; omega
    · have hfl := hLFL i
      rw [FromLed.iff] at hfl
      obtain ⟨L, hL, _⟩ := hfl (c - 1) (by omega) (by omega)
      rw [show c - 1 + 1 = c by omega, hct, hnone] at hL; cases hL
  have hack : ∀ n t A c, Acked st.msgs (TSet.insert ({ server := i, term := st.currentTerm i } : Elected server) st.leaders)
      (fun x => @ite _ (st.currentTerm i = x) (Classical.propDecidable _) (some (st.log i)) (st.ledLog x)) n t A c →
      Acked st.msgs st.leaders st.ledLog n t A c :=
    fun n t A c h => Acked.of_becomeLeader _ _ _ i _ _ n t A c hsame hmem hfresh h
  have hlen : ∀ n t A c, Acked st.msgs st.leaders st.ledLog n t A c → c ≤ A.length :=
    fun n t A c h => Acked.le_length _ _ _ _ _ _ _ (fun i' x' hx' => (hAF _ hx' n i' t x' rfl).2.2) h
  have hE : ∀ n cand u, Early st.msgs st.leaders st.ledLog n cand u →
      Early st.msgs (TSet.insert ({ server := i, term := st.currentTerm i } : Elected server) st.leaders)
        (fun x => @ite _ (st.currentTerm i = x) (Classical.propDecidable _) (some (st.log i)) (st.ledLog x)) n cand u := by
    intro n cand u he t A c ha htu li lt hr
    have ha' := hack n t A c ha
    rcases he t A c ha' htu li lt hr with h1 | h1
    · exact Or.inl (Covers.grows _ _ _ _ _ _ hg (hlen n t A c ha') h1)
    · exact Or.inr (LostIn.grows _ _ _ _ _ _ hg (hlen n t A c ha') (hLS t A ha'.1).2 h1)
  intro n t A c h
  have h' := hack n t A c h
  rcases hAH n t A c h' with h1 | h1
  · exact Or.inl h1
  · exact Or.inr (LostIn.grows _ _ _ _ _ _ hg (hlen n t A c h') (hLS t A h'.1).2 h1)

prove_veil_invariant_goal BecomeLeader AckVote using wp by
  have hOV := hinv.2.1
  have hGV := hinv.2.2.2.2.1
  have hLQ := hinv.2.2.2.2.2.1
  have hLO := hinv.2.2.2.2.2.2.2.2.1
  have hLHas := hinv.2.2.2.2.2.2.2.2.2.2.1
  have hLFL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hTP := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLS := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hAF := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hAV := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  first | intro (v : Vote server) hrole hq | intro hrole hq (v : Vote server)
  have key := winner_unique st.msgs st.votes st.leaders i (st.currentTerm i) hOV (fun j hj => by simpa using hGV _ hj) hLQ hq
  have hsame := winner_led st.leaders st.currentTerm st.log st.ledLog i key hLO hLHas
  have hg := ledGrows_set (d := fun _ => Classical.propDecidable _) st.ledLog (st.currentTerm i) (st.log i) hsame
  have hmem : ¬ st.ledLog (st.currentTerm i) = none →
      ({ server := i, term := st.currentTerm i } : Elected server) ∈ st.leaders := by
    intro h
    obtain ⟨x, hx, hxt⟩ := hLHas _ h
    have hxs := key x hx hxt
    cases x; simp only at hxs hxt; subst hxs hxt; exact hx
  have hfresh : st.ledLog (st.currentTerm i) = none → ∀ c, 2 ≤ c → TermAt (st.log i) c ≠ st.currentTerm i := by
    intro hnone c hc hct
    rcases Nat.lt_or_ge (st.log i).length c with h | h
    · have h0 := termAt_le_of_gt _ _ h; have := hTP i; omega
    · have hfl := hLFL i
      rw [FromLed.iff] at hfl
      obtain ⟨L, hL, _⟩ := hfl (c - 1) (by omega) (by omega)
      rw [show c - 1 + 1 = c by omega, hct, hnone] at hL; cases hL
  have hack : ∀ n t A c, Acked st.msgs (TSet.insert ({ server := i, term := st.currentTerm i } : Elected server) st.leaders)
      (fun x => @ite _ (st.currentTerm i = x) (Classical.propDecidable _) (some (st.log i)) (st.ledLog x)) n t A c →
      Acked st.msgs st.leaders st.ledLog n t A c :=
    fun n t A c h => Acked.of_becomeLeader _ _ _ i _ _ n t A c hsame hmem hfresh h
  have hlen : ∀ n t A c, Acked st.msgs st.leaders st.ledLog n t A c → c ≤ A.length :=
    fun n t A c h => Acked.le_length _ _ _ _ _ _ _ (fun i' x' hx' => (hAF _ hx' n i' t x' rfl).2.2) h
  have hE : ∀ n cand u, Early st.msgs st.leaders st.ledLog n cand u →
      Early st.msgs (TSet.insert ({ server := i, term := st.currentTerm i } : Elected server) st.leaders)
        (fun x => @ite _ (st.currentTerm i = x) (Classical.propDecidable _) (some (st.log i)) (st.ledLog x)) n cand u := by
    intro n cand u he t A c ha htu li lt hr
    have ha' := hack n t A c ha
    rcases he t A c ha' htu li lt hr with h1 | h1
    · exact Or.inl (Covers.grows _ _ _ _ _ _ hg (hlen n t A c ha') h1)
    · exact Or.inr (LostIn.grows _ _ _ _ _ _ hg (hlen n t A c ha') (hLS t A ha'.1).2 h1)
  intro n t A c h hv hvn htv li lt hreq
  have h' := hack n t A c h
  rcases hAV v n t A c h' hv hvn htv li lt hreq with h1 | h1
  · exact Or.inl (Covers.grows _ _ _ _ _ _ hg (hlen n t A c h') h1)
  · exact Or.inr (LostIn.grows _ _ _ _ _ _ hg (hlen n t A c h') (hLS t A h'.1).2 h1)

prove_veil_invariant_goal BecomeLeader EarlyQuorum using wp by
  have hOV := hinv.2.1
  have hGV := hinv.2.2.2.2.1
  have hLQ := hinv.2.2.2.2.2.1
  have hLO := hinv.2.2.2.2.2.2.2.2.1
  have hLHas := hinv.2.2.2.2.2.2.2.2.2.2.1
  have hLFL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hTP := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLS := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hAF := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hAV := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hEQ := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  first | intro (ld : Elected server) hrole hq | intro hrole hq (ld : Elected server)
  have key := winner_unique st.msgs st.votes st.leaders i (st.currentTerm i) hOV (fun j hj => by simpa using hGV _ hj) hLQ hq
  have hsame := winner_led st.leaders st.currentTerm st.log st.ledLog i key hLO hLHas
  have hg := ledGrows_set (d := fun _ => Classical.propDecidable _) st.ledLog (st.currentTerm i) (st.log i) hsame
  have hmem : ¬ st.ledLog (st.currentTerm i) = none →
      ({ server := i, term := st.currentTerm i } : Elected server) ∈ st.leaders := by
    intro h
    obtain ⟨x, hx, hxt⟩ := hLHas _ h
    have hxs := key x hx hxt
    cases x; simp only at hxs hxt; subst hxs hxt; exact hx
  have hfresh : st.ledLog (st.currentTerm i) = none → ∀ c, 2 ≤ c → TermAt (st.log i) c ≠ st.currentTerm i := by
    intro hnone c hc hct
    rcases Nat.lt_or_ge (st.log i).length c with h | h
    · have h0 := termAt_le_of_gt _ _ h; have := hTP i; omega
    · have hfl := hLFL i
      rw [FromLed.iff] at hfl
      obtain ⟨L, hL, _⟩ := hfl (c - 1) (by omega) (by omega)
      rw [show c - 1 + 1 = c by omega, hct, hnone] at hL; cases hL
  have hack : ∀ n t A c, Acked st.msgs (TSet.insert ({ server := i, term := st.currentTerm i } : Elected server) st.leaders)
      (fun x => @ite _ (st.currentTerm i = x) (Classical.propDecidable _) (some (st.log i)) (st.ledLog x)) n t A c →
      Acked st.msgs st.leaders st.ledLog n t A c :=
    fun n t A c h => Acked.of_becomeLeader _ _ _ i _ _ n t A c hsame hmem hfresh h
  have hlen : ∀ n t A c, Acked st.msgs st.leaders st.ledLog n t A c → c ≤ A.length :=
    fun n t A c h => Acked.le_length _ _ _ _ _ _ _ (fun i' x' hx' => (hAF _ hx' n i' t x' rfl).2.2) h
  have hE : ∀ n cand u, Early st.msgs st.leaders st.ledLog n cand u →
      Early st.msgs (TSet.insert ({ server := i, term := st.currentTerm i } : Elected server) st.leaders)
        (fun x => @ite _ (st.currentTerm i = x) (Classical.propDecidable _) (some (st.log i)) (st.ledLog x)) n cand u := by
    intro n cand u he t A c ha htu li lt hr
    have ha' := hack n t A c ha
    rcases he t A c ha' htu li lt hr with h1 | h1
    · exact Or.inl (Covers.grows _ _ _ _ _ _ hg (hlen n t A c ha') h1)
    · exact Or.inr (LostIn.grows _ _ _ _ _ _ hg (hlen n t A c ha') (hLS t A ha'.1).2 h1)
  intro hld
  have hold : ∀ ld' : Elected server, ld' ∈ st.leaders →
      (IsQuorum fun n => @decide (TSet.contains ({ voter := n, term := ld'.term, cand := ld'.server } : Vote server) st.votes = true ∧
        Early st.msgs (TSet.insert ({ server := i, term := st.currentTerm i } : Elected server) st.leaders)
          (fun x => @ite _ (st.currentTerm i = x) (Classical.propDecidable _) (some (st.log i)) (st.ledLog x)) n ld'.server ld'.term)
        (Classical.propDecidable _)) = true := by
    intro ld' hld'
    refine IsQuorum.mono _ _ ?_ (hEQ ld' hld')
    intro n hn
    simp only [decide_eq_true_eq] at hn ⊢
    exact ⟨hn.1, hE n _ _ hn.2⟩
  rw [RaftVeil.Lemmas.mem_insert] at hld
  rcases hld with rfl | hld
  · cases hnone : st.ledLog (st.currentTerm i) with
    | some L0 => exact hold _ (hmem (by rw [hnone]; exact Option.some_ne_none _))
    | none =>
      refine IsQuorum.mono _ _ ?_ hq
      intro n hn
      simp only [decide_eq_true_eq]
      have hvote : TSet.contains ({ voter := n, term := st.currentTerm i, cand := i } : Vote server) st.votes = true := by
        by_cases hni : n = i
        · subst hni; simpa using hn
        · simp only [hni, ite_false] at hn
          simpa using hGV _ hn
      refine ⟨hvote, ?_⟩
      intro t A c ha htu li lt hr
      have ha' := hack n t A c ha
      rcases hAV ⟨n, st.currentTerm i, i⟩ n t A c ha' hvote rfl htu li lt hr with h1 | ⟨w, h1, h2, B, hB, h3⟩
      · exact Or.inl (Covers.grows _ _ _ _ _ _ hg (hlen n t A c ha') h1)
      · have hw : w ≠ st.currentTerm i := by intro h; rw [h, hnone] at hB; cases hB
        exact Or.inr (LostIn.grows _ _ _ _ _ _ hg (hlen n t A c ha') (hLS t A ha'.1).2
          ⟨w, h1, by simp only at h2; omega, B, hB, h3⟩)
  · exact hold ld hld

prove_veil_invariant_goal BecomeLeader ConfirmedIsLed using wp by
  have hOV := hinv.2.1
  have hGV := hinv.2.2.2.2.1
  have hLQ := hinv.2.2.2.2.2.1
  have hLO := hinv.2.2.2.2.2.2.2.2.1
  have hLHas := hinv.2.2.2.2.2.2.2.2.2.2.1
  have hLFL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hTP := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLS := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hAF := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hCIL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro hrole hq
  have key := winner_unique st.msgs st.votes st.leaders i (st.currentTerm i) hOV (fun j hj => by simpa using hGV _ hj) hLQ hq
  have hsame := winner_led st.leaders st.currentTerm st.log st.ledLog i key hLO hLHas
  have hg := ledGrows_set (d := fun _ => Classical.propDecidable _) st.ledLog (st.currentTerm i) (st.log i) hsame
  have hmem : ¬ st.ledLog (st.currentTerm i) = none →
      ({ server := i, term := st.currentTerm i } : Elected server) ∈ st.leaders := by
    intro h
    obtain ⟨x, hx, hxt⟩ := hLHas _ h
    have hxs := key x hx hxt
    cases x; simp only at hxs hxt; subst hxs hxt; exact hx
  have hfresh : st.ledLog (st.currentTerm i) = none → ∀ c, 2 ≤ c → TermAt (st.log i) c ≠ st.currentTerm i := by
    intro hnone c hc hct
    rcases Nat.lt_or_ge (st.log i).length c with h | h
    · have h0 := termAt_le_of_gt _ _ h; have := hTP i; omega
    · have hfl := hLFL i
      rw [FromLed.iff] at hfl
      obtain ⟨L, hL, _⟩ := hfl (c - 1) (by omega) (by omega)
      rw [show c - 1 + 1 = c by omega, hct, hnone] at hL; cases hL
  have hack : ∀ n t A c, Acked st.msgs (TSet.insert ({ server := i, term := st.currentTerm i } : Elected server) st.leaders)
      (fun x => @ite _ (st.currentTerm i = x) (Classical.propDecidable _) (some (st.log i)) (st.ledLog x)) n t A c →
      Acked st.msgs st.leaders st.ledLog n t A c :=
    fun n t A c h => Acked.of_becomeLeader _ _ _ i _ _ n t A c hsame hmem hfresh h
  have hlen : ∀ n t A c, Acked st.msgs st.leaders st.ledLog n t A c → c ≤ A.length :=
    fun n t A c h => Acked.le_length _ _ _ _ _ _ _ (fun i' x' hx' => (hAF _ hx' n i' t x' rfl).2.2) h
  have hE : ∀ n cand u, Early st.msgs st.leaders st.ledLog n cand u →
      Early st.msgs (TSet.insert ({ server := i, term := st.currentTerm i } : Elected server) st.leaders)
        (fun x => @ite _ (st.currentTerm i = x) (Classical.propDecidable _) (some (st.log i)) (st.ledLog x)) n cand u := by
    intro n cand u he t A c ha htu li lt hr
    have ha' := hack n t A c ha
    rcases he t A c ha' htu li lt hr with h1 | h1
    · exact Or.inl (Covers.grows _ _ _ _ _ _ hg (hlen n t A c ha') h1)
    · exact Or.inr (LostIn.grows _ _ _ _ _ _ hg (hlen n t A c ha') (hLS t A ha'.1).2 h1)
  intro j
  rcases hCIL j with h | ⟨L, hL, h1, h2⟩
  · exact Or.inl h
  · obtain ⟨es, hL', _⟩ := hg _ L hL
    have hlL : st.confirmedIndex j ≤ L.length := by
      have := congrArg List.length h2; simp at this; omega
    exact Or.inr ⟨L ++ es, hL', h1, by rw [List.take_append_of_le_length hlL]; exact h2⟩

prove_veil_invariant_goal BecomeLeader CommitRoot using wp by
  have hOV := hinv.2.1
  have hGV := hinv.2.2.2.2.1
  have hLQ := hinv.2.2.2.2.2.1
  have hLO := hinv.2.2.2.2.2.2.2.2.1
  have hLHas := hinv.2.2.2.2.2.2.2.2.2.2.1
  have hLFL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hTP := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLS := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hAF := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hCR := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  first | intro (k : Commit server value) hrole hq | intro hrole hq (k : Commit server value)
  have key := winner_unique st.msgs st.votes st.leaders i (st.currentTerm i) hOV (fun j hj => by simpa using hGV _ hj) hLQ hq
  have hsame := winner_led st.leaders st.currentTerm st.log st.ledLog i key hLO hLHas
  have hg := ledGrows_set (d := fun _ => Classical.propDecidable _) st.ledLog (st.currentTerm i) (st.log i) hsame
  have hmem : ¬ st.ledLog (st.currentTerm i) = none →
      ({ server := i, term := st.currentTerm i } : Elected server) ∈ st.leaders := by
    intro h
    obtain ⟨x, hx, hxt⟩ := hLHas _ h
    have hxs := key x hx hxt
    cases x; simp only at hxs hxt; subst hxs hxt; exact hx
  have hfresh : st.ledLog (st.currentTerm i) = none → ∀ c, 2 ≤ c → TermAt (st.log i) c ≠ st.currentTerm i := by
    intro hnone c hc hct
    rcases Nat.lt_or_ge (st.log i).length c with h | h
    · have h0 := termAt_le_of_gt _ _ h; have := hTP i; omega
    · have hfl := hLFL i
      rw [FromLed.iff] at hfl
      obtain ⟨L, hL, _⟩ := hfl (c - 1) (by omega) (by omega)
      rw [show c - 1 + 1 = c by omega, hct, hnone] at hL; cases hL
  have hack : ∀ n t A c, Acked st.msgs (TSet.insert ({ server := i, term := st.currentTerm i } : Elected server) st.leaders)
      (fun x => @ite _ (st.currentTerm i = x) (Classical.propDecidable _) (some (st.log i)) (st.ledLog x)) n t A c →
      Acked st.msgs st.leaders st.ledLog n t A c :=
    fun n t A c h => Acked.of_becomeLeader _ _ _ i _ _ n t A c hsame hmem hfresh h
  have hlen : ∀ n t A c, Acked st.msgs st.leaders st.ledLog n t A c → c ≤ A.length :=
    fun n t A c h => Acked.le_length _ _ _ _ _ _ _ (fun i' x' hx' => (hAF _ hx' n i' t x' rfl).2.2) h
  have hE : ∀ n cand u, Early st.msgs st.leaders st.ledLog n cand u →
      Early st.msgs (TSet.insert ({ server := i, term := st.currentTerm i } : Elected server) st.leaders)
        (fun x => @ite _ (st.currentTerm i = x) (Classical.propDecidable _) (some (st.log i)) (st.ledLog x)) n cand u := by
    intro n cand u he t A c ha htu li lt hr
    have ha' := hack n t A c ha
    rcases he t A c ha' htu li lt hr with h1 | h1
    · exact Or.inl (Covers.grows _ _ _ _ _ _ hg (hlen n t A c ha') h1)
    · exact Or.inr (LostIn.grows _ _ _ _ _ _ hg (hlen n t A c ha') (hLS t A ha'.1).2 h1)
  intro hk
  obtain ⟨h1, r, h2, h3, h4, h5⟩ := hCR k hk
  exact ⟨h1, r, h2, Root.mono _ _ _ _ _ _ _ (fun a ha => ha)
    (fun a ha => (RaftVeil.Lemmas.mem_insert _ _ _).2 (Or.inr ha)) hg h3, h4, h5⟩

prove_veil_invariant_goal BecomeLeader CommitSafety using wp by
  have hCommitSafety := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeLeader ConfirmedTermBound using wp by
  have hConfirmedTermBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeLeader CommitTermBound using wp by
  have hCommitTermBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeLeader CommittedEntriesPreserved using wp by
  have hCommittedEntriesPreserved := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeLeader CommitIndexCommitted using wp by
  have hCommitIndexCommitted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeLeader AppliedCommitted using wp by
  have hAppliedCommitted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeLeader StateMachineSafety using wp by
  have hStateMachineSafety := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeLeader LeaderCompleteness using wp by
  have hOV := hinv.2.1
  have hGV := hinv.2.2.2.2.1
  have hLQ := hinv.2.2.2.2.2.1
  have hLO := hinv.2.2.2.2.2.2.2.2.1
  have hLHas := hinv.2.2.2.2.2.2.2.2.2.2.1
  have hBoot := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLBoot := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLFL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLedFL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hVHR := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hCL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLER := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hAV := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hEQ := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hCR := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLC := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro cc hrole hq i1 hc hr1 hlt
  by_cases hd : i = i1
  · subst hd
    obtain ⟨-, r, hcr, hroot, hr, hrt⟩ := hCR cc hc
    rw [isPrefix_iff]
    refine hcr.trans ?_
    have key := winner_unique st.msgs st.votes st.leaders i (st.currentTerm i) hOV (fun j hj => by simpa using hGV _ hj) hLQ hq
    cases hnone : st.ledLog (st.currentTerm i) with
    | some L0 =>
      have hsame := winner_led st.leaders st.currentTerm st.log st.ledLog i key hLO hLHas
      have h0 := hsame L0 hnone
      subst h0
      exact root_in_later st.msgs st.leaders st.votes st.ledLog hEQ hLHas hVHR hLER (fun t L h => (optAll_iff _ _).1 (hLedFL t) L h) (fun t L h => by simpa using (optAll_iff _ _).1 (hLBoot t) L h) r hroot (st.currentTerm i) (by omega) _ hnone
    | none =>
      have hq' : IsQuorum (fun n => TSet.contains ({ voter := n, term := st.currentTerm i, cand := i } : Vote server) st.votes) = true := by
        refine IsQuorum.mono _ _ ?_ hq
        intro n hn
        by_cases hni : n = i
        · subst hni; simpa using hn
        · simp only [hni, ite_false] at hn
          simpa using hGV _ hn
      exact cand_complete st.msgs st.leaders st.votes st.ledLog hEQ hLHas hVHR hLER
        (fun t L h => (optAll_iff _ _).1 (hLedFL t) L h)
        (fun t L h => by simpa using (optAll_iff _ _).1 (hLBoot t) L h)
        i (st.currentTerm i) (st.log i)
        (fun n t A c ha hv htu li lt hr => hAV ⟨n, st.currentTerm i, i⟩ n t A c ha hv rfl htu li lt hr)
        hnone hq' (fun li lt hm => hCL _ hm i (st.currentTerm i) li lt rfl rfl hnone) (hLFL i) (hBoot i)
        r hroot (by omega)
  · exact hLC cc i1 hc (hr1 hd) hlt

prove_veil_invariant_goal BecomeLeader ConfirmedWithinLog using wp by
  have hConfirmedWithinLog := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeLeader PreVoteRequestsBounded using wp by
  have hPreVoteRequestsBounded := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeLeader PreGrantsAnswer using wp by
  have hPreGrantsAnswer := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeLeader TimeoutNowFromLeader using wp by
  have hTN := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  rename_i a ha
  refine timeoutnow_mono _ _ a (hTN a ha) ?_
  intro s hx
  simp only [decide_eq_true_eq] at hx ⊢
  obtain ⟨⟨ld, hld⟩, h2⟩ := hx
  exact ⟨⟨ld, (RaftVeil.Lemmas.mem_insert _ _ _).2 (Or.inr hld)⟩, h2⟩

prove_veil_invariant_goal BecomeLeader TransferIsCandidate using wp by
  have hTransferIsCandidate := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeLeader SnapshotWithinLog using wp by
  have hSnapshotWithinLog := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeLeader BaseWithinSnapshot using wp by
  have hBaseWithinSnapshot := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeLeader SnapshotCommitted using wp by
  have hSnapshotCommitted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeLeader SnapshotApplied using wp by
  have hSnapshotApplied := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

-- LeaderAppend

prove_veil_invariant_goal LeaderAppend ElectionSafety using wp by
  have hElectionSafety := hinv.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal LeaderAppend OneVotePerTerm using wp by
  have hOneVotePerTerm := hinv.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal LeaderAppend VoteTermBound using wp by
  have hVoteTermBound := hinv.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal LeaderAppend VotesBound using wp by
  have hVotesBound := hinv.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal LeaderAppend GrantsAreVotes using wp by
  have hGrantsAreVotes := hinv.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal LeaderAppend LeadersHaveQuorum using wp by
  have hLeadersHaveQuorum := hinv.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal LeaderAppend LeaderIsElected using wp by
  have hLeaderIsElected := hinv.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal LeaderAppend LeadersTermBound using wp by
  have hLeadersTermBound := hinv.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal LeaderAppend LedOwner using wp by
  have hES := hinv.1
  have hLE := hinv.2.2.2.2.2.2.1
  have hLO := hinv.2.2.2.2.2.2.2.2.1
  clear hinv
  intro x hty hrole hx hxt
  by_cases hj : i = x.server
  · rw [RaftVeil.Lemmas.ifPos hj, RaftVeil.Lemmas.ifPos (show st.currentTerm i = x.term by rw [hxt, ← hj])]
  · rw [RaftVeil.Lemmas.ifNeg hj]
    by_cases hc : st.currentTerm i = x.term
    · exact absurd (hES x _ hx (hLE i hrole) hc.symm).symm hj
    · rw [RaftVeil.Lemmas.ifNeg hc]; exact hLO x hx hxt

prove_veil_invariant_goal LeaderAppend LeadersHaveLed using wp by
  have hLeadersHaveLed := hinv.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal LeaderAppend LedHasLeader using wp by
  have hLedHasLeader := hinv.2.2.2.2.2.2.2.2.2.2.1
  have hLeaderLogIsLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal LeaderAppend AppendFromLeader using wp by
  have hAppendFromLeader := hinv.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal LeaderAppend LeaderLogIsLed using wp by
  have hES := hinv.1
  have hLE := hinv.2.2.2.2.2.2.1
  have hLLL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro hty hrole j hjrole
  by_cases hj : i = j
  · subst hj; rw [RaftVeil.Lemmas.ifPos rfl, RaftVeil.Lemmas.ifPos rfl]
  · by_cases hc : st.currentTerm i = st.currentTerm j
    · exact absurd (hES _ _ (hLE j hjrole) (hLE i hrole) hc.symm).symm hj
    · rw [RaftVeil.Lemmas.ifNeg hc, RaftVeil.Lemmas.ifNeg hj]; exact hLLL j hjrole

prove_veil_invariant_goal LeaderAppend RequestsFromLed using wp by
  have hLLL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hRFL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro hty hrole
  have hled := hLLL i hrole
  intro m hm
  refine req_mono st.ledLog _ _ _ m (hRFL m hm) ?_ ?_
  · exact led_ext_set st.ledLog (st.currentTerm i) _
      (fun L hL => by rw [hled] at hL; cases hL; exact List.prefix_append _ _)
  · intro t l l' c hp hx
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hx ⊢
    exact commitPart_mono st.commits _ (fun k hk => hk) l l' c t hp hx

prove_veil_invariant_goal LeaderAppend BootEntry using wp by
  have hLLL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hBoot := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro hty hrole
  have hled := hLLL i hrole
  intro j
  by_cases hj : i = j
  · rw [RaftVeil.Lemmas.ifPos hj]
    have := hBoot i
    cases hl : st.log i with
    | nil => rw [hl] at this; simp at this
    | cons x xs => rw [hl] at this; exact this
  · rw [RaftVeil.Lemmas.ifNeg hj]; exact hBoot j

prove_veil_invariant_goal LeaderAppend LedBoot using wp by
  have hLLL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hBoot := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLBoot := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro hty hrole
  have hled := hLLL i hrole
  intro t
  refine (optAll_iff _ _).2 ?_
  intro L hL
  by_cases hc : st.currentTerm i = t
  · rw [RaftVeil.Lemmas.ifPos hc] at hL; cases hL
    have := hBoot i
    cases hl : st.log i with
    | nil => rw [hl] at this; simp at this
    | cons x xs => rw [hl] at this; exact this
  · rw [RaftVeil.Lemmas.ifNeg hc] at hL
    exact (optAll_iff _ _).1 (hLBoot t) L hL

prove_veil_invariant_goal LeaderAppend LogFromLed using wp by
  have hLLL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLFL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro hty hrole
  have hled := hLLL i hrole
  intro j
  by_cases hj : i = j
  · rw [RaftVeil.Lemmas.ifPos hj]; refine (leaderAppend_fromLed st.ledLog (st.log i) _ _ ?_ hled).2 (hLFL i); rfl
  · rw [RaftVeil.Lemmas.ifNeg hj]; refine (leaderAppend_fromLed st.ledLog (st.log i) _ _ ?_ hled).1 _ (hLFL j); rfl

prove_veil_invariant_goal LeaderAppend LedFromLed using wp by
  have hLLL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLFL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLedFL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro hty hrole
  have hled := hLLL i hrole
  intro t
  refine (optAll_iff _ _).2 ?_
  intro L hL
  by_cases hc : st.currentTerm i = t
  · rw [RaftVeil.Lemmas.ifPos hc] at hL; cases hL
    refine (leaderAppend_fromLed st.ledLog (st.log i) _ _ ?_ hled).2 (hLFL i); rfl
  · rw [RaftVeil.Lemmas.ifNeg hc] at hL
    refine (leaderAppend_fromLed st.ledLog (st.log i) _ _ ?_ hled).1 _ ((optAll_iff _ _).1 (hLedFL t) L hL); rfl

prove_veil_invariant_goal LeaderAppend LogMatching using wp by
  have hLLL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hBoot := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLFL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro hty hrole
  have hled := hLLL i hrole
  exact leaderAppend_matching st.ledLog st.log i _ hled hLFL hBoot

prove_veil_invariant_goal LeaderAppend TermsPositive using wp by
  have hTermsPositive := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal LeaderAppend LogTermsBound using wp by
  have hES := hinv.1
  have hLE := hinv.2.2.2.2.2.2.1
  have hLLL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLFL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLogTB := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLS := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hAF := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro hty hrole
  have hled := hLLL i hrole
  generalize hE : ({ term := st.currentTerm i, kind := ty, value := _ } : Entry value) = e
  have he : e.term = st.currentTerm i := by rw [← hE]
  have hg := ledGrows_append (d := fun _ => Classical.propDecidable _) st.ledLog (st.currentTerm i) (st.log i) e hled he
  have hlen : ∀ n t A c, Acked st.msgs st.leaders st.ledLog n t A c → c ≤ A.length :=
    fun n t A c h => Acked.le_length _ _ _ _ _ _ _ (fun i' x' hx' => (hAF _ hx' n i' t x' rfl).2.2) h
  have hold : ∀ n t A c, Acked st.msgs st.leaders (fun x => @ite _ (st.currentTerm i = x) (Classical.propDecidable _) (some (st.log i ++ [e])) (st.ledLog x)) n t A c →
      (∃ A0, Acked st.msgs st.leaders st.ledLog n t A0 c ∧ A0.take c = A.take c) ∨
      (t = st.currentTerm i ∧ n = i ∧ A = st.log i ++ [e] ∧ c = (st.log i).length + 1) := by
    intro n t A c h
    rcases Acked.of_leaderAppend (d := fun _ => Classical.propDecidable _) _ _ _ _ _ e n t A c hled
      (fun i' x' hx' => by
        obtain ⟨_, _, L, hL, hxL⟩ := hAF _ hx' n i' _ x' rfl
        rw [hled] at hL; cases hL; exact hxL) h with ⟨_, h'⟩ | ⟨rfl, rfl, ⟨hc, h'⟩ | ⟨hc, hin⟩⟩
    · exact Or.inl ⟨A, h', rfl⟩
    · exact Or.inl ⟨st.log i, h', by rw [List.take_append_of_le_length hc]⟩
    · exact Or.inr ⟨rfl, (hES _ _ hin (hLE i hrole) rfl), rfl, hc⟩
  intro j k
  have hs := Sorted.append (st.log i) [e] (st.currentTerm i)
    (sorted_of_fromLed st.ledLog _ _ (hLFL i) hLS (hLogTB i)) (by intro e' he'; simp at he'; rw [he', he])
  by_cases hj : i = j
  · subst hj; rw [RaftVeil.Lemmas.ifPos rfl]; exact hs.2 k
  · rw [RaftVeil.Lemmas.ifNeg hj]; exact hLogTB j k

prove_veil_invariant_goal LeaderAppend LedSorted using wp by
  have hES := hinv.1
  have hLE := hinv.2.2.2.2.2.2.1
  have hLLL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLS := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hAF := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro hty hrole
  have hled := hLLL i hrole
  generalize hE : ({ term := st.currentTerm i, kind := ty, value := _ } : Entry value) = e
  have he : e.term = st.currentTerm i := by rw [← hE]
  have hg := ledGrows_append (d := fun _ => Classical.propDecidable _) st.ledLog (st.currentTerm i) (st.log i) e hled he
  have hlen : ∀ n t A c, Acked st.msgs st.leaders st.ledLog n t A c → c ≤ A.length :=
    fun n t A c h => Acked.le_length _ _ _ _ _ _ _ (fun i' x' hx' => (hAF _ hx' n i' t x' rfl).2.2) h
  have hold : ∀ n t A c, Acked st.msgs st.leaders (fun x => @ite _ (st.currentTerm i = x) (Classical.propDecidable _) (some (st.log i ++ [e])) (st.ledLog x)) n t A c →
      (∃ A0, Acked st.msgs st.leaders st.ledLog n t A0 c ∧ A0.take c = A.take c) ∨
      (t = st.currentTerm i ∧ n = i ∧ A = st.log i ++ [e] ∧ c = (st.log i).length + 1) := by
    intro n t A c h
    rcases Acked.of_leaderAppend (d := fun _ => Classical.propDecidable _) _ _ _ _ _ e n t A c hled
      (fun i' x' hx' => by
        obtain ⟨_, _, L, hL, hxL⟩ := hAF _ hx' n i' _ x' rfl
        rw [hled] at hL; cases hL; exact hxL) h with ⟨_, h'⟩ | ⟨rfl, rfl, ⟨hc, h'⟩ | ⟨hc, hin⟩⟩
    · exact Or.inl ⟨A, h', rfl⟩
    · exact Or.inl ⟨st.log i, h', by rw [List.take_append_of_le_length hc]⟩
    · exact Or.inr ⟨rfl, (hES _ _ hin (hLE i hrole) rfl), rfl, hc⟩
  intro t L hL
  by_cases hc : st.currentTerm i = t
  · rw [RaftVeil.Lemmas.ifPos hc] at hL; cases hL
    rw [← hc]
    exact Sorted.append (st.log i) [e] (st.currentTerm i) (hLS _ _ hled) (by intro e' he'; simp at he'; rw [he', he])
  · rw [RaftVeil.Lemmas.ifNeg hc] at hL; exact hLS t L hL

prove_veil_invariant_goal LeaderAppend ReqFacts using wp by
  have hES := hinv.1
  have hLE := hinv.2.2.2.2.2.2.1
  have hLLL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hRF := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hAF := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  first | intro (a : Msg server value) hty hrole | intro hty hrole (a : Msg server value)
  have hled := hLLL i hrole
  generalize hE : ({ term := st.currentTerm i, kind := ty, value := _ } : Entry value) = e
  have he : e.term = st.currentTerm i := by rw [← hE]
  have hg := ledGrows_append (d := fun _ => Classical.propDecidable _) st.ledLog (st.currentTerm i) (st.log i) e hled he
  have hlen : ∀ n t A c, Acked st.msgs st.leaders st.ledLog n t A c → c ≤ A.length :=
    fun n t A c h => Acked.le_length _ _ _ _ _ _ _ (fun i' x' hx' => (hAF _ hx' n i' t x' rfl).2.2) h
  have hold : ∀ n t A c, Acked st.msgs st.leaders (fun x => @ite _ (st.currentTerm i = x) (Classical.propDecidable _) (some (st.log i ++ [e])) (st.ledLog x)) n t A c →
      (∃ A0, Acked st.msgs st.leaders st.ledLog n t A0 c ∧ A0.take c = A.take c) ∨
      (t = st.currentTerm i ∧ n = i ∧ A = st.log i ++ [e] ∧ c = (st.log i).length + 1) := by
    intro n t A c h
    rcases Acked.of_leaderAppend (d := fun _ => Classical.propDecidable _) _ _ _ _ _ e n t A c hled
      (fun i' x' hx' => by
        obtain ⟨_, _, L, hL, hxL⟩ := hAF _ hx' n i' _ x' rfl
        rw [hled] at hL; cases hL; exact hxL) h with ⟨_, h'⟩ | ⟨rfl, rfl, ⟨hc, h'⟩ | ⟨hc, hin⟩⟩
    · exact Or.inl ⟨A, h', rfl⟩
    · exact Or.inl ⟨st.log i, h', by rw [List.take_append_of_le_length hc]⟩
    · exact Or.inr ⟨rfl, (hES _ _ hin (hLE i hrole) rfl), rfl, hc⟩
  intro ha c u li lt heq
  obtain ⟨h1, h2⟩ := hRF a ha c u li lt heq
  exact ⟨h1, ReqOk.grows _ _ _ _ _ hg h2⟩

prove_veil_invariant_goal LeaderAppend ReqUnique using wp by
  have hReqUnique := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal LeaderAppend VoteHasReq using wp by
  have hVoteHasReq := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal LeaderAppend CandLog using wp by
  have hCandLog := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal LeaderAppend LedExtendsReq using wp by
  have hES := hinv.1
  have hLE := hinv.2.2.2.2.2.2.1
  have hLLL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLER := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hAF := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  first | intro (ld : Elected server) hty hrole | intro hty hrole (ld : Elected server)
  have hled := hLLL i hrole
  generalize hE : ({ term := st.currentTerm i, kind := ty, value := _ } : Entry value) = e
  have he : e.term = st.currentTerm i := by rw [← hE]
  have hg := ledGrows_append (d := fun _ => Classical.propDecidable _) st.ledLog (st.currentTerm i) (st.log i) e hled he
  have hlen : ∀ n t A c, Acked st.msgs st.leaders st.ledLog n t A c → c ≤ A.length :=
    fun n t A c h => Acked.le_length _ _ _ _ _ _ _ (fun i' x' hx' => (hAF _ hx' n i' t x' rfl).2.2) h
  have hold : ∀ n t A c, Acked st.msgs st.leaders (fun x => @ite _ (st.currentTerm i = x) (Classical.propDecidable _) (some (st.log i ++ [e])) (st.ledLog x)) n t A c →
      (∃ A0, Acked st.msgs st.leaders st.ledLog n t A0 c ∧ A0.take c = A.take c) ∨
      (t = st.currentTerm i ∧ n = i ∧ A = st.log i ++ [e] ∧ c = (st.log i).length + 1) := by
    intro n t A c h
    rcases Acked.of_leaderAppend (d := fun _ => Classical.propDecidable _) _ _ _ _ _ e n t A c hled
      (fun i' x' hx' => by
        obtain ⟨_, _, L, hL, hxL⟩ := hAF _ hx' n i' _ x' rfl
        rw [hled] at hL; cases hL; exact hxL) h with ⟨_, h'⟩ | ⟨rfl, rfl, ⟨hc, h'⟩ | ⟨hc, hin⟩⟩
    · exact Or.inl ⟨A, h', rfl⟩
    · exact Or.inl ⟨st.log i, h', by rw [List.take_append_of_le_length hc]⟩
    · exact Or.inr ⟨rfl, (hES _ _ hin (hLE i hrole) rfl), rfl, hc⟩
  intro hld m hm li lt heq L hL
  by_cases hc : st.currentTerm i = ld.term
  · rw [RaftVeil.Lemmas.ifPos hc] at hL; cases hL
    obtain ⟨h1, h2⟩ := hLER ld hld m hm li lt heq (st.log i) (by rw [← hc]; exact hled)
    show li ≤ (st.log i ++ [e]).length ∧ TermAt (st.log i ++ [e]) li = lt
    exact ⟨by simp; omega, by rw [termAt_append_left _ _ _ h1]; exact h2⟩
  · rw [RaftVeil.Lemmas.ifNeg hc] at hL; exact hLER ld hld m hm li lt heq L hL

prove_veil_invariant_goal LeaderAppend AckFacts using wp by
  have hES := hinv.1
  have hLE := hinv.2.2.2.2.2.2.1
  have hLLL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hAF := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  first | intro (a : Msg server value) hty hrole | intro hty hrole (a : Msg server value)
  have hled := hLLL i hrole
  generalize hE : ({ term := st.currentTerm i, kind := ty, value := _ } : Entry value) = e
  have he : e.term = st.currentTerm i := by rw [← hE]
  have hg := ledGrows_append (d := fun _ => Classical.propDecidable _) st.ledLog (st.currentTerm i) (st.log i) e hled he
  have hlen : ∀ n t A c, Acked st.msgs st.leaders st.ledLog n t A c → c ≤ A.length :=
    fun n t A c h => Acked.le_length _ _ _ _ _ _ _ (fun i' x' hx' => (hAF _ hx' n i' t x' rfl).2.2) h
  have hold : ∀ n t A c, Acked st.msgs st.leaders (fun x => @ite _ (st.currentTerm i = x) (Classical.propDecidable _) (some (st.log i ++ [e])) (st.ledLog x)) n t A c →
      (∃ A0, Acked st.msgs st.leaders st.ledLog n t A0 c ∧ A0.take c = A.take c) ∨
      (t = st.currentTerm i ∧ n = i ∧ A = st.log i ++ [e] ∧ c = (st.log i).length + 1) := by
    intro n t A c h
    rcases Acked.of_leaderAppend (d := fun _ => Classical.propDecidable _) _ _ _ _ _ e n t A c hled
      (fun i' x' hx' => by
        obtain ⟨_, _, L, hL, hxL⟩ := hAF _ hx' n i' _ x' rfl
        rw [hled] at hL; cases hL; exact hxL) h with ⟨_, h'⟩ | ⟨rfl, rfl, ⟨hc, h'⟩ | ⟨hc, hin⟩⟩
    · exact Or.inl ⟨A, h', rfl⟩
    · exact Or.inl ⟨st.log i, h', by rw [List.take_append_of_le_length hc]⟩
    · exact Or.inr ⟨rfl, (hES _ _ hin (hLE i hrole) rfl), rfl, hc⟩
  intro ha j i' t x heq
  obtain ⟨h1, h2, L, hL, hx⟩ := hAF a ha j i' t x heq
  obtain ⟨es, hL', _⟩ := hg t L hL
  exact ⟨h1, h2, L ++ es, hL', by simp; omega⟩

prove_veil_invariant_goal LeaderAppend AckedHeld using wp by
  have hES := hinv.1
  have hLE := hinv.2.2.2.2.2.2.1
  have hLLL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLS := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hAF := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hAH := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro hty hrole
  have hled := hLLL i hrole
  generalize hE : ({ term := st.currentTerm i, kind := ty, value := _ } : Entry value) = e
  have he : e.term = st.currentTerm i := by rw [← hE]
  have hg := ledGrows_append (d := fun _ => Classical.propDecidable _) st.ledLog (st.currentTerm i) (st.log i) e hled he
  have hlen : ∀ n t A c, Acked st.msgs st.leaders st.ledLog n t A c → c ≤ A.length :=
    fun n t A c h => Acked.le_length _ _ _ _ _ _ _ (fun i' x' hx' => (hAF _ hx' n i' t x' rfl).2.2) h
  have hold : ∀ n t A c, Acked st.msgs st.leaders (fun x => @ite _ (st.currentTerm i = x) (Classical.propDecidable _) (some (st.log i ++ [e])) (st.ledLog x)) n t A c →
      (∃ A0, Acked st.msgs st.leaders st.ledLog n t A0 c ∧ A0.take c = A.take c) ∨
      (t = st.currentTerm i ∧ n = i ∧ A = st.log i ++ [e] ∧ c = (st.log i).length + 1) := by
    intro n t A c h
    rcases Acked.of_leaderAppend (d := fun _ => Classical.propDecidable _) _ _ _ _ _ e n t A c hled
      (fun i' x' hx' => by
        obtain ⟨_, _, L, hL, hxL⟩ := hAF _ hx' n i' _ x' rfl
        rw [hled] at hL; cases hL; exact hxL) h with ⟨_, h'⟩ | ⟨rfl, rfl, ⟨hc, h'⟩ | ⟨hc, hin⟩⟩
    · exact Or.inl ⟨A, h', rfl⟩
    · exact Or.inl ⟨st.log i, h', by rw [List.take_append_of_le_length hc]⟩
    · exact Or.inr ⟨rfl, (hES _ _ hin (hLE i hrole) rfl), rfl, hc⟩
  intro n t A c h
  rcases hold n t A c h with ⟨A0, h', heq⟩ | ⟨rfl, rfl, rfl, rfl⟩
  · rcases hAH n t A0 c h' with h1 | h1
    · left
      rw [← heq]
      by_cases hj : i = n
      · subst hj; rw [RaftVeil.Lemmas.ifPos rfl]; exact h1.trans (List.prefix_append _ _)
      · rw [RaftVeil.Lemmas.ifNeg hj]; exact h1
    · exact Or.inr (LostIn.congr _ _ _ _ _ _ heq
        (LostIn.grows _ _ _ _ _ _ hg (hlen n t A0 c h') (hLS t A0 h'.1).2 h1))
  · left
    rw [RaftVeil.Lemmas.ifPos rfl]
    exact List.take_prefix _ _

prove_veil_invariant_goal LeaderAppend AckVote using wp by
  have hES := hinv.1
  have hVT := hinv.2.2.1
  have hVB := hinv.2.2.2.1
  have hLE := hinv.2.2.2.2.2.2.1
  have hLLL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLS := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hAF := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hAV := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  first | intro (v : Vote server) hty hrole | intro hty hrole (v : Vote server)
  have hled := hLLL i hrole
  generalize hE : ({ term := st.currentTerm i, kind := ty, value := _ } : Entry value) = e
  have he : e.term = st.currentTerm i := by rw [← hE]
  have hg := ledGrows_append (d := fun _ => Classical.propDecidable _) st.ledLog (st.currentTerm i) (st.log i) e hled he
  have hlen : ∀ n t A c, Acked st.msgs st.leaders st.ledLog n t A c → c ≤ A.length :=
    fun n t A c h => Acked.le_length _ _ _ _ _ _ _ (fun i' x' hx' => (hAF _ hx' n i' t x' rfl).2.2) h
  have hold : ∀ n t A c, Acked st.msgs st.leaders (fun x => @ite _ (st.currentTerm i = x) (Classical.propDecidable _) (some (st.log i ++ [e])) (st.ledLog x)) n t A c →
      (∃ A0, Acked st.msgs st.leaders st.ledLog n t A0 c ∧ A0.take c = A.take c) ∨
      (t = st.currentTerm i ∧ n = i ∧ A = st.log i ++ [e] ∧ c = (st.log i).length + 1) := by
    intro n t A c h
    rcases Acked.of_leaderAppend (d := fun _ => Classical.propDecidable _) _ _ _ _ _ e n t A c hled
      (fun i' x' hx' => by
        obtain ⟨_, _, L, hL, hxL⟩ := hAF _ hx' n i' _ x' rfl
        rw [hled] at hL; cases hL; exact hxL) h with ⟨_, h'⟩ | ⟨rfl, rfl, ⟨hc, h'⟩ | ⟨hc, hin⟩⟩
    · exact Or.inl ⟨A, h', rfl⟩
    · exact Or.inl ⟨st.log i, h', by rw [List.take_append_of_le_length hc]⟩
    · exact Or.inr ⟨rfl, (hES _ _ hin (hLE i hrole) rfl), rfl, hc⟩
  intro n t A c h hv hvn htv li lt hreq
  rcases hold n t A c h with ⟨A0, h', heq⟩ | ⟨rfl, rfl, rfl, rfl⟩
  · rcases hAV v n t A0 c h' hv hvn htv li lt hreq with h1 | h1
    · exact Or.inl (Covers.congr _ _ _ _ _ _ heq (Covers.grows _ _ _ _ _ _ hg (hlen n t A0 c h') h1))
    · exact Or.inr (LostIn.congr _ _ _ _ _ _ heq
        (LostIn.grows _ _ _ _ _ _ hg (hlen n t A0 c h') (hLS t A0 h'.1).2 h1))
  · have h1 := hVB v hv
    have h2 := hVT v.voter
    rw [hvn] at h1 h2
    omega

prove_veil_invariant_goal LeaderAppend EarlyQuorum using wp by
  have hES := hinv.1
  have hVT := hinv.2.2.1
  have hVB := hinv.2.2.2.1
  have hLE := hinv.2.2.2.2.2.2.1
  have hLLL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLS := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hAF := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hEQ := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  first | intro (ld : Elected server) hty hrole | intro hty hrole (ld : Elected server)
  have hled := hLLL i hrole
  generalize hE : ({ term := st.currentTerm i, kind := ty, value := _ } : Entry value) = e
  have he : e.term = st.currentTerm i := by rw [← hE]
  have hg := ledGrows_append (d := fun _ => Classical.propDecidable _) st.ledLog (st.currentTerm i) (st.log i) e hled he
  have hlen : ∀ n t A c, Acked st.msgs st.leaders st.ledLog n t A c → c ≤ A.length :=
    fun n t A c h => Acked.le_length _ _ _ _ _ _ _ (fun i' x' hx' => (hAF _ hx' n i' t x' rfl).2.2) h
  have hold : ∀ n t A c, Acked st.msgs st.leaders (fun x => @ite _ (st.currentTerm i = x) (Classical.propDecidable _) (some (st.log i ++ [e])) (st.ledLog x)) n t A c →
      (∃ A0, Acked st.msgs st.leaders st.ledLog n t A0 c ∧ A0.take c = A.take c) ∨
      (t = st.currentTerm i ∧ n = i ∧ A = st.log i ++ [e] ∧ c = (st.log i).length + 1) := by
    intro n t A c h
    rcases Acked.of_leaderAppend (d := fun _ => Classical.propDecidable _) _ _ _ _ _ e n t A c hled
      (fun i' x' hx' => by
        obtain ⟨_, _, L, hL, hxL⟩ := hAF _ hx' n i' _ x' rfl
        rw [hled] at hL; cases hL; exact hxL) h with ⟨_, h'⟩ | ⟨rfl, rfl, ⟨hc, h'⟩ | ⟨hc, hin⟩⟩
    · exact Or.inl ⟨A, h', rfl⟩
    · exact Or.inl ⟨st.log i, h', by rw [List.take_append_of_le_length hc]⟩
    · exact Or.inr ⟨rfl, (hES _ _ hin (hLE i hrole) rfl), rfl, hc⟩
  intro hld
  refine IsQuorum.mono _ _ ?_ (hEQ ld hld)
  intro n hn
  simp only [decide_eq_true_eq] at hn ⊢
  refine ⟨hn.1, ?_⟩
  intro t A c ha htu li lt hr
  rcases hold n t A c ha with ⟨A0, h', heq⟩ | ⟨rfl, rfl, rfl, rfl⟩
  · rcases hn.2 t A0 c h' htu li lt hr with h1 | h1
    · exact Or.inl (Covers.congr _ _ _ _ _ _ heq (Covers.grows _ _ _ _ _ _ hg (hlen n t A0 c h') h1))
    · exact Or.inr (LostIn.congr _ _ _ _ _ _ heq
        (LostIn.grows _ _ _ _ _ _ hg (hlen n t A0 c h') (hLS t A0 h'.1).2 h1))
  · have h1 := hVB _ hn.1
    have h2 := hVT n
    simp only at h1
    omega

prove_veil_invariant_goal LeaderAppend ConfirmedIsLed using wp by
  have hES := hinv.1
  have hLE := hinv.2.2.2.2.2.2.1
  have hLLL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hAF := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hCIL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro hty hrole
  have hled := hLLL i hrole
  generalize hE : ({ term := st.currentTerm i, kind := ty, value := _ } : Entry value) = e
  have he : e.term = st.currentTerm i := by rw [← hE]
  have hg := ledGrows_append (d := fun _ => Classical.propDecidable _) st.ledLog (st.currentTerm i) (st.log i) e hled he
  have hlen : ∀ n t A c, Acked st.msgs st.leaders st.ledLog n t A c → c ≤ A.length :=
    fun n t A c h => Acked.le_length _ _ _ _ _ _ _ (fun i' x' hx' => (hAF _ hx' n i' t x' rfl).2.2) h
  have hold : ∀ n t A c, Acked st.msgs st.leaders (fun x => @ite _ (st.currentTerm i = x) (Classical.propDecidable _) (some (st.log i ++ [e])) (st.ledLog x)) n t A c →
      (∃ A0, Acked st.msgs st.leaders st.ledLog n t A0 c ∧ A0.take c = A.take c) ∨
      (t = st.currentTerm i ∧ n = i ∧ A = st.log i ++ [e] ∧ c = (st.log i).length + 1) := by
    intro n t A c h
    rcases Acked.of_leaderAppend (d := fun _ => Classical.propDecidable _) _ _ _ _ _ e n t A c hled
      (fun i' x' hx' => by
        obtain ⟨_, _, L, hL, hxL⟩ := hAF _ hx' n i' _ x' rfl
        rw [hled] at hL; cases hL; exact hxL) h with ⟨_, h'⟩ | ⟨rfl, rfl, ⟨hc, h'⟩ | ⟨hc, hin⟩⟩
    · exact Or.inl ⟨A, h', rfl⟩
    · exact Or.inl ⟨st.log i, h', by rw [List.take_append_of_le_length hc]⟩
    · exact Or.inr ⟨rfl, (hES _ _ hin (hLE i hrole) rfl), rfl, hc⟩
  intro j
  rcases hCIL j with h | ⟨L, hL, h1, h2⟩
  · exact Or.inl h
  · obtain ⟨es, hL', _⟩ := hg _ L hL
    have hlL : st.confirmedIndex j ≤ L.length := by
      have := congrArg List.length h2; simp at this; omega
    refine Or.inr ⟨L ++ es, hL', ?_, ?_⟩
    · by_cases hj : i = j
      · subst hj; rw [RaftVeil.Lemmas.ifPos rfl]
        show st.confirmedIndex i ≤ (st.log i ++ [e]).length
        simp; omega
      · rw [RaftVeil.Lemmas.ifNeg hj]; exact h1
    · rw [List.take_append_of_le_length hlL]
      by_cases hj : i = j
      · subst hj; rw [RaftVeil.Lemmas.ifPos rfl]
        show List.take (st.confirmedIndex i) (st.log i ++ [e]) = List.take (st.confirmedIndex i) L
        rw [List.take_append_of_le_length h1]; exact h2
      · rw [RaftVeil.Lemmas.ifNeg hj]; exact h2

prove_veil_invariant_goal LeaderAppend CommitRoot using wp by
  have hES := hinv.1
  have hLE := hinv.2.2.2.2.2.2.1
  have hLLL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hAF := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hCR := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  first | intro (k : Commit server value) hty hrole | intro hty hrole (k : Commit server value)
  have hled := hLLL i hrole
  generalize hE : ({ term := st.currentTerm i, kind := ty, value := _ } : Entry value) = e
  have he : e.term = st.currentTerm i := by rw [← hE]
  have hg := ledGrows_append (d := fun _ => Classical.propDecidable _) st.ledLog (st.currentTerm i) (st.log i) e hled he
  have hlen : ∀ n t A c, Acked st.msgs st.leaders st.ledLog n t A c → c ≤ A.length :=
    fun n t A c h => Acked.le_length _ _ _ _ _ _ _ (fun i' x' hx' => (hAF _ hx' n i' t x' rfl).2.2) h
  have hold : ∀ n t A c, Acked st.msgs st.leaders (fun x => @ite _ (st.currentTerm i = x) (Classical.propDecidable _) (some (st.log i ++ [e])) (st.ledLog x)) n t A c →
      (∃ A0, Acked st.msgs st.leaders st.ledLog n t A0 c ∧ A0.take c = A.take c) ∨
      (t = st.currentTerm i ∧ n = i ∧ A = st.log i ++ [e] ∧ c = (st.log i).length + 1) := by
    intro n t A c h
    rcases Acked.of_leaderAppend (d := fun _ => Classical.propDecidable _) _ _ _ _ _ e n t A c hled
      (fun i' x' hx' => by
        obtain ⟨_, _, L, hL, hxL⟩ := hAF _ hx' n i' _ x' rfl
        rw [hled] at hL; cases hL; exact hxL) h with ⟨_, h'⟩ | ⟨rfl, rfl, ⟨hc, h'⟩ | ⟨hc, hin⟩⟩
    · exact Or.inl ⟨A, h', rfl⟩
    · exact Or.inl ⟨st.log i, h', by rw [List.take_append_of_le_length hc]⟩
    · exact Or.inr ⟨rfl, (hES _ _ hin (hLE i hrole) rfl), rfl, hc⟩
  intro hk
  obtain ⟨h1, r, h2, h3, h4, h5⟩ := hCR k hk
  exact ⟨h1, r, h2, Root.mono _ _ _ _ _ _ _ (fun a ha => ha) (fun a ha => ha) hg h3, h4, h5⟩

prove_veil_invariant_goal LeaderAppend CommitSafety using wp by
  have hCommitSafety := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal LeaderAppend ConfirmedTermBound using wp by
  have hConfirmedTermBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal LeaderAppend CommitTermBound using wp by
  have hCommitTermBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal LeaderAppend CommittedEntriesPreserved using wp by
  have hCEP := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro cc hty hrole hc
  by_cases hd : i = cc.server
  · rw [RaftVeil.Lemmas.ifPos hd, isPrefix_iff]
    have := hCEP cc hc
    rw [isPrefix_iff, ← hd] at this
    exact this.trans (List.prefix_append _ _)
  · rw [RaftVeil.Lemmas.ifNeg hd]; exact hCEP cc hc

prove_veil_invariant_goal LeaderAppend CommitIndexCommitted using wp by
  have hCommitIndexCommitted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal LeaderAppend AppliedCommitted using wp by
  have hAppliedCommitted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal LeaderAppend StateMachineSafety using wp by
  have hStateMachineSafety := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal LeaderAppend LeaderCompleteness using wp by
  have hLC := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro cc hty hrole i1 hc hrole1 hlt
  by_cases hd : i = i1
  · subst hd
    rw [RaftVeil.Lemmas.ifPos rfl, isPrefix_iff]
    have := hLC cc i hc hrole1 hlt
    rw [isPrefix_iff] at this
    exact this.trans (List.prefix_append _ _)
  · rw [RaftVeil.Lemmas.ifNeg hd]; exact hLC cc i1 hc hrole1 hlt

prove_veil_invariant_goal LeaderAppend ConfirmedWithinLog using wp by
  have hCWL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro hty hrole i1
  by_cases hd : i = i1
  · subst hd
    rw [RaftVeil.Lemmas.ifPos rfl]
    show _ ≤ (st.log i ++ [_]).length
    rw [List.length_append]
    have := hCWL i
    omega
  · rw [RaftVeil.Lemmas.ifNeg hd]; exact hCWL i1

prove_veil_invariant_goal LeaderAppend PreVoteRequestsBounded using wp by
  have hPreVoteRequestsBounded := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal LeaderAppend PreGrantsAnswer using wp by
  have hPreGrantsAnswer := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal LeaderAppend TimeoutNowFromLeader using wp by
  have hTimeoutNowFromLeader := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal LeaderAppend TransferIsCandidate using wp by
  have hTransferIsCandidate := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal LeaderAppend SnapshotWithinLog using wp by
  have hSWL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro hty hrole j
  by_cases hd : i = j
  · subst hd
    rw [RaftVeil.Lemmas.ifPos rfl]
    exact (isPrefix_iff _ _).2 (((isPrefix_iff _ _).1 (hSWL i)).trans (List.prefix_append _ _))
  · rw [RaftVeil.Lemmas.ifNeg hd]; exact hSWL j

prove_veil_invariant_goal LeaderAppend BaseWithinSnapshot using wp by
  have hBaseWithinSnapshot := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal LeaderAppend SnapshotCommitted using wp by
  have hSnapshotCommitted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal LeaderAppend SnapshotApplied using wp by
  have hSnapshotApplied := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

-- SendAppend

prove_veil_invariant_goal SendAppend ElectionSafety using wp by
  have hElectionSafety := hinv.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendAppend OneVotePerTerm using wp by
  have hOneVotePerTerm := hinv.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendAppend VoteTermBound using wp by
  have hVoteTermBound := hinv.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendAppend VotesBound using wp by
  have hVotesBound := hinv.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendAppend GrantsAreVotes using wp by
  have hGV := hinv.2.2.2.2.1
  clear hinv
  intros
  simp only [RaftVeil.Lemmas.mem_iff, RaftVeil.Lemmas.contains_insert_iff] at *
  repeat' split
  all_goals grind only

prove_veil_invariant_goal SendAppend LeadersHaveQuorum using wp by
  have hLeadersHaveQuorum := hinv.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendAppend LeaderIsElected using wp by
  have hLeaderIsElected := hinv.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendAppend LeadersTermBound using wp by
  have hLeadersTermBound := hinv.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendAppend LedOwner using wp by
  have hLedOwner := hinv.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendAppend LeadersHaveLed using wp by
  have hLeadersHaveLed := hinv.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendAppend LedHasLeader using wp by
  have hLedHasLeader := hinv.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendAppend AppendFromLeader using wp by
  have hAFL := hinv.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  rename_i ld p
  intro hji hld hsrv hpn hcm m hm
  rw [RaftVeil.Lemmas.mem_insert] at hm
  rcases hm with rfl | hm
  · subst hsrv
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not]
    exact ⟨hji, hld⟩
  · exact hAFL m hm

prove_veil_invariant_goal SendAppend LeaderLogIsLed using wp by
  have hLeaderLogIsLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendAppend RequestsFromLed using wp by
  have hLHL := hinv.2.2.2.2.2.2.2.2.2.1
  have hRFL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  rename_i ld p
  obtain ⟨p, hp⟩ := p
  obtain ⟨n, hn⟩ := a
  obtain ⟨c, hc⟩ := b
  intro hji hld hsrv hpn hcm m hm
  rw [RaftVeil.Lemmas.mem_insert] at hm
  rcases hm with rfl | hm
  · obtain ⟨l, hL⟩ := Option.ne_none_iff_exists'.1 (hLHL ld hld)
    simp only [hL, Option.getD_some, List.mem_range] at hc hpn hcm ⊢
    have hlen := subSeq_length l p n hpn
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, hlen]
    refine ⟨hpn, trivial, trivial, ?_⟩
    rcases hcm with h0 | ⟨k, hk1, hk2, hk3, hk4⟩
    · exact Or.inl h0
    · exact Or.inr ⟨by omega, ⟨k, hk3⟩, hk1, hk2, hk4⟩
  · exact hRFL m hm

prove_veil_invariant_goal SendAppend BootEntry using wp by
  have hBootEntry := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendAppend LedBoot using wp by
  have hLedBoot := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendAppend LogFromLed using wp by
  have hLogFromLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendAppend LedFromLed using wp by
  have hLedFromLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendAppend LogMatching using wp by
  have hLogMatching := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendAppend TermsPositive using wp by
  have hTermsPositive := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendAppend LogTermsBound using wp by
  have hLogTermsBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendAppend LedSorted using wp by
  have hLedSorted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendAppend ReqFacts using wp by
  have hReqFacts := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendAppend ReqUnique using wp by
  have hReqUnique := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendAppend VoteHasReq using wp by
  have hVoteHasReq := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendAppend CandLog using wp by
  have hCandLog := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendAppend LedExtendsReq using wp by
  have hLedExtendsReq := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendAppend AckFacts using wp by
  have hAckFacts := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendAppend AckedHeld using wp by
  have hAH := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  rename_i n t A c hack
  exact hAH n t A c (Acked.of_insert _ _ _ _ _ _ _ _ (fun _ _ _ _ h => by cases h) hack)

prove_veil_invariant_goal SendAppend AckVote using wp by
  have hAV := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro v
  intros
  rename_i n t A c hack hv hvn htv li lt hreq
  rcases (RaftVeil.Lemmas.contains_insert_iff _ _ _).1 hreq with h | h
  · cases h
  · exact hAV v n t A c (Acked.of_insert _ _ _ _ _ _ _ _ (fun _ _ _ _ h => by cases h) hack) hv hvn htv li lt h

prove_veil_invariant_goal SendAppend EarlyQuorum using wp by
  have hEQ := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro ld
  intros
  rename_i hld
  refine IsQuorum.mono _ _ ?_ (hEQ ld hld)
  intro n hn
  simp only [decide_eq_true_eq] at hn ⊢
  exact ⟨hn.1, Early.of_insert _ _ _ _ _ _ _ (fun _ _ _ _ h => by cases h) (fun _ _ h => by cases h) hn.2⟩

prove_veil_invariant_goal SendAppend ConfirmedIsLed using wp by
  have hConfirmedIsLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendAppend CommitRoot using wp by
  have hCR := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro k
  intros
  rename_i hk
  obtain ⟨h1, r, h2, h3, h4, h5⟩ := hCR k hk
  exact ⟨h1, r, h2, Root.mono _ _ _ _ _ _ _ (fun a ha => (RaftVeil.Lemmas.mem_insert _ _ _).2 (Or.inr ha))
    (fun a ha => ha) (LedGrows.refl _) h3, h4, h5⟩

prove_veil_invariant_goal SendAppend CommitSafety using wp by
  have hCommitSafety := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendAppend ConfirmedTermBound using wp by
  have hConfirmedTermBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendAppend CommitTermBound using wp by
  have hCommitTermBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendAppend CommittedEntriesPreserved using wp by
  have hCommittedEntriesPreserved := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendAppend CommitIndexCommitted using wp by
  have hCommitIndexCommitted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendAppend AppliedCommitted using wp by
  have hAppliedCommitted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendAppend StateMachineSafety using wp by
  have hStateMachineSafety := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendAppend LeaderCompleteness using wp by
  have hLeaderCompleteness := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendAppend ConfirmedWithinLog using wp by
  have hConfirmedWithinLog := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendAppend PreVoteRequestsBounded using wp by
  have hPreVoteRequestsBounded := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendAppend PreGrantsAnswer using wp by
  have hPGA := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  rename_i a ha
  rw [RaftVeil.Lemmas.mem_insert] at ha
  rcases ha with rfl | ha
  · rfl
  · refine pregrants_mono _ _ a (hPGA a ha) ?_
    intro d t hx
    simp only [decide_eq_true_eq] at hx ⊢
    obtain ⟨⟨m, hm⟩, hm2⟩ := hx
    exact ⟨⟨m, (RaftVeil.Lemmas.mem_insert _ _ _).2 (Or.inr hm)⟩, hm2⟩

prove_veil_invariant_goal SendAppend TimeoutNowFromLeader using wp by
  have hTimeoutNowFromLeader := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendAppend TransferIsCandidate using wp by
  have hTransferIsCandidate := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendAppend SnapshotWithinLog using wp by
  have hSnapshotWithinLog := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendAppend BaseWithinSnapshot using wp by
  have hBaseWithinSnapshot := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendAppend SnapshotCommitted using wp by
  have hSnapshotCommitted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendAppend SnapshotApplied using wp by
  have hSnapshotApplied := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

-- LeaderCommit

prove_veil_invariant_goal LeaderCommit ElectionSafety using wp by
  have hElectionSafety := hinv.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal LeaderCommit OneVotePerTerm using wp by
  have hOneVotePerTerm := hinv.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal LeaderCommit VoteTermBound using wp by
  have hVoteTermBound := hinv.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal LeaderCommit VotesBound using wp by
  have hVotesBound := hinv.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal LeaderCommit GrantsAreVotes using wp by
  have hGrantsAreVotes := hinv.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal LeaderCommit LeadersHaveQuorum using wp by
  have hLeadersHaveQuorum := hinv.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal LeaderCommit LeaderIsElected using wp by
  have hLeaderIsElected := hinv.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal LeaderCommit LeadersTermBound using wp by
  have hLeadersTermBound := hinv.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal LeaderCommit LedOwner using wp by
  have hLedOwner := hinv.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal LeaderCommit LeadersHaveLed using wp by
  have hLeadersHaveLed := hinv.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal LeaderCommit LedHasLeader using wp by
  have hLedHasLeader := hinv.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal LeaderCommit AppendFromLeader using wp by
  have hAppendFromLeader := hinv.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal LeaderCommit LeaderLogIsLed using wp by
  have hLeaderLogIsLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal LeaderCommit RequestsFromLed using wp by
  have hRFL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro _ _ c _ _ _ _ m hm
  refine req_mono st.ledLog st.ledLog _ _ m (hRFL m hm) (fun t l h => ⟨l, h, List.prefix_refl _⟩) ?_
  · intro t l l' c hp hx
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hx ⊢
    exact commitPart_mono st.commits _ (fun k hk => (RaftVeil.Lemmas.mem_insert _ _ _).2 (Or.inr hk)) l l' c t hp hx

prove_veil_invariant_goal LeaderCommit BootEntry using wp by
  have hBootEntry := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal LeaderCommit LedBoot using wp by
  have hLedBoot := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal LeaderCommit LogFromLed using wp by
  have hLogFromLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal LeaderCommit LedFromLed using wp by
  have hLedFromLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal LeaderCommit LogMatching using wp by
  have hLogMatching := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal LeaderCommit TermsPositive using wp by
  have hTermsPositive := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal LeaderCommit LogTermsBound using wp by
  have hLogTermsBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal LeaderCommit LedSorted using wp by
  have hLedSorted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal LeaderCommit ReqFacts using wp by
  have hReqFacts := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal LeaderCommit ReqUnique using wp by
  have hReqUnique := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal LeaderCommit VoteHasReq using wp by
  have hVoteHasReq := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal LeaderCommit CandLog using wp by
  have hCandLog := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal LeaderCommit LedExtendsReq using wp by
  have hLedExtendsReq := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal LeaderCommit AckFacts using wp by
  have hAckFacts := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal LeaderCommit AckedHeld using wp by
  have hAckedHeld := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal LeaderCommit AckVote using wp by
  have hAckVote := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal LeaderCommit EarlyQuorum using wp by
  have hEarlyQuorum := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal LeaderCommit ConfirmedIsLed using wp by
  have hConfirmedIsLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal LeaderCommit CommitRoot using wp by
  have hLHL := hinv.2.2.2.2.2.2.2.2.2.1
  have hBoot := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLBoot := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLFL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hCR := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro k hld hsrv c hc1 hc2 hct hq hk
  subst hsrv
  obtain ⟨A, hA⟩ := Option.ne_none_iff_exists'.1 (hLHL a hld)
  have hAB : A.head? = some Boot := by simpa using (optAll_iff _ _).1 (hLBoot a.term) A hA
  obtain ⟨hpre, hAt⟩ := take_prefix_led st.ledLog (st.log a.server) A a.term c (hLFL _) (hBoot _) hA hAB hc1 (by omega) hct
  have hlenK : (SubSeq (st.log a.server) 1 c).length = c := by
    rw [subSeq_one, List.length_take, Nat.min_eq_left (by omega)]
  have hRoot : Root st.msgs st.leaders st.ledLog
      { server := a.server, term := a.term, entries := SubSeq (st.log a.server) 1 c } := by
    refine ⟨hld, ⟨A, hA, by rw [subSeq_one]; exact hpre, by rw [hlenK]; exact hAt⟩, ?_⟩
    show QC st.msgs a.server a.term (SubSeq (st.log a.server) 1 c).length
    rw [hlenK]
    refine IsQuorum.mono _ _ ?_ hq
    intro j hj
    simp only [Bool.or_eq_true, decide_eq_true_eq] at hj ⊢
    rcases hj with hj | ⟨⟨m, hm⟩, hmm⟩
    · exact Or.inl hj
    · cases m with
      | ack src dst term index =>
        simp only [decide_eq_true_eq] at hmm
        obtain ⟨rfl, rfl, rfl, hidx⟩ := hmm
        exact Or.inr ⟨index, hm, hidx⟩
      | _ => simp at hmm
  rw [RaftVeil.Lemmas.mem_insert] at hk
  rcases hk with rfl | hk
  · refine ⟨?_, _, List.prefix_refl _, hRoot, (RaftVeil.Lemmas.mem_insert _ _ _).2 (Or.inl rfl), Nat.le_refl _⟩
    intro h
    have := congrArg List.length h
    rw [hlenK] at this
    simp at this; omega
  · obtain ⟨h1, r, h2, h3, h4, h5⟩ := hCR k hk
    exact ⟨h1, r, h2, h3, (RaftVeil.Lemmas.mem_insert _ _ _).2 (Or.inr h4), h5⟩

prove_veil_invariant_goal LeaderCommit CommitSafety using wp by
  have hLHL := hinv.2.2.2.2.2.2.2.2.2.1
  have hLHas := hinv.2.2.2.2.2.2.2.2.2.2.1
  have hBoot := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLBoot := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLFL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLedFL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hVHR := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLER := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hEQ := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hCR := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hSMS := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro r1 r2 hld hsrv c hc1 hc2 hct hq h1 h2
  subst hsrv
  obtain ⟨A, hA⟩ := Option.ne_none_iff_exists'.1 (hLHL a hld)
  have hAB : A.head? = some Boot := by simpa using (optAll_iff _ _).1 (hLBoot a.term) A hA
  obtain ⟨hpre, hAt⟩ := take_prefix_led st.ledLog (st.log a.server) A a.term c (hLFL _) (hBoot _) hA hAB hc1 (by omega) hct
  have hlenK : (SubSeq (st.log a.server) 1 c).length = c := by
    rw [subSeq_one, List.length_take, Nat.min_eq_left (by omega)]
  have hRoot : Root st.msgs st.leaders st.ledLog
      { server := a.server, term := a.term, entries := SubSeq (st.log a.server) 1 c } := by
    refine ⟨hld, ⟨A, hA, by rw [subSeq_one]; exact hpre, by rw [hlenK]; exact hAt⟩, ?_⟩
    show QC st.msgs a.server a.term (SubSeq (st.log a.server) 1 c).length
    rw [hlenK]
    refine IsQuorum.mono _ _ ?_ hq
    intro j hj
    simp only [Bool.or_eq_true, decide_eq_true_eq] at hj ⊢
    rcases hj with hj | ⟨⟨m, hm⟩, hmm⟩
    · exact Or.inl hj
    · cases m with
      | ack src dst term index =>
        simp only [decide_eq_true_eq] at hmm
        obtain ⟨rfl, rfl, rfl, hidx⟩ := hmm
        exact Or.inr ⟨index, hm, hidx⟩
      | _ => simp at hmm
  have cmp : ∀ b : Commit server value, b ∈ st.commits →
      SubSeq (st.log a.server) 1 c <+: b.entries ∨ b.entries <+: SubSeq (st.log a.server) 1 c := by
    intro b hb
    obtain ⟨_, r, hbr, hroot, hr, -⟩ := hCR b hb
    exact prefix_cmp_of_roots _ _ _ _ (List.prefix_refl _) hbr (roots_cmp st.msgs st.leaders st.votes st.ledLog hEQ hLHas hVHR hLER
      (fun t L h => (optAll_iff _ _).1 (hLedFL t) L h)
      (fun t L h => by simpa using (optAll_iff _ _).1 (hLBoot t) L h) _ r hRoot hroot)
  rw [RaftVeil.Lemmas.mem_insert] at h1 h2
  simp only [isPrefix_iff]
  rcases h1 with rfl | h1 <;> rcases h2 with rfl | h2
  · exact Or.inl (List.prefix_refl _)
  · exact cmp r2 h2
  · exact (cmp r1 h1).symm
  · have := hSMS r1 r2 h1 h2
    simpa only [isPrefix_iff] using this

prove_veil_invariant_goal LeaderCommit ConfirmedTermBound using wp by
  have hConfirmedTermBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal LeaderCommit CommitTermBound using wp by
  have hLeadersTermBound := hinv.2.2.2.2.2.2.2.1
  have hCommitTermBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal LeaderCommit CommittedEntriesPreserved using wp by
  have hCEP := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro cc hld hsrv c hc1 hc2 hct hq hk
  rw [RaftVeil.Lemmas.mem_insert] at hk
  rcases hk with rfl | hk
  · show IsPrefix (SubSeq (st.log i) 1 c) (st.log i) = true
    rw [isPrefix_iff, subSeq_one]; exact List.take_prefix _ _
  · exact hCEP cc hk

prove_veil_invariant_goal LeaderCommit CommitIndexCommitted using wp by
  have hCIC := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro hld hsrv c hc1 hc2 hct hq i1
  by_cases hd : i = i1
  · subst hd
    rw [RaftVeil.Lemmas.ifPos rfl]
    right
    rcases Nat.le_total c (st.commitIndex i) with hle | hle
    · rcases hCIC i with h0 | ⟨k, hk1, hk2, hk3⟩
      · omega
      · exact ⟨k, hk1, (RaftVeil.Lemmas.mem_insert _ _ _).2 (Or.inr hk2), by rw [Nat.max_eq_left hle]; exact hk3⟩
    · refine ⟨{ server := i, term := a.term, entries := SubSeq (st.log i) 1 c }, rfl,
        (RaftVeil.Lemmas.mem_insert _ _ _).2 (Or.inl rfl), ?_⟩
      show (SubSeq (st.log i) 1 c).length = max (st.commitIndex i) c
      rw [Nat.max_eq_right hle, subSeq_one, List.length_take]; omega
  · rw [RaftVeil.Lemmas.ifNeg hd]
    rcases hCIC i1 with h0 | ⟨k, hk1, hk2, hk3⟩
    · exact Or.inl h0
    · exact Or.inr ⟨k, hk1, (RaftVeil.Lemmas.mem_insert _ _ _).2 (Or.inr hk2), hk3⟩

prove_veil_invariant_goal LeaderCommit AppliedCommitted using wp by
  have hAppliedCommitted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal LeaderCommit StateMachineSafety using wp by
  have hStateMachineSafety := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal LeaderCommit LeaderCompleteness using wp by
  have hLHL := hinv.2.2.2.2.2.2.2.2.2.1
  have hLHas := hinv.2.2.2.2.2.2.2.2.2.2.1
  have hLLL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hBoot := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLBoot := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLFL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLedFL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hVHR := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLER := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hEQ := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLC := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro cc hld hsrv c hc1 hc2 hct hq i1 hk hrole hlt
  subst hsrv
  rw [RaftVeil.Lemmas.mem_insert] at hk
  rcases hk with rfl | hk
  · obtain ⟨A, hA⟩ := Option.ne_none_iff_exists'.1 (hLHL a hld)
    have hAB : A.head? = some Boot := by simpa using (optAll_iff _ _).1 (hLBoot a.term) A hA
    obtain ⟨hpre, hAt⟩ := take_prefix_led st.ledLog (st.log a.server) A a.term c (hLFL _) (hBoot _) hA hAB hc1 (by omega) hct
    have hlenK : (SubSeq (st.log a.server) 1 c).length = c := by
      rw [subSeq_one, List.length_take, Nat.min_eq_left (by omega)]
    have hRoot : Root st.msgs st.leaders st.ledLog
        { server := a.server, term := a.term, entries := SubSeq (st.log a.server) 1 c } := by
      refine ⟨hld, ⟨A, hA, by rw [subSeq_one]; exact hpre, by rw [hlenK]; exact hAt⟩, ?_⟩
      show QC st.msgs a.server a.term (SubSeq (st.log a.server) 1 c).length
      rw [hlenK]
      refine IsQuorum.mono _ _ ?_ hq
      intro j hj
      simp only [Bool.or_eq_true, decide_eq_true_eq] at hj ⊢
      rcases hj with hj | ⟨⟨m, hm⟩, hmm⟩
      · exact Or.inl hj
      · cases m with
        | ack src dst term index =>
          simp only [decide_eq_true_eq] at hmm
          obtain ⟨rfl, rfl, rfl, hidx⟩ := hmm
          exact Or.inr ⟨index, hm, hidx⟩
        | _ => simp at hmm
    show IsPrefix (SubSeq (st.log a.server) 1 c) (st.log i1) = true
    rw [isPrefix_iff]
    exact root_in_later st.msgs st.leaders st.votes st.ledLog hEQ hLHas hVHR hLER
      (fun t L h => (optAll_iff _ _).1 (hLedFL t) L h)
      (fun t L h => by simpa using (optAll_iff _ _).1 (hLBoot t) L h) _ hRoot (st.currentTerm i1) (Nat.le_of_lt hlt) _ (hLLL i1 hrole)
  · exact hLC cc i1 hk hrole hlt

prove_veil_invariant_goal LeaderCommit ConfirmedWithinLog using wp by
  have hConfirmedWithinLog := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal LeaderCommit PreVoteRequestsBounded using wp by
  have hPreVoteRequestsBounded := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal LeaderCommit PreGrantsAnswer using wp by
  have hPreGrantsAnswer := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal LeaderCommit TimeoutNowFromLeader using wp by
  have hTimeoutNowFromLeader := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal LeaderCommit TransferIsCandidate using wp by
  have hTransferIsCandidate := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal LeaderCommit SnapshotWithinLog using wp by
  have hSnapshotWithinLog := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal LeaderCommit BaseWithinSnapshot using wp by
  have hBaseWithinSnapshot := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal LeaderCommit SnapshotCommitted using wp by
  have hSnapshotCommitted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal LeaderCommit SnapshotApplied using wp by
  have hSnapshotApplied := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

-- DeleteSuffix

prove_veil_invariant_goal DeleteSuffix ElectionSafety using wp by
  have hElectionSafety := hinv.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal DeleteSuffix OneVotePerTerm using wp by
  have hOneVotePerTerm := hinv.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal DeleteSuffix VoteTermBound using wp by
  have hVoteTermBound := hinv.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal DeleteSuffix VotesBound using wp by
  have hVotesBound := hinv.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal DeleteSuffix GrantsAreVotes using wp by
  have hGrantsAreVotes := hinv.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal DeleteSuffix LeadersHaveQuorum using wp by
  have hLeadersHaveQuorum := hinv.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal DeleteSuffix LeaderIsElected using wp by
  have hLeaderIsElected := hinv.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal DeleteSuffix LeadersTermBound using wp by
  have hLeadersTermBound := hinv.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal DeleteSuffix LedOwner using wp by
  have hES := hinv.1
  have hLO := hinv.2.2.2.2.2.2.2.2.1
  have hAFL := hinv.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro x
  intro ha hisA hterm hprev k hk1 hk2 hfirst hlen hne hsnapk
  have hnl : ∀ x : Elected server, x ∈ st.leaders → x.term = a.term → x.server ≠ a.dst := by
    intro x hx hxt hxs
    have h := hAFL a ha
    cases a with
    | append src dst term p pt es c =>
      simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at h
      have := hES x _ hx h.2 hxt
      exact h.1 (hxs.symm.trans this)
    | _ => simp [Msg.isAppend] at hisA
  intro hx hxt
  by_cases hj : a.dst = x.server
  · exact absurd hj.symm (hnl x hx (by rw [hxt, ← hj, hterm]))
  · rw [RaftVeil.Lemmas.ifNeg hj]; exact hLO x hx hxt

prove_veil_invariant_goal DeleteSuffix LeadersHaveLed using wp by
  have hLeadersHaveLed := hinv.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal DeleteSuffix LedHasLeader using wp by
  have hLedHasLeader := hinv.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal DeleteSuffix AppendFromLeader using wp by
  have hAppendFromLeader := hinv.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal DeleteSuffix LeaderLogIsLed using wp by
  have hES := hinv.1
  have hLE := hinv.2.2.2.2.2.2.1
  have hAFL := hinv.2.2.2.2.2.2.2.2.2.2.2.1
  have hLLL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro ha hisA hterm hprev k hk1 hk2 hfirst hlen hne hsnapk
  have hnl : ∀ x : Elected server, x ∈ st.leaders → x.term = a.term → x.server ≠ a.dst := by
    intro x hx hxt hxs
    have h := hAFL a ha
    cases a with
    | append src dst term p pt es c =>
      simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at h
      have := hES x _ hx h.2 hxt
      exact h.1 (hxs.symm.trans this)
    | _ => simp [Msg.isAppend] at hisA
  intro j hj
  by_cases hd : a.dst = j
  · subst hd
    exact absurd rfl (hnl _ (hLE _ hj) hterm.symm)
  · rw [RaftVeil.Lemmas.ifNeg hd]; exact hLLL j hj

prove_veil_invariant_goal DeleteSuffix RequestsFromLed using wp by
  have hRequestsFromLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal DeleteSuffix BootEntry using wp by
  have hRFL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hBoot := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLBoot := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro ha hisA hterm hprev k hk1 hk2 hfirst hlen hne hsnapk
  obtain ⟨L, hL, hpn, hpt, hes, -⟩ := req_facts st.ledLog _ a (hRFL a ha) hisA
  intro j
  by_cases hj : a.dst = j
  · rw [RaftVeil.Lemmas.ifPos hj]
    exact delete_keeps_boot (st.log a.dst) L a.prevLogIndex k a.entries (hBoot a.dst)
      (by simpa using (optAll_iff _ _).1 (hLBoot a.term) L hL) hes (List.mem_range'_1.2 ⟨hk1, hk2⟩) hne
  · rw [RaftVeil.Lemmas.ifNeg hj]; exact hBoot j

prove_veil_invariant_goal DeleteSuffix LedBoot using wp by
  have hLedBoot := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal DeleteSuffix LogFromLed using wp by
  have hLFL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro ha hisA hterm hprev k hk1 hk2 hfirst hlen hne hsnapk j
  by_cases hj : a.dst = j
  · rw [RaftVeil.Lemmas.ifPos hj, subSeq_one]; exact FromLed.take _ _ _ (hLFL a.dst)
  · rw [RaftVeil.Lemmas.ifNeg hj]; exact hLFL j

prove_veil_invariant_goal DeleteSuffix LedFromLed using wp by
  have hLedFromLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal DeleteSuffix LogMatching using wp by
  have hRFL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hBoot := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLBoot := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLFL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro ha hisA hterm hprev k hk1 hk2 hfirst hlen hne hsnapk
  obtain ⟨L, hL, hpn, hpt, hes, -⟩ := req_facts st.ledLog _ a (hRFL a ha) hisA
  have hb := delete_keeps_boot (st.log a.dst) L a.prevLogIndex k a.entries (hBoot a.dst)
      (by simpa using (optAll_iff _ _).1 (hLBoot a.term) L hL) hes (List.mem_range'_1.2 ⟨hk1, hk2⟩) hne
  have hf : FromLed st.ledLog (SubSeq (st.log a.dst) 1 (a.prevLogIndex + k - 1)) := by
    rw [subSeq_one]; exact FromLed.take _ _ _ (hLFL a.dst)
  intro x y k' hk1' hk2'
  refine FromLed.matching st.ledLog _ _ ?_ ?_ ?_ ?_ k' (List.mem_range'_1.2 ⟨hk1', hk2'⟩)
  · by_cases hj : a.dst = x
    · rw [RaftVeil.Lemmas.ifPos hj]; exact hf
    · rw [RaftVeil.Lemmas.ifNeg hj]; exact hLFL x
  · by_cases hj : a.dst = y
    · rw [RaftVeil.Lemmas.ifPos hj]; exact hf
    · rw [RaftVeil.Lemmas.ifNeg hj]; exact hLFL y
  · by_cases hj : a.dst = x
    · rw [RaftVeil.Lemmas.ifPos hj]; exact hb
    · rw [RaftVeil.Lemmas.ifNeg hj]; exact hBoot x
  · by_cases hj : a.dst = y
    · rw [RaftVeil.Lemmas.ifPos hj]; exact hb
    · rw [RaftVeil.Lemmas.ifNeg hj]; exact hBoot y

prove_veil_invariant_goal DeleteSuffix TermsPositive using wp by
  have hTermsPositive := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal DeleteSuffix LogTermsBound using wp by
  have hRFL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLBoot := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLedFL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLogTB := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro ha hisA hterm hprev k hk1 hk2 hfirst hlen hne hsnapk
  obtain ⟨L, hL, hpn, hpt, hes, -⟩ := req_facts st.ledLog _ a (hRFL a ha) hisA
  rw [hpt] at hprev
  have hLedL := (optAll_iff _ _).1 (hLedFL a.term) L hL
  have hLB : L.head? = some Boot := by simpa using (optAll_iff _ _).1 (hLBoot a.term) L hL
  intro j k'
  by_cases hj : a.dst = j
  · subst hj; rw [RaftVeil.Lemmas.ifPos rfl, subSeq_one]
    rcases Nat.lt_or_ge (a.prevLogIndex + k - 1) k' with h | h
    · rw [termAt_le_of_gt _ _ (by simp; omega)]; omega
    · rw [termAt_take _ _ _ h]; exact hLogTB _ _
  · rw [RaftVeil.Lemmas.ifNeg hj]; exact hLogTB j k'

prove_veil_invariant_goal DeleteSuffix LedSorted using wp by
  have hLedSorted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal DeleteSuffix ReqFacts using wp by
  have hReqFacts := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal DeleteSuffix ReqUnique using wp by
  have hReqUnique := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal DeleteSuffix VoteHasReq using wp by
  have hVoteHasReq := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal DeleteSuffix CandLog using wp by
  have hRFL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLBoot := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLedFL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hCL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro ha hisA hterm hprev k hk1 hk2 hfirst hlen hne hsnapk
  obtain ⟨L, hL, hpn, hpt, hes, -⟩ := req_facts st.ledLog _ a (hRFL a ha) hisA
  rw [hpt] at hprev
  have hLedL := (optAll_iff _ _).1 (hLedFL a.term) L hL
  have hLB : L.head? = some Boot := by simpa using (optAll_iff _ _).1 (hLBoot a.term) L hL
  intro m hm c u li lt heq hcu hnone
  by_cases hj : a.dst = c
  · subst hj; rw [← hcu, ← hterm, hL] at hnone; cases hnone
  · repeat rw [RaftVeil.Lemmas.ifNeg hj]
    exact hCL m hm c u li lt heq hcu hnone

prove_veil_invariant_goal DeleteSuffix LedExtendsReq using wp by
  have hLedExtendsReq := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal DeleteSuffix AckFacts using wp by
  have hAckFacts := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal DeleteSuffix AckedHeld using wp by
  have hLTB := hinv.2.2.2.2.2.2.2.1
  have hRFL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLBoot := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLedFL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hAF := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hAH := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro ha hisA hterm hprev k hk1 hk2 hfirst hlen hne hsnapk
  obtain ⟨L, hL, hpn, hpt, hes, -⟩ := req_facts st.ledLog _ a (hRFL a ha) hisA
  rw [hpt] at hprev
  have hLedL := (optAll_iff _ _).1 (hLedFL a.term) L hL
  have hLB : L.head? = some Boot := by simpa using (optAll_iff _ _).1 (hLBoot a.term) L hL
  intro n t A c h
  rcases hAH n t A c h with h1 | h1
  · by_cases hj : a.dst = n
    · subst hj; rw [RaftVeil.Lemmas.ifPos rfl]
      have hcA := Acked.le_length _ _ _ _ _ _ _ (fun i' x' hx' => (hAF _ hx' a.dst i' t x' rfl).2.2) h
      rcases delete_held A (st.log a.dst) L c a.prevLogIndex k a.entries hcA h1 hpn hes hk1 (by omega) hlen hne with h2 | h2
      · exact Or.inl h2
      · right
        have hle : t ≤ st.currentTerm a.dst := by
          rcases h.2.2.2 with ⟨i', x, hx, _⟩ | ⟨hin, _⟩
          · exact (hAF _ hx _ i' t x rfl).2.1
          · exact hLTB _ hin
        have hne' : t ≠ a.term := by
          intro heq; subst heq
          have hA := h.1; rw [hL] at hA; cases hA
          exact h2 (List.take_prefix _ _)
        exact ⟨a.term, by omega, by omega, L, hL, h2⟩
    · rw [RaftVeil.Lemmas.ifNeg hj]; exact Or.inl h1
  · exact Or.inr h1

prove_veil_invariant_goal DeleteSuffix AckVote using wp by
  have hAckVote := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal DeleteSuffix EarlyQuorum using wp by
  have hEarlyQuorum := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal DeleteSuffix ConfirmedIsLed using wp by
  have hRFL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hBoot := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLBoot := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLFL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLedFL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hCIL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro ha hisA hterm hprev k hk1 hk2 hfirst hlen hne hsnapk
  obtain ⟨L, hL, hpn, hpt, hes, -⟩ := req_facts st.ledLog _ a (hRFL a ha) hisA
  rw [hpt] at hprev
  have hLedL := (optAll_iff _ _).1 (hLedFL a.term) L hL
  have hLB : L.head? = some Boot := by simpa using (optAll_iff _ _).1 (hLBoot a.term) L hL
  intro j
  by_cases hj : a.dst = j
  · subst hj
    repeat rw [RaftVeil.Lemmas.ifPos rfl]
    right
    refine ⟨L, hL, ?_⟩
    obtain ⟨h1, h2⟩ := checked_prefix st.ledLog (st.log a.dst) L a.prevLogIndex (k - 1) a.entries (hLFL a.dst) hLedL
      (hBoot a.dst) hLB hpn hes hprev (by omega) hfirst
    rw [subSeq_one, show a.prevLogIndex + k - 1 = a.prevLogIndex + (k - 1) by omega]
    exact ⟨by simp; omega, by rw [List.take_take]; simpa using h2⟩
  · repeat rw [RaftVeil.Lemmas.ifNeg hj]
    exact hCIL j

prove_veil_invariant_goal DeleteSuffix CommitRoot using wp by
  have hCommitRoot := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal DeleteSuffix CommitSafety using wp by
  have hCommitSafety := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal DeleteSuffix ConfirmedTermBound using wp by
  have hConfirmedTermBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal DeleteSuffix CommitTermBound using wp by
  have hCommitTermBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal DeleteSuffix CommittedEntriesPreserved using wp by
  have hLHas := hinv.2.2.2.2.2.2.2.2.2.2.1
  have hRFL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLBoot := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLedFL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hVHR := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLER := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hEQ := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hCR := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hCmT := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hCEP := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro cc ha hisA hterm hprev k hk1 hk2 hfirst hlen hne hsnapk hc
  by_cases hd : a.dst = cc.server
  · rw [RaftVeil.Lemmas.ifPos hd, isPrefix_iff]
    obtain ⟨L, hL, hpn, hpt, hes, -⟩ := req_facts st.ledLog _ a (hRFL a ha) hisA
    have h1 : cc.entries <+: st.log a.dst := by
      have := hCEP cc hc
      rw [isPrefix_iff] at this; rw [hd]; exact this
    obtain ⟨-, r, hcr, hroot, hr, hrt⟩ := hCR cc hc
    have hle : r.term ≤ a.term := by
      have := hCmT cc hc
      rw [hterm, hd]; omega
    have hB := root_in_later st.msgs st.leaders st.votes st.ledLog hEQ hLHas hVHR hLER
      (fun t L h => (optAll_iff _ _).1 (hLedFL t) L h)
      (fun t L h => by simpa using (optAll_iff _ _).1 (hLBoot t) L h) r hroot a.term hle L hL
    have hcL : cc.entries <+: L := hcr.trans hB
    have hd' := delete_held cc.entries (st.log a.dst) L cc.entries.length a.prevLogIndex k a.entries
      (Nat.le_refl _) (by rw [List.take_length]; exact h1) hpn hes hk1 (by omega) hlen hne
    rw [List.take_length] at hd'
    rcases hd' with h | h
    · exact h
    · exact absurd hcL h
  · rw [RaftVeil.Lemmas.ifNeg hd]; exact hCEP cc hc

prove_veil_invariant_goal DeleteSuffix CommitIndexCommitted using wp by
  have hCommitIndexCommitted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal DeleteSuffix AppliedCommitted using wp by
  have hAppliedCommitted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal DeleteSuffix StateMachineSafety using wp by
  have hStateMachineSafety := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal DeleteSuffix LeaderCompleteness using wp by
  have hES := hinv.1
  have hLE := hinv.2.2.2.2.2.2.1
  have hAFL := hinv.2.2.2.2.2.2.2.2.2.2.2.1
  have hLC := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro cc ha hisA hterm hprev k hk1 hk2 hfirst hlen hne hsnapk i hc hrole hlt
  have hnl : ∀ x : Elected server, x ∈ st.leaders → x.term = a.term → x.server ≠ a.dst := by
    intro x hx hxt hxs
    have h := hAFL a ha
    cases a with
    | append src dst term p pt es c =>
      simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at h
      have := hES x _ hx h.2 hxt
      exact h.1 (hxs.symm.trans this)
    | _ => simp [Msg.isAppend] at hisA
  by_cases hd : a.dst = i
  · subst hd
    exact absurd rfl (hnl _ (hLE _ hrole) hterm.symm)
  · rw [RaftVeil.Lemmas.ifNeg hd]; exact hLC cc i hc hrole hlt

prove_veil_invariant_goal DeleteSuffix ConfirmedWithinLog using wp by
  have hCWL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro ha hisA hterm hprev k hk1 hk2 hfirst hlen hne hsnapk i
  by_cases hd : a.dst = i
  · rw [RaftVeil.Lemmas.ifPos hd, RaftVeil.Lemmas.ifPos hd, subSeq_one, List.length_take]; omega
  · rw [RaftVeil.Lemmas.ifNeg hd, RaftVeil.Lemmas.ifNeg hd]; exact hCWL i

prove_veil_invariant_goal DeleteSuffix PreVoteRequestsBounded using wp by
  have hPreVoteRequestsBounded := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal DeleteSuffix PreGrantsAnswer using wp by
  have hPreGrantsAnswer := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal DeleteSuffix TimeoutNowFromLeader using wp by
  have hTimeoutNowFromLeader := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal DeleteSuffix TransferIsCandidate using wp by
  have hTransferIsCandidate := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal DeleteSuffix SnapshotWithinLog using wp by
  have hSWL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro ha hisA hterm hprev k hk1 hk2 hfirst hlen hne hsnapk i
  by_cases hd : a.dst = i
  · subst hd
    rw [RaftVeil.Lemmas.ifPos rfl, subSeq_one]
    have h := (isPrefix_iff _ _).1 (hSWL a.dst)
    exact (isPrefix_iff _ _).2 (List.prefix_take_iff.2 ⟨h, by omega⟩)
  · rw [RaftVeil.Lemmas.ifNeg hd]; exact hSWL i

prove_veil_invariant_goal DeleteSuffix BaseWithinSnapshot using wp by
  have hBaseWithinSnapshot := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal DeleteSuffix SnapshotCommitted using wp by
  have hSnapshotCommitted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal DeleteSuffix SnapshotApplied using wp by
  have hSnapshotApplied := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

-- StoreEntries

prove_veil_invariant_goal StoreEntries ElectionSafety using wp by
  have hElectionSafety := hinv.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StoreEntries OneVotePerTerm using wp by
  have hOneVotePerTerm := hinv.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StoreEntries VoteTermBound using wp by
  have hVoteTermBound := hinv.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StoreEntries VotesBound using wp by
  have hVotesBound := hinv.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StoreEntries GrantsAreVotes using wp by
  have hGrantsAreVotes := hinv.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StoreEntries LeadersHaveQuorum using wp by
  have hLeadersHaveQuorum := hinv.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StoreEntries LeaderIsElected using wp by
  have hLeaderIsElected := hinv.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StoreEntries LeadersTermBound using wp by
  have hLeadersTermBound := hinv.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StoreEntries LedOwner using wp by
  have hES := hinv.1
  have hLO := hinv.2.2.2.2.2.2.2.2.1
  have hAFL := hinv.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro x
  intro ha hisA hterm hprev k hk1 hk2 hfirst hlen
  have hnl : ∀ x : Elected server, x ∈ st.leaders → x.term = a.term → x.server ≠ a.dst := by
    intro x hx hxt hxs
    have h := hAFL a ha
    cases a with
    | append src dst term p pt es c =>
      simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at h
      have := hES x _ hx h.2 hxt
      exact h.1 (hxs.symm.trans this)
    | _ => simp [Msg.isAppend] at hisA
  intro hx hxt
  by_cases hj : a.dst = x.server
  · exact absurd hj.symm (hnl x hx (by rw [hxt, ← hj, hterm]))
  · rw [RaftVeil.Lemmas.ifNeg hj]; exact hLO x hx hxt

prove_veil_invariant_goal StoreEntries LeadersHaveLed using wp by
  have hLeadersHaveLed := hinv.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StoreEntries LedHasLeader using wp by
  have hLedHasLeader := hinv.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StoreEntries AppendFromLeader using wp by
  have hAppendFromLeader := hinv.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StoreEntries LeaderLogIsLed using wp by
  have hES := hinv.1
  have hLE := hinv.2.2.2.2.2.2.1
  have hAFL := hinv.2.2.2.2.2.2.2.2.2.2.2.1
  have hLLL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro ha hisA hterm hprev k hk1 hk2 hfirst hlen
  have hnl : ∀ x : Elected server, x ∈ st.leaders → x.term = a.term → x.server ≠ a.dst := by
    intro x hx hxt hxs
    have h := hAFL a ha
    cases a with
    | append src dst term p pt es c =>
      simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at h
      have := hES x _ hx h.2 hxt
      exact h.1 (hxs.symm.trans this)
    | _ => simp [Msg.isAppend] at hisA
  intro j hj
  by_cases hd : a.dst = j
  · subst hd
    exact absurd rfl (hnl _ (hLE _ hj) hterm.symm)
  · rw [RaftVeil.Lemmas.ifNeg hd]; exact hLLL j hj

prove_veil_invariant_goal StoreEntries RequestsFromLed using wp by
  have hRequestsFromLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StoreEntries BootEntry using wp by
  have hRFL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hBoot := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLBoot := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLFL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLedFL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro ha hisA hterm hprev k hk1 hk2 hfirst hlen
  obtain ⟨L, hL, hpn, hpt, hes, -⟩ := req_facts st.ledLog _ a (hRFL a ha) hisA
  rw [hpt] at hprev
  have hnew := store_fromLed st.ledLog (st.log a.dst) L a.prevLogIndex k a.entries (hLFL a.dst)
    ((optAll_iff _ _).1 (hLedFL a.term) L hL) (hBoot a.dst)
    (by simpa using (optAll_iff _ _).1 (hLBoot a.term) L hL) hpn hes hprev
    (List.mem_range'_1.2 ⟨hk1, hk2⟩) hfirst hlen
  intro j
  by_cases hj : a.dst = j
  · rw [RaftVeil.Lemmas.ifPos hj]; exact hnew.2
  · rw [RaftVeil.Lemmas.ifNeg hj]; exact hBoot j

prove_veil_invariant_goal StoreEntries LedBoot using wp by
  have hLedBoot := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StoreEntries LogFromLed using wp by
  have hRFL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hBoot := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLBoot := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLFL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLedFL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro ha hisA hterm hprev k hk1 hk2 hfirst hlen
  obtain ⟨L, hL, hpn, hpt, hes, -⟩ := req_facts st.ledLog _ a (hRFL a ha) hisA
  rw [hpt] at hprev
  have hnew := store_fromLed st.ledLog (st.log a.dst) L a.prevLogIndex k a.entries (hLFL a.dst)
    ((optAll_iff _ _).1 (hLedFL a.term) L hL) (hBoot a.dst)
    (by simpa using (optAll_iff _ _).1 (hLBoot a.term) L hL) hpn hes hprev
    (List.mem_range'_1.2 ⟨hk1, hk2⟩) hfirst hlen
  intro j
  by_cases hj : a.dst = j
  · rw [RaftVeil.Lemmas.ifPos hj]; exact hnew.1
  · rw [RaftVeil.Lemmas.ifNeg hj]; exact hLFL j

prove_veil_invariant_goal StoreEntries LedFromLed using wp by
  have hLedFromLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StoreEntries LogMatching using wp by
  have hRFL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hBoot := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLBoot := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLFL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLedFL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro ha hisA hterm hprev k hk1 hk2 hfirst hlen
  obtain ⟨L, hL, hpn, hpt, hes, -⟩ := req_facts st.ledLog _ a (hRFL a ha) hisA
  rw [hpt] at hprev
  have hnew := store_fromLed st.ledLog (st.log a.dst) L a.prevLogIndex k a.entries (hLFL a.dst)
    ((optAll_iff _ _).1 (hLedFL a.term) L hL) (hBoot a.dst)
    (by simpa using (optAll_iff _ _).1 (hLBoot a.term) L hL) hpn hes hprev
    (List.mem_range'_1.2 ⟨hk1, hk2⟩) hfirst hlen
  intro x y k' hk1' hk2'
  refine FromLed.matching st.ledLog _ _ ?_ ?_ ?_ ?_ k' (List.mem_range'_1.2 ⟨hk1', hk2'⟩)
  · by_cases hj : a.dst = x
    · rw [RaftVeil.Lemmas.ifPos hj]; exact hnew.1
    · rw [RaftVeil.Lemmas.ifNeg hj]; exact hLFL x
  · by_cases hj : a.dst = y
    · rw [RaftVeil.Lemmas.ifPos hj]; exact hnew.1
    · rw [RaftVeil.Lemmas.ifNeg hj]; exact hLFL y
  · by_cases hj : a.dst = x
    · rw [RaftVeil.Lemmas.ifPos hj]; exact hnew.2
    · rw [RaftVeil.Lemmas.ifNeg hj]; exact hBoot x
  · by_cases hj : a.dst = y
    · rw [RaftVeil.Lemmas.ifPos hj]; exact hnew.2
    · rw [RaftVeil.Lemmas.ifNeg hj]; exact hBoot y

prove_veil_invariant_goal StoreEntries TermsPositive using wp by
  have hTermsPositive := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StoreEntries LogTermsBound using wp by
  have hRFL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hBoot := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLBoot := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLFL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLedFL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLogTB := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLS := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro ha hisA hterm hprev k hk1 hk2 hfirst hlen
  obtain ⟨L, hL, hpn, hpt, hes, -⟩ := req_facts st.ledLog _ a (hRFL a ha) hisA
  rw [hpt] at hprev
  have hLedL := (optAll_iff _ _).1 (hLedFL a.term) L hL
  have hLB : L.head? = some Boot := by simpa using (optAll_iff _ _).1 (hLBoot a.term) L hL
  have hstore := store_eq st.ledLog (st.log a.dst) L a.prevLogIndex k a.entries (hLFL a.dst) hLedL (hBoot a.dst) hLB
    hpn hes hprev (List.mem_range'_1.2 ⟨hk1, hk2⟩) hfirst hlen
  intro j k'
  by_cases hj : a.dst = j
  · subst hj; rw [RaftVeil.Lemmas.ifPos rfl]
    show TermAt (st.log a.dst ++ SubSeq a.entries k a.entries.length) k' ≤ _
    rw [hstore, ← hterm]; exact (Sorted.take L a.term _ (hLS _ L hL)).2 k'
  · rw [RaftVeil.Lemmas.ifNeg hj]; exact hLogTB j k'

prove_veil_invariant_goal StoreEntries LedSorted using wp by
  have hLedSorted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StoreEntries ReqFacts using wp by
  have hReqFacts := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StoreEntries ReqUnique using wp by
  have hReqUnique := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StoreEntries VoteHasReq using wp by
  have hVoteHasReq := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StoreEntries CandLog using wp by
  have hRFL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hBoot := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLBoot := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLFL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLedFL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hCL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro ha hisA hterm hprev k hk1 hk2 hfirst hlen
  obtain ⟨L, hL, hpn, hpt, hes, -⟩ := req_facts st.ledLog _ a (hRFL a ha) hisA
  rw [hpt] at hprev
  have hLedL := (optAll_iff _ _).1 (hLedFL a.term) L hL
  have hLB : L.head? = some Boot := by simpa using (optAll_iff _ _).1 (hLBoot a.term) L hL
  have hstore := store_eq st.ledLog (st.log a.dst) L a.prevLogIndex k a.entries (hLFL a.dst) hLedL (hBoot a.dst) hLB
    hpn hes hprev (List.mem_range'_1.2 ⟨hk1, hk2⟩) hfirst hlen
  intro m hm c u li lt heq hcu hnone
  by_cases hj : a.dst = c
  · subst hj; rw [← hcu, ← hterm, hL] at hnone; cases hnone
  · repeat rw [RaftVeil.Lemmas.ifNeg hj]
    exact hCL m hm c u li lt heq hcu hnone

prove_veil_invariant_goal StoreEntries LedExtendsReq using wp by
  have hLedExtendsReq := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StoreEntries AckFacts using wp by
  have hAckFacts := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StoreEntries AckedHeld using wp by
  have hRFL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hBoot := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLBoot := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLFL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLedFL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hAH := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro ha hisA hterm hprev k hk1 hk2 hfirst hlen
  obtain ⟨L, hL, hpn, hpt, hes, -⟩ := req_facts st.ledLog _ a (hRFL a ha) hisA
  rw [hpt] at hprev
  have hLedL := (optAll_iff _ _).1 (hLedFL a.term) L hL
  have hLB : L.head? = some Boot := by simpa using (optAll_iff _ _).1 (hLBoot a.term) L hL
  have hstore := store_eq st.ledLog (st.log a.dst) L a.prevLogIndex k a.entries (hLFL a.dst) hLedL (hBoot a.dst) hLB
    hpn hes hprev (List.mem_range'_1.2 ⟨hk1, hk2⟩) hfirst hlen
  intro n t A c h
  rcases hAH n t A c h with h1 | h1
  · left
    by_cases hj : a.dst = n
    · subst hj; rw [RaftVeil.Lemmas.ifPos rfl]; exact h1.trans (List.prefix_append _ _)
    · rw [RaftVeil.Lemmas.ifNeg hj]; exact h1
  · exact Or.inr h1

prove_veil_invariant_goal StoreEntries AckVote using wp by
  have hAckVote := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StoreEntries EarlyQuorum using wp by
  have hEarlyQuorum := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StoreEntries ConfirmedIsLed using wp by
  have hRFL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hBoot := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLBoot := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLFL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLedFL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hCIL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro ha hisA hterm hprev k hk1 hk2 hfirst hlen
  obtain ⟨L, hL, hpn, hpt, hes, -⟩ := req_facts st.ledLog _ a (hRFL a ha) hisA
  rw [hpt] at hprev
  have hLedL := (optAll_iff _ _).1 (hLedFL a.term) L hL
  have hLB : L.head? = some Boot := by simpa using (optAll_iff _ _).1 (hLBoot a.term) L hL
  have hstore := store_eq st.ledLog (st.log a.dst) L a.prevLogIndex k a.entries (hLFL a.dst) hLedL (hBoot a.dst) hLB
    hpn hes hprev (List.mem_range'_1.2 ⟨hk1, hk2⟩) hfirst hlen
  intro j
  by_cases hj : a.dst = j
  · subst hj
    repeat rw [RaftVeil.Lemmas.ifPos rfl]
    right
    refine ⟨L, hL, ?_⟩
    show _ ≤ (st.log a.dst ++ SubSeq a.entries k a.entries.length).length ∧
      List.take _ (st.log a.dst ++ SubSeq a.entries k a.entries.length) = _
    rw [hstore]
    exact ⟨by simp; omega, by rw [List.take_take]; simp⟩
  · repeat rw [RaftVeil.Lemmas.ifNeg hj]
    exact hCIL j

prove_veil_invariant_goal StoreEntries CommitRoot using wp by
  have hCommitRoot := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StoreEntries CommitSafety using wp by
  have hCommitSafety := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StoreEntries ConfirmedTermBound using wp by
  have hConfirmedTermBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StoreEntries CommitTermBound using wp by
  have hCommitTermBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StoreEntries CommittedEntriesPreserved using wp by
  have hCEP := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro cc ha hisA hterm hprev k hk1 hk2 hfirst hlen hc
  by_cases hd : a.dst = cc.server
  · rw [RaftVeil.Lemmas.ifPos hd, isPrefix_iff]
    have := hCEP cc hc
    rw [isPrefix_iff, ← hd] at this
    exact this.trans (List.prefix_append _ _)
  · rw [RaftVeil.Lemmas.ifNeg hd]; exact hCEP cc hc

prove_veil_invariant_goal StoreEntries CommitIndexCommitted using wp by
  have hCommitIndexCommitted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StoreEntries AppliedCommitted using wp by
  have hAppliedCommitted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StoreEntries StateMachineSafety using wp by
  have hStateMachineSafety := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StoreEntries LeaderCompleteness using wp by
  have hES := hinv.1
  have hLE := hinv.2.2.2.2.2.2.1
  have hAFL := hinv.2.2.2.2.2.2.2.2.2.2.2.1
  have hLC := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro cc ha hisA hterm hprev k hk1 hk2 hfirst hlen i hc hrole hlt
  have hnl : ∀ x : Elected server, x ∈ st.leaders → x.term = a.term → x.server ≠ a.dst := by
    intro x hx hxt hxs
    have h := hAFL a ha
    cases a with
    | append src dst term p pt es c =>
      simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at h
      have := hES x _ hx h.2 hxt
      exact h.1 (hxs.symm.trans this)
    | _ => simp [Msg.isAppend] at hisA
  by_cases hd : a.dst = i
  · subst hd
    exact absurd rfl (hnl _ (hLE _ hrole) hterm.symm)
  · rw [RaftVeil.Lemmas.ifNeg hd]; exact hLC cc i hc hrole hlt

prove_veil_invariant_goal StoreEntries ConfirmedWithinLog using wp by
  have hCWL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro ha hisA hterm hprev k hk1 hk2 hfirst hlen i
  by_cases hd : a.dst = i
  · rw [RaftVeil.Lemmas.ifPos hd, RaftVeil.Lemmas.ifPos hd]
    show _ ≤ (st.log a.dst ++ SubSeq a.entries k a.entries.length).length
    simp only [SubSeq, List.length_append, List.length_take, List.length_drop]; omega
  · rw [RaftVeil.Lemmas.ifNeg hd, RaftVeil.Lemmas.ifNeg hd]; exact hCWL i

prove_veil_invariant_goal StoreEntries PreVoteRequestsBounded using wp by
  have hPreVoteRequestsBounded := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StoreEntries PreGrantsAnswer using wp by
  have hPreGrantsAnswer := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StoreEntries TimeoutNowFromLeader using wp by
  have hTimeoutNowFromLeader := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StoreEntries TransferIsCandidate using wp by
  have hTransferIsCandidate := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StoreEntries SnapshotWithinLog using wp by
  have hSWL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro ha hisA hterm hprev k hk1 hk2 hfirst hlen j
  by_cases hd : a.dst = j
  · subst hd
    rw [RaftVeil.Lemmas.ifPos rfl]
    exact (isPrefix_iff _ _).2 (((isPrefix_iff _ _).1 (hSWL a.dst)).trans (List.prefix_append _ _))
  · rw [RaftVeil.Lemmas.ifNeg hd]; exact hSWL j

prove_veil_invariant_goal StoreEntries BaseWithinSnapshot using wp by
  have hBaseWithinSnapshot := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StoreEntries SnapshotCommitted using wp by
  have hSnapshotCommitted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StoreEntries SnapshotApplied using wp by
  have hSnapshotApplied := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

-- Ack

prove_veil_invariant_goal Ack ElectionSafety using wp by
  have hElectionSafety := hinv.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Ack OneVotePerTerm using wp by
  have hOneVotePerTerm := hinv.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Ack VoteTermBound using wp by
  have hVoteTermBound := hinv.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Ack VotesBound using wp by
  have hVotesBound := hinv.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Ack GrantsAreVotes using wp by
  have hGV := hinv.2.2.2.2.1
  clear hinv
  intros
  simp only [RaftVeil.Lemmas.mem_iff, RaftVeil.Lemmas.contains_insert_iff] at *
  repeat' split
  all_goals grind only

prove_veil_invariant_goal Ack LeadersHaveQuorum using wp by
  have hLeadersHaveQuorum := hinv.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Ack LeaderIsElected using wp by
  have hLeaderIsElected := hinv.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Ack LeadersTermBound using wp by
  have hLeadersTermBound := hinv.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Ack LedOwner using wp by
  have hLedOwner := hinv.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Ack LeadersHaveLed using wp by
  have hLeadersHaveLed := hinv.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Ack LedHasLeader using wp by
  have hLedHasLeader := hinv.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Ack AppendFromLeader using wp by
  have hAppendFromLeader := hinv.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Ack LeaderLogIsLed using wp by
  have hLeaderLogIsLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Ack RequestsFromLed using wp by
  have hRequestsFromLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Ack BootEntry using wp by
  have hBootEntry := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Ack LedBoot using wp by
  have hLedBoot := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Ack LogFromLed using wp by
  have hLogFromLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Ack LedFromLed using wp by
  have hLedFromLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Ack LogMatching using wp by
  have hLogMatching := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Ack TermsPositive using wp by
  have hTermsPositive := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Ack LogTermsBound using wp by
  have hLogTermsBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Ack LedSorted using wp by
  have hLedSorted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Ack ReqFacts using wp by
  have hReqFacts := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Ack ReqUnique using wp by
  have hReqUnique := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Ack VoteHasReq using wp by
  have hVoteHasReq := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Ack CandLog using wp by
  have hCandLog := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Ack LedExtendsReq using wp by
  have hLedExtendsReq := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Ack AckFacts using wp by
  have hAFL := hinv.2.2.2.2.2.2.2.2.2.2.2.1
  have hRFL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hBoot := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLBoot := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLFL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLedFL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hAF := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  first | intro (m : Msg server value) ha hisA hterm hprev hfirst | intro ha hisA hterm hprev hfirst (m : Msg server value)
  obtain ⟨L, hL, hpn, hpt, hes, -⟩ := req_facts st.ledLog _ a (hRFL a ha) hisA
  rw [hpt] at hprev
  have hLedL := (optAll_iff _ _).1 (hLedFL a.term) L hL
  have hLB : L.head? = some Boot := by simpa using (optAll_iff _ _).1 (hLBoot a.term) L hL
  have hchk := checked_prefix st.ledLog (st.log a.dst) L a.prevLogIndex a.entries.length a.entries (hLFL a.dst) hLedL
    (hBoot a.dst) hLB hpn hes hprev (Nat.le_refl _) hfirst
  have hldr : TSet.contains ({ server := a.src, term := a.term } : Elected server) st.leaders = true := by
    have h := hAFL a ha
    cases a with
    | append src dst term p pt es c =>
      simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at h
      exact h.2
    | _ => simp [Msg.isAppend] at hisA
  intro hm j i' t x heq
  rw [RaftVeil.Lemmas.mem_insert] at hm
  rcases hm with rfl | hm
  · injection heq with h1 h2 h3 h4
    subst h1 h2 h3 h4
    exact ⟨hldr, by omega, L, hL, hpn⟩
  · exact hAF m hm j i' t x heq

prove_veil_invariant_goal Ack AckedHeld using wp by
  have hRFL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hBoot := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLBoot := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLFL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLedFL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hAH := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro ha hisA hterm hprev hfirst
  obtain ⟨L, hL, hpn, hpt, hes, -⟩ := req_facts st.ledLog _ a (hRFL a ha) hisA
  rw [hpt] at hprev
  have hLedL := (optAll_iff _ _).1 (hLedFL a.term) L hL
  have hLB : L.head? = some Boot := by simpa using (optAll_iff _ _).1 (hLBoot a.term) L hL
  have hchk := checked_prefix st.ledLog (st.log a.dst) L a.prevLogIndex a.entries.length a.entries (hLFL a.dst) hLedL
    (hBoot a.dst) hLB hpn hes hprev (Nat.le_refl _) hfirst
  intro n t A c h
  rcases Acked.of_insert_ack _ _ _ _ _ _ _ _ _ _ _ h with h' | ⟨rfl, rfl, hc, hA, hc2, hct⟩
  · exact hAH n t A c h'
  · left
    rw [hL] at hA; cases hA
    rw [take_prefix_iff _ _ _ (by omega)]
    refine ⟨by omega, ?_⟩
    have := congrArg (List.take c) hchk.2
    rw [List.take_take, List.take_take, Nat.min_eq_left hc] at this
    exact this.symm

prove_veil_invariant_goal Ack AckVote using wp by
  have hVT := hinv.2.2.1
  have hVB := hinv.2.2.2.1
  have hAV := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  first | intro (v : Vote server) ha hisA hterm hprev hfirst | intro ha hisA hterm hprev hfirst (v : Vote server)
  intro n t A c h hv hvn htv li lt hreq
  rcases (RaftVeil.Lemmas.contains_insert_iff _ _ _).1 hreq with hh | hreq'
  · cases hh
  · rcases Acked.of_insert_ack _ _ _ _ _ _ _ _ _ _ _ h with h' | ⟨rfl, rfl, _⟩
    · exact hAV v n t A c h' hv hvn htv li lt hreq'
    · have h1 := hVB v hv
      have h2 := hVT v.voter
      rw [hvn] at h1 h2
      omega

prove_veil_invariant_goal Ack EarlyQuorum using wp by
  have hVT := hinv.2.2.1
  have hVB := hinv.2.2.2.1
  have hEQ := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  first | intro (ld : Elected server) ha hisA hterm hprev hfirst | intro ha hisA hterm hprev hfirst (ld : Elected server)
  intro hld
  refine IsQuorum.mono _ _ ?_ (hEQ ld hld)
  intro n hn
  simp only [decide_eq_true_eq] at hn ⊢
  refine ⟨hn.1, ?_⟩
  intro t A c ha' htu li lt hr
  rw [RaftVeil.Lemmas.mem_insert] at hr
  rcases hr with hh | hr
  · cases hh
  · rcases Acked.of_insert_ack _ _ _ _ _ _ _ _ _ _ _ ha' with h' | ⟨rfl, rfl, _⟩
    · exact hn.2 t A c h' htu li lt hr
    · have h1 := hVB _ hn.1
      have h2 := hVT a.dst
      simp only at h1
      omega

prove_veil_invariant_goal Ack ConfirmedIsLed using wp by
  have hRFL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hBoot := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLBoot := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLFL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLedFL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hCIL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro ha hisA hterm hprev hfirst
  obtain ⟨L, hL, hpn, hpt, hes, -⟩ := req_facts st.ledLog _ a (hRFL a ha) hisA
  rw [hpt] at hprev
  have hLedL := (optAll_iff _ _).1 (hLedFL a.term) L hL
  have hLB : L.head? = some Boot := by simpa using (optAll_iff _ _).1 (hLBoot a.term) L hL
  have hchk := checked_prefix st.ledLog (st.log a.dst) L a.prevLogIndex a.entries.length a.entries (hLFL a.dst) hLedL
    (hBoot a.dst) hLB hpn hes hprev (Nat.le_refl _) hfirst
  intro j
  by_cases hj : a.dst = j
  · subst hj
    repeat rw [RaftVeil.Lemmas.ifPos rfl]
    by_cases hct' : st.confirmedTerm a.dst = a.term
    · repeat rw [RaftVeil.Lemmas.ifPos hct']
      rcases Nat.le_total (st.confirmedIndex a.dst) (a.prevLogIndex + a.entries.length) with hle | hle
      · rw [Nat.max_eq_right hle]; exact Or.inr ⟨L, hL, hchk.1, hchk.2⟩
      · rw [Nat.max_eq_left hle]
        rcases hCIL a.dst with h0 | ⟨L0, hL0, h1, h2⟩
        · exact Or.inl h0
        · rw [hct', hL] at hL0; cases hL0; exact Or.inr ⟨L, hL, h1, h2⟩
    · repeat rw [RaftVeil.Lemmas.ifNeg hct']
      exact Or.inr ⟨L, hL, hchk.1, hchk.2⟩
  · repeat rw [RaftVeil.Lemmas.ifNeg hj]
    exact hCIL j

prove_veil_invariant_goal Ack CommitRoot using wp by
  have hCR := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro k
  intros
  rename_i hk
  obtain ⟨h1, r, h2, h3, h4, h5⟩ := hCR k hk
  exact ⟨h1, r, h2, Root.mono _ _ _ _ _ _ _ (fun a ha => (RaftVeil.Lemmas.mem_insert _ _ _).2 (Or.inr ha))
    (fun a ha => ha) (LedGrows.refl _) h3, h4, h5⟩

prove_veil_invariant_goal Ack CommitSafety using wp by
  have hCommitSafety := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Ack ConfirmedTermBound using wp by
  have hConfirmedTermBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Ack CommitTermBound using wp by
  have hCommitTermBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Ack CommittedEntriesPreserved using wp by
  have hCommittedEntriesPreserved := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Ack CommitIndexCommitted using wp by
  have hCommitIndexCommitted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Ack AppliedCommitted using wp by
  have hAppliedCommitted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Ack StateMachineSafety using wp by
  have hStateMachineSafety := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Ack LeaderCompleteness using wp by
  have hLeaderCompleteness := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Ack ConfirmedWithinLog using wp by
  have hCWL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro ha hisA hterm hprev hfirst i
  by_cases hd : a.dst = i
  · subst hd
    rw [RaftVeil.Lemmas.ifPos rfl]
    have hlast := ack_within _ _ _ _ hprev hfirst
    have := hCWL a.dst
    split <;> omega
  · rw [RaftVeil.Lemmas.ifNeg hd]; exact hCWL i

prove_veil_invariant_goal Ack PreVoteRequestsBounded using wp by
  have hPreVoteRequestsBounded := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Ack PreGrantsAnswer using wp by
  have hPGA := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  rename_i a ha
  rw [RaftVeil.Lemmas.mem_insert] at ha
  rcases ha with rfl | ha
  · rfl
  · refine pregrants_mono _ _ a (hPGA a ha) ?_
    intro d t hx
    simp only [decide_eq_true_eq] at hx ⊢
    obtain ⟨⟨m, hm⟩, hm2⟩ := hx
    exact ⟨⟨m, (RaftVeil.Lemmas.mem_insert _ _ _).2 (Or.inr hm)⟩, hm2⟩

prove_veil_invariant_goal Ack TimeoutNowFromLeader using wp by
  have hTimeoutNowFromLeader := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Ack TransferIsCandidate using wp by
  have hTransferIsCandidate := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Ack SnapshotWithinLog using wp by
  have hSnapshotWithinLog := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Ack BaseWithinSnapshot using wp by
  have hBaseWithinSnapshot := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Ack SnapshotCommitted using wp by
  have hSnapshotCommitted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Ack SnapshotApplied using wp by
  have hSnapshotApplied := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

-- FollowerCommit

prove_veil_invariant_goal FollowerCommit ElectionSafety using wp by
  have hElectionSafety := hinv.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal FollowerCommit OneVotePerTerm using wp by
  have hOneVotePerTerm := hinv.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal FollowerCommit VoteTermBound using wp by
  have hVoteTermBound := hinv.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal FollowerCommit VotesBound using wp by
  have hVotesBound := hinv.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal FollowerCommit GrantsAreVotes using wp by
  have hGrantsAreVotes := hinv.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal FollowerCommit LeadersHaveQuorum using wp by
  have hLeadersHaveQuorum := hinv.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal FollowerCommit LeaderIsElected using wp by
  have hLeaderIsElected := hinv.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal FollowerCommit LeadersTermBound using wp by
  have hLeadersTermBound := hinv.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal FollowerCommit LedOwner using wp by
  have hLedOwner := hinv.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal FollowerCommit LeadersHaveLed using wp by
  have hLeadersHaveLed := hinv.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal FollowerCommit LedHasLeader using wp by
  have hLedHasLeader := hinv.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal FollowerCommit AppendFromLeader using wp by
  have hAppendFromLeader := hinv.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal FollowerCommit LeaderLogIsLed using wp by
  have hLeaderLogIsLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal FollowerCommit RequestsFromLed using wp by
  have hRFL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  rename_i m hm
  refine req_mono st.ledLog st.ledLog _ _ m (hRFL m hm) (fun t l h => ⟨l, h, List.prefix_refl _⟩) ?_
  · intro t l l' c hp hx
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hx ⊢
    exact commitPart_mono st.commits _ (fun k hk => (RaftVeil.Lemmas.mem_insert _ _ _).2 (Or.inr hk)) l l' c t hp hx

prove_veil_invariant_goal FollowerCommit BootEntry using wp by
  have hBootEntry := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal FollowerCommit LedBoot using wp by
  have hLedBoot := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal FollowerCommit LogFromLed using wp by
  have hLogFromLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal FollowerCommit LedFromLed using wp by
  have hLedFromLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal FollowerCommit LogMatching using wp by
  have hLogMatching := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal FollowerCommit TermsPositive using wp by
  have hTermsPositive := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal FollowerCommit LogTermsBound using wp by
  have hLogTermsBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal FollowerCommit LedSorted using wp by
  have hLedSorted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal FollowerCommit ReqFacts using wp by
  have hReqFacts := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal FollowerCommit ReqUnique using wp by
  have hReqUnique := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal FollowerCommit VoteHasReq using wp by
  have hVoteHasReq := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal FollowerCommit CandLog using wp by
  have hCandLog := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal FollowerCommit LedExtendsReq using wp by
  have hLedExtendsReq := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal FollowerCommit AckFacts using wp by
  have hAckFacts := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal FollowerCommit AckedHeld using wp by
  have hAckedHeld := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal FollowerCommit AckVote using wp by
  have hAckVote := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal FollowerCommit EarlyQuorum using wp by
  have hEarlyQuorum := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal FollowerCommit ConfirmedIsLed using wp by
  have hConfirmedIsLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal FollowerCommit CommitRoot using wp by
  have hRFL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hCIL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hCR := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro k ha hisA hct c hc1 hc2 hci hcm hk
  obtain ⟨L, hL, hpn, hpt, hes, hX⟩ := req_facts st.ledLog _ a (hRFL a ha) hisA
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hX
  have hcmin : c ≤ a.commit ∧ c ≤ st.confirmedIndex a.dst := by omega
  rcases hX with h0 | ⟨hcl, ⟨kk, hkk⟩, hkt, hk1, hk2⟩
  · omega
  rcases hCIL a.dst with h0 | ⟨L0, hL0, hc1', hc2'⟩
  · omega
  rw [← hct, hL] at hL0; cases hL0
  have hlenK : (SubSeq (st.log a.dst) 1 c).length = c := by
    rw [subSeq_one, List.length_take, Nat.min_eq_left (by omega)]
  have hK : SubSeq (st.log a.dst) 1 c <+: kk.entries := by
    rw [subSeq_one]
    have e1 : (st.log a.dst).take c = L.take c := by
      have := congrArg (List.take c) hc2'
      rwa [List.take_take, List.take_take, Nat.min_eq_left hcmin.2] at this
    have e2 : kk.entries.take c = L.take c := by
      rw [subSeq_one, subSeq_one] at hk2
      have := congrArg (List.take c) hk2
      rwa [List.take_take, List.take_take, Nat.min_eq_left hcmin.1] at this
    rw [e1, ← e2]; exact List.take_prefix _ _
  rw [RaftVeil.Lemmas.mem_insert] at hk
  rcases hk with rfl | hk
  · obtain ⟨_, r, hkr, hroot, hr, hrt⟩ := hCR kk hkk
    refine ⟨?_, r, hK.trans hkr, hroot, (RaftVeil.Lemmas.mem_insert _ _ _).2 (Or.inr hr), Nat.le_trans hrt hkt⟩
    intro h
    have := congrArg List.length h
    rw [hlenK] at this
    simp at this; omega
  · obtain ⟨h1, r, h2, h3, h4, h5⟩ := hCR k hk
    exact ⟨h1, r, h2, h3, (RaftVeil.Lemmas.mem_insert _ _ _).2 (Or.inr h4), h5⟩

prove_veil_invariant_goal FollowerCommit CommitSafety using wp by
  have hRFL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hCIL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hSMS := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro r1 r2 ha hisA hct c hc1 hc2 hci hcm h1 h2
  obtain ⟨L, hL, hpn, hpt, hes, hX⟩ := req_facts st.ledLog _ a (hRFL a ha) hisA
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hX
  have hcmin : c ≤ a.commit ∧ c ≤ st.confirmedIndex a.dst := by omega
  rcases hX with h0 | ⟨hcl, ⟨kk, hkk⟩, hkt, hk1, hk2⟩
  · omega
  rcases hCIL a.dst with h0 | ⟨L0, hL0, hc1', hc2'⟩
  · omega
  rw [← hct, hL] at hL0; cases hL0
  have hlenK : (SubSeq (st.log a.dst) 1 c).length = c := by
    rw [subSeq_one, List.length_take, Nat.min_eq_left (by omega)]
  have hK : SubSeq (st.log a.dst) 1 c <+: kk.entries := by
    rw [subSeq_one]
    have e1 : (st.log a.dst).take c = L.take c := by
      have := congrArg (List.take c) hc2'
      rwa [List.take_take, List.take_take, Nat.min_eq_left hcmin.2] at this
    have e2 : kk.entries.take c = L.take c := by
      rw [subSeq_one, subSeq_one] at hk2
      have := congrArg (List.take c) hk2
      rwa [List.take_take, List.take_take, Nat.min_eq_left hcmin.1] at this
    rw [e1, ← e2]; exact List.take_prefix _ _
  have cmp : ∀ b : Commit server value, b ∈ st.commits →
      SubSeq (st.log a.dst) 1 c <+: b.entries ∨ b.entries <+: SubSeq (st.log a.dst) 1 c := by
    intro b hb
    have := hSMS kk b hkk hb
    simp only [isPrefix_iff] at this
    rcases this with h | h
    · exact Or.inl (hK.trans h)
    · exact prefix_cmp_of_prefix _ _ kk.entries hK h
  rw [RaftVeil.Lemmas.mem_insert] at h1 h2
  simp only [isPrefix_iff]
  rcases h1 with rfl | h1 <;> rcases h2 with rfl | h2
  · exact Or.inl (List.prefix_refl _)
  · exact cmp r2 h2
  · exact (cmp r1 h1).symm
  · have := hSMS r1 r2 h1 h2
    simpa only [isPrefix_iff] using this

prove_veil_invariant_goal FollowerCommit ConfirmedTermBound using wp by
  have hConfirmedTermBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal FollowerCommit CommitTermBound using wp by
  have hConfirmedTermBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hCommitTermBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal FollowerCommit CommittedEntriesPreserved using wp by
  have hCEP := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro cc ha hisA hct c hc1 hc2 hci hcm hk
  rw [RaftVeil.Lemmas.mem_insert] at hk
  rcases hk with rfl | hk
  · show IsPrefix (SubSeq (st.log a.dst) 1 c) (st.log a.dst) = true
    rw [isPrefix_iff, subSeq_one]; exact List.take_prefix _ _
  · exact hCEP cc hk

prove_veil_invariant_goal FollowerCommit CommitIndexCommitted using wp by
  have hCIC := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hCWL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro ha hisA hct c hc1 hc2 hci hcm i1
  by_cases hd : a.dst = i1
  · subst hd
    rw [RaftVeil.Lemmas.ifPos rfl]
    refine Or.inr ⟨{ server := a.dst, term := a.term, entries := SubSeq (st.log a.dst) 1 c }, rfl,
      (RaftVeil.Lemmas.mem_insert _ _ _).2 (Or.inl rfl), ?_⟩
    show (SubSeq (st.log a.dst) 1 c).length = c
    have := hCWL a.dst
    rw [subSeq_one, List.length_take]; omega
  · rw [RaftVeil.Lemmas.ifNeg hd]
    rcases hCIC i1 with h0 | ⟨k, hk1, hk2, hk3⟩
    · exact Or.inl h0
    · exact Or.inr ⟨k, hk1, (RaftVeil.Lemmas.mem_insert _ _ _).2 (Or.inr hk2), hk3⟩

prove_veil_invariant_goal FollowerCommit AppliedCommitted using wp by
  have hAppliedCommitted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal FollowerCommit StateMachineSafety using wp by
  have hStateMachineSafety := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal FollowerCommit LeaderCompleteness using wp by
  have hRFL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hCIL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLC := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro cc ha hisA hct c hc1 hc2 hci hcm i1 hk hrole hlt
  rw [RaftVeil.Lemmas.mem_insert] at hk
  rcases hk with rfl | hk
  · obtain ⟨L, hL, hpn, hpt, hes, hX⟩ := req_facts st.ledLog _ a (hRFL a ha) hisA
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hX
    have hcmin : c ≤ a.commit ∧ c ≤ st.confirmedIndex a.dst := by omega
    rcases hX with h0 | ⟨hcl, ⟨kk, hkk⟩, hkt, hk1, hk2⟩
    · omega
    rcases hCIL a.dst with h0 | ⟨L0, hL0, hc1', hc2'⟩
    · omega
    rw [← hct, hL] at hL0; cases hL0
    have hK : SubSeq (st.log a.dst) 1 c <+: kk.entries := by
      rw [subSeq_one]
      have e1 : (st.log a.dst).take c = L.take c := by
        have := congrArg (List.take c) hc2'
        rwa [List.take_take, List.take_take, Nat.min_eq_left hcmin.2] at this
      have e2 : kk.entries.take c = L.take c := by
        rw [subSeq_one, subSeq_one] at hk2
        have := congrArg (List.take c) hk2
        rwa [List.take_take, List.take_take, Nat.min_eq_left hcmin.1] at this
      rw [e1, ← e2]; exact List.take_prefix _ _
    show IsPrefix (SubSeq (st.log a.dst) 1 c) (st.log i1) = true
    have := hLC kk i1 hkk hrole (Nat.lt_of_le_of_lt hkt hlt)
    rw [isPrefix_iff] at this ⊢
    exact hK.trans this
  · exact hLC cc i1 hk hrole hlt

prove_veil_invariant_goal FollowerCommit ConfirmedWithinLog using wp by
  have hConfirmedWithinLog := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal FollowerCommit PreVoteRequestsBounded using wp by
  have hPreVoteRequestsBounded := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal FollowerCommit PreGrantsAnswer using wp by
  have hPreGrantsAnswer := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal FollowerCommit TimeoutNowFromLeader using wp by
  have hTimeoutNowFromLeader := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal FollowerCommit TransferIsCandidate using wp by
  have hTransferIsCandidate := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal FollowerCommit SnapshotWithinLog using wp by
  have hSnapshotWithinLog := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal FollowerCommit BaseWithinSnapshot using wp by
  have hBaseWithinSnapshot := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal FollowerCommit SnapshotCommitted using wp by
  have hSnapshotCommitted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal FollowerCommit SnapshotApplied using wp by
  have hSnapshotApplied := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

-- Apply

prove_veil_invariant_goal Apply ElectionSafety using wp by
  have hElectionSafety := hinv.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Apply OneVotePerTerm using wp by
  have hOneVotePerTerm := hinv.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Apply VoteTermBound using wp by
  have hVoteTermBound := hinv.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Apply VotesBound using wp by
  have hVotesBound := hinv.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Apply GrantsAreVotes using wp by
  have hGrantsAreVotes := hinv.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Apply LeadersHaveQuorum using wp by
  have hLeadersHaveQuorum := hinv.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Apply LeaderIsElected using wp by
  have hLeaderIsElected := hinv.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Apply LeadersTermBound using wp by
  have hLeadersTermBound := hinv.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Apply LedOwner using wp by
  have hLedOwner := hinv.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Apply LeadersHaveLed using wp by
  have hLeadersHaveLed := hinv.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Apply LedHasLeader using wp by
  have hLedHasLeader := hinv.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Apply AppendFromLeader using wp by
  have hAppendFromLeader := hinv.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Apply LeaderLogIsLed using wp by
  have hLeaderLogIsLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Apply RequestsFromLed using wp by
  have hRequestsFromLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Apply BootEntry using wp by
  have hBootEntry := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Apply LedBoot using wp by
  have hLedBoot := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Apply LogFromLed using wp by
  have hLogFromLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Apply LedFromLed using wp by
  have hLedFromLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Apply LogMatching using wp by
  have hLogMatching := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Apply TermsPositive using wp by
  have hTermsPositive := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Apply LogTermsBound using wp by
  have hLogTermsBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Apply LedSorted using wp by
  have hLedSorted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Apply ReqFacts using wp by
  have hReqFacts := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Apply ReqUnique using wp by
  have hReqUnique := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Apply VoteHasReq using wp by
  have hVoteHasReq := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Apply CandLog using wp by
  have hCandLog := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Apply LedExtendsReq using wp by
  have hLedExtendsReq := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Apply AckFacts using wp by
  have hAckFacts := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Apply AckedHeld using wp by
  have hAckedHeld := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Apply AckVote using wp by
  have hAckVote := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Apply EarlyQuorum using wp by
  have hEarlyQuorum := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Apply ConfirmedIsLed using wp by
  have hConfirmedIsLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Apply CommitRoot using wp by
  have hCommitRoot := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Apply CommitSafety using wp by
  have hCommitSafety := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Apply ConfirmedTermBound using wp by
  have hConfirmedTermBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Apply CommitTermBound using wp by
  have hCommitTermBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Apply CommittedEntriesPreserved using wp by
  have hCommittedEntriesPreserved := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Apply CommitIndexCommitted using wp by
  have hCommitIndexCommitted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Apply AppliedCommitted using wp by
  have hCEP := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hCIC := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hAC := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro x h1 h2 hx
  rw [RaftVeil.Lemmas.mem_insert] at hx
  rcases hx with rfl | hx
  · rcases hCIC i with h0 | ⟨k, hk1, hk2, hk3⟩
    · omega
    · have hp := hCEP k hk2
      rw [isPrefix_iff, hk1] at hp
      refine ⟨Nat.le_add_left 1 _, k, hk2, ?_⟩
      show k.entries[st.lastApplied i + 1 - 1]? = some _
      rw [Nat.add_sub_cancel]
      exact prefix_getD _ _ _ _ hp (by omega)
  · exact hAC x hx

prove_veil_invariant_goal Apply StateMachineSafety using wp by
  have hSMS := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hCEP := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hCIC := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hAC := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hSM := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro x y h1 h2 hx hy hxy
  have hnew : ∃ k : Commit server value, k ∈ st.commits ∧
      k.entries[st.lastApplied i]? = some ((st.log i)[st.lastApplied i]?.getD noEntry) := by
    rcases hCIC i with h0 | ⟨k, hk1, hk2, hk3⟩
    · omega
    · have hp := hCEP k hk2
      rw [isPrefix_iff, hk1] at hp
      exact ⟨k, hk2, prefix_getD _ _ _ _ hp (by omega)⟩
  have cmp : ∀ k k' : Commit server value, k ∈ st.commits → k' ∈ st.commits →
      k.entries <+: k'.entries ∨ k'.entries <+: k.entries := by
    intro k k' hk hk'
    have := hSMS k k' hk hk'
    simpa only [isPrefix_iff] using this
  rw [RaftVeil.Lemmas.mem_insert] at hx hy
  rcases hx with rfl | hx <;> rcases hy with rfl | hy
  · rfl
  · obtain ⟨k, hk, hke⟩ := hnew
    obtain ⟨hy1, k', hk', hke'⟩ := hAC y hy
    simp only at hxy
    rw [← hxy] at hke'
    exact prefix_get_eq _ _ _ _ _ (cmp k k' hk hk') hke hke'
  · obtain ⟨k, hk, hke⟩ := hnew
    obtain ⟨hx1, k', hk', hke'⟩ := hAC x hx
    simp only at hxy
    rw [hxy] at hke'
    exact prefix_get_eq _ _ _ _ _ (cmp k' k hk' hk) hke' hke
  · exact hSM x y hx hy hxy

prove_veil_invariant_goal Apply LeaderCompleteness using wp by
  have hLeaderCompleteness := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Apply ConfirmedWithinLog using wp by
  have hConfirmedWithinLog := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Apply PreVoteRequestsBounded using wp by
  have hPreVoteRequestsBounded := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Apply PreGrantsAnswer using wp by
  have hPreGrantsAnswer := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Apply TimeoutNowFromLeader using wp by
  have hTimeoutNowFromLeader := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Apply TransferIsCandidate using wp by
  have hTransferIsCandidate := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Apply SnapshotWithinLog using wp by
  have hSnapshotWithinLog := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Apply BaseWithinSnapshot using wp by
  have hBaseWithinSnapshot := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Apply SnapshotCommitted using wp by
  have hSnapshotCommitted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Apply SnapshotApplied using wp by
  have hSnapshotApplied := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

-- Restart

prove_veil_invariant_goal Restart ElectionSafety using wp by
  have hElectionSafety := hinv.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Restart OneVotePerTerm using wp by
  have hOneVotePerTerm := hinv.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Restart VoteTermBound using wp by
  have hVoteTermBound := hinv.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Restart VotesBound using wp by
  have hVotesBound := hinv.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Restart GrantsAreVotes using wp by
  have hGrantsAreVotes := hinv.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Restart LeadersHaveQuorum using wp by
  have hLeadersHaveQuorum := hinv.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Restart LeaderIsElected using wp by
  have hLeaderIsElected := hinv.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Restart LeadersTermBound using wp by
  have hLeadersTermBound := hinv.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Restart LedOwner using wp by
  have hLedOwner := hinv.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Restart LeadersHaveLed using wp by
  have hLeadersHaveLed := hinv.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Restart LedHasLeader using wp by
  have hLedHasLeader := hinv.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Restart AppendFromLeader using wp by
  have hAppendFromLeader := hinv.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Restart LeaderLogIsLed using wp by
  have hLeaderLogIsLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Restart RequestsFromLed using wp by
  have hRequestsFromLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Restart BootEntry using wp by
  have hBootEntry := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Restart LedBoot using wp by
  have hLedBoot := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Restart LogFromLed using wp by
  have hLogFromLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Restart LedFromLed using wp by
  have hLedFromLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Restart LogMatching using wp by
  have hLogMatching := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Restart TermsPositive using wp by
  have hTermsPositive := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Restart LogTermsBound using wp by
  have hLogTermsBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Restart LedSorted using wp by
  have hLedSorted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Restart ReqFacts using wp by
  have hReqFacts := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Restart ReqUnique using wp by
  have hReqUnique := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Restart VoteHasReq using wp by
  have hVoteHasReq := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Restart CandLog using wp by
  have hCandLog := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Restart LedExtendsReq using wp by
  have hLedExtendsReq := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Restart AckFacts using wp by
  have hAckFacts := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Restart AckedHeld using wp by
  have hAckedHeld := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Restart AckVote using wp by
  have hAckVote := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Restart EarlyQuorum using wp by
  have hEarlyQuorum := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Restart ConfirmedIsLed using wp by
  have hConfirmedIsLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Restart CommitRoot using wp by
  have hCommitRoot := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Restart CommitSafety using wp by
  have hCommitSafety := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Restart ConfirmedTermBound using wp by
  have hConfirmedTermBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Restart CommitTermBound using wp by
  have hCommitTermBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Restart CommittedEntriesPreserved using wp by
  have hCommittedEntriesPreserved := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Restart CommitIndexCommitted using wp by
  have hCommitIndexCommitted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Restart AppliedCommitted using wp by
  have hAppliedCommitted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Restart StateMachineSafety using wp by
  have hStateMachineSafety := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Restart LeaderCompleteness using wp by
  have hLeaderCompleteness := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Restart ConfirmedWithinLog using wp by
  have hConfirmedWithinLog := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Restart PreVoteRequestsBounded using wp by
  have hPreVoteRequestsBounded := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Restart PreGrantsAnswer using wp by
  have hPreGrantsAnswer := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Restart TimeoutNowFromLeader using wp by
  have hTimeoutNowFromLeader := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Restart TransferIsCandidate using wp by
  have hTransferIsCandidate := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Restart SnapshotWithinLog using wp by
  have hSnapshotWithinLog := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Restart BaseWithinSnapshot using wp by
  have hBaseWithinSnapshot := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Restart SnapshotCommitted using wp by
  have hSnapshotCommitted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Restart SnapshotApplied using wp by
  have hSnapshotApplied := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

-- SendPreVote

prove_veil_invariant_goal SendPreVote ElectionSafety using wp by
  have hElectionSafety := hinv.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendPreVote OneVotePerTerm using wp by
  have hOneVotePerTerm := hinv.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendPreVote VoteTermBound using wp by
  have hVoteTermBound := hinv.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendPreVote VotesBound using wp by
  have hVotesBound := hinv.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendPreVote GrantsAreVotes using wp by
  have hGV := hinv.2.2.2.2.1
  clear hinv
  intros
  rename_i m hm
  rw [RaftVeil.Lemmas.mem_insert] at hm
  rcases hm with rfl | hm
  · rfl
  · exact hGV m hm

prove_veil_invariant_goal SendPreVote LeadersHaveQuorum using wp by
  have hLeadersHaveQuorum := hinv.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendPreVote LeaderIsElected using wp by
  have hLeaderIsElected := hinv.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendPreVote LeadersTermBound using wp by
  have hLeadersTermBound := hinv.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendPreVote LedOwner using wp by
  have hLedOwner := hinv.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendPreVote LeadersHaveLed using wp by
  have hLeadersHaveLed := hinv.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendPreVote LedHasLeader using wp by
  have hLedHasLeader := hinv.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendPreVote AppendFromLeader using wp by
  have hAppendFromLeader := hinv.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendPreVote LeaderLogIsLed using wp by
  have hLeaderLogIsLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendPreVote RequestsFromLed using wp by
  have hRequestsFromLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendPreVote BootEntry using wp by
  have hBootEntry := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendPreVote LedBoot using wp by
  have hLedBoot := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendPreVote LogFromLed using wp by
  have hLogFromLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendPreVote LedFromLed using wp by
  have hLedFromLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendPreVote LogMatching using wp by
  have hLogMatching := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendPreVote TermsPositive using wp by
  have hTermsPositive := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendPreVote LogTermsBound using wp by
  have hLogTermsBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendPreVote LedSorted using wp by
  have hLedSorted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendPreVote ReqFacts using wp by
  have hReqFacts := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendPreVote ReqUnique using wp by
  have hReqUnique := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendPreVote VoteHasReq using wp by
  have hVoteHasReq := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendPreVote CandLog using wp by
  have hCandLog := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendPreVote LedExtendsReq using wp by
  have hLedExtendsReq := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendPreVote AckFacts using wp by
  have hAckFacts := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendPreVote AckedHeld using wp by
  have hAH := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  rename_i n t A c hack
  exact hAH n t A c (Acked.of_insert _ _ _ _ _ _ _ _ (fun _ _ _ _ h => by cases h) hack)

prove_veil_invariant_goal SendPreVote AckVote using wp by
  have hAV := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro v
  intros
  rename_i n t A c hack hv hvn htv li lt hreq
  rcases (RaftVeil.Lemmas.contains_insert_iff _ _ _).1 hreq with h | h
  · cases h
  · exact hAV v n t A c (Acked.of_insert _ _ _ _ _ _ _ _ (fun _ _ _ _ h => by cases h) hack) hv hvn htv li lt h

prove_veil_invariant_goal SendPreVote EarlyQuorum using wp by
  have hEQ := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro ld
  intros
  rename_i hld
  refine IsQuorum.mono _ _ ?_ (hEQ ld hld)
  intro n hn
  simp only [decide_eq_true_eq] at hn ⊢
  exact ⟨hn.1, Early.of_insert _ _ _ _ _ _ _ (fun _ _ _ _ h => by cases h) (fun _ _ h => by cases h) hn.2⟩

prove_veil_invariant_goal SendPreVote ConfirmedIsLed using wp by
  have hConfirmedIsLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendPreVote CommitRoot using wp by
  have hCR := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro k
  intros
  rename_i hk
  obtain ⟨h1, r, h2, h3, h4, h5⟩ := hCR k hk
  exact ⟨h1, r, h2, Root.mono _ _ _ _ _ _ _ (fun a ha => (RaftVeil.Lemmas.mem_insert _ _ _).2 (Or.inr ha))
    (fun a ha => ha) (LedGrows.refl _) h3, h4, h5⟩

prove_veil_invariant_goal SendPreVote CommitSafety using wp by
  have hCommitSafety := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendPreVote ConfirmedTermBound using wp by
  have hConfirmedTermBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendPreVote CommitTermBound using wp by
  have hCommitTermBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendPreVote CommittedEntriesPreserved using wp by
  have hCommittedEntriesPreserved := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendPreVote CommitIndexCommitted using wp by
  have hCommitIndexCommitted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendPreVote AppliedCommitted using wp by
  have hAppliedCommitted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendPreVote StateMachineSafety using wp by
  have hStateMachineSafety := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendPreVote LeaderCompleteness using wp by
  have hLeaderCompleteness := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendPreVote ConfirmedWithinLog using wp by
  have hConfirmedWithinLog := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendPreVote PreVoteRequestsBounded using wp by
  have hPreVoteRequestsBounded := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendPreVote PreGrantsAnswer using wp by
  have hPGA := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  rename_i a ha
  rw [RaftVeil.Lemmas.mem_insert] at ha
  rcases ha with rfl | ha
  · rfl
  · refine pregrants_mono _ _ a (hPGA a ha) ?_
    intro d t hx
    simp only [decide_eq_true_eq] at hx ⊢
    obtain ⟨⟨m, hm⟩, hm2⟩ := hx
    exact ⟨⟨m, (RaftVeil.Lemmas.mem_insert _ _ _).2 (Or.inr hm)⟩, hm2⟩

prove_veil_invariant_goal SendPreVote TimeoutNowFromLeader using wp by
  have hTimeoutNowFromLeader := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendPreVote TransferIsCandidate using wp by
  have hTransferIsCandidate := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendPreVote SnapshotWithinLog using wp by
  have hSnapshotWithinLog := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendPreVote BaseWithinSnapshot using wp by
  have hBaseWithinSnapshot := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendPreVote SnapshotCommitted using wp by
  have hSnapshotCommitted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendPreVote SnapshotApplied using wp by
  have hSnapshotApplied := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

-- GrantPreVote

prove_veil_invariant_goal GrantPreVote ElectionSafety using wp by
  have hElectionSafety := hinv.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal GrantPreVote OneVotePerTerm using wp by
  have hOneVotePerTerm := hinv.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal GrantPreVote VoteTermBound using wp by
  have hVoteTermBound := hinv.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal GrantPreVote VotesBound using wp by
  have hVotesBound := hinv.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal GrantPreVote GrantsAreVotes using wp by
  have hGV := hinv.2.2.2.2.1
  clear hinv
  intros
  rename_i m hm
  rw [RaftVeil.Lemmas.mem_insert] at hm
  rcases hm with rfl | hm
  · rfl
  · exact hGV m hm

prove_veil_invariant_goal GrantPreVote LeadersHaveQuorum using wp by
  have hLeadersHaveQuorum := hinv.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal GrantPreVote LeaderIsElected using wp by
  have hLeaderIsElected := hinv.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal GrantPreVote LeadersTermBound using wp by
  have hLeadersTermBound := hinv.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal GrantPreVote LedOwner using wp by
  have hLedOwner := hinv.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal GrantPreVote LeadersHaveLed using wp by
  have hLeadersHaveLed := hinv.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal GrantPreVote LedHasLeader using wp by
  have hLedHasLeader := hinv.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal GrantPreVote AppendFromLeader using wp by
  have hAppendFromLeader := hinv.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal GrantPreVote LeaderLogIsLed using wp by
  have hLeaderLogIsLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal GrantPreVote RequestsFromLed using wp by
  have hRequestsFromLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal GrantPreVote BootEntry using wp by
  have hBootEntry := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal GrantPreVote LedBoot using wp by
  have hLedBoot := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal GrantPreVote LogFromLed using wp by
  have hLogFromLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal GrantPreVote LedFromLed using wp by
  have hLedFromLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal GrantPreVote LogMatching using wp by
  have hLogMatching := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal GrantPreVote TermsPositive using wp by
  have hTermsPositive := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal GrantPreVote LogTermsBound using wp by
  have hLogTermsBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal GrantPreVote LedSorted using wp by
  have hLedSorted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal GrantPreVote ReqFacts using wp by
  have hReqFacts := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal GrantPreVote ReqUnique using wp by
  have hReqUnique := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal GrantPreVote VoteHasReq using wp by
  have hVoteHasReq := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal GrantPreVote CandLog using wp by
  have hCandLog := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal GrantPreVote LedExtendsReq using wp by
  have hLedExtendsReq := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal GrantPreVote AckFacts using wp by
  have hAckFacts := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal GrantPreVote AckedHeld using wp by
  have hAH := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  rename_i n t A c hack
  exact hAH n t A c (Acked.of_insert _ _ _ _ _ _ _ _ (fun _ _ _ _ h => by cases h) hack)

prove_veil_invariant_goal GrantPreVote AckVote using wp by
  have hAV := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro v
  intros
  rename_i n t A c hack hv hvn htv li lt hreq
  rcases (RaftVeil.Lemmas.contains_insert_iff _ _ _).1 hreq with h | h
  · cases h
  · exact hAV v n t A c (Acked.of_insert _ _ _ _ _ _ _ _ (fun _ _ _ _ h => by cases h) hack) hv hvn htv li lt h

prove_veil_invariant_goal GrantPreVote EarlyQuorum using wp by
  have hEQ := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro ld
  intros
  rename_i hld
  refine IsQuorum.mono _ _ ?_ (hEQ ld hld)
  intro n hn
  simp only [decide_eq_true_eq] at hn ⊢
  exact ⟨hn.1, Early.of_insert _ _ _ _ _ _ _ (fun _ _ _ _ h => by cases h) (fun _ _ h => by cases h) hn.2⟩

prove_veil_invariant_goal GrantPreVote ConfirmedIsLed using wp by
  have hConfirmedIsLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal GrantPreVote CommitRoot using wp by
  have hCR := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro k
  intros
  rename_i hk
  obtain ⟨h1, r, h2, h3, h4, h5⟩ := hCR k hk
  exact ⟨h1, r, h2, Root.mono _ _ _ _ _ _ _ (fun a ha => (RaftVeil.Lemmas.mem_insert _ _ _).2 (Or.inr ha))
    (fun a ha => ha) (LedGrows.refl _) h3, h4, h5⟩

prove_veil_invariant_goal GrantPreVote CommitSafety using wp by
  have hCommitSafety := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal GrantPreVote ConfirmedTermBound using wp by
  have hConfirmedTermBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal GrantPreVote CommitTermBound using wp by
  have hCommitTermBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal GrantPreVote CommittedEntriesPreserved using wp by
  have hCommittedEntriesPreserved := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal GrantPreVote CommitIndexCommitted using wp by
  have hCommitIndexCommitted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal GrantPreVote AppliedCommitted using wp by
  have hAppliedCommitted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal GrantPreVote StateMachineSafety using wp by
  have hStateMachineSafety := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal GrantPreVote LeaderCompleteness using wp by
  have hLeaderCompleteness := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal GrantPreVote ConfirmedWithinLog using wp by
  have hConfirmedWithinLog := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal GrantPreVote PreVoteRequestsBounded using wp by
  have hPreVoteRequestsBounded := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal GrantPreVote PreGrantsAnswer using wp by
  have hPGA := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  -- `a` is the request the action chose; `b` the message the invariant speaks of.
  rename_i hm hpv hsrc hterm hup b hb
  rw [RaftVeil.Lemmas.mem_insert] at hb
  rcases hb with rfl | hb
  · cases a with
    | prevote s t li lt =>
      simp only [decide_eq_true_eq]
      refine ⟨⟨Msg.prevote s t li lt, (RaftVeil.Lemmas.mem_insert _ _ _).2 (Or.inr hm)⟩, ?_⟩
      simp [Msg.src, Msg.term]
    | _ => simp [Msg.isPreVote] at hpv
  · refine pregrants_mono _ _ b (hPGA b hb) ?_
    intro d t hx
    simp only [decide_eq_true_eq] at hx ⊢
    obtain ⟨⟨m', hm'⟩, hm2⟩ := hx
    exact ⟨⟨m', (RaftVeil.Lemmas.mem_insert _ _ _).2 (Or.inr hm')⟩, hm2⟩

prove_veil_invariant_goal GrantPreVote TimeoutNowFromLeader using wp by
  have hTimeoutNowFromLeader := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal GrantPreVote TransferIsCandidate using wp by
  have hTransferIsCandidate := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal GrantPreVote SnapshotWithinLog using wp by
  have hSnapshotWithinLog := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal GrantPreVote BaseWithinSnapshot using wp by
  have hBaseWithinSnapshot := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal GrantPreVote SnapshotCommitted using wp by
  have hSnapshotCommitted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal GrantPreVote SnapshotApplied using wp by
  have hSnapshotApplied := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

-- SendTimeoutNow

prove_veil_invariant_goal SendTimeoutNow ElectionSafety using wp by
  have hElectionSafety := hinv.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendTimeoutNow OneVotePerTerm using wp by
  have hOneVotePerTerm := hinv.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendTimeoutNow VoteTermBound using wp by
  have hVoteTermBound := hinv.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendTimeoutNow VotesBound using wp by
  have hVotesBound := hinv.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendTimeoutNow GrantsAreVotes using wp by
  have hGV := hinv.2.2.2.2.1
  clear hinv
  intros
  rename_i m hm
  rw [RaftVeil.Lemmas.mem_insert] at hm
  rcases hm with rfl | hm
  · rfl
  · exact hGV m hm

prove_veil_invariant_goal SendTimeoutNow LeadersHaveQuorum using wp by
  have hLeadersHaveQuorum := hinv.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendTimeoutNow LeaderIsElected using wp by
  have hLeaderIsElected := hinv.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendTimeoutNow LeadersTermBound using wp by
  have hLeadersTermBound := hinv.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendTimeoutNow LedOwner using wp by
  have hLedOwner := hinv.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendTimeoutNow LeadersHaveLed using wp by
  have hLeadersHaveLed := hinv.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendTimeoutNow LedHasLeader using wp by
  have hLedHasLeader := hinv.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendTimeoutNow AppendFromLeader using wp by
  have hAppendFromLeader := hinv.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendTimeoutNow LeaderLogIsLed using wp by
  have hLeaderLogIsLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendTimeoutNow RequestsFromLed using wp by
  have hRequestsFromLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendTimeoutNow BootEntry using wp by
  have hBootEntry := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendTimeoutNow LedBoot using wp by
  have hLedBoot := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendTimeoutNow LogFromLed using wp by
  have hLogFromLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendTimeoutNow LedFromLed using wp by
  have hLedFromLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendTimeoutNow LogMatching using wp by
  have hLogMatching := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendTimeoutNow TermsPositive using wp by
  have hTermsPositive := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendTimeoutNow LogTermsBound using wp by
  have hLogTermsBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendTimeoutNow LedSorted using wp by
  have hLedSorted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendTimeoutNow ReqFacts using wp by
  have hReqFacts := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendTimeoutNow ReqUnique using wp by
  have hReqUnique := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendTimeoutNow VoteHasReq using wp by
  have hVoteHasReq := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendTimeoutNow CandLog using wp by
  have hCandLog := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendTimeoutNow LedExtendsReq using wp by
  have hLedExtendsReq := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendTimeoutNow AckFacts using wp by
  have hAckFacts := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendTimeoutNow AckedHeld using wp by
  have hAH := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  rename_i n t A c hack
  exact hAH n t A c (Acked.of_insert _ _ _ _ _ _ _ _ (fun _ _ _ _ h => by cases h) hack)

prove_veil_invariant_goal SendTimeoutNow AckVote using wp by
  have hAV := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  rename_i x v hx hxi hne n t A c hack hv hvn htv li lt hreq
  rcases (RaftVeil.Lemmas.contains_insert_iff _ _ _).1 hreq with h | h
  · cases h
  · exact hAV v n t A c (Acked.of_insert _ _ _ _ _ _ _ _ (fun _ _ _ _ h => by cases h) hack) hv hvn htv li lt h

prove_veil_invariant_goal SendTimeoutNow EarlyQuorum using wp by
  have hEQ := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  rename_i x ld hx hxi hne hld
  refine IsQuorum.mono _ _ ?_ (hEQ ld hld)
  intro n hn
  simp only [decide_eq_true_eq] at hn ⊢
  exact ⟨hn.1, Early.of_insert _ _ _ _ _ _ _ (fun _ _ _ _ h => by cases h) (fun _ _ h => by cases h) hn.2⟩

prove_veil_invariant_goal SendTimeoutNow ConfirmedIsLed using wp by
  have hConfirmedIsLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendTimeoutNow CommitRoot using wp by
  have hCR := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  rename_i x k hx hxi hne hk
  obtain ⟨h1, r, h2, h3, h4, h5⟩ := hCR k hk
  exact ⟨h1, r, h2, Root.mono _ _ _ _ _ _ _ (fun a ha => (RaftVeil.Lemmas.mem_insert _ _ _).2 (Or.inr ha))
    (fun a ha => ha) (LedGrows.refl _) h3, h4, h5⟩

prove_veil_invariant_goal SendTimeoutNow CommitSafety using wp by
  have hCommitSafety := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendTimeoutNow ConfirmedTermBound using wp by
  have hConfirmedTermBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendTimeoutNow CommitTermBound using wp by
  have hCommitTermBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendTimeoutNow CommittedEntriesPreserved using wp by
  have hCommittedEntriesPreserved := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendTimeoutNow CommitIndexCommitted using wp by
  have hCommitIndexCommitted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendTimeoutNow AppliedCommitted using wp by
  have hAppliedCommitted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendTimeoutNow StateMachineSafety using wp by
  have hStateMachineSafety := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendTimeoutNow LeaderCompleteness using wp by
  have hLeaderCompleteness := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendTimeoutNow ConfirmedWithinLog using wp by
  have hConfirmedWithinLog := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendTimeoutNow PreVoteRequestsBounded using wp by
  have hPreVoteRequestsBounded := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendTimeoutNow PreGrantsAnswer using wp by
  have hPGA := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  rename_i a ha
  rw [RaftVeil.Lemmas.mem_insert] at ha
  rcases ha with rfl | ha
  · rfl
  · refine pregrants_mono _ _ a (hPGA a ha) ?_
    intro d t hx
    simp only [decide_eq_true_eq] at hx ⊢
    obtain ⟨⟨m, hm⟩, hm2⟩ := hx
    exact ⟨⟨m, (RaftVeil.Lemmas.mem_insert _ _ _).2 (Or.inr hm)⟩, hm2⟩

prove_veil_invariant_goal SendTimeoutNow TimeoutNowFromLeader using wp by
  have hTN := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  rename_i ld hld hldi hne a ha
  rw [RaftVeil.Lemmas.mem_insert] at ha
  rcases ha with rfl | ha
  · simp only [decide_eq_true_eq]
    exact ⟨⟨ld, hld⟩, hldi⟩
  · exact hTN a ha

prove_veil_invariant_goal SendTimeoutNow TransferIsCandidate using wp by
  have hTransferIsCandidate := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendTimeoutNow SnapshotWithinLog using wp by
  have hSnapshotWithinLog := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendTimeoutNow BaseWithinSnapshot using wp by
  have hBaseWithinSnapshot := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendTimeoutNow SnapshotCommitted using wp by
  have hSnapshotCommitted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendTimeoutNow SnapshotApplied using wp by
  have hSnapshotApplied := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

-- TimeoutNow

prove_veil_invariant_goal TimeoutNow ElectionSafety using wp by
  have hElectionSafety := hinv.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal TimeoutNow OneVotePerTerm using wp by
  have hOneVotePerTerm := hinv.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal TimeoutNow VoteTermBound using wp by
  have hVoteTermBound := hinv.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal TimeoutNow VotesBound using wp by
  have hVotesBound := hinv.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal TimeoutNow GrantsAreVotes using wp by
  have hGrantsAreVotes := hinv.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal TimeoutNow LeadersHaveQuorum using wp by
  have hLeadersHaveQuorum := hinv.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal TimeoutNow LeaderIsElected using wp by
  have hLeaderIsElected := hinv.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal TimeoutNow LeadersTermBound using wp by
  have hLeadersTermBound := hinv.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal TimeoutNow LedOwner using wp by
  have hLedOwner := hinv.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal TimeoutNow LeadersHaveLed using wp by
  have hLeadersHaveLed := hinv.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal TimeoutNow LedHasLeader using wp by
  have hLedHasLeader := hinv.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal TimeoutNow AppendFromLeader using wp by
  have hAppendFromLeader := hinv.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal TimeoutNow LeaderLogIsLed using wp by
  have hLeaderLogIsLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal TimeoutNow RequestsFromLed using wp by
  have hRequestsFromLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal TimeoutNow BootEntry using wp by
  have hBootEntry := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal TimeoutNow LedBoot using wp by
  have hLedBoot := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal TimeoutNow LogFromLed using wp by
  have hLogFromLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal TimeoutNow LedFromLed using wp by
  have hLedFromLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal TimeoutNow LogMatching using wp by
  have hLogMatching := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal TimeoutNow TermsPositive using wp by
  have hTermsPositive := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal TimeoutNow LogTermsBound using wp by
  have hLogTermsBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal TimeoutNow LedSorted using wp by
  have hLedSorted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal TimeoutNow ReqFacts using wp by
  have hReqFacts := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal TimeoutNow ReqUnique using wp by
  have hReqUnique := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal TimeoutNow VoteHasReq using wp by
  have hVoteHasReq := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal TimeoutNow CandLog using wp by
  have hCandLog := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal TimeoutNow LedExtendsReq using wp by
  have hLedExtendsReq := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal TimeoutNow AckFacts using wp by
  have hAckFacts := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal TimeoutNow AckedHeld using wp by
  have hAckedHeld := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal TimeoutNow AckVote using wp by
  have hAckVote := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal TimeoutNow EarlyQuorum using wp by
  have hEarlyQuorum := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal TimeoutNow ConfirmedIsLed using wp by
  have hConfirmedIsLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal TimeoutNow CommitRoot using wp by
  have hCommitRoot := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal TimeoutNow CommitSafety using wp by
  have hCommitSafety := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal TimeoutNow ConfirmedTermBound using wp by
  have hConfirmedTermBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal TimeoutNow CommitTermBound using wp by
  have hCommitTermBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal TimeoutNow CommittedEntriesPreserved using wp by
  have hCommittedEntriesPreserved := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal TimeoutNow CommitIndexCommitted using wp by
  have hCommitIndexCommitted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal TimeoutNow AppliedCommitted using wp by
  have hAppliedCommitted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal TimeoutNow StateMachineSafety using wp by
  have hStateMachineSafety := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal TimeoutNow LeaderCompleteness using wp by
  have hLeaderCompleteness := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal TimeoutNow ConfirmedWithinLog using wp by
  have hConfirmedWithinLog := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal TimeoutNow PreVoteRequestsBounded using wp by
  have hPreVoteRequestsBounded := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal TimeoutNow PreGrantsAnswer using wp by
  have hPreGrantsAnswer := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal TimeoutNow TimeoutNowFromLeader using wp by
  have hTimeoutNowFromLeader := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal TimeoutNow TransferIsCandidate using wp by
  have hTransferIsCandidate := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal TimeoutNow SnapshotWithinLog using wp by
  have hSnapshotWithinLog := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal TimeoutNow BaseWithinSnapshot using wp by
  have hBaseWithinSnapshot := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal TimeoutNow SnapshotCommitted using wp by
  have hSnapshotCommitted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal TimeoutNow SnapshotApplied using wp by
  have hSnapshotApplied := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

-- TakeSnapshot

prove_veil_invariant_goal TakeSnapshot ElectionSafety using wp by
  have hElectionSafety := hinv.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal TakeSnapshot OneVotePerTerm using wp by
  have hOneVotePerTerm := hinv.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal TakeSnapshot VoteTermBound using wp by
  have hVoteTermBound := hinv.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal TakeSnapshot VotesBound using wp by
  have hVotesBound := hinv.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal TakeSnapshot GrantsAreVotes using wp by
  have hGrantsAreVotes := hinv.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal TakeSnapshot LeadersHaveQuorum using wp by
  have hLeadersHaveQuorum := hinv.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal TakeSnapshot LeaderIsElected using wp by
  have hLeaderIsElected := hinv.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal TakeSnapshot LeadersTermBound using wp by
  have hLeadersTermBound := hinv.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal TakeSnapshot LedOwner using wp by
  have hLedOwner := hinv.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal TakeSnapshot LeadersHaveLed using wp by
  have hLeadersHaveLed := hinv.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal TakeSnapshot LedHasLeader using wp by
  have hLedHasLeader := hinv.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal TakeSnapshot AppendFromLeader using wp by
  have hAppendFromLeader := hinv.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal TakeSnapshot LeaderLogIsLed using wp by
  have hLeaderLogIsLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal TakeSnapshot RequestsFromLed using wp by
  have hRequestsFromLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal TakeSnapshot BootEntry using wp by
  have hBootEntry := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal TakeSnapshot LedBoot using wp by
  have hLedBoot := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal TakeSnapshot LogFromLed using wp by
  have hLogFromLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal TakeSnapshot LedFromLed using wp by
  have hLedFromLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal TakeSnapshot LogMatching using wp by
  have hLogMatching := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal TakeSnapshot TermsPositive using wp by
  have hTermsPositive := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal TakeSnapshot LogTermsBound using wp by
  have hLogTermsBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal TakeSnapshot LedSorted using wp by
  have hLedSorted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal TakeSnapshot ReqFacts using wp by
  have hReqFacts := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal TakeSnapshot ReqUnique using wp by
  have hReqUnique := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal TakeSnapshot VoteHasReq using wp by
  have hVoteHasReq := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal TakeSnapshot CandLog using wp by
  have hCandLog := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal TakeSnapshot LedExtendsReq using wp by
  have hLedExtendsReq := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal TakeSnapshot AckFacts using wp by
  have hAckFacts := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal TakeSnapshot AckedHeld using wp by
  have hAckedHeld := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal TakeSnapshot AckVote using wp by
  have hAckVote := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal TakeSnapshot EarlyQuorum using wp by
  have hEarlyQuorum := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal TakeSnapshot ConfirmedIsLed using wp by
  have hConfirmedIsLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal TakeSnapshot CommitRoot using wp by
  have hCommitRoot := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal TakeSnapshot CommitSafety using wp by
  have hCommitSafety := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal TakeSnapshot ConfirmedTermBound using wp by
  have hConfirmedTermBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal TakeSnapshot CommitTermBound using wp by
  have hCommitTermBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal TakeSnapshot CommittedEntriesPreserved using wp by
  have hCommittedEntriesPreserved := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal TakeSnapshot CommitIndexCommitted using wp by
  have hCommitIndexCommitted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal TakeSnapshot AppliedCommitted using wp by
  have hAppliedCommitted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal TakeSnapshot StateMachineSafety using wp by
  have hStateMachineSafety := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal TakeSnapshot LeaderCompleteness using wp by
  have hLeaderCompleteness := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal TakeSnapshot ConfirmedWithinLog using wp by
  have hConfirmedWithinLog := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal TakeSnapshot PreVoteRequestsBounded using wp by
  have hPreVoteRequestsBounded := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal TakeSnapshot PreGrantsAnswer using wp by
  have hPreGrantsAnswer := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal TakeSnapshot TimeoutNowFromLeader using wp by
  have hTimeoutNowFromLeader := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal TakeSnapshot TransferIsCandidate using wp by
  have hTransferIsCandidate := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal TakeSnapshot SnapshotWithinLog using wp by
  have hSWL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro hS k hk1 hk2 hgt hcm j
  by_cases hd : i = j
  · subst hd
    have e : Append.append (st.snap i) (SubSeq (st.log i) ((st.snap i).length + 1) k) = (st.log i).take k :=
      snap_extend _ _ k ((isPrefix_iff _ _).1 (hSWL i)) (by omega)
    rw [RaftVeil.Lemmas.ifPos rfl, e]
    exact (isPrefix_iff _ _).2 (List.take_prefix _ _)
  · rw [RaftVeil.Lemmas.ifNeg hd]; exact hSWL j

prove_veil_invariant_goal TakeSnapshot BaseWithinSnapshot using wp by
  have hBWS := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro hS k hk1 hk2 hgt hcm j
  by_cases hd : i = j
  · subst hd
    rw [RaftVeil.Lemmas.ifPos rfl]
    exact Nat.le_trans (hBWS i) (snap_extend_length _ _ k (by omega)).1
  · rw [RaftVeil.Lemmas.ifNeg hd]; exact hBWS j

prove_veil_invariant_goal TakeSnapshot SnapshotCommitted using wp by
  have hCEP := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hCIC := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hSWL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hSC := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro hS k hk1 hk2 hgt hcm j
  by_cases hd : i = j
  · subst hd
    have e : Append.append (st.snap i) (SubSeq (st.log i) ((st.snap i).length + 1) k) = (st.log i).take k :=
      snap_extend _ _ k ((isPrefix_iff _ _).1 (hSWL i)) (by omega)
    rw [RaftVeil.Lemmas.ifPos rfl, e]
    right
    rcases hCIC i with h0 | ⟨c, hcs, hc, hcl⟩
    · omega
    · refine ⟨c, hc, (isPrefix_iff _ _).2 ?_⟩
      have hcp := (isPrefix_iff _ _).1 (hCEP c hc)
      rw [hcs] at hcp
      exact take_prefix_of_prefix _ _ k hcp (by omega)
  · rw [RaftVeil.Lemmas.ifNeg hd]; exact hSC j

prove_veil_invariant_goal TakeSnapshot SnapshotApplied using wp by
  have hSA := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  clear hinv
  intro hS k hk1 hk2 hgt hcm j
  by_cases hd : i = j
  · subst hd
    rw [RaftVeil.Lemmas.ifPos rfl]
    exact Nat.le_trans (snap_extend_length _ _ k (by omega)).2 (by omega)
  · rw [RaftVeil.Lemmas.ifNeg hd]; exact hSA j
-- CompactLog

prove_veil_invariant_goal CompactLog ElectionSafety using wp by
  have hElectionSafety := hinv.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal CompactLog OneVotePerTerm using wp by
  have hOneVotePerTerm := hinv.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal CompactLog VoteTermBound using wp by
  have hVoteTermBound := hinv.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal CompactLog VotesBound using wp by
  have hVotesBound := hinv.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal CompactLog GrantsAreVotes using wp by
  have hGrantsAreVotes := hinv.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal CompactLog LeadersHaveQuorum using wp by
  have hLeadersHaveQuorum := hinv.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal CompactLog LeaderIsElected using wp by
  have hLeaderIsElected := hinv.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal CompactLog LeadersTermBound using wp by
  have hLeadersTermBound := hinv.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal CompactLog LedOwner using wp by
  have hLedOwner := hinv.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal CompactLog LeadersHaveLed using wp by
  have hLeadersHaveLed := hinv.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal CompactLog LedHasLeader using wp by
  have hLedHasLeader := hinv.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal CompactLog AppendFromLeader using wp by
  have hAppendFromLeader := hinv.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal CompactLog LeaderLogIsLed using wp by
  have hLeaderLogIsLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal CompactLog RequestsFromLed using wp by
  have hRequestsFromLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal CompactLog BootEntry using wp by
  have hBootEntry := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal CompactLog LedBoot using wp by
  have hLedBoot := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal CompactLog LogFromLed using wp by
  have hLogFromLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal CompactLog LedFromLed using wp by
  have hLedFromLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal CompactLog LogMatching using wp by
  have hLogMatching := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal CompactLog TermsPositive using wp by
  have hTermsPositive := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal CompactLog LogTermsBound using wp by
  have hLogTermsBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal CompactLog LedSorted using wp by
  have hLedSorted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal CompactLog ReqFacts using wp by
  have hReqFacts := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal CompactLog ReqUnique using wp by
  have hReqUnique := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal CompactLog VoteHasReq using wp by
  have hVoteHasReq := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal CompactLog CandLog using wp by
  have hCandLog := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal CompactLog LedExtendsReq using wp by
  have hLedExtendsReq := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal CompactLog AckFacts using wp by
  have hAckFacts := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal CompactLog AckedHeld using wp by
  have hAckedHeld := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal CompactLog AckVote using wp by
  have hAckVote := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal CompactLog EarlyQuorum using wp by
  have hEarlyQuorum := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal CompactLog ConfirmedIsLed using wp by
  have hConfirmedIsLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal CompactLog CommitRoot using wp by
  have hCommitRoot := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal CompactLog CommitSafety using wp by
  have hCommitSafety := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal CompactLog ConfirmedTermBound using wp by
  have hConfirmedTermBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal CompactLog CommitTermBound using wp by
  have hCommitTermBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal CompactLog CommittedEntriesPreserved using wp by
  have hCommittedEntriesPreserved := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal CompactLog CommitIndexCommitted using wp by
  have hCommitIndexCommitted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal CompactLog AppliedCommitted using wp by
  have hAppliedCommitted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal CompactLog StateMachineSafety using wp by
  have hStateMachineSafety := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal CompactLog LeaderCompleteness using wp by
  have hLeaderCompleteness := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal CompactLog ConfirmedWithinLog using wp by
  have hConfirmedWithinLog := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal CompactLog PreVoteRequestsBounded using wp by
  have hPreVoteRequestsBounded := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal CompactLog PreGrantsAnswer using wp by
  have hPreGrantsAnswer := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal CompactLog TimeoutNowFromLeader using wp by
  have hTimeoutNowFromLeader := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal CompactLog TransferIsCandidate using wp by
  have hTransferIsCandidate := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal CompactLog SnapshotWithinLog using wp by
  have hSnapshotWithinLog := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal CompactLog BaseWithinSnapshot using wp by
  have hBaseWithinSnapshot := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal CompactLog SnapshotCommitted using wp by
  have hSnapshotCommitted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal CompactLog SnapshotApplied using wp by
  have hSnapshotApplied := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

-- InstallSnapshot

prove_veil_invariant_goal InstallSnapshot ElectionSafety using wp by
  have hElectionSafety := hinv.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal InstallSnapshot OneVotePerTerm using wp by
  have hOneVotePerTerm := hinv.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal InstallSnapshot VoteTermBound using wp by
  have hVoteTermBound := hinv.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal InstallSnapshot VotesBound using wp by
  have hVotesBound := hinv.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal InstallSnapshot GrantsAreVotes using wp by
  have hGrantsAreVotes := hinv.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal InstallSnapshot LeadersHaveQuorum using wp by
  have hLeadersHaveQuorum := hinv.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal InstallSnapshot LeaderIsElected using wp by
  have hLeaderIsElected := hinv.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal InstallSnapshot LeadersTermBound using wp by
  have hLeadersTermBound := hinv.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal InstallSnapshot LedOwner using wp by
  have hLedOwner := hinv.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal InstallSnapshot LeadersHaveLed using wp by
  have hLeadersHaveLed := hinv.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal InstallSnapshot LedHasLeader using wp by
  have hLedHasLeader := hinv.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal InstallSnapshot AppendFromLeader using wp by
  have hAppendFromLeader := hinv.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal InstallSnapshot LeaderLogIsLed using wp by
  have hLeaderLogIsLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal InstallSnapshot RequestsFromLed using wp by
  have hRequestsFromLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal InstallSnapshot BootEntry using wp by
  have hBootEntry := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal InstallSnapshot LedBoot using wp by
  have hLedBoot := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal InstallSnapshot LogFromLed using wp by
  have hLogFromLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal InstallSnapshot LedFromLed using wp by
  have hLedFromLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal InstallSnapshot LogMatching using wp by
  have hLogMatching := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal InstallSnapshot TermsPositive using wp by
  have hTermsPositive := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal InstallSnapshot LogTermsBound using wp by
  have hLogTermsBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal InstallSnapshot LedSorted using wp by
  have hLedSorted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal InstallSnapshot ReqFacts using wp by
  have hReqFacts := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal InstallSnapshot ReqUnique using wp by
  have hReqUnique := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal InstallSnapshot VoteHasReq using wp by
  have hVoteHasReq := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal InstallSnapshot CandLog using wp by
  have hCandLog := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal InstallSnapshot LedExtendsReq using wp by
  have hLedExtendsReq := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal InstallSnapshot AckFacts using wp by
  have hAckFacts := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal InstallSnapshot AckedHeld using wp by
  have hAckedHeld := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal InstallSnapshot AckVote using wp by
  have hAckVote := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal InstallSnapshot EarlyQuorum using wp by
  have hEarlyQuorum := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal InstallSnapshot ConfirmedIsLed using wp by
  have hConfirmedIsLed := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal InstallSnapshot CommitRoot using wp by
  have hCommitRoot := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal InstallSnapshot CommitSafety using wp by
  have hCommitSafety := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal InstallSnapshot ConfirmedTermBound using wp by
  have hConfirmedTermBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal InstallSnapshot CommitTermBound using wp by
  have hCommitTermBound := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal InstallSnapshot CommittedEntriesPreserved using wp by
  have hCommittedEntriesPreserved := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal InstallSnapshot CommitIndexCommitted using wp by
  have hCommitIndexCommitted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal InstallSnapshot AppliedCommitted using wp by
  have hAppliedCommitted := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal InstallSnapshot StateMachineSafety using wp by
  have hStateMachineSafety := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal InstallSnapshot LeaderCompleteness using wp by
  have hLeaderCompleteness := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal InstallSnapshot ConfirmedWithinLog using wp by
  have hConfirmedWithinLog := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal InstallSnapshot PreVoteRequestsBounded using wp by
  have hPreVoteRequestsBounded := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal InstallSnapshot PreGrantsAnswer using wp by
  have hPreGrantsAnswer := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal InstallSnapshot TimeoutNowFromLeader using wp by
  have hTimeoutNowFromLeader := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal InstallSnapshot TransferIsCandidate using wp by
  have hTransferIsCandidate := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal InstallSnapshot SnapshotWithinLog using wp by
  have hRFL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hBoot := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLBoot := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLFL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hLedFL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hSWL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro hS a ha hisA hp0 hlen1 hcommit hterm hnewer hnewer' hfirst j
  by_cases hd : a.dst = j
  · subst hd
    rw [RaftVeil.Lemmas.ifPos rfl]
    obtain ⟨L, hL, hpn, hpt, hes, -⟩ := req_facts st.ledLog _ a (hRFL a ha) hisA
    have hLedL := (optAll_iff _ _).1 (hLedFL a.term) L hL
    have hLB : L.head? = some Boot := by simpa using (optAll_iff _ _).1 (hLBoot a.term) L hL
    have hprev : PrevOk (st.log a.dst) a.prevLogIndex (TermAt L a.prevLogIndex) = true := by rw [hp0]; rfl
    have hchk := checked_prefix st.ledLog (st.log a.dst) L a.prevLogIndex a.entries.length a.entries (hLFL a.dst) hLedL
      (hBoot a.dst) hLB hpn hes hprev (Nat.le_refl _) hfirst
    simp only [hp0, Nat.zero_add] at hchk hes
    rw [subSeq_one] at hes
    refine (isPrefix_iff _ _).2 ?_
    rw [hes, ← hchk.2]
    exact List.take_prefix _ _
  · rw [RaftVeil.Lemmas.ifNeg hd]; exact hSWL j

prove_veil_invariant_goal InstallSnapshot BaseWithinSnapshot using wp by
  have hBaseWithinSnapshot := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal InstallSnapshot SnapshotCommitted using wp by
  have hRFL := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hSC := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  clear hinv
  intro hS a ha hisA hp0 hlen1 hcommit hterm hnewer hnewer' hfirst j
  by_cases hd : a.dst = j
  · subst hd
    rw [RaftVeil.Lemmas.ifPos rfl]
    right
    obtain ⟨L, hL, hpn, hpt, hes, hX⟩ := req_facts st.ledLog _ a (hRFL a ha) hisA
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hX
    rcases hX with h0 | ⟨hcl, ⟨kk, hkk⟩, hkt, hk1, hk2⟩
    · omega
    · refine ⟨kk, hkk, (isPrefix_iff _ _).2 ?_⟩
      simp only [hp0, Nat.zero_add] at hes
      rw [subSeq_one] at hes
      rw [subSeq_one, subSeq_one] at hk2
      have e : kk.entries.take a.entries.length = L.take a.entries.length := by
        have := congrArg (List.take a.entries.length) hk2
        rwa [List.take_take, List.take_take, Nat.min_eq_left hcommit] at this
      rw [hes, ← e]
      exact List.take_prefix _ _
  · rw [RaftVeil.Lemmas.ifNeg hd]; exact hSC j

prove_veil_invariant_goal InstallSnapshot SnapshotApplied using wp by
  have hSnapshotApplied := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  clear hinv
  intros
  have hRole := Role_Enum.distinct
  simp only [distinctN, distinctPairs, ne_eq, List.foldr_cons, List.foldr_nil, List.map_nil, List.map_cons,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, andN_cons_append,
    andN] at hRole
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

end RaftVeil
