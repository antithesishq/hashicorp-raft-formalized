module

public import Veil

/-!
`../spec/Raft.tla` in Veil, one to one: the same variables, the same actions
with the same parameters, the same properties. Each TLA+ definition is quoted
above its translation. See README.md for how the two are kept in step.

Encoding:
* `Server` is the type `server`. `Cardinality(S)` for a set `S` of servers given by a condition
  is `Card` of that condition: the number of servers that satisfy it, counted over the list of
  all servers that the class `Servers` provides.
* `Nil` is `none`: `voteFor` is `server → Option server`, an entry's value is `Option value`.
* A log is a `List`; entry `k` of the source is element `k - 1`.
* `confirmed[i]`, a record, is the two fields `confirmedTerm i` and `confirmedIndex i`.
* The four kinds of fact in `msgs` are the constructors of `Msg`.
* `ledLog`, a function whose domain grows, is `Nat → Option log`: `none` outside the domain.
* Sets (`msgs`, `votes`, `leaders`, `commits`) are TSets.
* An action reads the fields of the message it chose through accessors (`m.dst`, `m.entries`),
  not by pattern matching: Veil cannot generate proof goals for a match inside an action.

The file has three parts: the model; its invariants (those of Raft.tla, then five more that the
proofs need); and the proofs, for ElectionSafety and OneVotePerTerm so far.
-/

namespace RaftVeil.Lemmas
open Veil

-- Facts about TSets, for the proofs at the end of this file. They ask for no decidable equality
-- on the elements, because the proof goals give none for `server`.

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

end RaftVeil.Lemmas

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

-- The fields of an append request, read the way the source reads `m.dst`, `m.entries` and so
-- on. Actions use them only on a message they have required to be an append request; the
-- values given for the other kinds are never read.
def Msg.isAppend {server value : Type} (m : Msg server value) : Bool :=
  match m with | .append .. => true | _ => false
def Msg.src {server value : Type} (m : Msg server value) : server :=
  match m with | .vote s .. => s | .grant s .. => s | .append s .. => s | .ack s .. => s
def Msg.dst {server value : Type} (m : Msg server value) : server :=
  match m with | .vote s .. => s | .grant _ d _ => d | .append _ d .. => d | .ack _ d .. => d
def Msg.term {server value : Type} (m : Msg server value) : Nat :=
  match m with | .vote _ t .. => t | .grant _ _ t => t | .append _ _ t .. => t | .ack _ _ t _ => t
def Msg.prevLogIndex {server value : Type} (m : Msg server value) : Nat :=
  match m with | .append _ _ _ p .. => p | _ => 0
def Msg.prevLogTerm {server value : Type} (m : Msg server value) : Nat :=
  match m with | .append _ _ _ _ pt .. => pt | _ => 0
def Msg.entries {server value : Type} (m : Msg server value) : List (Entry value) :=
  match m with | .append _ _ _ _ _ es _ => es | _ => []
def Msg.commit {server value : Type} (m : Msg server value) : Nat :=
  match m with | .append _ _ _ _ _ _ c => c | _ => 0

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

-- TermAt(l, k) == IF k > 0 /\ k <= Len(l) THEN l[k].term ELSE 0
def TermAt {value : Type} (l : List (Entry value)) (k : Nat) : Nat :=
  match k with
  | 0 => 0
  | k + 1 => match l[k]? with
    | some e => e.term
    | none => 0

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

-- Facts about quorums, for the proofs at the end of this file.

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

type server
type value
type MsgSet
type VoteSet
type LeaderSet
type CommitSet
instantiate srv : Servers server
instantiate msgSet : TSet (Msg server value) MsgSet
instantiate vSet : TSet (Vote server) VoteSet
instantiate lSet : TSet (Elected server) LeaderSet
instantiate cSet : TSet (Commit server value) CommitSet

-- The bounds of MCRaft.tla's `Bounded`.
immutable individual MaxTerm : Nat
immutable individual MaxLog : Nat
immutable individual MaxBatch : Nat
immutable individual MaxMsgs : Nat

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
}

-- BecomeCandidate(i) == role' = [role EXCEPT ![i] = Candidate]
action BecomeCandidate (i : server) {
  role i := Candidate
}

-- BecomeFollower(i) == role' = [role EXCEPT ![i] = Follower]
action BecomeFollower (i : server) {
  role i := Follower
}

-- StartElection(i) ==
--     /\ role[i] = Candidate
--     /\ currentTerm' = [currentTerm EXCEPT ![i] = @ + 1]
--     /\ msgs' = msgs \cup {VoteRequest(i, currentTerm[i] + 1)}
action StartElection (i : server) {
  require role i = Candidate
  let t := currentTerm i + 1
  let l := log i
  currentTerm i := t
  msgs := msgSet.insert (.vote i t l.length (TermAt l l.length)) msgs
}

-- AdoptTerm(i, t) ==
--     /\ t > currentTerm[i]
--     /\ \E k \in Server \ {i} : currentTerm[k] >= t
--     /\ currentTerm' = [currentTerm EXCEPT ![i] = t]
--     /\ role' = [role EXCEPT ![i] = Follower]
-- Next: \E t \in {currentTerm[k] : k \in Server} : AdoptTerm(i, t)
action AdoptTerm (i : server) {
  let k ← pick server
  let t := currentTerm k
  require t > currentTerm i
  require ∃ k', k' ≠ i ∧ currentTerm k' ≥ t
  currentTerm i := t
  role i := Follower
}

-- Voted(i) == voteTerm[i] = currentTerm[i] /\ voteFor[i] # Nil
-- SetVoteTerm(i) ==
--     /\ ~Voted(i)
--     /\ voteTerm' = [voteTerm EXCEPT ![i] = currentTerm[i]]
action SetVoteTerm (i : server) {
  require ¬ (voteTerm i = currentTerm i ∧ voteFor i ≠ none)
  voteTerm i := currentTerm i
}

-- UpToDate(m, i) ==
--     \/ m.lastLogTerm > LastTerm(i)
--     \/ m.lastLogTerm = LastTerm(i) /\ m.lastLogIndex >= Len(log[i])
-- SetVoteFor(i, c) ==
--     /\ voteTerm[i] = currentTerm[i]
--     /\ \A v \in votes : v.voter = i /\ v.term = voteTerm[i] => v.cand = c
--     /\ \/ c = i /\ role[i] = Candidate
--        \/ /\ c # i
--           /\ \E m \in msgs : m.type = "vote" /\ m.src = c /\ m.term = currentTerm[i] /\ UpToDate(m, i)
--     /\ voteFor' = [voteFor EXCEPT ![i] = c]
--     /\ votes' = votes \cup {[voter |-> i, term |-> voteTerm[i], cand |-> c]}
action SetVoteFor (i : server) (c : server) {
  require voteTerm i = currentTerm i
  require ∀ v : { v // v ∈ votes }, v.val.voter = i ∧ v.val.term = voteTerm i → v.val.cand = c
  let l := log i
  let lastTerm := TermAt l l.length
  let cur := currentTerm i
  require (c = i ∧ role i = Candidate) ∨
    (c ≠ i ∧ ∃ m : { m // m ∈ msgs },
      (match m.val with
        | .vote src term lastLogIndex lastLogTerm =>
          decide (src = c ∧ term = cur ∧
            (lastLogTerm > lastTerm ∨ (lastLogTerm = lastTerm ∧ lastLogIndex ≥ l.length)))
        | _ => false) = true)
  voteFor i := some c
  votes := vSet.insert { voter := i, term := voteTerm i, cand := c } votes
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
}

-- LeaderAppend(i, es) ==
--     /\ role[i] = Leader
--     /\ Len(es) > 0
--     /\ \A k \in 1..Len(es) : es[k].term = currentTerm[i]
--     /\ log' = [log EXCEPT ![i] = @ \o es]
--     /\ ledLog' = WithLed(currentTerm[i], log[i] \o es)
-- Next: \E ty \in {"noop", "barrier"} : LeaderAppend(i, <<Entry(currentTerm[i], ty, Nil)>>)
--       \E v \in Values : LeaderAppend(i, <<Entry(currentTerm[i], "command", v)>>)
-- `ty` and `v` stand for the two disjuncts of Next: a marker entry (`v` is then not used), or a
-- command with value `v`.
action LeaderAppend (i : server) (ty : EntryType) (v : value) {
  require ty ≠ .config
  require role i = Leader
  let cur := currentTerm i
  let l := log i ++ [{ term := cur, kind := ty, value := if ty = .command then some v else none }]
  log i := l
  ledLog cur := some l
}

-- CommittedIn(l, c) ==
--     \/ c = 0
--     \/ /\ c <= Len(l)
--        /\ \E k \in commits : c <= Len(k.entries) /\ SubSeq(k.entries, 1, c) = SubSeq(l, 1, c)
-- SendAppend(i, j, t, p, n, c) ==
--     /\ [server |-> i, term |-> t] \in leaders
--     /\ j # i
--     /\ p + n <= Len(ledLog[t])
--     /\ CommittedIn(ledLog[t], c)
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
      c.val ≤ k.val.entries.length ∧ SubSeq k.val.entries 1 c.val = SubSeq l 1 c.val)
  msgs := msgSet.insert
    (.append i j t p.val (TermAt l p.val) (SubSeq l (p.val + 1) (p.val + n.val)) c.val) msgs
}

-- Acked(i, t, c) ==
--     {i} \cup {j \in Server \ {i} :
--                  \E a \in msgs : a.type = "ack" /\ a.src = j /\ a.dst = i /\ a.term = t /\ a.index >= c}
-- Committed(s, t) == [server |-> s, term |-> t, entries |-> SubSeq(log[s], 1, commitIndex'[s])]
-- LeaderCommit(i, t, c) ==
--     /\ [server |-> i, term |-> t] \in leaders
--     /\ c > commitIndex[i]
--     /\ c <= Len(log[i])
--     /\ log[i][c].term = t
--     /\ IsQuorum(Acked(i, t, c))
--     /\ commitIndex' = [commitIndex EXCEPT ![i] = c]
--     /\ commits' = commits \cup {Committed(i, t)}
-- Next: \E c \in 1..Len(log[i]), l \in leaders : l.server = i /\ LeaderCommit(i, l.term, c)
action LeaderCommit (i : server) {
  let ld : { ld // ld ∈ leaders } :| ld.val.server = i
  let t := ld.val.term
  let l := log i
  let c : { c // c ∈ List.range' 1 l.length } :|
    c.val > commitIndex i ∧ TermAt l c.val = t
  let ms := msgs
  require IsQuorum (fun j =>
    if j = i then true
    else decide (∃ a : { a // a ∈ ms },
      (match a.val with
        | .ack src dst term index => decide (src = j ∧ dst = i ∧ term = t ∧ index ≥ c.val)
        | _ => false) = true))
  commitIndex i := c.val
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
--     /\ currentTerm[j] >= m.term
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
  require currentTerm j ≥ m.term
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
--     /\ commits' = commits \cup {Committed(j, m.term)}
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

-- Restart(i) ==
--     /\ role' = [role EXCEPT ![i] = Follower]
--     /\ commitIndex' = [commitIndex EXCEPT ![i] = 0]
--     /\ votes' = IF voteFor[i] # Nil
--                 THEN votes \cup {[voter |-> i, term |-> voteTerm[i], cand |-> voteFor[i]]}
--                 ELSE votes
action Restart (i : server) {
  role i := Follower
  commitIndex i := 0
  let vf := voteFor i
  if vf ≠ none then
    votes := vSet.insert { voter := i, term := voteTerm i, cand := vf.getD i } votes
}

-- ElectionSafety == \A a, b \in leaders : a.term = b.term => a.server = b.server
invariant [ElectionSafety]
  ∀ a b : { x // x ∈ leaders }, a.val.term = b.val.term → a.val.server = b.val.server

-- OneVotePerTerm ==
--     \A a, b \in votes : a.voter = b.voter /\ a.term = b.term => a.cand = b.cand
invariant [OneVotePerTerm]
  ∀ a b : { x // x ∈ votes }, a.val.voter = b.val.voter ∧ a.val.term = b.val.term → a.val.cand = b.val.cand

-- Invariants that are not in Raft.tla: what the proof of ElectionSafety and OneVotePerTerm
-- needs besides those two. Each is also checked by the model checker.

-- A node's vote record is never ahead of its term.
invariant [VoteTermBound] ∀ i : server, voteTerm i ≤ currentTerm i

-- Every vote a node has given is at or before its vote record's term.
invariant [VotesBound] ∀ v : { v // v ∈ votes }, v.val.term ≤ voteTerm v.val.voter

-- A vote given in the term of the node's vote record is the one the record holds.
invariant [VoteRecord]
  ∀ v : { v // v ∈ votes }, v.val.term = voteTerm v.val.voter → voteFor v.val.voter = some v.val.cand

-- A granted reply states a vote that exists.
invariant [GrantsAreVotes]
  ∀ m : { m // m ∈ msgs }, (match m.val with
    | .grant src dst term => vSet.contains { voter := src, term := term, cand := dst } votes
    | _ => true) = true

-- Every leader was voted for by a quorum in its term.
invariant [LeadersHaveQuorum]
  ∀ ld : { x // x ∈ leaders },
    IsQuorum (fun j => vSet.contains { voter := j, term := ld.val.term, cand := ld.val.server } votes) = true

-- LogMatching ==
--     \A a, b \in Server :
--         \A k \in 1..Min(Len(log[a]), Len(log[b])) :
--             log[a][k].term = log[b][k].term => SubSeq(log[a], 1, k) = SubSeq(log[b], 1, k)
invariant [LogMatching]
  ∀ a b : server, ∀ k ∈ List.range' 1 (min (log a).length (log b).length),
    TermAt (log a) k = TermAt (log b) k → SubSeq (log a) 1 k = SubSeq (log b) 1 k

-- StateMachineSafety ==
--     \A a, b \in commits : IsPrefix(a.entries, b.entries) \/ IsPrefix(b.entries, a.entries)
invariant [StateMachineSafety]
  ∀ a b : { x // x ∈ commits },
    IsPrefix a.val.entries b.val.entries ∨ IsPrefix b.val.entries a.val.entries

-- LeaderCompleteness ==
--     \A i \in Server, c \in commits :
--         role[i] = Leader /\ c.term < currentTerm[i] => IsPrefix(c.entries, log[i])
invariant [LeaderCompleteness]
  ∀ i : server, ∀ c : { x // x ∈ commits },
    role i = Leader ∧ c.val.term < currentTerm i → IsPrefix c.val.entries (log i)

-- CommittedEntriesPreserved == \A c \in commits : IsPrefix(c.entries, log[c.server])
invariant [CommittedEntriesPreserved]
  ∀ c : { x // x ∈ commits }, IsPrefix c.val.entries (log c.val.server)

-- LeaderLogIsLed ==
--     \A i \in Server : role[i] = Leader =>
--         /\ currentTerm[i] \in DOMAIN ledLog
--         /\ log[i] = ledLog[currentTerm[i]]
invariant [LeaderLogIsLed]
  ∀ i : server, role i = Leader → ledLog (currentTerm i) = some (log i)

-- ConfirmedWithinLog == \A i \in Server : confirmed[i].index <= Len(log[i])
invariant [ConfirmedWithinLog]
  ∀ i : server, confirmedIndex i ≤ (log i).length

-- RequestsFromLed ==
--     \A m \in msgs : m.type = "append" =>
--         /\ m.term \in DOMAIN ledLog
--         /\ m.prevLogIndex + Len(m.entries) <= Len(ledLog[m.term])
--         /\ m.prevLogTerm = TermAt(ledLog[m.term], m.prevLogIndex)
--         /\ m.entries = SubSeq(ledLog[m.term], m.prevLogIndex + 1, m.prevLogIndex + Len(m.entries))
--         /\ CommittedIn(ledLog[m.term], m.commit)
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
              commit ≤ k.val.entries.length ∧ SubSeq k.val.entries 1 commit = SubSeq l 1 commit))))
    | _ => true) = true

-- Bounded (MCRaft.tla) ==
--     /\ \A i \in Server : currentTerm[i] <= MaxTerm /\ Len(log[i]) <= MaxLog
--     /\ \A m \in msgs : m.type = "append" => Len(m.entries) <= MaxBatch
--     /\ Cardinality(msgs) <= MaxMsgs
state_constraint [Bounded]
  (∀ i, currentTerm i ≤ MaxTerm ∧ (log i).length ≤ MaxLog) ∧
  (∀ m : { m // m ∈ msgs }, (match m.val with
    | .append _ _ _ _ _ entries _ => decide (entries.length ≤ MaxBatch)
    | _ => true) = true) ∧
  msgSet.count msgs ≤ MaxMsgs

#gen_spec
#gen_executable

-- Compared with TLC on the unrestricted `Spec` without symmetry, at the bounds of
-- `../spec/MCCount2.cfg` and `MCCount3.cfg` (MaxMsgs 2 and 3): both checkers find 73,512 and
-- 277,792 distinct states and no violation. `../scripts/veil-count.sh MAXMSGS` runs this side.
-- The check is commented out so that building this file does not run it.
-- #model_check compiled
--   { server := Fin 3, value := Fin 1, Role := Role_IndT, MsgSet := OrdList _,
--     VoteSet := OrdList _, LeaderSet := OrdList _, CommitSet := OrdList _ }
--   { MaxTerm := 2, MaxLog := 2, MaxBatch := 1, MaxMsgs := 2 }

-- ---------------------------------------------------------------------------------------
-- Proofs. ElectionSafety and OneVotePerTerm, with the five invariants above that support
-- them, are preserved by every action and hold initially: one goal per action and invariant.
-- Each proof names the facts it uses (`grind only`, `simp only`), so checking replays it
-- without searching a lemma library. The other invariants of this file are checked by the
-- model checker only; no proof here uses them.
--
-- `hES ... hLQ` are the seven invariants in the state before the step, in the order
-- ElectionSafety, OneVotePerTerm, VoteTermBound, VotesBound, VoteRecord, GrantsAreVotes,
-- LeadersHaveQuorum.
--
-- Check with `lake build` (about 8 minutes on 4 cores; most of it is Veil preparing each goal).

-- initializer

prove_veil_invariant_goal initializer ElectionSafety using tr by
  obtain ⟨-, -, -, -, -, -, -, -, hm, hv, hl, -, hc⟩ := htr
  subst hm hv hl hc
  intros
  exact (RaftVeil.Lemmas.sub_empty a).elim

prove_veil_invariant_goal initializer OneVotePerTerm using tr by
  obtain ⟨-, -, -, -, -, -, -, -, hm, hv, hl, -, hc⟩ := htr
  subst hm hv hl hc
  intros
  exact (RaftVeil.Lemmas.sub_empty a).elim

prove_veil_invariant_goal initializer VoteTermBound using tr by
  obtain ⟨h1, h2, -⟩ := htr
  rw [← h1 i, ← h2 i]
  exact Nat.zero_le 1

prove_veil_invariant_goal initializer VotesBound using tr by
  obtain ⟨-, -, -, -, -, -, -, -, hm, hv, hl, -, hc⟩ := htr
  subst hm hv hl hc
  intros
  exact (RaftVeil.Lemmas.sub_empty v).elim

prove_veil_invariant_goal initializer VoteRecord using tr by
  obtain ⟨-, -, -, -, -, -, -, -, hm, hv, hl, -, hc⟩ := htr
  subst hm hv hl hc
  intros
  exact (RaftVeil.Lemmas.sub_empty v).elim

prove_veil_invariant_goal initializer GrantsAreVotes using tr by
  obtain ⟨-, -, -, -, -, -, -, -, hm, hv, hl, -, hc⟩ := htr
  subst hm hv hl hc
  intros
  exact (RaftVeil.Lemmas.sub_empty m).elim

prove_veil_invariant_goal initializer LeadersHaveQuorum using tr by
  obtain ⟨-, -, -, -, -, -, -, -, hm, hv, hl, -, hc⟩ := htr
  subst hm hv hl hc
  intros
  exact (RaftVeil.Lemmas.sub_empty ld).elim

-- BecomeCandidate

prove_veil_invariant_goal BecomeCandidate ElectionSafety using wp by
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeCandidate OneVotePerTerm using wp by
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeCandidate VoteTermBound using wp by
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeCandidate VotesBound using wp by
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeCandidate VoteRecord using wp by
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeCandidate GrantsAreVotes using wp by
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeCandidate LeadersHaveQuorum using wp by
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

-- BecomeFollower

prove_veil_invariant_goal BecomeFollower ElectionSafety using wp by
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeFollower OneVotePerTerm using wp by
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeFollower VoteTermBound using wp by
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeFollower VotesBound using wp by
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeFollower VoteRecord using wp by
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeFollower GrantsAreVotes using wp by
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeFollower LeadersHaveQuorum using wp by
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

-- StartElection

prove_veil_invariant_goal StartElection ElectionSafety using wp by
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StartElection OneVotePerTerm using wp by
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StartElection VoteTermBound using wp by
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StartElection VotesBound using wp by
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StartElection VoteRecord using wp by
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StartElection GrantsAreVotes using wp by
  try obtain ⟨hES, hOV, hVT, hVB, hVR, hGV, hLQ, -⟩ := hinv
  intros
  simp only [RaftVeil.Lemmas.mem_iff, RaftVeil.Lemmas.contains_insert_iff] at *
  repeat' split
  all_goals grind only

prove_veil_invariant_goal StartElection LeadersHaveQuorum using wp by
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

-- AdoptTerm

prove_veil_invariant_goal AdoptTerm ElectionSafety using wp by
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal AdoptTerm OneVotePerTerm using wp by
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal AdoptTerm VoteTermBound using wp by
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal AdoptTerm VotesBound using wp by
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal AdoptTerm VoteRecord using wp by
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal AdoptTerm GrantsAreVotes using wp by
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal AdoptTerm LeadersHaveQuorum using wp by
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

-- SetVoteTerm

prove_veil_invariant_goal SetVoteTerm ElectionSafety using wp by
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SetVoteTerm OneVotePerTerm using wp by
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SetVoteTerm VoteTermBound using wp by
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SetVoteTerm VotesBound using wp by
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SetVoteTerm VoteRecord using wp by
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SetVoteTerm GrantsAreVotes using wp by
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SetVoteTerm LeadersHaveQuorum using wp by
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

-- SetVoteFor

prove_veil_invariant_goal SetVoteFor ElectionSafety using wp by
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SetVoteFor OneVotePerTerm using wp by
  try obtain ⟨hES, hOV, hVT, hVB, hVR, hGV, hLQ, -⟩ := hinv
  intros
  simp only [RaftVeil.Lemmas.mem_iff, RaftVeil.Lemmas.contains_insert_iff] at *
  repeat' split
  all_goals grind only

prove_veil_invariant_goal SetVoteFor VoteTermBound using wp by
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SetVoteFor VotesBound using wp by
  try obtain ⟨hES, hOV, hVT, hVB, hVR, hGV, hLQ, -⟩ := hinv
  intros
  simp only [RaftVeil.Lemmas.mem_iff, RaftVeil.Lemmas.contains_insert_iff] at *
  repeat' split
  all_goals grind only

prove_veil_invariant_goal SetVoteFor VoteRecord using wp by
  try obtain ⟨hES, hOV, hVT, hVB, hVR, hGV, hLQ, -⟩ := hinv
  intro a h1 h2 h3 hb ht
  have hb' := (RaftVeil.Lemmas.mem_insert _ _ _).mp hb
  rcases hb' with heq | hb'
  · subst heq; simp
  · by_cases hia : i = a.voter
    · subst hia
      have hc := h2 a hb' rfl ht
      simp [hc]
    · simp only [hia, ite_false]
      exact hVR a hb' ht

prove_veil_invariant_goal SetVoteFor GrantsAreVotes using wp by
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SetVoteFor LeadersHaveQuorum using wp by
  obtain ⟨hES, hOV, hVT, hVB, hVR, hGV, hLQ, -⟩ := hinv
  intros
  refine IsQuorum.mono _ _ ?_ (hLQ _ ‹_ ∈ st.leaders›)
  intro j hj
  simp only [RaftVeil.Lemmas.contains_insert_iff, hj, or_true]

-- GrantVote

prove_veil_invariant_goal GrantVote ElectionSafety using wp by
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal GrantVote OneVotePerTerm using wp by
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal GrantVote VoteTermBound using wp by
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal GrantVote VotesBound using wp by
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal GrantVote VoteRecord using wp by
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal GrantVote GrantsAreVotes using wp by
  try obtain ⟨hES, hOV, hVT, hVB, hVR, hGV, hLQ, -⟩ := hinv
  intro ha hv hc m hm
  rw [RaftVeil.Lemmas.mem_insert] at hm
  rcases hm with rfl | hm
  · subst hv
    cases a
    exact ha
  · exact hGV m hm

prove_veil_invariant_goal GrantVote LeadersHaveQuorum using wp by
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

-- BecomeLeader

prove_veil_invariant_goal BecomeLeader ElectionSafety using wp by
  try obtain ⟨hES, hOV, hVT, hVB, hVR, hGV, hLQ, -⟩ := hinv
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
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeLeader VoteTermBound using wp by
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeLeader VotesBound using wp by
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeLeader VoteRecord using wp by
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeLeader GrantsAreVotes using wp by
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal BecomeLeader LeadersHaveQuorum using wp by
  try obtain ⟨hES, hOV, hVT, hVB, hVR, hGV, hLQ, -⟩ := hinv
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

-- LeaderAppend

prove_veil_invariant_goal LeaderAppend ElectionSafety using wp by
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal LeaderAppend OneVotePerTerm using wp by
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal LeaderAppend VoteTermBound using wp by
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal LeaderAppend VotesBound using wp by
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal LeaderAppend VoteRecord using wp by
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal LeaderAppend GrantsAreVotes using wp by
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal LeaderAppend LeadersHaveQuorum using wp by
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

-- SendAppend

prove_veil_invariant_goal SendAppend ElectionSafety using wp by
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendAppend OneVotePerTerm using wp by
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendAppend VoteTermBound using wp by
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendAppend VotesBound using wp by
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendAppend VoteRecord using wp by
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal SendAppend GrantsAreVotes using wp by
  try obtain ⟨hES, hOV, hVT, hVB, hVR, hGV, hLQ, -⟩ := hinv
  intros
  simp only [RaftVeil.Lemmas.mem_iff, RaftVeil.Lemmas.contains_insert_iff] at *
  repeat' split
  all_goals grind only

prove_veil_invariant_goal SendAppend LeadersHaveQuorum using wp by
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

-- LeaderCommit

prove_veil_invariant_goal LeaderCommit ElectionSafety using wp by
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal LeaderCommit OneVotePerTerm using wp by
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal LeaderCommit VoteTermBound using wp by
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal LeaderCommit VotesBound using wp by
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal LeaderCommit VoteRecord using wp by
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal LeaderCommit GrantsAreVotes using wp by
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal LeaderCommit LeadersHaveQuorum using wp by
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

-- DeleteSuffix

prove_veil_invariant_goal DeleteSuffix ElectionSafety using wp by
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal DeleteSuffix OneVotePerTerm using wp by
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal DeleteSuffix VoteTermBound using wp by
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal DeleteSuffix VotesBound using wp by
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal DeleteSuffix VoteRecord using wp by
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal DeleteSuffix GrantsAreVotes using wp by
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal DeleteSuffix LeadersHaveQuorum using wp by
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

-- StoreEntries

prove_veil_invariant_goal StoreEntries ElectionSafety using wp by
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StoreEntries OneVotePerTerm using wp by
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StoreEntries VoteTermBound using wp by
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StoreEntries VotesBound using wp by
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StoreEntries VoteRecord using wp by
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StoreEntries GrantsAreVotes using wp by
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal StoreEntries LeadersHaveQuorum using wp by
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

-- Ack

prove_veil_invariant_goal Ack ElectionSafety using wp by
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Ack OneVotePerTerm using wp by
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Ack VoteTermBound using wp by
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Ack VotesBound using wp by
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Ack VoteRecord using wp by
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Ack GrantsAreVotes using wp by
  try obtain ⟨hES, hOV, hVT, hVB, hVR, hGV, hLQ, -⟩ := hinv
  intros
  simp only [RaftVeil.Lemmas.mem_iff, RaftVeil.Lemmas.contains_insert_iff] at *
  repeat' split
  all_goals grind only

prove_veil_invariant_goal Ack LeadersHaveQuorum using wp by
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

-- FollowerCommit

prove_veil_invariant_goal FollowerCommit ElectionSafety using wp by
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal FollowerCommit OneVotePerTerm using wp by
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal FollowerCommit VoteTermBound using wp by
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal FollowerCommit VotesBound using wp by
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal FollowerCommit VoteRecord using wp by
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal FollowerCommit GrantsAreVotes using wp by
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal FollowerCommit LeadersHaveQuorum using wp by
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

-- Restart

prove_veil_invariant_goal Restart ElectionSafety using wp by
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Restart OneVotePerTerm using wp by
  try obtain ⟨hES, hOV, hVT, hVB, hVR, hGV, hLQ, -⟩ := hinv
  split
  · exact hOV
  · rename_i hne
    cases hc : st.voteFor i with
    | none => exact absurd hc hne
    | some c =>
      have hrec : ∀ x : Vote server, x ∈ st.votes → x.voter = i → x.term = st.voteTerm i → x.cand = c := by
        intro x hx h1 h2
        have h3 := hVR x hx (by rw [h1]; exact h2)
        rw [h1, hc] at h3
        exact (Option.some.inj h3).symm
      intro a b ha hb hv ht
      rw [RaftVeil.Lemmas.mem_insert] at ha hb
      rcases ha with rfl | ha <;> rcases hb with rfl | hb
      · rfl
      · exact (hrec b hb hv.symm ht.symm).symm
      · exact hrec a ha hv ht
      · exact hOV a b ha hb hv ht

prove_veil_invariant_goal Restart VoteTermBound using wp by
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Restart VotesBound using wp by
  try obtain ⟨hES, hOV, hVT, hVB, hVR, hGV, hLQ, -⟩ := hinv
  intros
  simp only [RaftVeil.Lemmas.mem_iff, RaftVeil.Lemmas.contains_insert_iff] at *
  repeat' split
  all_goals grind only

prove_veil_invariant_goal Restart VoteRecord using wp by
  try obtain ⟨hES, hOV, hVT, hVB, hVR, hGV, hLQ, -⟩ := hinv
  split
  · exact hVR
  · rename_i hne
    intro a ha ht
    rw [RaftVeil.Lemmas.mem_insert] at ha
    rcases ha with rfl | ha
    · cases h : st.voteFor i with
      | none => exact absurd h hne
      | some c => simp
    · exact hVR a ha ht

prove_veil_invariant_goal Restart GrantsAreVotes using wp by
  intros
  try simp only [RaftVeil.Lemmas.mem_insert] at *
  grind only [TSet.contains_insert_self, TSet.contains_insert_other, TSet.empty_contains]

prove_veil_invariant_goal Restart LeadersHaveQuorum using wp by
  try obtain ⟨hES, hOV, hVT, hVB, hVR, hGV, hLQ, -⟩ := hinv
  intros
  repeat' split
  all_goals first
    | (refine IsQuorum.mono _ _ ?_ (hLQ _ ‹_ ∈ st.leaders›)
       intro j hj
       simp [RaftVeil.Lemmas.contains_insert_iff, hj])
    | (intro a ha
       refine IsQuorum.mono _ _ ?_ (hLQ a ha)
       intro j hj
       simp [RaftVeil.Lemmas.contains_insert_iff, hj])
    | exact hLQ

end RaftVeil
