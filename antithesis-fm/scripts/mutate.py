#!/usr/bin/env python3
"""Make a non-conforming copy of an accepted stream.

    mutate.py MUTATION SRC_STREAM DST_STREAM
    mutate.py list | list-accepted | expect | source MUTATION

Each mutation is a behaviour the model must not allow (scripts/validator-tests.sh).
Prints the index of the first changed event; the check must reject there or later.
Sources: traces/happy, traces/prevote, traces/snap (`mutate.py source MUTATION`).
A few names are hand-written behaviours rather than mutations; `mutate.py expect`
gives the required verdict for each name.
"""
import copy
import json
import sys

NODES = ["raft1", "raft2", "raft3"]


def vote_writes(node, term, cand):
    """The two writes of a vote, in raft's order (patches/README.md, R2)."""
    t = {"node": node, "e": "stable.set", "key": "LastVoteTerm", "value": term}
    c = {"node": node, "e": "stable.set", "key": "LastVoteCand", "value": cand}
    return [c, t]


def find(L, pred, skip=0):
    for k, e in enumerate(L):
        if pred(e):
            if skip == 0:
                return k
            skip -= 1
    sys.exit("no event to mutate")


def other(*used):
    return next(n for n in NODES if n not in used)


def vote_twice(L):
    """A node that has recorded its vote records another candidate in the same term."""
    k = find(L, lambda e: e["e"] == "stable.set" and e["key"] == "LastVoteCand")
    dup = copy.deepcopy(L[k])
    dup["value"] = other(L[k]["node"], L[k]["value"])
    L.insert(k + 1, dup)


def term_decrease(L):
    """A node writes a term lower than the one it has."""
    k = find(L, lambda e: e["e"] == "stable.set" and e["key"] == "CurrentTerm" and e["value"] >= 2, skip=1)
    dup = copy.deepcopy(L[k])
    dup["value"] -= 1
    L.insert(k + 1, dup)


def forged_entry(L):
    """A follower stores an entry with a payload no request carried."""
    k = find(L, lambda e: e["e"] == "log.store" and any(x["type"] == "command" for x in e["entries"])
             and not is_leader_store(L, e), skip=1)
    for x in L[k]["entries"]:
        if x["type"] == "command":
            x["value"] = ("00" if not x["value"].startswith("00") else "ff") + x["value"][2:]


def is_leader_store(L, ev):
    """The store is the leader's own: its entries appear in none of the requests sent before it."""
    k = L.index(ev)
    role = "follower"
    for e in L[:k]:
        if e["node"] == ev["node"] and e["e"] == "role":
            role = e["role"]
    return role == "leader"


def commit_without_quorum(L):
    """A leader sends a commit index that covers entries nobody has acknowledged."""
    k = find(L, lambda e: e["e"] == "rpc.send" and e["kind"] == "append" and e["req"]["entries"], skip=3)
    L[k]["req"]["commit"] = L[k]["req"]["prevLogIndex"] + len(L[k]["req"]["entries"])


def lost_write(L):
    """A follower acknowledges entries whose store was never reported."""
    k = find(L, lambda e: e["e"] == "log.store" and e["first"] > 1 and not is_leader_store(L, e), skip=2)
    del L[k]


def stale_leader_append(L):
    """A leader stores an entry stamped with an older term."""
    k = find(L, lambda e: e["e"] == "log.store" and is_leader_store(L, e), skip=2)
    L[k]["entries"][0]["term"] -= 1


def follower_commits_ahead(L):
    """A follower commits past the commit index its leader sent."""
    k = find(L, lambda e: e["e"] == "rpc.reply" and e["kind"] == "append" and e["resp"]["success"]
             and e["commit"] > 0 and e["commit"] == e["req"]["commit"], skip=2)
    L[k]["commit"] += 1


def second_leader(L):
    """A second node becomes leader in a term that has one."""
    k = find(L, lambda e: e["e"] == "role" and e["role"] == "leader")
    dup = copy.deepcopy(L[k])
    dup["node"] = other(L[k]["node"])
    L.insert(k + 1, dup)


def ungranted_vote(L):
    """A node reports granting its vote to a candidate it did not record."""
    k = find(L, lambda e: e["e"] == "rpc.reply" and e["kind"] == "vote" and e["resp"]["granted"])
    L[k]["src"] = other(L[k]["node"], L[k]["src"])


def send_by_follower(L):
    """A node that is not the leader sends entries."""
    k = find(L, lambda e: e["e"] == "rpc.send" and e["kind"] == "append" and e["req"]["entries"], skip=2)
    dup = copy.deepcopy(L[k])
    dup["node"], dup["peer"] = L[k]["peer"], L[k]["node"]
    L.insert(k + 1, dup)


def send_not_from_leader_log(L):
    """A leader sends an entry that its log as leader of that term never held."""
    k = find(L, lambda e: e["e"] == "rpc.send" and e["kind"] == "append" and e["req"]["entries"], skip=2)
    L[k]["req"]["entries"][-1]["term"] -= 1


def reply_never_sent(L):
    """A caller receives a successful reply that its peer never gave."""
    k = find(L, lambda e: e["e"] == "rpc.return" and e["kind"] == "append" and e["resp"]["success"]
             and e["req"]["entries"], skip=2)
    L[k]["req"]["entries"].append(copy.deepcopy(L[k]["req"]["entries"][-1]))


def same_process(a, b):
    return a["node"] == b["node"] and a["boot"] == b["boot"]


def apply_wrong_entry(L):
    """A node hands its state machine a command that its log does not hold at that index."""
    k = find(L, lambda e: e["e"] == "fsm.apply", skip=2)
    v = L[k]["entry"]["value"]
    L[k]["entry"]["value"] = ("00" if not v.startswith("00") else "ff") + v[2:]


def apply_skips_command(L):
    """A node hands its state machine a command without the command before it (patches/README.md, R3)."""
    applies = [k for k, e in enumerate(L) if e["e"] == "fsm.apply"]
    for k in applies[2:]:
        if any(same_process(L[k], L[j]) for j in applies if j > k):
            del L[k]
            return
    sys.exit("no event to mutate")


def apply_beyond_commit(L):
    """A node hands its state machine an entry as soon as it has stored it, before it is committed."""
    applies = [k for k, e in enumerate(L) if e["e"] == "fsm.apply"]
    for k in applies[2:]:
        a = L[k]
        # The write that stored the entry, with every earlier apply of the node before it.
        earlier = [j for j in applies if j < k and same_process(a, L[j])]
        for j in range(k - 1, (earlier[-1] if earlier else 0), -1):
            w = L[j]
            if w["e"] == "log.store" and same_process(a, w) and w["first"] <= a["index"] < w["first"] + len(w["entries"]):
                moved = copy.deepcopy(a)
                moved["commit"] = a["index"] - 1
                del L[k]
                L.insert(j + 1, moved)
                return
    sys.exit("no event to mutate")


def late_request(L, acked):
    """Hand-written continuation after the first election: term-2 leader a stores and sends an
    entry; b stores it, wins term 3 with a's vote and commits it and one of its own; a follows;
    c stays in term 2. Then a sends c a term-2 request carrying the commit. Valid iff b and c
    acknowledged the entry in term 2 (acked), so that a committed it as leader."""
    k = find(L, lambda e: e["e"] == "role" and e["role"] == "leader")
    a = L[k]["node"]
    b, c = [n for n in NODES if n != a]
    boot = {n: next(e["boot"] for e in L if e["node"] == n) for n in NODES}
    del L[k + 1:]
    e2 = {"term": 2, "type": "noop", "value": ""}
    e3 = {"term": 3, "type": "noop", "value": ""}

    def req(term, prev, prev_term, entries, commit):
        return {"term": term, "prevLogIndex": prev, "prevLogTerm": prev_term, "entries": entries, "commit": commit}

    def ev(node, e, **kv):
        L.append(dict(kv, node=node, e=e, boot=boot[node], k=0))

    def cast(node, term, cand):
        for w in vote_writes(node, term, cand):
            L.append(dict(w, boot=boot[node], k=0))

    def exchange(src, dst, r, commit, store=None, reply=True):
        ok = {"term": r["term"], "success": True, "lastLog": r["prevLogIndex"] + len(r["entries"])}
        ev(src, "rpc.send", kind="append", peer=dst, req=r)
        ev(dst, "rpc.recv", kind="append", src=src, req=r)
        if store:
            ev(dst, "log.store", first=r["prevLogIndex"] + 1, entries=r["entries"])
        if reply:
            ev(dst, "rpc.reply", kind="append", src=src, req=r, resp=ok, commit=commit)
            ev(src, "rpc.return", kind="append", peer=dst, req=r, resp=ok)

    ev(a, "log.store", first=2, entries=[e2])
    first = req(2, 1, 1, [e2], 0)
    exchange(a, b, first, 0, store=True, reply=acked)
    exchange(a, c, first, 0, store=True, reply=acked)
    vote = {"term": 3, "lastLogIndex": 2, "lastLogTerm": 2}
    ev(b, "role", role="candidate")
    ev(b, "stable.set", key="CurrentTerm", value=3)
    cast(b, 3, b)
    ev(b, "rpc.send", kind="vote", peer=a, req=vote)
    ev(a, "stable.set", key="CurrentTerm", value=3)
    ev(a, "role", role="follower")
    cast(a, 3, b)
    ev(a, "rpc.reply", kind="vote", src=b, req=vote, resp={"term": 3, "granted": True}, commit=0)
    ev(b, "rpc.return", kind="vote", peer=a, req=vote, resp={"term": 3, "granted": True})
    ev(b, "role", role="leader")
    ev(b, "log.store", first=3, entries=[e3])
    exchange(b, a, req(3, 2, 2, [e3], 0), 0, store=True)
    exchange(b, a, req(3, 3, 3, [], 3), 3)
    exchange(a, c, req(2, 2, 2, [], 2), 2)


def stale_commit_request(L):
    """A deposed leader sends a request of its old term with a commit index it learned from a later leader."""
    late_request(L, acked=False)


def late_leader_commit(L):
    """A deposed leader's request of its old term shows a commit it made as that leader, after
    its commit index has moved further under a later leader."""
    late_request(L, acked=True)


def torn_vote(L):
    """Hand-written torn vote record (patches/README.md, R2): b votes for c in term 2; a wins
    term 3 and commits an entry with b; in term 4 b is killed after writing only the candidate
    of its own vote, so its record reads (term 2, b); after restart it grants c term 4 and c
    leads without the committed entry."""
    k = find(L, lambda e: e["e"] == "role")
    a, b, c = "raft1", "raft2", "raft3"
    boot = {n: next(e["boot"] for e in L if e["node"] == n) for n in NODES}
    del L[k:]
    e3 = {"term": 3, "type": "noop", "value": ""}

    def ev(node, e, **kv):
        L.append(dict(kv, node=node, e=e, boot=boot[node], k=0))

    def vote(node, term, cand, only_first=False):
        for w in vote_writes(node, term, cand)[:1 if only_first else 2]:
            L.append(dict(w, boot=boot[node], k=0))

    def ask(cand, voter, term, adopt=True):
        r = {"term": term, "lastLogIndex": 1, "lastLogTerm": 1}
        ev(cand, "rpc.send", kind="vote", peer=voter, req=r)
        if adopt:
            ev(voter, "stable.set", key="CurrentTerm", value=term)
            ev(voter, "role", role="follower")
            vote(voter, term, cand)
        ev(voter, "rpc.reply", kind="vote", src=cand, req=r, resp={"term": term, "granted": True}, commit=0)
        ev(cand, "rpc.return", kind="vote", peer=voter, req=r, resp={"term": term, "granted": True})

    def exchange(src, dst, r, commit, store=False, adopt=None):
        ok = {"term": r["term"], "success": True, "lastLog": r["prevLogIndex"] + len(r["entries"])}
        ev(src, "rpc.send", kind="append", peer=dst, req=r)
        ev(dst, "rpc.recv", kind="append", src=src, req=r)
        if adopt:
            ev(dst, "stable.set", key="CurrentTerm", value=adopt)
        if store:
            ev(dst, "log.store", first=r["prevLogIndex"] + 1, entries=r["entries"])
        ev(dst, "rpc.reply", kind="append", src=src, req=r, resp=ok, commit=commit)
        ev(src, "rpc.return", kind="append", peer=dst, req=r, resp=ok)

    # Term 2: c is a candidate and b votes for it; c does not get to lead.
    ev(c, "role", role="candidate")
    ev(c, "stable.set", key="CurrentTerm", value=2)
    vote(c, 2, c)
    ask(c, b, 2)
    # Term 3: a wins with c's vote and commits an entry with b.
    ev(a, "role", role="candidate")
    ev(a, "stable.set", key="CurrentTerm", value=2)
    ev(a, "stable.set", key="CurrentTerm", value=3)
    vote(a, 3, a)
    ask(a, c, 3)
    ev(a, "role", role="leader")
    ev(a, "log.store", first=2, entries=[e3])
    exchange(a, b, {"term": 3, "prevLogIndex": 1, "prevLogTerm": 1, "entries": [e3], "commit": 0}, 0, store=True, adopt=3)
    exchange(a, b, {"term": 3, "prevLogIndex": 2, "prevLogTerm": 3, "entries": [], "commit": 2}, 2)
    # Term 4: c asks for votes. b starts an election too and is killed in the middle of
    # writing its vote for itself.
    ev(c, "role", role="candidate")
    ev(c, "stable.set", key="CurrentTerm", value=4)
    vote(c, 4, c)
    ev(b, "role", role="candidate")
    ev(b, "stable.set", key="CurrentTerm", value=4)
    vote(b, 4, b, only_first=True)
    boot[b] = str(int(boot[b]) + 1)
    ev(b, "boot", term=4, voteTerm=2, voteFor=b, lastIndex=2, lastTerm=3)
    # b grants c its vote for term 4, and c takes the leadership.
    ask(c, b, 4, adopt=False)
    ev(c, "role", role="leader")


def prevote_when_off(L):
    """A candidate asks for a pre-vote in a build that has none."""
    k = find(L, lambda e: e["e"] == "rpc.send" and e["kind"] == "vote")
    dup = copy.deepcopy(L[k])
    dup["kind"] = "prevote"
    dup["req"] = {f: dup["req"][f] for f in ("term", "lastLogIndex", "lastLogTerm")}
    L.insert(k, dup)


def timeoutnow_from_follower(L):
    """A node that has never led tells another to start an election."""
    k = find(L, lambda e: e["e"] == "role" and e["role"] == "leader")
    a = L[k]["node"]
    b, c = [n for n in NODES if n != a]
    dup = {"node": b, "e": "rpc.send", "kind": "timeoutnow", "peer": c, "req": {},
           "boot": next(e["boot"] for e in L if e["node"] == b), "k": 0}
    L.insert(k + 1, dup)


# Mutations of traces/prevote (pre-votes and leadership transfers).

def elections(L):
    """(k, by order) for each election started: the write of the next term by a candidate."""
    role, term, order, out = {}, {}, set(), []
    for k, e in enumerate(L):
        n = e["node"]
        if e["e"] == "boot":
            role[n], term[n] = "follower", e["term"]
            order.discard(n)
        elif e["e"] == "role":
            role[n] = e["role"]
            if e["role"] != "candidate":
                order.discard(n)
        elif e["e"] == "rpc.recv" and e["kind"] == "timeoutnow":
            order.add(n)
        elif e["e"] == "stable.set" and e["key"] == "CurrentTerm":
            if role.get(n) == "candidate" and e["value"] == term.get(n, 1) + 1:
                out.append((k, n in order))
                order.discard(n)
            term[n] = e["value"]
    return out


def election_without_prevotes(L):
    """A candidate starts an election although nobody has said it would vote for it."""
    k = next((k for k, by_order in elections(L) if not by_order), None)
    if k is None:
        sys.exit("no event to mutate")
    cand, term = L[k]["node"], L[k]["value"]
    grants = [j for j in range(k) if L[j]["e"] == "rpc.reply" and L[j]["kind"] == "prevote"
              and L[j]["src"] == cand and L[j]["req"]["term"] == term and L[j]["resp"]["granted"]]
    for j in reversed(grants):
        del L[j]


def election_without_order(L):
    """A node starts an election without pre-votes and without a leader's order."""
    k = next((k for k, by_order in elections(L) if by_order), None)
    if k is None:
        sys.exit("no event to mutate")
    n = L[k]["node"]
    j = max(j for j in range(k) if L[j]["node"] == n and L[j]["e"] == "rpc.recv" and L[j]["kind"] == "timeoutnow")
    del L[j]


def prevote_for_shorter_log(L):
    """A node says it would vote for a candidate whose log is behind its own."""
    k = find(L, lambda e: e["e"] == "rpc.reply" and e["kind"] == "prevote" and e["resp"]["granted"])
    L[k]["req"]["lastLogIndex"], L[k]["req"]["lastLogTerm"] = 0, 0


def prevote_for_past_term(L):
    """A node says it would vote in a term it has passed."""
    k = find(L, lambda e: e["e"] == "rpc.reply" and e["kind"] == "prevote" and e["resp"]["granted"])
    L[k]["req"]["term"] = 0


def late_prevote_after_order(L):
    """A node that was asking for pre-votes is told by a leader to start an election, and
    a request of the attempt it gave up is sent only then, before it starts the election.
    The election is by order and needs no pre-vote: the stream is one the model allows."""
    k = next((k for k, by_order in elections(L) if by_order), None)
    if k is None:
        sys.exit("no event to mutate")
    n = L[k]["node"]
    v = next(e for e in L[k:] if e["node"] == n and e["e"] == "rpc.send" and e["kind"] == "vote")
    req = {f: v["req"][f] for f in ("term", "lastLogIndex", "lastLogTerm")}
    L.insert(k, {"node": n, "e": "rpc.send", "kind": "prevote", "peer": v["peer"], "req": req,
                 "boot": L[k]["boot"], "k": 0})


# ---- snapshots (mutations of traces/snap)

def cut(L, k, more=400):
    """Keep the stream up to a little after event k: the streams with snapshots are long."""
    del L[k + more:]


def is_install(e):
    return e["e"] == "snap.store" and e["kind"] == "install"


def snapshot_of_uncommitted(L):
    """A node takes a snapshot of more than it has committed."""
    k = find(L, lambda e: e["e"] == "snap.store" and e["kind"] == "take", skip=2)
    L[k]["index"] = L[k]["commit"] + 3
    cut(L, k)


def compact_past_snapshot(L):
    """A node deletes an entry from the front of its log that its snapshot does not cover."""
    k = find(L, lambda e: e["e"] == "log.delete" and e["from"] == e.get("first") and "commit" not in e, skip=1)
    L[k]["to"] += 1
    cut(L, k)


def install_other_snapshot(L):
    """A node stores, as the snapshot it was sent, one of another term."""
    k = find(L, is_install)
    L[k]["term"] += 1
    cut(L, k)


def ack_without_install(L):
    """A node says it has installed a snapshot that it did not store."""
    k = find(L, is_install)
    del L[k]
    cut(L, k)


def snapshot_from_follower(L):
    """A node that did not lead the request's term sends a snapshot."""
    k = find(L, lambda e: e["e"] == "rpc.send" and e["kind"] == "snapshot")
    L[k]["node"] = other(L[k]["node"], L[k]["peer"])
    cut(L, k)


def stale_install(L):
    """A node stores again a snapshot it already has, sent a second time (patches/README.md, R4).
    With the patches the node answers without storing it."""
    k = find(L, is_install)
    node = L[k]["node"]
    recv = max(j for j in range(k) if L[j]["node"] == node and L[j]["e"] == "rpc.recv" and L[j]["kind"] == "snapshot")
    reply = next(j for j in range(k, len(L)) if L[j]["node"] == node and L[j]["e"] == "rpc.reply" and L[j]["kind"] == "snapshot")
    send = max(j for j in range(recv) if L[j]["e"] == "rpc.send" and L[j]["kind"] == "snapshot"
               and L[j]["peer"] == node and L[j]["req"] == L[recv]["req"])
    again = [copy.deepcopy(L[j]) for j in (send, recv, k, reply)]
    L[reply + 1:reply + 1] = again
    cut(L, reply + 1, more=60)


SNAPSHOT_MUTATIONS = {f.__name__.replace("_", "-"): f for f in (
    snapshot_of_uncommitted, compact_past_snapshot, install_other_snapshot, ack_without_install,
    snapshot_from_follower, stale_install)}

MUTATIONS = {f.__name__.replace("_", "-"): f for f in (
    vote_twice, term_decrease, forged_entry, commit_without_quorum, lost_write,
    stale_leader_append, follower_commits_ahead, second_leader, ungranted_vote,
    send_by_follower, send_not_from_leader_log, reply_never_sent,
    apply_wrong_entry, apply_skips_command, apply_beyond_commit, stale_commit_request,
    prevote_when_off, timeoutnow_from_follower)}
# Mutations of traces/prevote.
PREVOTE_MUTATIONS = {f.__name__.replace("_", "-"): f for f in (
    election_without_prevotes, election_without_order, prevote_for_shorter_log, prevote_for_past_term)}
ACCEPTED = {f.__name__.replace("_", "-"): f for f in (late_leader_commit, late_prevote_after_order)}
# Names whose source is traces/prevote.
PREVOTE_SOURCE = set(PREVOTE_MUTATIONS) | {"late-prevote-after-order"}
WRITTEN = {f.__name__.replace("_", "-"): f for f in (torn_vote,)}

# What the check must say: "reject", or "accept" and the notes it must make.
EXPECT = dict({m: "reject" for m in list(MUTATIONS) + list(PREVOTE_MUTATIONS) + list(SNAPSHOT_MUTATIONS)},
              **{"late-leader-commit": "accept", "torn-vote": "reject",
                 "late-prevote-after-order": "accept P-prevote-election T-transfer-election"})

if __name__ == "__main__":
    if len(sys.argv) == 2 and sys.argv[1] == "list":
        print(" ".join(list(MUTATIONS) + list(PREVOTE_MUTATIONS) + list(SNAPSHOT_MUTATIONS)))
        sys.exit(0)
    if len(sys.argv) == 2 and sys.argv[1] == "list-accepted":
        print(" ".join(ACCEPTED))
        sys.exit(0)
    if len(sys.argv) == 2 and sys.argv[1] == "expect":
        for name, what in EXPECT.items():
            print(name, what)
        sys.exit(0)
    if len(sys.argv) == 3 and sys.argv[1] == "source":
        print("snap" if sys.argv[2] in SNAPSHOT_MUTATIONS else "prevote" if sys.argv[2] in PREVOTE_SOURCE else "happy")
        sys.exit(0)
    MUTATIONS.update(PREVOTE_MUTATIONS)
    MUTATIONS.update(SNAPSHOT_MUTATIONS)
    MUTATIONS.update(ACCEPTED)
    MUTATIONS.update(WRITTEN)
    if len(sys.argv) != 4 or sys.argv[1] not in MUTATIONS:
        sys.exit(__doc__ + "\nmutations: " + ", ".join(MUTATIONS))
    L = [json.loads(l) for l in open(sys.argv[2]) if l.strip()]
    before = [json.dumps(e, sort_keys=True) for e in L]
    MUTATIONS[sys.argv[1]](L)
    for n, e in enumerate(L, 1):     # renumber k
        if "k" in e:
            e["k"] = n
    after = [json.dumps(e, sort_keys=True) for e in L]
    with open(sys.argv[3], "w") as f:
        for line in after:
            f.write(line + "\n")
    print(next((k + 1 for k, (x, y) in enumerate(zip(before, after)) if x != y), min(len(before), len(after)) + 1))
