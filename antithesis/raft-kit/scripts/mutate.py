#!/usr/bin/env python3
"""Make a non-conforming copy of an accepted raft-kit stream.

    mutate.py MUTATION SRC_STREAM DST_STREAM

Each mutation is a behaviour the model must not allow; the stream check is
trusted only if it rejects every one (scripts/validator-tests.sh). Prints the
index of the first event that differs from the source: the check must reject
there or later, never before.
"""
import copy
import json
import sys

NODES = ["raft1", "raft2", "raft3"]


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


MUTATIONS = {f.__name__.replace("_", "-"): f for f in (
    vote_twice, term_decrease, forged_entry, commit_without_quorum, lost_write,
    stale_leader_append, follower_commits_ahead, second_leader, ungranted_vote,
    send_by_follower, send_not_from_leader_log, reply_never_sent)}

if __name__ == "__main__":
    if len(sys.argv) == 2 and sys.argv[1] == "list":
        print(" ".join(MUTATIONS))
        sys.exit(0)
    if len(sys.argv) != 4 or sys.argv[1] not in MUTATIONS:
        sys.exit(__doc__ + "\nmutations: " + ", ".join(MUTATIONS))
    L = [json.loads(l) for l in open(sys.argv[2]) if l.strip()]
    before = [json.dumps(e, sort_keys=True) for e in L]
    MUTATIONS[sys.argv[1]](L)
    after = [json.dumps(e, sort_keys=True) for e in L]
    with open(sys.argv[3], "w") as f:
        for line in after:
            f.write(line + "\n")
    print(next((k + 1 for k, (x, y) in enumerate(zip(before, after)) if x != y), min(len(before), len(after)) + 1))
