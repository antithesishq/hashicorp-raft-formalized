#!/usr/bin/env python3
"""What do recorded raft-kit streams exercise?

    scripts/coverage.py RUN_DIR...        (each holding kit/stream.ndjson)

Counts events by kind and the branches of the binding that matter. A row
with 0 means conformance on these runs says nothing about that branch.
"""
import collections
import glob
import json
import os
import sys

c = collections.Counter()
ROWS = [
    "boot: first", "boot: restart, last write had happened", "boot: restart, last write taken back",
    "boot: restart, nothing pending",
    "role: candidate", "role: leader", "role: follower", "role: shutdown",
    "stable.set: election start", "stable.set: adopt a later term", "stable.set: same term again",
    "stable.set: vote term", "stable.set: vote for self", "stable.set: vote for another",
    "log.store: bootstrap", "log.store: leader", "log.store: follower", "log.delete",
    "rpc.send: vote", "rpc.send: heartbeat", "rpc.send: append", "rpc.send: append, several entries",
    "rpc.send: append, commit index moved",
    "rpc.reply: vote granted", "rpc.reply: vote refused", "rpc.reply: append success",
    "rpc.reply: append success, commit moved", "rpc.reply: append refused",
    "rpc.reply: commit moved without the request explaining it",
    "rpc.return: vote", "rpc.return: append", "rpc.return: heartbeat", "rpc.fail",
]
for run in sys.argv[1:]:
    paths = glob.glob(os.path.join(run, "kit", "stream.ndjson")) or ([run] if os.path.isfile(run) else [])
    for path in paths:
        st = collections.defaultdict(lambda: dict(term=0, vt=0, vf="", last=0, lastTerm=0, role="follower",
                                                  commit=0, boots=0, pre=None))
        for line in open(path):
            ev = json.loads(line)
            n, e = ev["node"], ev["e"]
            s = st[n]
            if e == "boot":
                s["boots"] += 1
                rec = (ev["term"], ev["voteTerm"], ev["voteFor"], ev["lastIndex"])
                cur = (s["term"], s["vt"], s["vf"], s["last"])
                if s["boots"] == 1:
                    c["boot: first"] += 1
                elif s["pre"] is None:
                    c["boot: restart, nothing pending"] += 1
                elif rec == cur:
                    c["boot: restart, last write had happened"] += 1
                else:
                    c["boot: restart, last write taken back"] += 1
                s.update(term=ev["term"], vt=ev["voteTerm"], vf=ev["voteFor"], last=ev["lastIndex"],
                         role="follower", commit=0, pre=None)
            elif e == "role":
                c["role: " + ev["role"]] += 1
                if ev["role"] != "shutdown":
                    s["role"] = ev["role"]
            elif e == "stable.set":
                pre = (s["term"], s["vt"], s["vf"], s["last"])
                if ev["key"] == "CurrentTerm":
                    if ev["value"] == s["term"]:
                        c["stable.set: same term again"] += 1
                    elif s["role"] == "candidate" and ev["value"] == s["term"] + 1:
                        c["stable.set: election start"] += 1
                    else:
                        c["stable.set: adopt a later term"] += 1
                    s["term"] = ev["value"]
                elif ev["key"] == "LastVoteTerm":
                    c["stable.set: vote term"] += 1
                    s["vt"] = ev["value"]
                else:
                    c["stable.set: vote for " + ("self" if ev["value"] == n else "another")] += 1
                    s["vf"] = ev["value"]
                s["pre"] = pre
            elif e == "log.store":
                kind = "bootstrap" if ev["first"] == 1 and s["last"] == 0 else ("leader" if s["role"] == "leader" else "follower")
                c["log.store: " + kind] += 1
                s["pre"] = (s["term"], s["vt"], s["vf"], s["last"])
                s["last"] = ev["first"] + len(ev["entries"]) - 1
            elif e == "log.delete":
                c["log.delete"] += 1
                s["pre"] = (s["term"], s["vt"], s["vf"], s["last"])
                s["last"] = ev["from"] - 1
            elif e == "rpc.send":
                c["rpc.send: " + ev["kind"]] += 1
                if ev["kind"] == "append":
                    if len(ev["req"]["entries"]) > 1:
                        c["rpc.send: append, several entries"] += 1
                    if ev["req"]["commit"] > s["commit"]:
                        c["rpc.send: append, commit index moved"] += 1
                        s["commit"] = ev["req"]["commit"]
            elif e == "rpc.reply":
                moved = ev["commit"] > s["commit"]
                if ev["kind"] == "vote":
                    c["rpc.reply: vote " + ("granted" if ev["resp"]["granted"] else "refused")] += 1
                    explained = False
                else:
                    ok = ev["resp"]["success"]
                    c["rpc.reply: append " + ("success" if ok else "refused")] += 1
                    explained = ok and ev["commit"] <= ev["req"]["commit"]
                    if ok and moved and explained:
                        c["rpc.reply: append success, commit moved"] += 1
                if moved and not explained:
                    c["rpc.reply: commit moved without the request explaining it"] += 1
                s["commit"] = max(s["commit"], ev["commit"])
            elif e == "rpc.return":
                c["rpc.return: " + ev["kind"]] += 1
            elif e == "rpc.fail":
                c["rpc.fail"] += 1
            else:
                c[e + "  (unlisted)"] += 1
for r in ROWS:
    print(f"{c[r]:8d}  {r}")
for r in sorted(set(c) - set(ROWS)):
    print(f"{c[r]:8d}  {r}")
