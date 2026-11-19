#!/usr/bin/env python3
"""Print the compose file for a cluster of N nodes.

    compose-nodes.py N < config/docker-compose.yaml > configN/docker-compose.yaml

Repeats the raft3 service and its volume as raft4..raftN. Peers and node URLs
come from PEERS and NODE_URLS (scripts/build-env.sh).
"""
import re
import sys

n = int(sys.argv[1])
s = sys.stdin.read()
block = re.search(r"\n  raft3:\n.*?\n(?=\n  driver:\n)", s, re.S)
vol = "  raft3-data:\n"
assert block and s.count(vol) == 1, "the compose file is not laid out as expected"
more = "".join(block.group(0).replace("raft3", "raft%d" % k) for k in range(4, n + 1))
s = s.replace(block.group(0), block.group(0) + more)
s = s.replace(vol, vol + "".join("  raft%d-data:\n" % k for k in range(4, n + 1)))
sys.stdout.write("# Written by scripts/compose-nodes.py %d from config/docker-compose.yaml. Do not edit.\n" % n + s)
