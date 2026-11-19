#!/usr/bin/env python3
"""Replay a recorded stream into a file at a given rate, for testing streamcheck.

    replay.py SRC DST EVENTS_PER_SECOND [--report]

Appends SRC's lines to DST, then creates DST.eof. With --report, prints how
far the checker (DST.progress) is behind the writer, sampled as it goes.
"""
import os
import sys
import time

src, dst, rate = sys.argv[1], sys.argv[2], float(sys.argv[3])
report = "--report" in sys.argv
lines = open(src).readlines()
lags = []
start = time.time()
with open(dst, "a") as f:
    for k, line in enumerate(lines, 1):
        f.write(line)
        f.flush()
        due = start + k / rate
        if due > time.time():
            time.sleep(due - time.time())
        if report and k % 50 == 0:
            try:
                waiting_for = int(open(dst + ".progress").read())
            except (OSError, ValueError):
                waiting_for = 1
            lags.append(k + 1 - waiting_for)   # events written but not yet matched
open(dst + ".eof", "w").close()
if report and lags:
    tail = lags[len(lags) // 4:]
    print(f"replayed {len(lines)} events in {time.time() - start:.1f}s; "
          f"checker behind by max {max(lags)} events overall, max {max(tail)} after warm-up")
