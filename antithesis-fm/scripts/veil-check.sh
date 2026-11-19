#!/usr/bin/env bash
# Checks the proofs of veil/RaftVeil.lean in parallel: per-action proof sections are split
# into JOBS files, each with a copy of the model (same proofs as `lake build`, faster).
#
#   scripts/veil-check.sh [JOBS] [LIMIT_SECONDS_PER_FILE]   default: cores/memory; 1800 s
# Env: PER_ACTION=1 one file per action; ACTIONS="Apply Restart" only these actions
#      (`initializer` is the initial state); OUT=dir keeps each file, Lean's output and
#      the failed goals.
#
# Prints one line per file (ok/FAIL/TIMEOUT, time, first failed goal) and a total.
# Exits 0 only if every file is ok (no error, no `sorry`, no timeout).
set -uo pipefail
here=$(cd "$(dirname "$0")/.." && pwd)
limit=${2:-1800}
# Default: min(cores, memory / 2.5 GB).
if [ -n "${1:-}" ]; then jobs=$1; else
  mem=$(awk '/MemAvailable/ {print int($2 / 1048576 / 2.5)}' /proc/meminfo)
  jobs=$(nproc); [ "$mem" -lt "$jobs" ] && jobs=$mem; [ "$jobs" -lt 1 ] && jobs=1
fi
cd "$here/veil"
# Build Veil and its dependencies (slow the first time).
lake build Veil > /dev/null
[ -f "$HOME/.elan/env" ] && . "$HOME/.elan/env"
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"; rm -f "$here"/veil/Check_*.lean' EXIT
mkdir -p "$here/runs"; times="$here/runs/veil-check.times"
python3 - "$tmp" "$jobs" "${PER_ACTION:-}" "${ACTIONS:-}" "$times" <<'PY'
import re, sys
s = open('RaftVeil.lean').read()
i = s.index('-- Proofs.')
head, proofs = s[:i].rsplit('\n', 2)[0], s[i:]
names = re.findall(r'\n-- (\w+)\n\nprove_veil_invariant_goal', proofs)
everything = len(names)
only = sys.argv[4].split()
if only:
    missing = [a for a in only if a not in names]
    assert not missing, 'no proof section for: %s (sections: %s)' % (' '.join(missing), ' '.join(names))
    names = [a for a in names if a in only]
jobs = int(sys.argv[2])
n = len(names) if sys.argv[3] else min(jobs, len(names))
groups = [[] for _ in range(n)]
total = 0
for k, a in enumerate(names):
    body = re.search(r'\n-- %s\n\n(.*?)(?=\n-- \w+\n\nprove_veil_invariant_goal|\nend RaftVeil)' % a, proofs, re.S).group(1)
    total += body.count('prove_veil_invariant_goal ')
    groups[k % n].append((a, body))
assert only or total == proofs.count('\nprove_veil_invariant_goal '), 'a proof is outside every action section'
# Spare processes split the slowest actions in two, by runs/veil-check.times
# or else by the action's length in the model.
import os
times = {}
if os.path.exists(sys.argv[5]):
    for line in open(sys.argv[5]):
        a, t = line.split()
        times[a.split('_')[0]] = times.get(a.split('_')[0], 0) + int(t)
def weight(a):
    m = re.search(r'\naction %s\b.*?\n}' % a, head, re.S)
    return (times.get(a, 0), len(m.group(0)) if m else 0)
spare = min(jobs - n, n) if n == len(names) else 0
for a in sorted(names, key=weight, reverse=True)[:spare]:
    k = next(k for k, g in enumerate(groups) if g[0][0] == a)
    goals = re.split(r'(?m)^(?=prove_veil_invariant_goal )', groups[k][0][1])
    goals = [goals[0] + goals[1]] + goals[2:]
    h = len(goals) // 2
    groups[k] = [(a, ''.join(goals[:h]))]
    groups.append([(a + '_2', ''.join(goals[h:]))])
n = len(groups)
labels = []
for k, g in enumerate(groups):
    label = g[0][0] if len(g) == 1 else 'g%d' % (k + 1)
    labels.append(label)
    open('Check_%s.lean' % label, 'w').write(head + '\n' + '\n\n'.join(b for _, b in g) + '\n\nend RaftVeil\n')
    open('%s/%s.sections' % (sys.argv[1], label), 'w').write(' '.join(a for a, _ in g))
open(sys.argv[1] + '/names', 'w').write('\n'.join(labels) + '\n')
print('%d proofs of %d actions in %d files%s' % (total, len(names), n, ' (of %d actions in all)' % everything if only else ''))
PY
one() {
  a=$1; s=$(date +%s)
  timeout "$limit" lake env lean "Check_$a.lean" > "$tmp/$a.out" 2>&1; rc=$?
  e=$(( $(date +%s) - s ))
  if [ $rc -eq 124 ]; then st=TIMEOUT
  elif [ $rc -ne 0 ] || grep -q ': error' "$tmp/$a.out" || grep -q 'sorry' "$tmp/$a.out"; then st=FAIL
  else st=ok; fi
  why=""; : > "$tmp/$a.failed"
  if [ $st = FAIL ]; then
    ln=$(grep -m1 ': error' "$tmp/$a.out" | cut -d: -f2)
    [ -n "$ln" ] && why=$(head -n "$ln" "Check_$a.lean" | grep '^prove_veil_invariant_goal' | tail -1 | cut -d' ' -f2,3)
    why="first failure: ${why:-?}: $(grep -m1 ': error' "$tmp/$a.out" | cut -d: -f4- | cut -c1-80)"
    # Every goal that failed, for OUT.
    grep ': error' "$tmp/$a.out" | cut -d: -f2 | sort -un | while read -r l; do
      head -n "$l" "Check_$a.lean" | grep '^prove_veil_invariant_goal' | tail -1 | cut -d' ' -f2,3
    done | sort -u > "$tmp/$a.failed"
  fi
  if [ -n "${OUT:-}" ]; then mkdir -p "$OUT"; cp "$tmp/$a.out" "$OUT/"; cp "$tmp/$a.failed" "$OUT/"; cp "Check_$a.lean" "$OUT/"; fi
  [ $st = ok ] && echo "$a $e" >> "$tmp/times"
  echo "$st $a ${e}s ($(cat "$tmp/$a.sections")) $why"
}
export -f one; export limit tmp OUT
xargs -P "$jobs" -I{} bash -c 'one {}' < "$tmp/names" | tee "$tmp/all"
# Save per-file times of a full run for the next split.
[ -z "${ACTIONS:-}" ] && cp "$tmp/times" "$times" 2>/dev/null
bad=$(grep -vc '^ok ' "$tmp/all")
echo "$(grep -c '^ok ' "$tmp/all") of $(wc -l < "$tmp/names") files ok"
[ "$bad" -eq 0 ]
