#!/usr/bin/env bash
# Runs Veil's model checker on veil/RaftVeil.lean at one bound and prints the
# number of distinct states, to compare with TLC on spec/MCCount<MaxMsgs>.cfg
# (scripts/mc.sh MCCount<MaxMsgs>.cfg 600). The proofs are left out of the run.
#
#   scripts/veil-count.sh MAXMSGS [LIMIT_SECONDS]     e.g. 2 -> 73,512; 3 -> 277,792
set -euo pipefail
here=$(cd "$(dirname "$0")/.." && pwd)
m=${1:?MaxMsgs}; limit=${2:-900}
cd "$here/veil"
[ -f "$HOME/.elan/env" ] && . "$HOME/.elan/env"
tmp=Count$m.lean
trap 'rm -f "$tmp"' EXIT
python3 - "$m" > "$tmp" <<'PY'
import sys
s = open('RaftVeil.lean').read()
s = s[:s.index('-- Proofs.')].rsplit('\n', 2)[0]
s = (s.replace('-- #model_check compiled', '#model_check compiled')
      .replace('--   { server := Fin 3', '  { server := Fin 3')
      .replace('--     VoteSet', '    VoteSet')
      .replace('--   { MaxTerm := 2, MaxLog := 2, MaxBatch := 1, MaxMsgs := 2 }',
               '  { MaxTerm := 2, MaxLog := 2, MaxBatch := 1, MaxMsgs := %s }' % sys.argv[1]))
assert '\n#model_check compiled' in s
print(s + '\nend RaftVeil')
PY
timeout "$limit" lake env lean "$tmp" | grep -E 'explored|Violation' || { echo "no verdict within ${limit}s"; exit 2; }
