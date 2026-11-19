#!/usr/bin/env bash
# Runs Veil's model checker on veil/RaftVeil.lean (without proofs and PROOF-ONLY
# invariants) at one bound and prints the distinct-state count, to compare with TLC on
# spec/MCCountPV<MaxMsgs>.cfg, or with PREVOTE=0 on spec/MCCount<MaxMsgs>.cfg.
#
#   scripts/veil-count.sh MAXMSGS [LIMIT_SECONDS]              e.g. 4 -> 17,704; 5 -> 113,968
#   PREVOTE=0 scripts/veil-count.sh MAXMSGS [LIMIT_SECONDS]    e.g. 2 -> 6,488; 3 -> 30,880
#   SNAPSHOTS=1 MAXLOG=3 PREVOTE=0 scripts/veil-count.sh ...   snapshots, logs up to 3 entries
set -euo pipefail
here=$(cd "$(dirname "$0")/.." && pwd)
m=${1:?MaxMsgs}; limit=${2:-900}
cd "$here/veil"
# Build Veil and its dependencies (slow the first time).
lake build Veil > /dev/null
[ -f "$HOME/.elan/env" ] && . "$HOME/.elan/env"
tmp=Count$m-$$.lean
trap 'rm -f "$tmp"' EXIT
pv=true; [ "${PREVOTE:-1}" = 0 ] && pv=false
sn=false; [ "${SNAPSHOTS:-0}" = 1 ] && sn=true
python3 - "$m" "$pv" "$sn" "${MAXLOG:-2}" > "$tmp" <<'PY'
import sys
s = open('RaftVeil.lean').read()
s = s[:s.index('-- Lemmas.')].rsplit('\n', 2)[0]             # the model and its invariants
# Bound quantifiers over terms to MaxTerm + 1.
if '-- PROOF-ONLY BEGIN' in s:                                 # invariants it cannot evaluate
    a, b = s.index('-- PROOF-ONLY BEGIN'), s.index('-- PROOF-ONLY END')
    s = s[:a] + s[b:]
i, j = s.index('\ninvariant ['), s.index('\n#gen_spec')     # only in the invariants, not in lemmas
s = s[:i] + s[i:j].replace('∀ t : Nat,', '∀ t ∈ List.range (MaxTerm + 2),') + s[j:]
s = (s.replace('-- #model_check compiled', '#model_check compiled')
      .replace('--   { server := Fin 3', '  { server := Fin 3')
      .replace('--     VoteSet', '    VoteSet')
      .replace('--   { MaxTerm := 2, MaxLog := 2, MaxBatch := 1, MaxMsgs := 2, PreVote := false, Snapshots := false }',
               '  { MaxTerm := 2, MaxLog := %s, MaxBatch := 1, MaxMsgs := %s, PreVote := %s, Snapshots := %s }'
               % (sys.argv[4], sys.argv[1], sys.argv[2], sys.argv[3])))
assert '\n#model_check compiled' in s
print(s + '\nend RaftVeil')
PY
out=$(timeout "$limit" lake env lean "$tmp" 2>&1) && rc=0 || rc=$?
echo "$out" | grep -E 'explored|Violation' || true
[ $rc -eq 124 ] && { echo "stopped at the ${limit}s limit, no verdict"; exit 2; }
[ $rc -ne 0 ] && { echo "lean failed (exit $rc):"; echo "$out" | grep -m3 'error'; exit 1; }
exit 0
