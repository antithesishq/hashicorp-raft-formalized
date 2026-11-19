#!/usr/bin/env bash
# Tests of the stream check. Every recorded stream in traces/ must be accepted;
# every mutant from scripts/mutate.py must get the verdict `mutate.py expect` gives:
#   reject    rejected at the first changed event or later
#   accept    accepted, with exactly the notes listed
# Prints ok/FAIL per case; exit 1 on any FAIL.
#
#   scripts/validator-tests.sh
set -uo pipefail
here=$(cd "$(dirname "$0")/.." && pwd)
traces="$here/traces"
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
fail=0
# A trace directory's `config` file names its TLC configuration, if not the default.
config_for() { cat "$(dirname "$1")/config" 2>/dev/null || echo RaftBinding.cfg; }
check() { # name stream expectation... first-changed-index config
  local name=$1 stream=$2 want=$3 notes=$4 at0=$5
  export TRACEKIT_STREAM_CONFIG=${6:-RaftBinding.cfg}
  cp "$stream" "$tmp/s.ndjson"; rm -f "$tmp"/s.ndjson.*; touch "$tmp/s.ndjson.eof"
  out=$("$here/tracekit/check/streamcheck.py" "$here/spec/manifest.json" "$tmp/s.ndjson" 2>&1); code=$?
  verdict=$(echo "$out" | awk '{print $1}'); at=$(echo "$out" | awk '{print $2}')
  # Step notes (names with a hyphen).
  got=$(cut -d' ' -f2 "$tmp/s.ndjson.progress.notes" 2>/dev/null | grep -- - | sort -u | tr '\n' ' ' | sed 's/ $//')
  ok=1
  case "$want" in
    reject) [ "$verdict" = REJECTED ] && [ "$at" -ge "$at0" ] || ok=0 ;;
    accept) [ "$verdict" = ACCEPTED ] || ok=0 ;;
    violate:*) [ "$verdict" = VIOLATED ] && echo "$out" | grep -q "${want#violate:}" || ok=0 ;;
  esac
  [ "$want" = reject ] || [ "$got" = "$notes" ] || ok=0
  if [ $ok = 0 ]; then echo "FAIL  $name: expected $want${notes:+ with notes $notes}: $(echo "$out" | cut -c1-160)${got:+ [notes: $got]}"; fail=1
  else echo "ok    $name: $(echo "$out" | cut -c1-50)${got:+  [notes: $got]}${at0:+  [first changed event $at0]}"; fi
}
for f in "$traces"/*/stream.ndjson; do
  # Expected step notes are in the trace's `notes` file.
  check "accept $(basename "$(dirname "$f")")" "$f" accept "$(cat "$(dirname "$f")/notes" 2>/dev/null)" "" "$(config_for "$f")"
done
while read -r m what rest; do
  src="$traces/$("$here/scripts/mutate.py" source "$m")/stream.ndjson"; cfg=$(config_for "$src")
  at=$("$here/scripts/mutate.py" "$m" "$src" "$tmp/$m.ndjson") \
    || { echo "FAIL  $m: could not write"; fail=1; continue; }
  case "$what" in
    reject) check "reject $m" "$tmp/$m.ndjson" reject "" "$at" "$cfg" ;;
    accept) check "accept $m" "$tmp/$m.ndjson" accept "$rest" "" "$cfg" ;;
  esac
done < <("$here/scripts/mutate.py" expect)
exit $fail
