#!/usr/bin/env bash
# Differential test of the search reducer (search/reducer.js) against TLC.
# On every mutation of traces/happy the two must give the same verdict at the
# same event. On every recorded stream (traces/* and, with ALL=1, runs/*)
# the reducer must agree with TLC's verdict.
#
#   scripts/search-tests.sh          mutations and fixtures
#   ALL=1 scripts/search-tests.sh    also every stream under runs/ (reducer only; TLC accepted them)
set -uo pipefail
here=$(cd "$(dirname "$0")/.." && pwd)
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
fail=0
tlc() { cp "$1" "$tmp/s.ndjson"; rm -f "$tmp"/s.ndjson.*; touch "$tmp/s.ndjson.eof"
        "$here/../tracekit/check/streamcheck.py" "$here/spec/manifest.json" "$tmp/s.ndjson" 2>&1 | awk '{print $1, $2}'; }
js() { "$here/search/check.js" "$1" | awk '{print $1, $2}'; }
same() { # name stream
  a=$(tlc "$2"); b=$(js "$2")
  if [ "$a" = "$b" ]; then echo "ok    $1: both $a"; else echo "FAIL  $1: TLC '$a', reducer '$b'"; fail=1; fi
}
for f in "$here"/traces/*/stream.ndjson; do same "fixture $(basename "$(dirname "$f")")" "$f"; done
for m in $("$here/scripts/mutate.py" list); do
  "$here/scripts/mutate.py" "$m" "$here/traces/happy/stream.ndjson" "$tmp/$m.ndjson" >/dev/null || { echo "FAIL  $m: could not mutate"; fail=1; continue; }
  same "mutation $m" "$tmp/$m.ndjson"
done
if [ "${ALL:-}" = 1 ]; then
  n=0; bad=0
  for f in "$here"/runs/*/kit/stream.ndjson; do
    n=$((n + 1)); r=$("$here/search/check.js" "$f" | cut -c1-200)
    case "$r" in ACCEPTED*) ;; *) bad=$((bad + 1)); echo "      $(basename "$(dirname "$(dirname "$f")")"): $r" ;; esac
  done
  echo "recorded runs: reducer accepts $((n - bad)) of $n"
fi
exit $fail
