#!/usr/bin/env bash
# Tests of the stream check itself. The recorded streams in traces/ must be
# accepted. Every mutation of traces/happy must be rejected, at the first
# changed event or later, never before.
#
#   scripts/validator-tests.sh
set -uo pipefail
here=$(cd "$(dirname "$0")/.." && pwd)
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
fail=0
check() { # name stream expected-exit first-changed-index
  cp "$2" "$tmp/s.ndjson"; rm -f "$tmp"/s.ndjson.*; touch "$tmp/s.ndjson.eof"
  out=$("$here/../tracekit/check/streamcheck.py" "$here/spec/manifest.json" "$tmp/s.ndjson" 2>&1); code=$?
  at=$(echo "$out" | awk '{print $2}')
  if [ "$code" != "$3" ] || { [ "$3" = 1 ] && [ "$at" -lt "$4" ]; }; then
    echo "FAIL  $1: expected exit $3${4:+ at event >= $4}: $(echo "$out" | cut -c1-160)"; fail=1
  else echo "ok    $1: $(echo "$out" | cut -c1-50)${4:+  [first changed event $4]}"; fi
}
for f in "$here"/traces/*/stream.ndjson; do
  check "accept $(basename "$(dirname "$f")")" "$f" 0 ""
done
for m in $("$here/scripts/mutate.py" list); do
  at=$("$here/scripts/mutate.py" "$m" "$here/traces/happy/stream.ndjson" "$tmp/$m.ndjson") \
    || { echo "FAIL  $m: could not mutate"; fail=1; continue; }
  check "reject $m" "$tmp/$m.ndjson" 1 "$at"
done
exit $fail
