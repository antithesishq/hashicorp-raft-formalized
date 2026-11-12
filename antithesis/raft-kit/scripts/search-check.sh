#!/usr/bin/env bash
# Checks every timeline of an Antithesis run against the model with one
# event-set query (search/reducer.js inside a fold). The run must have been
# launched with UNFILTERED=1, so that the printed stream is in its events.
#
#   scripts/search-check.sh RUN_ID
#
# Prints how many stream lines the run holds, how many non-conforming steps
# the query found (one per timeline branch, at its first), and a sample of
# them with their moments. To confirm one with TLC, download that timeline
# (snouty runs logs RUN_ID HASH VTIME --json), take the driver's
# `trace-kit ` lines as stream.ndjson, and run tracekit/check/streamcheck.py.
set -uo pipefail
here=$(cd "$(dirname "$0")/.." && pwd)
run=${1:?run id}
lines=$(snouty runs search "$run" 'matches({container: "driver"}).filter(e => (e.output_text || "").startsWith("trace-kit "))' --count | grep -o '^[0-9]*')
found=$(snouty runs search "$run" "$("$here/search/query.sh")" --count | grep -o '^[0-9]*')
deepest=$(snouty runs search "$run" "$("$here/search/query.sh" progress).narrow([\"matched\"])" --limit 999 --json 2>/dev/null | grep -o '"matched":[0-9]*' | cut -d: -f2 | sort -n | tail -1)
echo "stream lines in the run: $lines"
echo "longest timeline matched at least: ${deepest:-0} lines"
echo "non-conforming steps: $found"
if [ "${found:-0}" != 0 ]; then
  snouty runs search "$run" "$("$here/search/query.sh").narrow([\"conformance\",\"why\",\"k\",\"event\"])" --limit 20 --json | cut -c1-600
  exit 1
fi
