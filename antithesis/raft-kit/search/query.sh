#!/usr/bin/env bash
# Prints the event-set query that runs the reducer over every timeline of a
# run and yields one event per timeline branch at its first non-conforming
# step, with fields `conformance` (rejected | violated), `why` and `k` (the
# stream line).
#
#   search/query.sh            the query
#   search/query.sh progress   a query yielding every 1000th matched line instead (how far timelines got)
#
# The run must have been launched with the stream kept in its events
# (UNFILTERED=1 scripts/launch.sh).
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
reducer=$(grep -v '^\s*//' "$here/reducer.js")
init=$(tr -d '\n' < "$here/init.json")
if [ "${1:-}" = progress ]; then
  emit='const o = (!s.dead && s.k % 1000 === 0) ? [e.add_fields({matched: s.k})] : [];'
else
  emit='const o = r[0].map((v) => e.add_fields({conformance: v.kind, why: v.why, k: s.k, event: ev}));'
fi
cat <<Q
matches({container: "driver"}).filter(e => (e.output_text || "").startsWith("trace-kit ")).fold((s, e) => { const step = $reducer; const ev = JSON.parse(e.output_text.slice(10)); const r = step(s, ev); s = r[1]; $emit return [o, s]; }, $init)
Q
