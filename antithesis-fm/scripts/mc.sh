#!/usr/bin/env bash
# Runs TLC on one configuration under a time limit; prints a one-line result.
#
#   scripts/mc.sh CONFIG LIMIT_SECONDS [extra TLC args, e.g. -simulate -depth 100]
#
# CONFIG is a file in spec/; module MCRaft.tla (MODULE overrides). Env: TLC_HEAP,
# TLC_WORKERS. Full output in runs/mc/<config>-<time>.log.
set -uo pipefail
here=$(cd "$(dirname "$0")/.." && pwd)
cfg=${1:?config}; limit=${2:?limit in seconds}; shift 2
mkdir -p "$here/runs/mc"
log="$here/runs/mc/${cfg%.cfg}-$(date +%H%M%S).log"
meta=$(mktemp -d)
( cd "$here/spec" && timeout "$limit" java -XX:+UseParallelGC -Xmx"${TLC_HEAP:-6g}" \
    -cp "$here/tracekit/tools/tla2tools.jar" tlc2.TLC -workers "${TLC_WORKERS:-auto}" -metadir "$meta" \
    -noGenerateSpecTE -config "$cfg" "$@" "${MODULE:-MCRaft}.tla" ) > "$log" 2>&1
code=$?
rm -rf "$meta"
states=$(grep -oE '[0-9,]+ distinct states found' "$log" | tail -1 | cut -d' ' -f1)
sim=$(grep -oE '[0-9]+ states checked, [0-9]+ traces generated' "$log" | tail -1)
depth=$(grep -oE 'Progress\([0-9]+\)' "$log" | tail -1 | tr -dc 0-9)
viol=$(grep -oE '(Invariant|Action property|Temporal property) [A-Za-z]+ (is|was) violated' "$log" | head -1)
if [ -n "$viol" ]; then echo "$cfg: VIOLATION: $viol (${states:-$sim}) [$log]"
elif grep -q 'Model checking completed. No error' "$log"; then echo "$cfg: completed, $states states, no violation [$log]"
elif [ "$code" = 124 ]; then echo "$cfg: stopped at the ${limit}s limit, depth ${depth:-?}, ${states:-$sim}, no violation so far [$log]"
else echo "$cfg: ERROR (exit $code) [$log]"; grep -m3 -iE 'error|exception' "$log"; fi
