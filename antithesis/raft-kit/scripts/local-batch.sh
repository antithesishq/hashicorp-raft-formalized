#!/usr/bin/env bash
# Runs N runs in a row and prints the verdict lines of each.
#
#   scripts/local-batch.sh [N] [DURATION] [CHAOS]     CHAOS: 1 (default) or kills
set -uo pipefail
here=$(cd "$(dirname "$0")/.." && pwd)
n=${1:-20}; duration=${2:-60}; chaos=${3:-1}
( cd "$here/config" && COMPOSE_FILE=docker-compose.yaml docker compose build -q ) || exit 2
ok=0
for i in $(seq 1 "$n"); do
  log=$(mktemp)
  BUILD=0 CHAOS=$chaos ${EXTRA_ENV:-} "$here/scripts/local-run.sh" "$duration" > "$log" 2>&1
  code=$?
  dir=$(sed -n 's/^output in //p' "$log")
  [ -n "$dir" ] && cp "$log" "$dir/run.log"
  [ "$code" = 0 ] && ok=$((ok + 1))
  echo "run $i [$(grep -c '^chaos:' "$log") faults, exit $code] $dir"
  grep -E '^(kit|driver assertions)' -A0 "$log" | cut -c1-260 | sed 's/^/    /'
  [ "$code" = 2 ] && sed 's/^/    /' "$log" | tail -5
  rm -f "$log"
done
echo "accepted: $ok of $n"
[ "$ok" = "$n" ]
