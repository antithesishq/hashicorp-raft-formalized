#!/usr/bin/env bash
# Local conformance run: start the cluster, run the workload for DURATION
# seconds (default 40) with the stream check following it live, then check
# the recorded stream once more from the file.
#
#   scripts/local-run.sh [DURATION]
#   CHAOS=1 scripts/local-run.sh 60      # also kills, restarts and pauses nodes
#   CHAOS=kills scripts/local-run.sh 60  # one kill every second or two
#   BUILD=0 scripts/local-run.sh         # reuse the images
#
# Exit status: 0 accepted, 1 not.
set -uo pipefail
here=$(cd "$(dirname "$0")/.." && pwd)
duration=${1:-40}
out="$here/runs/$(date +%Y%m%d-%H%M%S)"
mkdir -p "$out"
cd "$here/config"
export COMPOSE_FILE=docker-compose.yaml:../local/docker-compose.local.yaml
export COMPOSE_PROJECT_NAME=raftkit-local

docker compose down -v --remove-orphans >/dev/null 2>&1 || true
if [ "${BUILD:-1}" = 1 ]; then docker compose build -q || exit 2; fi
docker compose up -d > "$out/up.log" 2>&1 || { sleep 3; docker compose down -v >/dev/null 2>&1; docker compose up -d >> "$out/up.log" 2>&1; } \
  || { echo "could not start the cluster; see $out/up.log"; exit 2; }
docker compose exec -T driver /opt/antithesis/test/v1/main/first_start_workload
timeout 120 sh -c 'until docker compose exec -T driver grep -qs antithesis_setup /tmp/sdk.jsonl; do sleep 1; done' \
  || { echo "setup did not complete"; docker compose logs --no-color > "$out/compose.log" 2>&1; exit 2; }
echo "setup complete; running for ${duration}s"

if [ "${CHAOS:-}" = kills ]; then
  (
    end=$((SECONDS + duration - 8))
    while [ $SECONDS -lt $end ]; do
      sleep 1.$((RANDOM % 9))
      n=raft$((RANDOM % 3 + 1))
      echo "chaos: kill $n"; docker kill "$n" >/dev/null; sleep 0.$((RANDOM % 9 + 1)); docker start "$n" >/dev/null
    done
  ) 2>&1 | tee "$out/chaos.log" &
  chaos=$!
fi
if [ "${CHAOS:-}" = 1 ]; then
  (
    end=$((SECONDS + duration - 8))
    while [ $SECONDS -lt $end ]; do
      sleep $((RANDOM % 6 + 3))
      n=raft$((RANDOM % 3 + 1))
      case $((RANDOM % 5)) in
        0) echo "chaos: restart $n"; docker restart -t 2 "$n" >/dev/null ;;
        1) echo "chaos: kill $n"; docker kill "$n" >/dev/null; sleep $((RANDOM % 4 + 1)); docker start "$n" >/dev/null ;;
        2) echo "chaos: pause $n"; docker pause "$n" >/dev/null; sleep $((RANDOM % 5 + 1)); docker unpause "$n" >/dev/null ;;
        3) echo "chaos: short pause $n"; docker pause "$n" >/dev/null; sleep 0.$((RANDOM % 9 + 1)); docker unpause "$n" >/dev/null ;;
        4) echo "chaos: kill all"; docker kill raft1 raft2 raft3 >/dev/null; sleep 1; docker start raft1 raft2 raft3 >/dev/null ;;
      esac
    done
  ) 2>&1 | tee "$out/chaos.log" &
  chaos=$!
fi

sleep "$duration"
[ -n "${chaos:-}" ] && wait "$chaos"

# Stop the nodes first, so the driver has every event before the copy.
docker kill raft1 raft2 raft3 >/dev/null 2>&1
sleep 1
docker compose cp driver:/trace-kit "$out/kit" >/dev/null
docker compose cp driver:/tmp/sdk.jsonl "$out/sdk.jsonl" >/dev/null 2>&1
docker compose logs --no-color > "$out/compose.log" 2>&1
docker compose down -v >/dev/null 2>&1
echo "output in $out"
failed=$(jq -r 'select(.antithesis_assert.hit and (.antithesis_assert.condition | not) and .antithesis_assert.assert_type == "always") | .antithesis_assert.message' "$out/sdk.jsonl" 2>/dev/null | sort | uniq -c)
[ -n "$failed" ] && printf 'driver assertions failed:\n%s\n' "$failed"

status=0
# What the driver's stream check did while the run was going.
live() { # label dir pattern
  local written next stopped
  written=$(wc -l < "$2/stream.ndjson" 2>/dev/null || echo 0)
  next=$(cat "$2/stream.ndjson.progress" 2>/dev/null || echo 1)
  stopped=$(grep -o "$3: .*" "$out/compose.log" | cut -c1-400)
  if [ -n "$stopped" ]; then echo "$1 live: $stopped"; return 1
  else echo "$1 live: matched $((next - 1)) of $written events and was still running"; fi
}
live kit "$out/kit" "stream check stopped" || status=1
# The recorded stream, checked again from the file.
cp "$out/kit/stream.ndjson" "$out/kit/again.ndjson"; touch "$out/kit/again.ndjson.eof"
again=$("$here/../tracekit/check/streamcheck.py" "$here/spec/manifest.json" "$out/kit/again.ndjson" | cut -c1-600)
echo "kit file: $again"
case "$again" in ACCEPTED*) ;; *) status=1 ;; esac
exit $status
