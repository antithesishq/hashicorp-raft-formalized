#!/usr/bin/env bash
# Local conformance run: runs the cluster and workload for DURATION seconds
# (default 40) with the live stream check, then re-checks the recorded stream.
#
#   scripts/local-run.sh [DURATION]
# Env: CHAOS=1 (kills, restarts, pauses, network cuts), CHAOS=kills, CHAOS=cuts
#      (finer cuts need sudo); BUILD=0 reuses images; DRIVER_*_RATE (see
#      local/docker-compose.local.yaml); PREVOTE, NODES, SNAPSHOTS, RAFT_PATCHES
#      as in build-env.sh.
# Output in runs/<time>/. Exit status: 0 accepted, 1 not, 2 setup failed.
set -uo pipefail
here=$(cd "$(dirname "$0")/.." && pwd)
. "$here/scripts/build-env.sh"
duration=${1:-40}
out="$here/runs/$(date +%Y%m%d-%H%M%S)"
mkdir -p "$out"
cd "$CONFIG_DIR"
export COMPOSE_FILE=docker-compose.yaml:../local/docker-compose.local.yaml
export COMPOSE_PROJECT_NAME=hashicorp-raft-local
echo "raft patches: ${RAFT_PATCHES:-none} (pre-votes: $PREVOTE; nodes: $NODES; snapshots: $SNAPSHOTS)"

docker compose down -v --remove-orphans >/dev/null 2>&1 || true
if [ "${BUILD:-1}" = 1 ]; then docker compose build -q || exit 2; fi
docker compose up -d > "$out/up.log" 2>&1 || { sleep 3; docker compose down -v >/dev/null 2>&1; docker compose up -d >> "$out/up.log" 2>&1; } \
  || { echo "could not start the cluster; see $out/up.log"; exit 2; }
docker compose exec -T driver /opt/antithesis/test/v1/main/first_start_workload
timeout 120 sh -c 'until docker compose exec -T driver grep -qs antithesis_setup /tmp/sdk.jsonl; do sleep 1; done' \
  || { echo "setup did not complete"; docker compose logs --no-color > "$out/compose.log" 2>&1; exit 2; }
echo "setup complete; running for ${duration}s"

# Chaos. cut_off disconnects a node from the network (its step reports use a
# shared volume); put_back reconnects it under its service name.
net="${COMPOSE_PROJECT_NAME}_default"
pick() { set -- $NODE_NAMES; shift $((RANDOM % $#)); echo "$1"; }
cut_off() { docker network disconnect "$net" "$1" >/dev/null; }
put_back() { docker network connect --alias "${1#hashicorp-}" "$net" "$1" >/dev/null; }
# Finer cuts: iptables rules in a node's network namespace (need sudo). A node
# cut off from its peers still accepts client writes it cannot commit.
filter() { # node iptables-arguments...
  local pid; pid=$(docker inspect -f '{{.State.Pid}}' "$1" 2>/dev/null) || return 1
  [ "${pid:-0}" -gt 0 ] && sudo -n nsenter -t "$pid" -n iptables "${@:2}" 2>/dev/null
}
address() { docker inspect -f '{{range .NetworkSettings.Networks}}{{.IPAddress}}{{end}}' "$1" 2>/dev/null; }
peers() { # node -I|-D: its traffic with the other nodes (raft's port), both ways
  filter "$1" "$2" INPUT -p tcp --dport 7000 -j DROP; filter "$1" "$2" OUTPUT -p tcp --dport 7000 -j DROP
}
deaf() { # node other -I|-D: node stops hearing other; other still hears node
  local ip; ip=$(address "$2"); [ -n "$ip" ] && filter "$1" "$3" INPUT -s "$ip" -j DROP
}
finer=0; sudo -n true 2>/dev/null && finer=1
if [ "${CHAOS:-}" = kills ]; then
  (
    end=$((SECONDS + duration - 8))
    while [ $SECONDS -lt $end ]; do
      sleep 1.$((RANDOM % 9))
      n=$(pick)
      echo "chaos: kill $n"; docker kill "$n" >/dev/null; sleep 0.$((RANDOM % 9 + 1)); docker start "$n" >/dev/null
    done
  ) 2>&1 | tee "$out/chaos.log" &
  chaos=$!
fi
if [ "${CHAOS:-}" = 1 ] || [ "${CHAOS:-}" = cuts ]; then
  (
    end=$((SECONDS + duration - 8))
    while [ $SECONDS -lt $end ]; do
      sleep $((RANDOM % 6 + 3))
      n=$(pick)
      if [ "$CHAOS" = cuts ]; then k=$((RANDOM % (3 + 3 * finer) + 5)); else k=$((RANDOM % (8 + 3 * finer))); fi
      case $k in
        0) echo "chaos: restart $n"; docker restart -t 2 "$n" >/dev/null ;;
        1) echo "chaos: kill $n"; docker kill "$n" >/dev/null; sleep $((RANDOM % 4 + 1)); docker start "$n" >/dev/null ;;
        2) echo "chaos: pause $n"; docker pause "$n" >/dev/null; sleep $((RANDOM % 5 + 1)); docker unpause "$n" >/dev/null ;;
        3) echo "chaos: short pause $n"; docker pause "$n" >/dev/null; sleep 0.$((RANDOM % 9 + 1)); docker unpause "$n" >/dev/null ;;
        4) echo "chaos: kill all"; docker kill $NODE_NAMES >/dev/null; sleep 1; docker start $NODE_NAMES >/dev/null ;;
        5) echo "chaos: cut $n off"; cut_off "$n"; sleep $((RANDOM % 6 + 2)); put_back "$n" ;;
        6) m=$(pick); [ "$m" = "$n" ] && continue
           echo "chaos: cut $n and $m off"; cut_off "$n"; cut_off "$m"; sleep $((RANDOM % 6 + 2)); put_back "$n"; sleep $((RANDOM % 3)); put_back "$m" ;;
        7) echo "chaos: cut $n off and kill it"; cut_off "$n"; sleep $((RANDOM % 4 + 2)); docker kill "$n" >/dev/null; put_back "$n"; docker start "$n" >/dev/null ;;
        8) echo "chaos: cut $n off from its peers"; peers "$n" -I; sleep $((RANDOM % 6 + 2)); peers "$n" -D ;;
        9) m=$(pick); [ "$m" = "$n" ] && continue
           echo "chaos: $n stops hearing $m"; deaf "$n" "$m" -I; sleep $((RANDOM % 6 + 2)); deaf "$n" "$m" -D ;;
        10) m=$(pick); [ "$m" = "$n" ] && continue
           echo "chaos: cut $n and $m off from their peers, one after the other"
           peers "$n" -I; sleep $((RANDOM % 4 + 2)); peers "$m" -I; peers "$n" -D; sleep $((RANDOM % 4 + 2)); peers "$m" -D ;;
      esac
    done
  ) 2>&1 | tee "$out/chaos.log" &
  chaos=$!
fi

sleep "$duration"
[ -n "${chaos:-}" ] && wait "$chaos"

# Stop the nodes first, so the driver has every event before the copy.
docker kill $NODE_NAMES >/dev/null 2>&1
sleep 1
docker compose cp driver:/trace-kit "$out/kit" >/dev/null
docker compose cp driver:/tmp/sdk.jsonl "$out/sdk.jsonl" >/dev/null 2>&1
notes=$(cut -d' ' -f2 "$out/kit/stream.ndjson.progress.notes" 2>/dev/null | sort | uniq -c | tr -s ' \n' ' ')
[ -n "$notes" ] && echo "noted steps:$notes"
docker compose logs --no-color > "$out/compose.log" 2>&1
docker compose down -v >/dev/null 2>&1
echo "output in $out"
failed=$(jq -r 'select(.antithesis_assert.hit and (.antithesis_assert.condition | not) and .antithesis_assert.assert_type == "always") | .antithesis_assert.message' "$out/sdk.jsonl" 2>/dev/null | sort | uniq -c)
[ -n "$failed" ] && printf 'driver assertions failed:\n%s\n' "$failed"

status=0
# Result of the driver's live stream check.
live() { # label dir pattern
  local written next stopped
  written=$(wc -l < "$2/stream.ndjson" 2>/dev/null || echo 0)
  next=$(cat "$2/stream.ndjson.progress" 2>/dev/null || echo 1)
  stopped=$(grep -o "$3: .*" "$out/compose.log" | cut -c1-400)
  if [ -n "$stopped" ]; then echo "$1 live: $stopped"; return 1
  else echo "$1 live: matched $((next - 1)) of $written events and was still running"; fi
}
live kit "$out/kit" "stream check stopped" || status=1
# Re-check the recorded stream from the file.
cp "$out/kit/stream.ndjson" "$out/kit/again.ndjson"; touch "$out/kit/again.ndjson.eof"
again=$("$here/tracekit/check/streamcheck.py" "$here/spec/manifest.json" "$out/kit/again.ndjson" | cut -c1-600)
echo "kit file: $again"
case "$again" in ACCEPTED*) ;; *) status=1 ;; esac
exit $status
