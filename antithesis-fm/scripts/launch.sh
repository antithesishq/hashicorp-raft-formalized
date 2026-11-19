#!/usr/bin/env bash
# Builds, validates (snouty validate) and launches the workload on Antithesis.
#
#   scripts/launch.sh COMPUTE_HOURS ["description"]    (minimum 12 hours)
# Env: UNFILTERED=1 keeps the printed stream in the run's events; TIER=standard|fast|turbo;
#      VARIANT=name is recorded on the run; PREVOTE, NODES, SNAPSHOTS, RAFT_PATCHES
#      as in build-env.sh.
set -euo pipefail
hours=${1:?usage: launch.sh COMPUTE_HOURS [description]}
desc=${2:-"hashicorp-raft formalized: small-step model checked from raft's interfaces"}
here=$(cd "$(dirname "$0")/.." && pwd)
repo=$(cd "$here/.." && pwd)
. "$here/scripts/build-env.sh"
plugin_version=${ANTITHESIS_PLUGIN_VERSION:-0.0.9}
export SNOUTY_CONTAINER_ENGINE=${SNOUTY_CONTAINER_ENGINE:-docker}

# Drop the printed stream from the run's events unless UNFILTERED=1.
filter='^trace-kit '
[ "${UNFILTERED:-}" = 1 ] && filter='^no-such-line$'

cd "$CONFIG_DIR"
# The build's settings go into .env, which the config image carries.
printf 'RAFT_PATCHES=%s\nPREVOTE=%s\nPREVOTE_DISABLED=%s\nSTREAM_CONFIG=%s\nPEERS=%s\nNODE_URLS=%s\n' \
  "$RAFT_PATCHES" "$PREVOTE" "$PREVOTE_DISABLED" "$STREAM_CONFIG" "$PEERS" "$NODE_URLS" > .env
printf 'SNAPSHOTS=%s\n' "$SNAPSHOTS" >> .env
if [ "$SNAPSHOTS" = 1 ]; then
  printf 'SNAPSHOT_INTERVAL=%s\nSNAPSHOT_THRESHOLD=%s\nTRAILING_LOGS=%s\n' "$SNAPSHOT_INTERVAL" "$SNAPSHOT_THRESHOLD" "$TRAILING_LOGS" >> .env
fi
trap 'rm -f "$CONFIG_DIR/.env"' EXIT
docker compose build
docker compose down -v >/dev/null 2>&1 || true
snouty validate . --timeout 5m
docker compose down -v >/dev/null 2>&1 || true

raft_rev=$(git -C "$repo" rev-parse --short HEAD)
SNOUTY_UNSTABLE_FEATURES=teams snouty launch \
  --launcher basic_test \
  --config . \
  --test-name hashicorp-raft-formalized \
  --description "$desc" \
  --fault-tolerance high_availability \
  --fault-exclusions '^(hashicorp-)?driver$' \
  --max-compute-hours "$hours" \
  --performance-tier "${TIER:-standard}" \
  --param attrs.variant="${VARIANT:-patched}" \
  --param attrs.raft_patches="${RAFT_PATCHES:-none}" \
  --param attrs.prevote="$PREVOTE" \
  --param attrs.nodes="$NODES" \
  --param attrs.snapshots="$SNAPSHOTS" \
  --param antithesis.filter_logs_matching="$filter" \
  --param attrs.workload=hashicorp-raft-formalized \
  --param attrs.raft_rev="$raft_rev" \
  --param attrs.plugin_version="$plugin_version"
