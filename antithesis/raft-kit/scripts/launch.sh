#!/usr/bin/env bash
# Builds, validates and launches the raft-kit workload on Antithesis.
#
#   scripts/launch.sh COMPUTE_HOURS ["description"]
#   UNFILTERED=1 scripts/launch.sh 12   # keep the printed stream in the run's events
#   TIER=turbo scripts/launch.sh 50     # performance tier: standard (default), fast, turbo
#   VARIANT=name scripts/launch.sh 50   # recorded on the run, e.g. for a seeded bug
#
# The minimum is 12 compute hours. Check the budget first (snouty runs usage).
set -euo pipefail
hours=${1:?usage: launch.sh COMPUTE_HOURS [description]}
desc=${2:-"raft-kit: small-step model checked from raft's interfaces"}
here=$(cd "$(dirname "$0")/.." && pwd)
repo=$(cd "$here/../.." && pwd)
plugin_version=${ANTITHESIS_PLUGIN_VERSION:-0.0.9}
export SNOUTY_CONTAINER_ENGINE=${SNOUTY_CONTAINER_ENGINE:-docker}

# The printed stream is suppressed during fuzzing unless UNFILTERED=1, which
# keeps it in the run's events so it can be queried (scripts/search-check.sh).
filter='^trace-kit '
[ "${UNFILTERED:-}" = 1 ] && filter='^no-such-line$'

cd "$here/config"
docker compose build
docker compose down -v >/dev/null 2>&1 || true
snouty validate . --timeout 5m
docker compose down -v >/dev/null 2>&1 || true

raft_rev=$(git -C "$repo" rev-parse --short HEAD)
SNOUTY_UNSTABLE_FEATURES=teams snouty launch \
  --launcher basic_test \
  --config . \
  --test-name raft-kit \
  --description "$desc" \
  --fault-tolerance high_availability \
  --fault-exclusions '^driver$' \
  --max-compute-hours "$hours" \
  --performance-tier "${TIER:-standard}" \
  --param attrs.variant="${VARIANT:-clean}" \
  --param antithesis.filter_logs_matching="$filter" \
  --param attrs.workload=raft-kit \
  --param attrs.raft_rev="$raft_rev" \
  --param attrs.plugin_version="$plugin_version"
