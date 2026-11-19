#!/usr/bin/env bash
# Fetches the TLA+ jars into tracekit/tools, compiles the TraceKit stream
# operator into tracekit/stream/classes, and reports which other tools are
# on PATH.
#
#   scripts/setup.sh
set -euo pipefail
here=$(cd "$(dirname "$0")/.." && pwd)
TLA2TOOLS=v1.8.0
COMMUNITY_MODULES=202611060952
tools=$here/tracekit/tools
mkdir -p "$tools"
[ -s "$tools/tla2tools.jar" ] || curl -fsSL -o "$tools/tla2tools.jar" \
  "https://github.com/tlaplus/tlaplus/releases/download/$TLA2TOOLS/tla2tools.jar"
[ -s "$tools/CommunityModules-deps.jar" ] || curl -fsSL -o "$tools/CommunityModules-deps.jar" \
  "https://github.com/tlaplus/CommunityModules/releases/download/$COMMUNITY_MODULES/CommunityModules-deps.jar"
if command -v javac > /dev/null; then
  ( cd "$here/tracekit" && javac --release 17 -cp "$tools/tla2tools.jar:$tools/CommunityModules-deps.jar" \
      -d stream/classes stream/TraceKit.java )
else
  "$here/tracekit/stream/build.sh"   # compiles in a JDK container
fi
echo "tracekit/tools and tracekit/stream/classes are ready"
have() { if command -v "$1" > /dev/null; then echo "  ok       $1"; else echo "  missing  $1  ($2)"; fi; }
echo "Tools on PATH:"
have java    "TLC, trace validation"
have python3 "trace validation scripts"
have docker  "local cluster runs"
have lake    "Lean proofs; install elan"
have tlapm   "TLAPS proofs; or set TLAPM"
