#!/usr/bin/env bash
# Compiles the TraceKit override (StreamEvent) into stream/classes, using a
# JDK image. TOOLS (default ../tools) holds tla2tools.jar and
# CommunityModules-deps.jar.
set -euo pipefail
here=$(cd "$(dirname "$0")/.." && pwd)
tools=$(readlink -f "${TOOLS:-$here/tools}")
docker run --rm -u "$(id -u):$(id -g)" -v "$here":/w -v "$tools":/tools:ro -w /w eclipse-temurin:21-jdk \
  javac --release 17 -cp /tools/tla2tools.jar:/tools/CommunityModules-deps.jar -d stream/classes stream/TraceKit.java
