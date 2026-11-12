# Build context: the repository root.
FROM rust:1-bookworm AS build
WORKDIR /src/antithesis/raft-kit/driver
COPY antithesis/raft-kit/driver/Cargo.toml antithesis/raft-kit/driver/Cargo.lock ./
COPY antithesis/raft-kit/driver/src ./src
COPY antithesis/tracekit/driver /src/antithesis/tracekit/driver
RUN cargo build --release

FROM eclipse-temurin:21-jdk AS stream
COPY antithesis/tracekit/tools/ /w/tools/
COPY antithesis/tracekit/stream/TraceKit.java /w/kit/
RUN cd /w && javac --release 17 -cp tools/tla2tools.jar:tools/CommunityModules-deps.jar -d kit/classes kit/TraceKit.java

FROM debian:bookworm-slim
RUN apt-get update && apt-get install -y --no-install-recommends curl jq ca-certificates procps \
    python3 default-jre-headless coreutils \
    && rm -rf /var/lib/apt/lists/*
COPY --from=build /src/antithesis/raft-kit/driver/target/release/driver /usr/local/bin/
COPY antithesis/raft-kit/driver/first_start_workload /opt/antithesis/test/v1/main/
RUN chmod 755 /opt/antithesis/test/v1/main/first_start_workload
# The stream check: TLC, the model, the binding and the generic checker.
COPY antithesis/tracekit/tools/ /opt/kit/raft-kit/tools/
COPY antithesis/raft-kit/spec/ /opt/kit/raft-kit/spec/
COPY antithesis/tracekit/tla/ /opt/kit/tracekit/tla/
COPY antithesis/tracekit/check/ /opt/kit/tracekit/check/
COPY --from=stream /w/kit/classes/ /opt/kit/tracekit/stream/classes/
ENV TRACEKIT_CHECK=/opt/kit/tracekit/check/streamcheck.py \
    TRACEKIT_MANIFEST=/opt/kit/raft-kit/spec/manifest.json \
    TLC_HEAP=2g
CMD ["/usr/local/bin/driver"]
