# Build context: the repository root.
FROM rust:1-bookworm AS build
WORKDIR /src/antithesis-fm/driver
COPY antithesis-fm/driver/Cargo.toml antithesis-fm/driver/Cargo.lock ./
COPY antithesis-fm/driver/src ./src
COPY antithesis-fm/tracekit/driver /src/antithesis-fm/tracekit/driver
RUN cargo build --release

FROM eclipse-temurin:21-jdk AS stream
COPY antithesis-fm/tracekit/tools/ /w/tools/
COPY antithesis-fm/tracekit/stream/TraceKit.java /w/kit/
RUN cd /w && javac --release 17 -cp tools/tla2tools.jar:tools/CommunityModules-deps.jar -d kit/classes kit/TraceKit.java

FROM debian:bookworm-slim
RUN apt-get update && apt-get install -y --no-install-recommends curl jq ca-certificates procps \
    python3 default-jre-headless coreutils \
    && rm -rf /var/lib/apt/lists/*
COPY --from=build /src/antithesis-fm/driver/target/release/driver /usr/local/bin/
COPY antithesis-fm/driver/first_start_workload /opt/antithesis/test/v1/main/
RUN chmod 755 /opt/antithesis/test/v1/main/first_start_workload
# Stream check: TLC, the model and binding, tracekit's checker.
COPY antithesis-fm/tracekit/tools/ /opt/kit/tracekit/tools/
COPY antithesis-fm/spec/ /opt/kit/spec/
COPY antithesis-fm/tracekit/tla/ /opt/kit/tracekit/tla/
COPY antithesis-fm/tracekit/check/ /opt/kit/tracekit/check/
COPY --from=stream /w/kit/classes/ /opt/kit/tracekit/stream/classes/
ENV TRACEKIT_CHECK=/opt/kit/tracekit/check/streamcheck.py \
    TRACEKIT_MANIFEST=/opt/kit/spec/manifest.json \
    TLC_HEAP=2g
CMD ["/usr/local/bin/driver"]
