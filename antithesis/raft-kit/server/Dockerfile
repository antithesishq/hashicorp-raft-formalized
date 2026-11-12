# Builds raft-kit's server (the running-sum service, server/) against this
# checkout of hashicorp/raft, with Antithesis coverage instrumentation and
# assertion cataloging.
# Build context: the repository root.

FROM rust:1-bookworm AS log-forward
RUN rustup target add x86_64-unknown-linux-musl
COPY antithesis/raft-kit/driver/log-forward/ /src/
RUN cd /src && cargo build --release --target x86_64-unknown-linux-musl

FROM golang:1.26-bookworm AS build
RUN go install github.com/antithesishq/antithesis-sdk-go/tools/antithesis-go-toolexec@v0.8.0
WORKDIR /src
COPY go.mod go.sum ./
COPY antithesis/raft-kit/server/go.mod antithesis/raft-kit/server/go.sum antithesis/raft-kit/server/
COPY antithesis/tracekit/go antithesis/tracekit/go
RUN cd antithesis/raft-kit/server && go mod download
COPY . .
WORKDIR /src/antithesis/raft-kit/server
ENV CGO_ENABLED=1 \
    ANTITHESIS_INSTRUMENT=github.com/hashicorp/raft,raftsum \
    ANTITHESIS_SYMBOLS_DIR=/symbols
RUN mkdir -p /symbols && go build -toolexec=antithesis-go-toolexec -o /raft-sum . && ls -la /symbols

FROM debian:bookworm-slim
RUN apt-get update && apt-get install -y --no-install-recommends bash curl jq ca-certificates procps \
    && rm -rf /var/lib/apt/lists/*
COPY --from=build /raft-sum /usr/local/bin/raft-sum
COPY --from=build /symbols /symbols
COPY --from=log-forward /src/target/x86_64-unknown-linux-musl/release/log-forward /usr/local/bin/
COPY antithesis/raft-kit/driver/forward-logs /usr/local/bin/
RUN mkdir -p /data
ENTRYPOINT ["forward-logs", "raft-sum"]
