# Sourced by the scripts that build or run the images; sets and exports:
#   RAFT_PATCHES  patches/ applied to raft in the image (default "R1 R2 R3 R4";
#                 see patches/README.md). The model is of raft with all four.
#   PREVOTE       1 (default) or 0: raft's PreVoteDisabled and the model's PreVote.
#   SNAPSHOTS     1 (default): snapshot after 8 applied entries, checked every 2 s,
#                 and drop the covered log (SNAPSHOT_THRESHOLD, SNAPSHOT_INTERVAL,
#                 TRAILING_LOGS override); 0: no snapshots.
#   NODES         3 (default) or 5 voters; 5 writes config5/docker-compose.yaml.
#   CONFIG_DIR, PEERS, NODE_URLS, STREAM_CONFIG are derived.
case "${PREVOTE:=1}" in
  0) PREVOTE_DISABLED=1; STREAM_CONFIG=RaftBindingNoPV.cfg ;;
  1) PREVOTE_DISABLED=0; STREAM_CONFIG=RaftBinding.cfg ;;
  *) echo "PREVOTE must be 0 or 1" >&2; exit 2 ;;
esac
export PREVOTE PREVOTE_DISABLED STREAM_CONFIG TRACEKIT_STREAM_CONFIG="$STREAM_CONFIG"
case "${SNAPSHOTS:=1}" in
  0) ;;
  1) : "${SNAPSHOT_INTERVAL:=2s}" "${SNAPSHOT_THRESHOLD:=8}" "${TRAILING_LOGS:=0}"
     export SNAPSHOT_INTERVAL SNAPSHOT_THRESHOLD TRAILING_LOGS ;;
  *) echo "SNAPSHOTS must be 0 or 1" >&2; exit 2 ;;
esac
export SNAPSHOTS
kit=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
case "${NODES:=3}" in
  3) CONFIG_DIR="$kit/config" ;;
  5) CONFIG_DIR="$kit/config5"; mkdir -p "$CONFIG_DIR"
     "$kit/scripts/compose-nodes.py" 5 < "$kit/config/docker-compose.yaml" > "$CONFIG_DIR/docker-compose.yaml"
     STREAM_CONFIG=${STREAM_CONFIG%.cfg}5.cfg ;;
  *) echo "NODES must be 3 or 5" >&2; exit 2 ;;
esac
PEERS=$(for k in $(seq 1 "$NODES"); do printf 'raft%d=raft%d:7000,' "$k" "$k"; done); PEERS=${PEERS%,}
NODE_URLS=$(for k in $(seq 1 "$NODES"); do printf 'http://raft%d:8000,' "$k"; done); NODE_URLS=${NODE_URLS%,}
NODE_NAMES=$(for k in $(seq 1 "$NODES"); do printf 'hashicorp-raft%d ' "$k"; done)
export NODES CONFIG_DIR PEERS NODE_URLS STREAM_CONFIG TRACEKIT_STREAM_CONFIG="$STREAM_CONFIG"
: "${RAFT_PATCHES=R1 R2 R3 R4}"
export RAFT_PATCHES
