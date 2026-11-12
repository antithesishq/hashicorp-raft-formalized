#!/usr/bin/env bash
# Sensitivity of the whole loop: build raft with one seeded bug at a time,
# run it, and require the stream check to reject the run while it is going.
# Restores the source and rebuilds the clean image afterwards.
#
#   scripts/sut-mutants.sh [NAME]      one mutant, or all
set -uo pipefail
here=$(cd "$(dirname "$0")/.." && pwd)
root=$(cd "$here/../.." && pwd)
fail=0
only=${1:-}
mutant() { # name file sed-expression [chaos mode] [tries]
  [ -n "$only" ] && [ "$only" != "$1" ] && return
  cp "$root/$2" "$root/$2.orig"
  sed -i "$3" "$root/$2"
  if cmp -s "$root/$2" "$root/$2.orig"; then echo "FAIL  $1: the edit did not apply"; fail=1; rm "$root/$2.orig"; return; fi
  # A mutant that does not compile would leave the previous image in use.
  if ! ( cd "$root" && go build ./... ) 2>/dev/null; then
    echo "FAIL  $1: the mutant does not compile"; fail=1; mv "$root/$2.orig" "$root/$2"; return
  fi
  log=$(mktemp); hit=""; build=1
  for try in $(seq 1 "${5:-1}"); do
    if [ -n "${4:-}" ]; then BUILD=$build CHAOS=$4 DRIVER_ADD_RATE=20 "$here/scripts/local-run.sh" 60 > "$log" 2>&1
    else BUILD=$build "$here/scripts/local-run.sh" 20 > "$log" 2>&1; fi
    build=0
    if grep -q '^kit live: stream check stopped: \(REJECTED\|VIOLATED\)' "$log"; then hit=$try; break; fi
  done
  mv "$root/$2.orig" "$root/$2"
  if [ -n "$hit" ]; then echo "ok    $1 (run $hit): $(grep "^kit live:" "$log" | cut -c33-150) [$(sed -n "s/^output in //p" "$log")]"
  else echo "FAIL  $1: not rejected in ${5:-1} run(s): $(grep '^kit live' "$log" | cut -c1-100)"; fail=1; fi
  rm -f "$log"
}
# A follower commits one entry past what the leader told it.
mutant follower-commits-ahead raft.go \
  's/idx := min(a.LeaderCommitIndex, r.getLastIndex())/idx := min(a.LeaderCommitIndex+1, r.getLastIndex())/'
# A leader commits what any single server has stored, not a quorum.
mutant commit-without-quorum commitment.go \
  's/quorumMatchIndex := matched\[(len(matched)-1)\/2\]/quorumMatchIndex := matched[len(matched)-1]/'
# These two need faults before they show: two candidates in one term, and a
# follower whose log has diverged. They get chaos and several tries.
# A node grants its vote although it has already voted in the term.
mutant votes-twice raft.go \
  's/if lastVoteTerm == req.Term \&\& lastVoteCandBytes != nil {/if lastVoteTerm == req.Term+1 \&\& lastVoteCandBytes != nil {/' 1 8
# A follower accepts entries without checking the previous entry's term.
mutant no-prev-check raft.go \
  's/if a.PrevLogTerm != prevLogTerm {/if false \&\& a.PrevLogTerm != prevLogTerm {/' 1 10
# FIXES.md R1 undone: a replicator sends what it read after its node stopped
# leading the term.
mutant deposed-replicator-sends replication.go \
  's/if r.getState() != Leader || r.getCurrentTerm() != s.currentTerm {/if false \&\& r.getState() != Leader {/' 1 10
( cd "$here/config" && COMPOSE_FILE=docker-compose.yaml docker compose build -q )
exit $fail
