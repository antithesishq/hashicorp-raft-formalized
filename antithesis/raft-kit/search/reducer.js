// The raft-kit trace check as a reducer: (state, event) -> [violations, state].
//
// It is spec/RaftBinding.tla written out by hand, with the guards of the
// spec/Raft.tla actions it uses. One event is one step; there is no search.
// It runs in two places from this one source:
//   - locally under Node (check.js), where it is tested against TLC;
//   - inside an Antithesis event-set query, as the body of a fold
//     (query.sh), which walks every timeline of a run.
// TLC and the TLA+ files stay the authority. A rejection found by search is
// confirmed by replaying that timeline's stream through TLC.
//
// The file is one function expression so that it can be pasted into a query.
// It must not refer to anything outside itself.
(s, ev) => {
  const SERVERS = ["raft1", "raft2", "raft3"];
  const out = [];
  const N = s.nodes;
  const n = ev.node;

  // ---- helpers
  const stop = (kind, why) => { s.dead = { k: ev.k, kind: kind, why: why }; out.push({ kind: kind, why: why }); };
  const reject = (why) => stop("rejected", why);
  const violate = (name) => stop("violated", name);
  const sameEntry = (a, b) => a.term === b.term && a.type === b.type && a.value === b.value;
  const sameEntries = (a, b) => a.length === b.length && a.every((x, i) => sameEntry(x, b[i]));
  const termAt = (log, k) => (k > 0 && k <= log.length ? log[k - 1].term : 0);
  const lastTerm = (x) => termAt(x.log, x.log.length);
  const quorum = (count) => count * 2 > SERVERS.length;
  const appendKey = (src, dst, r) => JSON.stringify([src, dst, r.term, r.prevLogIndex, r.prevLogTerm,
    r.entries.map((e) => [e.term, e.type, e.value]), r.commit]);
  const voteKey = (src, r) => src + "|" + r.term + "|" + r.lastLogIndex + "|" + r.lastLogTerm;
  const prevOk = (x, m) => m.prevLogIndex === 0 ||
    (m.prevLogIndex <= x.log.length && x.log[m.prevLogIndex - 1].term === m.prevLogTerm);
  const hasFirst = (x, m, k) => {
    for (let q = 1; q <= k; q++) {
      const at = m.prevLogIndex + q;
      if (at > x.log.length || x.log[at - 1].term !== m.entries[q - 1].term) return false;
    }
    return true;
  };
  const acked = (leader, t, c) => {
    let count = 1;
    for (const j of SERVERS) if (j !== leader && (s.acks[j + "|" + leader + "|" + t] || -1) >= c) count++;
    return count;
  };
  // Raft's LeaderCommit, for the term of the entry at c.
  const ledCommit = (x, c) => c <= x.log.length && s.leaderSet[n + "|" + x.log[c - 1].term] === true &&
    quorum(acked(n, x.log[c - 1].term, c));
  const pre = (x) => ({ term: x.term, vt: x.vt, vf: x.vf, keep: x.log.length, suffix: [], conf: x.conf,
    vote: null, msg: null });
  const addVote = (voter, term, cand) => {
    const key = voter + "|" + term;
    if (s.votes[key] !== undefined && s.votes[key] !== cand) { violate("OneVotePerTerm"); return false; }
    const added = s.votes[key] === undefined;
    s.votes[key] = cand;
    return added;
  };
  const minTerm = () => Math.min(...SERVERS.map((j) => N[j].term));
  // A request fact, with how many copies of it are on their way.
  const sent = (dst, key, fact) => {
    const have = s.appends[dst][key];
    if (have) have.out++; else { fact.out = 1; s.appends[dst][key] = fact; }
  };

  // Forgetting facts (TraceKit, convention 4). Never earlier than the TLA+
  // binding would need them: a request a node is handling is kept.
  const forgetFor = (j) => {
    const x = N[j];
    const reqs = s.appends[j];
    for (const key in reqs) if (reqs[key].term < x.term && x.pending !== key) delete reqs[key];
    for (const key in s.grants) { const p = key.split("|"); if (p[1] === j && Number(p[2]) < x.term) delete s.grants[key]; }
    for (const key in s.acks) {
      const p = key.split("|");
      if (p[1] === j && Number(p[2]) < x.term && x.commit >= s.acks[key]) delete s.acks[key];
    }
    const low = minTerm();
    for (const key in s.voteReqs) if (s.voteReqs[key] < low) delete s.voteReqs[key];
    for (const t in s.ledLog) if (Number(t) < low) delete s.ledLog[t];
  };

  // Safety, step by step (see Track in RaftBinding.tla). verified[j] is how
  // much of j's log is known to equal the longest committed prefix (chain),
  // so each check only looks at what is new.
  const agreeUpTo = (j, upto) => {
    const x = N[j];
    for (let k = x.verified + 1; k <= upto; k++) {
      if (k > x.log.length) return false;
      if (k <= s.chain.length) { if (!sameEntry(x.log[k - 1], s.chain[k - 1])) return false; }
      else s.chain.push(x.log[k - 1]);
    }
    if (upto > x.verified) x.verified = upto;
    return true;
  };
  const committed = (x, c, ct, follower) => {
    x.commit = c;
    if (!agreeUpTo(n, c)) return violate("StateMachineSafety");
    for (const j of SERVERS) {
      if (j !== n && N[j].role === "leader" && ct < N[j].term && !agreeUpTo(j, c)) return violate("LeaderCompleteness");
    }
    s.termLen[ct] = Math.max(s.termLen[ct] || 0, c);
    if (c > x.srvLen) x.srvLen = c;
    if (follower && c > x.conf.index) return violate("CommitBeyondConfirmed");
    forgetFor(n);
  };
  const appended = (x, from) => {
    for (const j of SERVERS) {
      if (j === n) continue;
      const b = N[j].log;
      for (let k = from; k <= Math.min(x.log.length, b.length); k++) {
        if (x.log[k - 1].term !== b[k - 1].term) continue;
        if (!sameEntry(x.log[k - 1], b[k - 1]) || (k > 1 && x.log[k - 2].term !== b[k - 2].term)) return violate("LogMatching");
      }
    }
  };

  // ---- the step
  if (s.dead) return [[], s];
  if (ev.k !== s.k + 1) { reject("stream line " + ev.k + " follows line " + s.k); return [out, s]; }
  s.k = ev.k;
  const x = N[n];
  if (!x) { reject("unknown node"); return [out, s]; }

  if (ev.e === "boot") {
    const rec = (t, vt, vf, len, lt) => ev.term === t && ev.voteTerm === vt && ev.voteFor === vf &&
      ev.lastIndex === len && ev.lastTerm === lt;
    if (!x.ready) {
      if (ev.lastIndex >= 1) {
        if (!rec(x.term, x.vt, x.vf, x.log.length, lastTerm(x))) reject("recovered state differs from the initial state");
        x.ready = true;
      }
    } else {
      if (!rec(x.term, x.vt, x.vf, x.log.length, lastTerm(x))) {
        const u = x.undo;
        const log = u ? x.log.slice(0, u.keep).concat(u.suffix) : null;
        if (!u || !rec(u.term, u.vt, u.vf, log.length, termAt(log, log.length))) {
          reject("recovered state is neither the model's nor the model's before its last write");
        } else {
          // The last announced write did not happen: take it back. If it
          // was a leader's append, nobody was sent it.
          if (x.role === "leader" && s.ledLog[x.term]) s.ledLog[x.term] = log.slice();
          x.term = u.term; x.vt = u.vt; x.vf = u.vf; x.log = log; x.conf = u.conf;
          if (x.verified > u.keep && u.suffix.length === 0) x.verified = u.keep;
          if (u.msg) delete s.voteReqs[u.msg];
          if (u.vote) delete s.votes[u.vote];
        }
      }
      if (!s.dead) {
        x.role = "follower"; x.commit = 0; x.undo = null; x.pending = null;
        if (x.vf !== "") addVote(n, x.vt, x.vf);
      }
    }
  } else if (ev.e === "stable.set") {
    if (x.ready) {
      const u = pre(x);
      if (ev.key === "CurrentTerm") {
        if (ev.value !== x.term) {
          if (x.role === "candidate" && ev.value === x.term + 1) {
            x.term = ev.value;                                   // StartElection
            const key = voteKey(n, { term: x.term, lastLogIndex: x.log.length, lastLogTerm: lastTerm(x) });
            if (s.voteReqs[key] === undefined) u.msg = key;
            s.voteReqs[key] = x.term;
          } else if (ev.value > x.term && SERVERS.some((j) => j !== n && N[j].term >= ev.value)) {
            x.term = ev.value; x.role = "follower";              // AdoptTerm
          } else reject("term " + ev.value + " is neither the next election nor one another node has reached");
          if (!s.dead) forgetFor(n);
        }
      } else if (ev.key === "LastVoteTerm") {
        if (ev.value === x.term && !(x.vt === x.term && x.vf !== "")) x.vt = x.term;   // SetVoteTerm
        else reject("vote term written by a node that has voted in its term, or for another term");
      } else if (ev.key === "LastVoteCand") {
        const c = ev.value;
        const cast = s.votes[n + "|" + x.vt];
        let ok = x.vt === x.term && (cast === undefined || cast === c);
        if (ok && c === n) ok = x.role === "candidate";
        else if (ok) {
          ok = false;
          for (const key in s.voteReqs) {
            const p = key.split("|");
            if (p[0] === c && Number(p[1]) === x.term &&
                (Number(p[3]) > lastTerm(x) || (Number(p[3]) === lastTerm(x) && Number(p[2]) >= x.log.length))) { ok = true; break; }
          }
        }
        if (ok) { x.vf = c; if (addVote(n, x.vt, c)) u.vote = n + "|" + x.vt; }  // SetVoteFor
        else reject("vote for " + c + " is not allowed: already voted, no such request, or its log is behind");
      } else reject("unknown stable key");
      if (!s.dead) x.undo = u;
    }
  } else if (ev.e === "log.store") {
    if (!x.ready) {
      if (ev.first === 1 && sameEntries(ev.entries, x.log)) x.ready = true;
      else reject("bootstrap stored something other than the configuration entry");
    } else if (ev.first !== x.log.length + 1) {
      reject("entries stored at " + ev.first + ", log ends at " + x.log.length);
    } else {
      const u = pre(x);
      if (x.role === "leader") {
        if (ev.entries.length > 0 && ev.entries.every((e) => e.term === x.term)) {                         // LeaderAppend
          x.log.push(...ev.entries);
          if (s.ledLog[x.term]) s.ledLog[x.term].push(...ev.entries);
        }
        else reject("leader stored entries not of its term");
      } else {
        let found = null;
        const reqs = s.appends[n];
        for (const key in reqs) {
          const m = reqs[key];
          const k = ev.first - m.prevLogIndex;
          if (m.term === x.term && k >= 1 && k <= m.entries.length && sameEntries(m.entries.slice(k - 1), ev.entries) &&
              prevOk(x, m) && hasFirst(x, m, k - 1)) { found = m; break; }
        }
        if (found) {                                              // StoreEntries
          x.log.push(...ev.entries);
          x.conf = { term: found.term, index: found.prevLogIndex + found.entries.length };
        } else reject("no request in this term explains the stored entries");
      }
      if (!s.dead) { x.undo = u; appended(x, ev.first); }
    }
  } else if (ev.e === "log.delete") {
    let found = null;
    const reqs = s.appends[n];
    if (x.ready && ev.to === x.log.length) {
      for (const key in reqs) {
        const m = reqs[key];
        const k = ev.from - m.prevLogIndex;
        if (m.term === x.term && k >= 1 && k <= m.entries.length && prevOk(x, m) && hasFirst(x, m, k - 1) &&
            m.prevLogIndex + k <= x.log.length && x.log[m.prevLogIndex + k - 1].term !== m.entries[k - 1].term) { found = m; break; }
      }
    }
    if (found) {                                                  // DeleteSuffix
      const u = pre(x);
      u.keep = ev.from - 1; u.suffix = x.log.slice(ev.from - 1);
      x.log.length = ev.from - 1;
      x.conf = { term: found.term, index: ev.from - 1 };
      x.undo = u;
      if (x.verified > ev.from - 1) x.verified = ev.from - 1;
      if (ev.from - 1 < x.srvLen) violate("CommittedEntriesPreserved");
    } else reject("no request in this term conflicts with the deleted suffix");
  } else if (ev.e === "role") {
    if (x.ready) {
      if (ev.role === "follower" || ev.role === "candidate") x.role = ev.role;
      else if (ev.role === "leader") {
        let count = s.votes[n + "|" + x.term] === n ? 1 : 0;
        for (const j of SERVERS) if (j !== n && s.grants[j + "|" + n + "|" + x.term]) count++;
        if (x.role === "candidate" && quorum(count)) {            // BecomeLeader
          x.role = "leader";
          if (s.leaderOf[x.term] !== undefined && s.leaderOf[x.term] !== n) violate("ElectionSafety");
          else {
            s.leaderOf[x.term] = n; s.leaderSet[n + "|" + x.term] = true;
            s.ledLog[x.term] = x.log.slice();
            let need = 0;
            for (const t in s.termLen) if (Number(t) < x.term && s.termLen[t] > need) need = s.termLen[t];
            if (!agreeUpTo(n, need)) violate("LeaderCompleteness");
          }
        } else reject("became leader without being a candidate with a quorum of votes");
      }
    }
  } else if (ev.e === "rpc.send") {
    const r = ev.req;
    if (!x.ready) reject("request sent before bootstrap");
    else if (ev.kind === "vote") {
      if (s.voteReqs[voteKey(n, r)] === undefined && !(minTerm() > r.term)) reject("vote request was never made");
    } else if (ev.kind === "heartbeat" || ev.kind === "append") {
      // SendAppend, after LeaderCommit if the request shows a commit index
      // not seen yet. Checked against the log the node had as leader of the
      // request's term, not against the node as it is now: the report can
      // come after the node has left that term.
      const p = r.prevLogIndex, len = r.entries.length, c = r.commit;
      const l = s.ledLog[r.term];
      const prefixOf = (a, b, upto) => { for (let k = 0; k < upto; k++) if (!sameEntry(a[k], b[k])) return false; return true; };
      if (minTerm() > r.term) {
        // Every node has left the term: nobody can accept the request.
      } else if (s.leaderSet[n + "|" + r.term] === true && l !== undefined && ev.peer !== n &&
          p + len <= l.length && r.prevLogTerm === termAt(l, p) && sameEntries(r.entries, l.slice(p, p + len)) &&
          (c > x.commit
            ? ledCommit(x, c) && c <= l.length && prefixOf(x.log, l, c)
            : c === 0 || (c <= l.length && c <= s.chain.length && prefixOf(s.chain, l, c)))) {
        if (c > x.commit) committed(x, c, x.log[c - 1].term, false);   // LeaderCommit
        if (!s.dead) {                                                // SendAppend
          sent(ev.peer, appendKey(n, ev.peer, r), { src: n, term: r.term, prevLogIndex: p, prevLogTerm: r.prevLogTerm, entries: r.entries, commit: c });
        }
      } else reject("request is not what the log and commit index of that term's leader allow");
    } else reject("unknown request kind");
  } else if (ev.e === "rpc.recv") {
    x.pending = appendKey(ev.src, n, ev.req);
  } else if (ev.e === "rpc.reply") {
    if (x.ready) {
      const moved = ev.commit > x.commit;
      const late = () => {            // the node committed as a leader earlier
        if (ledCommit(x, ev.commit)) committed(x, ev.commit, x.log[ev.commit - 1].term, false);
        else reject("commit index " + ev.commit + " is explained neither by the request nor by a past leadership");
      };
      if (ev.kind === "vote") {
        if (ev.resp.granted) {
          if (s.votes[n + "|" + ev.req.term] === ev.src) s.grants[n + "|" + ev.src + "|" + ev.req.term] = true;  // GrantVote
          else reject("vote granted but not recorded");
        } else if (ev.resp.term > x.term) reject("reply carries a term the node has not reached");
        if (!s.dead && moved) late();
      } else if (ev.kind === "append") {
        const key = appendKey(ev.src, n, ev.req);
        const m = s.appends[n][key];
        if (ev.resp.success) {
          if (m && x.term >= m.term && prevOk(x, m) && hasFirst(x, m, m.entries.length)) {   // Ack
            const last = m.prevLogIndex + m.entries.length;
            const ak = n + "|" + ev.src + "|" + m.term;
            if ((s.acks[ak] === undefined ? -1 : s.acks[ak]) < last) s.acks[ak] = last;
            x.conf = { term: m.term, index: x.conf.term === m.term ? Math.max(x.conf.index, last) : last };
            if (moved) {
              if (ev.commit <= m.commit) committed(x, ev.commit, m.term, true);   // FollowerCommit
              else late();
            }
          } else reject("successful reply, but the log does not hold what the request carries");
        } else {
          if (ev.resp.term > x.term) reject("reply carries a term the node has not reached");
          else if (moved) late();
        }
        // Forget the request once every copy that was sent has been replied
        // to: the same request can be sent, and delivered, several times.
        x.pending = null;
        if (m && --m.out <= 0) delete s.appends[n][key];
      } else reject("unknown reply kind");
    }
  } else if (ev.e === "rpc.return") {
    const r = ev.req;
    if (ev.kind === "vote") {
      if (ev.resp.granted && !s.grants[ev.peer + "|" + n + "|" + r.term] && !(x.term > r.term)) reject("granted reply returned that was never sent");
    } else if (ev.kind === "append" || ev.kind === "heartbeat") {
      const last = r.prevLogIndex + r.entries.length;
      const a = s.acks[ev.peer + "|" + n + "|" + r.term];
      if (ev.resp.success && !(a !== undefined && a >= last) && !(x.term > r.term && x.commit >= last)) reject("successful reply returned that was never sent");
    } else reject("unknown reply kind");
  } else if (ev.e !== "rpc.fail") {
    reject("no model action for event " + ev.e);
  }
  return [out, s];
}
