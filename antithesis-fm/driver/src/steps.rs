//! Properties of a single node, checked on the steps it reports (the
//! tracekit stream; see server/wrap.go for the events). They hold whether or
//! not the stream check is running, and need nothing from the model.

use antithesis_sdk::assert_always;
use serde_json::{json, Value};
use std::collections::HashMap;

#[derive(Default)]
struct Node {
    term: u64,
    vote_term: u64,
    vote_for: String,
    cand: String,
    /// Index of the last entry handed to the state machine since the boot,
    /// or of the snapshot it was put at.
    applied: u64,
    /// Index of the node's newest snapshot.
    snap: u64,
    /// Index of a snapshot the node has stored and whose request it has not
    /// answered yet: its state machine may not be at the snapshot yet.
    installing: u64,
}

#[derive(Default)]
pub struct Steps {
    nodes: HashMap<String, Node>,
}

impl Steps {
    pub fn observe(&mut self, ev: &Value) {
        let Some(name) = ev["node"].as_str() else { return };
        let n = self.nodes.entry(name.to_string()).or_default();
        match ev["e"].as_str().unwrap_or("") {
            // What the node recovered from disk. A write announced just before
            // a kill may not have happened, so this replaces what was announced.
            "boot" => {
                n.term = ev["term"].as_u64().unwrap_or(0);
                n.vote_term = ev["voteTerm"].as_u64().unwrap_or(0);
                n.vote_for = ev["voteFor"].as_str().unwrap_or("").to_string();
                n.cand = n.vote_for.clone();
                // The state machine starts from the node's snapshot (from
                // nothing if there is none) and is handed the log after it.
                n.snap = ev["snapIndex"].as_u64().unwrap_or(0);
                n.applied = n.snap;
                n.installing = 0;
            }
            "stable.set" => match ev["key"].as_str().unwrap_or("") {
                "CurrentTerm" => {
                    let t = ev["value"].as_u64().unwrap_or(0);
                    assert_always!(
                        t >= n.term,
                        "a node's current term never decreases",
                        &json!({"node": name, "old_term": n.term, "new_term": t, "k": ev["k"]})
                    );
                    n.term = t;
                }
                // A vote is two writes (patches/README.md, R2): the candidate, then
                // the term. The vote exists from the second.
                "LastVoteCand" => {
                    n.cand = ev["value"].as_str().unwrap_or("").to_string();
                }
                "LastVoteTerm" => {
                    let t = ev["value"].as_u64().unwrap_or(0);
                    assert_always!(
                        t >= n.vote_term,
                        "a node's vote term never decreases",
                        &json!({"node": name, "old_term": n.vote_term, "new_term": t, "k": ev["k"]})
                    );
                    assert_always!(
                        t != n.vote_term || n.vote_for == n.cand,
                        "a node votes for at most one candidate per term",
                        &json!({"node": name, "term": t, "candidate": n.cand, "prev_candidate": n.vote_for, "k": ev["k"]})
                    );
                    n.vote_term = t;
                    n.vote_for = n.cand.clone();
                }
                _ => {}
            },
            "log.delete" => {
                if let (Some(from), Some(commit), Some(applied)) =
                    (ev["from"].as_u64(), ev["commit"].as_u64(), ev["applied"].as_u64())
                {
                    // Entries that a snapshot covers are deleted from the
                    // front of the log, and a log that a snapshot replaces is
                    // deleted whole; this is about the end of a log.
                    assert_always!(
                        from <= n.snap || (from > commit && from > applied),
                        "a follower never truncates committed or applied log entries",
                        &json!({"node": name, "from": from, "to": ev["to"], "commit_index": commit,
                                "last_applied": applied, "k": ev["k"]})
                    );
                }
            }
            // A snapshot made the node's newest. One that the node was sent
            // puts its state machine at the snapshot.
            "snap.store" => {
                if let Some(index) = ev["index"].as_u64() {
                    if ev["kind"].as_str() == Some("install") {
                        assert_always!(
                            index > n.applied && index > n.snap,
                            "a node installs a snapshot only if it is newer than what its state machine holds",
                            &json!({"node": name, "index": index, "last_applied": n.applied,
                                    "snapshot_index": n.snap, "k": ev["k"]})
                        );
                        n.installing = index;
                        n.snap = index;
                    } else {
                        n.snap = n.snap.max(index);
                    }
                }
            }
            // The node has answered the request to install a snapshot: its
            // state machine is at the snapshot.
            "rpc.reply" => {
                if ev["kind"].as_str() == Some("snapshot") && n.installing > 0 {
                    n.applied = n.applied.max(n.installing);
                    n.installing = 0;
                }
            }
            // An entry handed to the state machine, with the node's commit
            // index then. Whether a command was skipped is the stream
            // check's to say: it takes the node's log.
            "fsm.apply" => {
                if let (Some(index), Some(commit)) = (ev["index"].as_u64(), ev["commit"].as_u64()) {
                    // Entries queued for the state machine before a snapshot
                    // was stored are handed over before it is put at the
                    // snapshot.
                    assert_always!(
                        index > n.applied,
                        "a node hands entries to its state machine in increasing index order",
                        &json!({"node": name, "index": index, "prev_index": n.applied, "k": ev["k"]})
                    );
                    assert_always!(
                        index <= commit,
                        "a node hands its state machine only entries within its commit index",
                        &json!({"node": name, "index": index, "commit_index": commit, "k": ev["k"]})
                    );
                    n.applied = index;
                }
            }
            _ => {}
        }
    }
}
