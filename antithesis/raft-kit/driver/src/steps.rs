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
                // A vote is two writes: the term, then the candidate.
                "LastVoteTerm" => {
                    let t = ev["value"].as_u64().unwrap_or(0);
                    assert_always!(
                        t >= n.vote_term,
                        "a node's vote term never decreases",
                        &json!({"node": name, "old_term": n.vote_term, "new_term": t, "k": ev["k"]})
                    );
                    if t > n.vote_term {
                        n.vote_term = t;
                        n.vote_for.clear();
                    }
                }
                "LastVoteCand" => {
                    let c = ev["value"].as_str().unwrap_or("");
                    // After a kill between the two writes the term can stand
                    // with no candidate, or with an older term's; raft then
                    // only ever repeats that candidate, so this still holds.
                    assert_always!(
                        n.vote_for.is_empty() || n.vote_for == c,
                        "a node votes for at most one candidate per term",
                        &json!({"node": name, "term": n.vote_term, "candidate": c, "prev_candidate": n.vote_for, "k": ev["k"]})
                    );
                    n.vote_for = c.to_string();
                }
                _ => {}
            },
            "log.delete" => {
                if let (Some(from), Some(commit), Some(applied)) =
                    (ev["from"].as_u64(), ev["commit"].as_u64(), ev["applied"].as_u64())
                {
                    assert_always!(
                        from > commit && from > applied,
                        "a follower never truncates committed or applied log entries",
                        &json!({"node": name, "from": from, "to": ev["to"], "commit_index": commit,
                                "last_applied": applied, "k": ev["k"]})
                    );
                }
            }
            _ => {}
        }
    }
}
