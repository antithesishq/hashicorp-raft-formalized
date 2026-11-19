//! The driver's model of the cluster: every write it sent and its outcome,
//! and the history the nodes applied, index by index, learned from their
//! forwarded logs. Every check that compares what one node did with what
//! another node or a client saw lives here.

use antithesis_sdk::{assert_always, assert_reachable};
use serde_json::json;
use std::collections::{BTreeMap, HashMap};
use std::time::{Duration, Instant};

/// How many applied indexes the model remembers. Older ones are forgotten,
/// so checks against them are skipped.
const MAX_APPLIES: usize = 100_000;
/// How long the model remembers a write after sending it.
const OP_MEMORY: Duration = Duration::from_secs(300);

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Outcome {
    /// Sent, no response yet.
    Pending,
    /// The leader acknowledged it at this log index, with this sum.
    Acked { index: u64, sum: i64 },
    /// Definitely never appended to the log (not leader, enqueue timeout).
    Rejected,
    /// Timed out or lost leadership: it may or may not be committed.
    Unknown,
}

pub struct OpRec {
    pub value: i64,
    pub sent: Instant,
    pub outcome: Outcome,
}

/// One applied command, as the first node to report it applied it.
#[derive(Clone, Debug)]
pub struct Applied {
    pub term: u64,
    pub op: u64,
    pub value: i64,
    pub sum: i64,
    pub count: u64,
    pub digest: u64,
    pub node: String,
}

/// A state machine state at a log index, as reported by a read or a
/// snapshot restore.
#[derive(Clone, Debug)]
pub struct StateAt {
    pub index: u64,
    pub term: u64,
    pub sum: i64,
    pub count: u64,
    pub digest: u64,
    pub node: String,
}

#[derive(Clone, Copy, Debug)]
pub enum StateSource {
    LinearRead,
    StaleRead,
    Restore,
}

enum Expect {
    Ack { op: u64, sum: i64, node: String },
    State(StateAt, StateSource),
}

#[derive(Default)]
pub struct Model {
    pub next_op: u64,
    ops: HashMap<u64, OpRec>,
    applies: BTreeMap<u64, Applied>,
    op_index: HashMap<u64, u64>,
    pending: BTreeMap<u64, Vec<Expect>>,
    /// Highest index of any acknowledged write.
    pub max_acked_index: u64,
    /// Highest index any linearizable read returned.
    pub max_linear_read_index: u64,
    sends_since_prune: u64,
}

impl Model {
    pub fn new() -> Self {
        Model { next_op: 1, ..Default::default() }
    }

    /// Records a write as sent, before sending it, and returns its op id.
    pub fn send(&mut self, value: i64) -> u64 {
        let op = self.next_op;
        self.next_op += 1;
        self.ops.insert(op, OpRec { value, sent: Instant::now(), outcome: Outcome::Pending });
        self.sends_since_prune += 1;
        if self.sends_since_prune >= 1000 {
            self.sends_since_prune = 0;
            let now = Instant::now();
            self.ops.retain(|_, r| now.duration_since(r.sent) < OP_MEMORY);
        }
        op
    }

    pub fn complete(&mut self, op: u64, outcome: Outcome, node: &str) {
        if let Some(rec) = self.ops.get_mut(&op) {
            rec.outcome = outcome;
        }
        match outcome {
            Outcome::Acked { index, sum } => {
                self.max_acked_index = self.max_acked_index.max(index);
                self.expect(index, Expect::Ack { op, sum, node: node.to_string() });
            }
            Outcome::Rejected => {
                if let Some(index) = self.op_index.get(&op) {
                    let a = &self.applies[index];
                    assert_always!(
                        false,
                        "a write rejected before reaching the log is never applied",
                        &json!({"op": op, "index": index, "applied_by": a.node, "rejected_by": node})
                    );
                }
            }
            _ => {}
        }
    }

    /// Checks a state a node reported (a read or a restored snapshot)
    /// against the applied history at its index.
    pub fn observe_state(&mut self, st: StateAt, source: StateSource) {
        if st.index == 0 {
            assert_always!(
                st.sum == 0 && st.count == 0,
                "a state machine that applied nothing has an empty sum",
                &json!({"node": st.node, "sum": st.sum, "count": st.count})
            );
            return;
        }
        let index = st.index;
        self.expect(index, Expect::State(st, source));
    }

    fn expect(&mut self, index: u64, e: Expect) {
        if let Some(a) = self.applies.get(&index) {
            check_expect(index, a, &e);
        } else if self.applies.first_key_value().map_or(true, |(&lo, _)| index >= lo) {
            self.pending.entry(index).or_default().push(e);
        }
    }

    /// Records a command a node applied, from its log line, and checks it
    /// against what other nodes applied and what the workload sent.
    pub fn record_apply(&mut self, index: u64, a: Applied) {
        // The workload sent it, with this value.
        assert_always!(
            a.op >= 1 && a.op < self.next_op,
            "nodes apply only commands the workload sent",
            &json!({"node": a.node, "index": index, "op": a.op, "next_op": self.next_op})
        );
        if let Some(rec) = self.ops.get(&a.op) {
            assert_always!(
                rec.value == a.value,
                "nodes apply a command with the value the workload sent",
                &json!({"node": a.node, "index": index, "op": a.op, "sent": rec.value, "applied": a.value})
            );
            assert_always!(
                rec.outcome != Outcome::Rejected,
                "a write rejected before reaching the log is never applied",
                &json!({"node": a.node, "index": index, "op": a.op})
            );
            if rec.outcome == Outcome::Unknown {
                assert_reachable!(
                    "a write whose outcome the client never learned is applied",
                    &json!({"node": a.node, "index": index, "op": a.op})
                );
            }
        }

        if let Some(first) = self.applies.get(&index) {
            // State machine safety: every node applies the same command at
            // each index, and the same history up to it.
            assert_always!(
                first.term == a.term
                    && first.op == a.op
                    && first.value == a.value
                    && first.sum == a.sum
                    && first.count == a.count
                    && first.digest == a.digest,
                "nodes apply the same command and history at every log index",
                &json!({
                    "index": index,
                    "first": {"node": first.node, "term": first.term, "op": first.op, "value": first.value,
                              "sum": first.sum, "count": first.count, "digest": first.digest.to_string()},
                    "this": {"node": a.node, "term": a.term, "op": a.op, "value": a.value,
                             "sum": a.sum, "count": a.count, "digest": a.digest.to_string()},
                })
            );
            return;
        }

        // Each write is applied at one index at most.
        let other = self.op_index.get(&a.op).copied();
        assert_always!(
            other.map_or(true, |o| o == index),
            "each write is applied at exactly one log index",
            &json!({"op": a.op, "index": index, "other_index": other, "node": a.node})
        );
        if let Some(lo) = self.applies.first_key_value().map(|(&k, _)| k) {
            if index < lo {
                return; // Older than anything we remember.
            }
        }
        self.op_index.insert(a.op, index);
        if let Some(es) = self.pending.remove(&index) {
            for e in &es {
                check_expect(index, &a, e);
            }
        }
        self.applies.insert(index, a);
        while self.applies.len() > MAX_APPLIES {
            if let Some((_, old)) = self.applies.pop_first() {
                self.op_index.remove(&old.op);
            }
        }
        if let Some(lo) = self.applies.first_key_value().map(|(&k, _)| k) {
            while let Some((&k, _)) = self.pending.first_key_value() {
                if k >= lo {
                    break;
                }
                self.pending.pop_first();
            }
        }
    }

    pub fn applied_at(&self, index: u64) -> Option<&Applied> {
        self.applies.get(&index)
    }

    pub fn acked_ops(&self) -> Vec<(u64, u64)> {
        self.ops
            .iter()
            .filter_map(|(&op, r)| match r.outcome {
                Outcome::Acked { index, .. } => Some((op, index)),
                _ => None,
            })
            .collect()
    }
}

fn check_expect(index: u64, a: &Applied, e: &Expect) {
    match e {
        Expect::Ack { op, sum, node } => {
            assert_always!(
                a.op == *op && a.sum == *sum,
                "an acknowledged write is the command committed at its log index",
                &json!({"index": index, "acked_op": op, "acked_sum": sum, "acked_by": node,
                        "applied_op": a.op, "applied_sum": a.sum, "applied_by": a.node})
            );
        }
        Expect::State(st, source) => {
            let ok = a.term == st.term && a.sum == st.sum && a.count == st.count && a.digest == st.digest;
            let details = json!({
                "index": index,
                "reported": {"node": st.node, "term": st.term, "sum": st.sum, "count": st.count, "digest": st.digest.to_string()},
                "applied": {"node": a.node, "term": a.term, "sum": a.sum, "count": a.count, "digest": a.digest.to_string()},
            });
            match source {
                StateSource::LinearRead => assert_always!(
                    ok,
                    "a linearizable read returns the state the nodes applied at its index",
                    &details
                ),
                StateSource::StaleRead => assert_always!(
                    ok,
                    "a stale read returns the state the nodes applied at its index",
                    &details
                ),
                // A state machine put at a snapshot holds what the nodes
                // applied up to the snapshot's index.
                StateSource::Restore => assert_always!(
                    ok,
                    "a restored snapshot is the state the nodes applied at its index",
                    &details
                ),
            }
        }
    }
}
