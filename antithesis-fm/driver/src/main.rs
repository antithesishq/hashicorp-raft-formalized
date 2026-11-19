//! The driver: a 3-node hashicorp/raft cluster whose state
//! machine keeps a running sum of the integers clients add, restricted to the
//! features the TLA+ model covers (see spec/README.md).
//!
//! Besides checking client-visible behaviour, it collects
//! the steps the nodes report and runs the TLC stream check on them
//! (tracekit's trace.rs), and checks single-node properties on the same
//! steps (steps.rs).
//!
//! Rules send adds and reads to the nodes and record each outcome in the
//! model. The nodes' forwarded logs feed the model with what every node
//! applied, so each response and each node's history is checked against the
//! others as it arrives.

mod logs;
mod model;
#[path = "../../tracekit/driver/trace.rs"]
mod trace;
mod steps;

use antithesis_sdk::{assert_always, assert_reachable, assert_sometimes_greater_than};
use hegel::generators as gs;
use hegel::stateful::machine;
use hegel::TestCase;
use logs::Logs;
use model::{Model, Outcome, StateAt, StateSource};
use serde_json::{json, Value};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, Mutex, RwLock};
use std::time::{Duration, Instant};

/// The nodes' names, from the hosts of NODE_URLS: three by default, five with
/// NODES=5 (scripts/build-env.sh).
static NODES: std::sync::LazyLock<Vec<String>> = std::sync::LazyLock::new(|| {
    node_urls()
        .iter()
        .map(|u| u.trim_start_matches("http://").split(':').next().unwrap_or("").to_string())
        .collect()
});

pub fn node_count() -> usize {
    NODES.len()
}

fn node_urls() -> Vec<String> {
    std::env::var("NODE_URLS")
        .unwrap_or_else(|_| "http://raft1:8000,http://raft2:8000,http://raft3:8000".into())
        .split(',')
        .map(String::from)
        .collect()
}
const EVENTUALLY_P: f64 = 0.0001;
/// TLC cannot follow a behaviour past 65,535 states, so the streaming check
/// dies at that many events. The eventually starts before that.
const TRACE_LIMIT: u64 = 55_000;
/// Operations per second across all workers. Every add and every
/// linearizable read is a log entry, and trace validation cost grows with the
/// number of steps, so the rates are low.
const DEFAULT_ADD_RATE: f64 = 5.0;
const DEFAULT_LINEAR_RATE: f64 = 2.0;
const DEFAULT_STALE_RATE: f64 = 5.0;
/// Leadership transfers per second. Each one stops writes for up to an
/// election timeout and causes an election.
const DEFAULT_TRANSFER_RATE: f64 = 0.1;
/// Snapshots asked for per second, in a build whose nodes take snapshots.
/// The nodes also take them on their own, by how much they have applied.
const DEFAULT_SNAPSHOT_RATE: f64 = 0.3;

/// Whether the nodes run with pre-votes (the build's PREVOTE setting).
fn prevote() -> bool {
    std::env::var("PREVOTE").map_or(true, |v| v != "0")
}

/// Whether the nodes take snapshots (the build's SNAPSHOTS setting).
fn snapshots() -> bool {
    std::env::var("SNAPSHOTS").map_or(false, |v| v == "1")
}

/// A reachability assertion whose name is chosen while the driver runs: the
/// pre-vote paths exist only in a build with pre-votes, and an assertion
/// made with the SDK's macros is expected in every build. `hit` false
/// declares the assertion, so that a run which never reaches it says so.
pub fn reach(name: &str, details: &Value, hit: bool) {
    antithesis_sdk::assert::assert_raw(
        true,
        name.to_string(),
        details,
        String::new(),
        String::new(),
        String::new(),
        0,
        0,
        hit,
        true,
        antithesis_sdk::assert::AssertType::Reachability,
        "Reachable".to_string(),
        name.to_string(),
    );
}

/// The steps of an election with pre-votes, noted by the stream check or
/// seen in a node's log (logs.rs).
pub const PREVOTE_PATHS: [(&str, &str); 5] = [
    ("P-prevote-election", "a node starts an election on a quorum of pre-votes"),
    ("pre-vote campaign failed", "a pre-vote campaign fails"),
    ("rejecting pre-vote request since we have a leader",
     "a pre-vote is refused because the node knows of a leader"),
    ("rejecting pre-vote request since our last term is greater",
     "a pre-vote is refused because the candidate's last log term is behind"),
    ("rejecting pre-vote request since our last index is greater",
     "a pre-vote is refused because the candidate's log is shorter"),
];

/// The steps of snapshots, noted by the stream check
/// (spec/RaftBinding.tla, SnapshotNotes). Expected only in a build whose
/// nodes take snapshots.
pub const SNAPSHOT_PATHS: [(&str, &str); 5] = [
    ("S-snapshot-taken", "a node takes a snapshot"),
    ("S-log-compacted", "a node deletes from its log what its snapshot covers"),
    ("S-snapshot-installed", "a node installs a snapshot it was sent"),
    ("S-snapshot-replaces-log", "a node that installs a snapshot discards a log that does not continue it"),
    ("S-restart-from-snapshot", "a node restarts from a snapshot"),
];

/// A token bucket: `rate` tokens per second, holding at most one second's worth.
struct Bucket {
    rate: f64,
    state: Mutex<(f64, Instant)>,
}

impl Bucket {
    fn new(env: &str, default: f64) -> Self {
        let rate = std::env::var(env).ok().and_then(|v| v.parse().ok()).unwrap_or(default);
        Bucket { rate, state: Mutex::new((0.0, Instant::now())) }
    }

    /// Takes a token if there is one. Without one, waits briefly so idle
    /// workers do not spin.
    fn take(&self) -> bool {
        let got = {
            let mut b = self.state.lock().unwrap_or_else(|e| e.into_inner());
            let now = Instant::now();
            b.0 = (b.0 + now.duration_since(b.1).as_secs_f64() * self.rate).min(self.rate.max(1.0));
            b.1 = now;
            if b.0 >= 1.0 {
                b.0 -= 1.0;
                true
            } else {
                false
            }
        };
        if !got {
            std::thread::sleep(Duration::from_millis(20));
        }
        got
    }
}

fn log(msg: &str) {
    eprintln!("driver: {msg}");
}

enum Resp {
    Ok(Value),
    /// The server answered with an error body.
    Err(u16, Value),
    /// No answer: connection refused, reset or timed out.
    NoAnswer(String),
}

struct Client {
    agent: ureq::Agent,
    urls: Vec<String>,
}

impl Client {
    fn new() -> Self {
        let urls = node_urls();
        let agent = ureq::AgentBuilder::new()
            .timeout_connect(Duration::from_millis(500))
            .timeout(Duration::from_secs(3))
            .build();
        Client { agent, urls }
    }

    fn call(&self, node: usize, method: &str, path: &str) -> Resp {
        let url = format!("{}{}", self.urls[node], path);
        match self.agent.request(method, &url).call() {
            Ok(r) => match r.into_json::<Value>() {
                Ok(v) => Resp::Ok(v),
                Err(e) => Resp::NoAnswer(format!("bad body: {e}")),
            },
            Err(ureq::Error::Status(code, r)) => Resp::Err(code, r.into_json::<Value>().unwrap_or(Value::Null)),
            Err(e) => Resp::NoAnswer(e.to_string()),
        }
    }
}

fn node_index(name: &str) -> Option<usize> {
    NODES.iter().position(|n| *n == name)
}

fn state_from(v: &Value) -> Option<StateAt> {
    Some(StateAt {
        index: v["index"].as_u64()?,
        term: v["term"].as_u64()?,
        sum: v["sum"].as_i64()?,
        count: v["count"].as_u64()?,
        digest: v["digest"].as_str()?.parse().ok()?,
        node: v["node"].as_str()?.to_string(),
    })
}

struct Driver {
    client: Client,
    model: Arc<Mutex<Model>>,
    logs: Arc<Logs>,
    leader_hint: AtomicUsize,
    /// Every rule holds a read guard while it acts; the eventually takes the
    /// write guard, so it starts once in-flight requests finish.
    quiesce: RwLock<()>,
    eventually_lock: Mutex<()>,
    eventually_enabled: bool,
    trace: trace::Trace,
    add_bucket: Bucket,
    linear_bucket: Bucket,
    stale_bucket: Bucket,
    transfer_bucket: Bucket,
    snapshot_bucket: Bucket,
}

impl Driver {
    fn model(&self) -> std::sync::MutexGuard<'_, Model> {
        self.model.lock().unwrap_or_else(|e| e.into_inner())
    }

    fn update_hint(&self, body: &Value) {
        if let Some(i) = body["leader"].as_str().and_then(node_index) {
            self.leader_hint.store(i, Ordering::Relaxed);
        }
    }

    /// Picks the node a leader-only request goes to: usually the believed
    /// leader, sometimes any node, so followers' redirects get exercised.
    fn pick_target(&self, tc: &TestCase) -> usize {
        if tc.draw(gs::weighted_booleans(0.8)) {
            self.leader_hint.load(Ordering::Relaxed)
        } else {
            tc.draw(gs::integers::<usize>().max_value(NODES.len() - 1))
        }
    }

    /// Sends one add and records its outcome. Returns the leader hint from
    /// a not-leader response, if any.
    fn add_once(&self, node: usize, value: i64) -> (Outcome, Option<usize>) {
        let op = self.model().send(value);
        let resp = self.client.call(node, "POST", &format!("/add?op={op}&value={value}"));
        let (outcome, hint) = match &resp {
            Resp::Ok(v) => match (v["index"].as_u64(), v["sum"].as_i64()) {
                (Some(index), Some(sum)) => {
                    self.leader_hint.store(node, Ordering::Relaxed);
                    (Outcome::Acked { index, sum }, None)
                }
                _ => (Outcome::Unknown, None),
            },
            Resp::Err(_, b) if b["error"] == "not_leader" => {
                self.update_hint(b);
                (Outcome::Rejected, b["leader"].as_str().and_then(node_index))
            }
            Resp::Err(_, b) if b["error"] == "enqueue_timeout" => (Outcome::Rejected, None),
            Resp::Err(..) | Resp::NoAnswer(_) => (Outcome::Unknown, None),
        };
        if outcome == Outcome::Unknown {
            assert_reachable!(
                "a write's outcome is unknown to the client",
                &json!({"node": NODES[node], "op": op, "resp": match &resp {
                    Resp::Err(c, b) => json!({"code": c, "body": b}),
                    Resp::NoAnswer(e) => json!(e),
                    Resp::Ok(v) => v.clone(),
                }})
            );
        }
        self.model().complete(op, outcome, &NODES[node]);
        (outcome, hint)
    }

    fn most_lagging(&self) -> Option<usize> {
        let s = self.logs.states.lock().unwrap_or_else(|e| e.into_inner());
        s.nodes.iter().min_by_key(|(_, n)| n.applied).and_then(|(c, _)| node_index(c))
    }

    /// Retries a linearizable read, following not-leader hints, until one
    /// succeeds or the deadline passes.
    fn linear_read_until(&self, first: usize, deadline: Instant) -> Option<StateAt> {
        let mut target = first;
        let mut attempts = 0usize;
        while Instant::now() < deadline {
            attempts += 1;
            match self.client.call(target, "GET", "/sum") {
                Resp::Ok(v) => return state_from(&v),
                Resp::Err(_, b) if b["error"] == "not_leader" => {
                    target = b["leader"].as_str().and_then(node_index).unwrap_or((target + 1) % NODES.len());
                }
                _ => target = (target + 1) % NODES.len(),
            }
            if attempts > 1 {
                std::thread::sleep(Duration::from_millis(200));
            }
        }
        None
    }

    fn eventually(&self) {
        let Ok(_once) = self.eventually_lock.try_lock() else { return };
        let _quiet = self.quiesce.write().unwrap_or_else(|e| e.into_inner());
        log("eventually: stopping faults");
        if let Ok(cmd) = std::env::var("ANTITHESIS_STOP_FAULTS") {
            match std::process::Command::new(&cmd).arg("3600").status() {
                Ok(s) => log(&format!("eventually: {cmd} exited {s}")),
                Err(e) => log(&format!("eventually: cannot run {cmd}: {e}")),
            }
        }

        // 1. Recovery: every node answers, they agree on a leader, and a
        //    write through it commits.
        let deadline = Instant::now() + Duration::from_secs(180);
        let mut recovered = None;
        let mut last_wait = String::new();
        // Nodes that have answered since the faults stopped. A node that the
        // fault injector stopped and has not started again cannot recover,
        // whatever raft does; that is reported under its own name.
        let mut answered = vec![false; NODES.len()];
        while Instant::now() < deadline {
            let statuses: Vec<Option<Value>> = (0..NODES.len())
                .map(|i| match self.client.call(i, "GET", "/status") {
                    Resp::Ok(v) => Some(v),
                    _ => None,
                })
                .collect();
            for (i, s) in statuses.iter().enumerate() {
                answered[i] |= s.is_some();
            }
            let wait = describe_statuses(&statuses);
            if wait != last_wait {
                log(&format!("eventually: waiting for recovery: {wait}"));
                last_wait = wait;
            }
            if let Some(leader) = agreed_leader(&statuses) {
                let value = 1;
                if let (Outcome::Acked { index, .. }, _) = self.add_once(leader, value) {
                    recovered = Some((leader, index));
                    break;
                }
            }
            std::thread::sleep(Duration::from_millis(250));
        }
        log("eventually: assertions start");
        let silent: Vec<&String> = NODES.iter().zip(&answered).filter(|(_, a)| !**a).map(|(n, _)| n).collect();
        assert_always!(
            silent.is_empty(),
            "every node is running again within three minutes of the faults stopping",
            &json!({"never_answered": silent, "waiting_for": last_wait})
        );
        if silent.is_empty() {
            assert_always!(
                recovered.is_some(),
                "the cluster recovers once faults stop",
                &json!({"waiting_for": last_wait})
            );
        }
        let Some((leader, write_index)) = recovered else {
            self.check_trace();
            log("eventually: ending timeline (cluster did not recover)");
            std::process::exit(0);
        };

        // 2. Convergence: every node applies up to that write, and they hold
        //    the same state there.
        let deadline = Instant::now() + Duration::from_secs(60);
        let mut states: Vec<Option<StateAt>> = vec![None; NODES.len()];
        while Instant::now() < deadline {
            for i in 0..NODES.len() {
                if let Resp::Ok(v) = self.client.call(i, "GET", "/sum?mode=stale") {
                    states[i] = state_from(&v);
                }
            }
            if states.iter().all(|s| s.as_ref().is_some_and(|s| s.index >= write_index)) {
                break;
            }
            std::thread::sleep(Duration::from_millis(250));
        }
        let converged = states.iter().all(|s| s.as_ref().is_some_and(|s| s.index >= write_index));
        let summary: Vec<Value> = states
            .iter()
            .map(|s| match s {
                Some(s) => json!({"node": s.node, "index": s.index, "sum": s.sum, "count": s.count, "digest": s.digest.to_string()}),
                None => Value::Null,
            })
            .collect();
        let same = converged && {
            let s0 = states[0].as_ref().unwrap();
            states.iter().flatten().all(|s| (s.index, s.sum, s.count, s.digest) == (s0.index, s0.sum, s0.count, s0.digest))
        };
        assert_always!(
            converged && same,
            "every node converges to the same state once faults stop",
            &json!({"write_index": write_index, "states": summary})
        );

        // 3. Durability: a linearizable read covers every acknowledged
        //    write, and matches the history the nodes applied.
        // Leadership can still move after recovery (a node that ran for
        // election during a partition has a higher term), so follow it.
        let read = self.linear_read_until(leader, Instant::now() + Duration::from_secs(60));
        std::thread::sleep(Duration::from_secs(1)); // Let the last log lines arrive.
        let max_acked = self.model().max_acked_index;
        assert_always!(
            read.as_ref().is_some_and(|r| r.index >= max_acked),
            "acknowledged writes survive once faults stop",
            &json!({"read": read.as_ref().map(|r| json!({"index": r.index, "sum": r.sum})), "max_acked_index": max_acked})
        );
        {
            let m = self.model();
            let mut missing = Vec::new();
            for (op, index) in m.acked_ops() {
                if let Some(a) = m.applied_at(index) {
                    if a.op != op {
                        missing.push(json!({"op": op, "index": index, "applied_op": a.op}));
                    }
                }
            }
            assert_always!(
                missing.is_empty(),
                "every acknowledged write is in the final history",
                &json!({"missing": missing})
            );
        }
        if let Some(r) = read {
            self.model().observe_state(r, StateSource::LinearRead);
        }
        self.check_trace();
        log("eventually: ending timeline");
        std::process::exit(0);
    }

    /// At the end of a timeline the stream check should have matched
    /// everything the nodes did up to now.
    fn check_trace(&self) {
        let deadline = Instant::now() + Duration::from_secs(60);
        if self.trace.checking {
            let written = self.trace.events.load(Ordering::Relaxed);
            while self.trace.matched() < written && !self.trace.stopped() && Instant::now() < deadline {
                std::thread::sleep(Duration::from_millis(100));
            }
            let matched = self.trace.matched();
            report_notes(&self.trace);
            log(&format!("eventually: stream check matched {matched} events, {written} written before it was asked"));
            if !self.trace.stopped() {
                assert_always!(
                    matched >= written,
                    "the stream check keeps up with the run",
                    &json!({"written": written, "matched": matched})
                );
                if matched >= written {
                    assert_reachable!(
                        "a timeline's whole stream is matched by the model",
                        &json!({"events": matched})
                    );
                }
            }
        }
    }
}

/// Steps of a leadership transfer or of an election with pre-votes that
/// the stream check noted (spec/RaftBinding.tla, TransferNotes). Returns
/// whether the note was one of these.
fn report_transfer_note(k: u64, name: &str) -> bool {
    // A property that a step broke is noted under its own name (no hyphen).
    // The check's verdict reports it.
    if !name.contains('-') {
        return true;
    }
    let details = json!({"event_index": k});
    match name {
        "T-timeoutnow-late" => assert_reachable!(
            "a node that no longer leads sends a TimeoutNow request",
            &details
        ),
        "T-timeoutnow-to-leader" => assert_reachable!(
            "a TimeoutNow request makes a leader a candidate",
            &details
        ),
        "T-transfer-election" => assert_reachable!(
            "a node starts an election on a leader's order",
            &details
        ),
        "P-prevote-election" => reach(PREVOTE_PATHS[0].1, &details, true),
        _ => match SNAPSHOT_PATHS.iter().find(|(note, _)| *note == name) {
            Some((_, path)) => reach(path, &details, true),
            None => return false,
        },
    }
    true
}

/// Reports the steps the stream check noted. The only note that is not a
/// step worth reaching is of a step raft should never take: a node rejects
/// the request that continues from its snapshot (patches/README.md, R4).
fn report_notes(trace: &trace::Trace) {
    for (k, name) in trace.new_notes() {
        if report_transfer_note(k, &name) {
            continue;
        }
        antithesis_sdk::assert_unreachable!(
            "a node rejects the request that continues from its snapshot",
            &json!({"event_index": k, "note": name})
        );
    }
}

fn describe_statuses(statuses: &[Option<Value>]) -> String {
    statuses
        .iter()
        .enumerate()
        .map(|(i, s)| match s {
            Some(v) => format!("{}={}/t{}/leader={}", NODES[i], v["state"], v["term"], v["leader"]),
            None => format!("{}=down", NODES[i]),
        })
        .collect::<Vec<_>>()
        .join(" ")
}

/// The node every node agrees is leader, in the same term.
fn agreed_leader(statuses: &[Option<Value>]) -> Option<usize> {
    let all: Vec<&Value> = statuses.iter().flatten().collect();
    if all.len() != NODES.len() {
        return None;
    }
    let leader = all[0]["leader"].as_str()?;
    let term = all[0]["term"].as_u64()?;
    let ok = all.iter().all(|v| v["leader"].as_str() == Some(leader) && v["term"].as_u64() == Some(term));
    let i = node_index(leader)?;
    (ok && statuses[i].as_ref()?["state"] == "leader").then_some(i)
}

impl Driver {
    fn add(&self, tc: TestCase) {
        let target = self.pick_target(&tc);
        let value = tc.draw(gs::integers::<i64>().min_value(-1000).max_value(1000));
        let retry = tc.draw(gs::weighted_booleans(0.9));
        if !self.add_bucket.take() {
            return;
        }
        let _g = self.quiesce.read().unwrap_or_else(|e| e.into_inner());
        let (outcome, hint) = self.add_once(target, value);
        // A real client follows the redirect once, as a new request.
        if let (Outcome::Rejected, Some(leader), true) = (outcome, hint, retry) {
            if leader != target {
                if let (Outcome::Acked { .. }, _) = self.add_once(leader, value) {
                    assert_reachable!("a write redirected to the leader succeeds", &json!({}));
                }
            }
        }
    }

    fn linear_read(&self, tc: TestCase) {
        let target = self.pick_target(&tc);
        if !self.linear_bucket.take() {
            return;
        }
        let _g = self.quiesce.read().unwrap_or_else(|e| e.into_inner());
        let (acked_floor, read_floor) = {
            let m = self.model();
            (m.max_acked_index, m.max_linear_read_index)
        };
        match self.client.call(target, "GET", "/sum") {
            Resp::Ok(v) => {
                let st = state_from(&v);
                assert_always!(st.is_some(), "a linearizable read returns a well-formed state", &json!({"body": v}));
                let Some(st) = st else { return };
                self.leader_hint.store(target, Ordering::Relaxed);
                assert_always!(
                    st.index >= acked_floor,
                    "a linearizable read reflects every write acknowledged before it started",
                    &json!({"node": st.node, "read_index": st.index, "max_acked_index_at_start": acked_floor})
                );
                assert_always!(
                    st.index >= read_floor,
                    "a linearizable read never returns an older state than a completed one",
                    &json!({"node": st.node, "read_index": st.index, "max_read_index_at_start": read_floor})
                );
                let mut m = self.model();
                m.max_linear_read_index = m.max_linear_read_index.max(st.index);
                m.observe_state(st, StateSource::LinearRead);
            }
            Resp::Err(_, b) if b["error"] == "not_leader" => self.update_hint(&b),
            Resp::Err(..) | Resp::NoAnswer(_) => {
                assert_reachable!("a linearizable read fails without an answer", &json!({"node": NODES[target]}));
            }
        }
    }

    fn stale_read(&self, tc: TestCase) {
        let random = tc.draw(gs::integers::<usize>().max_value(NODES.len() - 1));
        // Half the time, read from the node furthest behind, by its logs.
        let target = if tc.draw(gs::booleans()) { self.most_lagging().unwrap_or(random) } else { random };
        if !self.stale_bucket.take() {
            return;
        }
        let _g = self.quiesce.read().unwrap_or_else(|e| e.into_inner());
        let acked_floor = self.model().max_acked_index;
        if let Resp::Ok(v) = self.client.call(target, "GET", "/sum?mode=stale") {
            if let Some(st) = state_from(&v) {
                assert_sometimes_greater_than!(
                    acked_floor as i64 - st.index as i64,
                    50i64,
                    "a stale read trails acknowledged writes by more than 50 entries",
                    &json!({"node": st.node, "read_index": st.index, "max_acked_index_at_start": acked_floor})
                );
                self.model().observe_state(st, StateSource::StaleRead);
            }
        }
    }

    /// Asks a node to hand its leadership to another. The node picks the
    /// follower that is furthest along.
    fn transfer(&self, tc: TestCase) {
        let target = self.pick_target(&tc);
        if !self.transfer_bucket.take() {
            return;
        }
        let _g = self.quiesce.read().unwrap_or_else(|e| e.into_inner());
        match self.client.call(target, "POST", "/transfer") {
            Resp::Ok(_) => {
                assert_reachable!("a leadership transfer completes", &json!({"node": NODES[target]}));
            }
            Resp::Err(_, b) if b["error"] == "not_leader" => self.update_hint(&b),
            Resp::Err(_, b) if b["error"] == "transfer" => {
                assert_reachable!(
                    "a leadership transfer fails",
                    &json!({"node": NODES[target], "detail": b["detail"]})
                );
            }
            Resp::Err(..) | Resp::NoAnswer(_) => {}
        }
    }

    /// Asks a node to take a snapshot now, whatever it has applied since its
    /// last. Half the time the node asked is the one furthest behind.
    fn snapshot(&self, tc: TestCase) {
        let random = tc.draw(gs::integers::<usize>().max_value(NODES.len() - 1));
        let target = if tc.draw(gs::booleans()) { self.most_lagging().unwrap_or(random) } else { random };
        if !self.snapshot_bucket.take() {
            return;
        }
        let _g = self.quiesce.read().unwrap_or_else(|e| e.into_inner());
        if let Resp::Ok(v) = self.client.call(target, "POST", "/snapshot") {
            if v["nothing_new"] == false {
                reach("a node takes a snapshot when asked", &json!({"node": NODES[target]}), true);
            }
        }
    }

    fn eventually_rule(&self, tc: TestCase) {
        if !self.eventually_enabled {
            return;
        }
        let full = self.trace.checking && self.trace.events.load(Ordering::Relaxed) >= TRACE_LIMIT;
        if tc.draw(gs::weighted_booleans(EVENTUALLY_P)) || full {
            self.eventually();
        }
    }
}

/// Waits until every node answers and a linearizable read succeeds.
fn wait_for_cluster(client: &Client) {
    let mut last = String::new();
    loop {
        let statuses: Vec<Option<Value>> = (0..NODES.len())
            .map(|i| match client.call(i, "GET", "/status") {
                Resp::Ok(v) => Some(v),
                _ => None,
            })
            .collect();
        let mut msg = describe_statuses(&statuses);
        if let Some(leader) = agreed_leader(&statuses) {
            match client.call(leader, "GET", "/sum") {
                Resp::Ok(_) => {
                    log(&format!("cluster ready: {msg}"));
                    return;
                }
                Resp::Err(c, b) => msg.push_str(&format!(" read={c} {b}")),
                Resp::NoAnswer(e) => msg.push_str(&format!(" read={e}")),
            }
        }
        if msg != last {
            log(&format!("waiting for cluster: {msg}"));
            last = msg;
        }
        std::thread::sleep(Duration::from_millis(200));
    }
}

#[hegel::main(phases = [hegel::Phase::Generate])]
fn main(tc: TestCase) {
    antithesis_sdk::antithesis_init();
    log(&format!(
        "net.unix.max_dgram_qlen={}",
        std::fs::read_to_string("/proc/sys/net/unix/max_dgram_qlen").unwrap_or_default().trim()
    ));
    let mut steps = steps::Steps::default();
    let trace = trace::start(move |ev| steps.observe(ev));
    {
        let trace = trace.clone();
        std::thread::spawn(move || loop {
            report_notes(&trace);
            std::thread::sleep(Duration::from_millis(200));
        });
    }
    let model = Arc::new(Mutex::new(Model::new()));
    let logs = Logs::start(model.clone());
    let client = Client::new();

    wait_for_cluster(&client);
    antithesis_sdk::lifecycle::setup_complete(&json!({"nodes": &*NODES}));
    log("setup complete; waiting for /workload-active");
    while !std::path::Path::new("/workload-active").exists() {
        std::thread::sleep(Duration::from_millis(100));
    }
    logs.active.store(true, Ordering::Relaxed);
    assert_reachable!("the workload starts", &json!({}));
    if prevote() {
        for (_, name) in PREVOTE_PATHS {
            reach(name, &json!({}), false);
        }
    }
    if snapshots() {
        for (_, name) in SNAPSHOT_PATHS {
            reach(name, &json!({}), false);
        }
        reach("a node takes a snapshot when asked", &json!({}), false);
    }
    log("workload active");

    let eventually_enabled = std::env::var("DRIVER_EVENTUALLY").map_or(true, |v| v != "off");
    let driver = Arc::new(Driver {
        client,
        model,
        logs,
        leader_hint: AtomicUsize::new(0),
        quiesce: RwLock::new(()),
        eventually_lock: Mutex::new(()),
        eventually_enabled,
        trace,
        add_bucket: Bucket::new("DRIVER_ADD_RATE", DEFAULT_ADD_RATE),
        linear_bucket: Bucket::new("DRIVER_LINEAR_RATE", DEFAULT_LINEAR_RATE),
        stale_bucket: Bucket::new("DRIVER_STALE_RATE", DEFAULT_STALE_RATE),
        transfer_bucket: Bucket::new("DRIVER_TRANSFER_RATE", DEFAULT_TRANSFER_RATE),
        snapshot_bucket: Bucket::new("DRIVER_SNAPSHOT_RATE", if snapshots() { DEFAULT_SNAPSHOT_RATE } else { 0.0 }),
    });
    // For the local loop: run the eventually after a fixed time.
    if let Some(secs) = std::env::var("DRIVER_EVENTUALLY_AFTER").ok().and_then(|v| v.parse::<u64>().ok()) {
        let d = driver.clone();
        std::thread::spawn(move || {
            std::thread::sleep(Duration::from_secs(secs));
            d.eventually();
        });
    }
    machine(ArcDriver(driver)).max_concurrency(4).steps(i64::MAX).run_concurrent(tc);
}

/// The machine owns its model; this wrapper lets the eventually thread share it.
struct ArcDriver(Arc<Driver>);

#[hegel::concurrent_state_machine]
impl ArcDriver {
    #[rule(weight = 10.0)]
    fn add(&self, tc: TestCase) {
        self.0.add(tc)
    }

    #[rule(weight = 4.0)]
    fn linear_read(&self, tc: TestCase) {
        self.0.linear_read(tc)
    }

    #[rule(weight = 3.0)]
    fn stale_read(&self, tc: TestCase) {
        self.0.stale_read(tc)
    }

    #[rule(weight = 1.0)]
    fn transfer(&self, tc: TestCase) {
        self.0.transfer(tc)
    }

    #[rule(weight = 1.0)]
    fn snapshot(&self, tc: TestCase) {
        self.0.snapshot(tc)
    }

    #[rule(weight = 1.0)]
    fn eventually_rule(&self, tc: TestCase) {
        self.0.eventually_rule(tc)
    }
}
