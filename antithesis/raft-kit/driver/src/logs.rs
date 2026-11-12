//! Receives the nodes' forwarded log lines and checks the guarantees that
//! need several nodes' state: at most one leader per term, terms that never
//! go backwards, and (through the model) state machine safety. Also notes
//! which of raft's fault-only paths a run reached, from raft's own warnings.

use crate::model::{Applied, Model, StateAt, StateSource};
use antithesis_sdk::{assert_always, assert_reachable, assert_sometimes, assert_sometimes_greater_than};
use serde::Deserialize;
use serde_json::json;
use std::collections::{BTreeMap, HashMap};
use std::os::unix::fs::PermissionsExt;
use std::os::unix::net::UnixDatagram;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::mpsc::{sync_channel};
use std::sync::{Arc, Mutex};

pub const SOCKET: &str = "/logs/driver.sock";

#[derive(Deserialize)]
struct Datagram {
    container: String,
    boot: u128,
    seq: u64,
    line: String,
}

#[derive(Default, Clone)]
pub struct NodeState {
    pub boot: u128,
    pub boots: u64,
    pub seq: u64,
    pub role: String,
    pub term: u64,
    pub applied: u64,
}

#[derive(Default)]
pub struct NodeStates {
    pub nodes: HashMap<String, NodeState>,
    /// Highest term each container ever reported, across restarts.
    max_term: HashMap<String, u64>,
    /// The first container seen as leader of each term. Never forgotten.
    leaders: BTreeMap<u64, String>,
}

fn fields(line: &str) -> HashMap<&str, &str> {
    line.split_whitespace().filter_map(|t| t.split_once('=')).collect()
}

fn num<T: std::str::FromStr>(f: &HashMap<&str, &str>, k: &str) -> Option<T> {
    f.get(k).and_then(|v| v.parse().ok())
}

/// Asks for a large receive buffer, so a briefly stalled driver doesn't drop
/// lines. The kernel caps it at net.core.rmem_max.
fn set_rcvbuf(sock: &UnixDatagram, bytes: libc::c_int) {
    use std::os::fd::AsRawFd;
    let fd = sock.as_raw_fd();
    for opt in [libc::SO_RCVBUFFORCE, libc::SO_RCVBUF] {
        // SAFETY: fd is a valid socket and the value is a c_int.
        let r = unsafe {
            libc::setsockopt(fd, libc::SOL_SOCKET, opt, &bytes as *const _ as *const libc::c_void,
                std::mem::size_of::<libc::c_int>() as libc::socklen_t)
        };
        if r == 0 {
            break;
        }
    }
}

/// Raft's own log messages for paths that only faults reach. Seeing one in a
/// node's forwarded log is the evidence that the run got there. The forwarder
/// passes these lines on because LOG_FORWARD_MATCH (the compose file) names
/// the start of each message.
const RARE_PATHS: [(&str, &str); 6] = [
    ("Election timeout reached", "an election times out without a winner"),
    ("failed to contact quorum of nodes", "a leader steps down after losing contact with a quorum"),
    ("previous log term mis-match", "a follower rejects entries whose previous log term mismatches"),
    ("rejecting vote request since our last term is greater",
     "a vote is refused because the candidate's last log term is behind"),
    ("rejecting vote request since our last index is greater",
     "a vote is refused because the candidate's log is shorter"),
    ("peer has newer term", "a leader learns from a follower that its term is stale"),
];

fn rare_path(d: &Datagram) {
    let details = json!({"node": d.container, "line": d.line});
    // One macro call per message: an assertion's name must be a literal.
    macro_rules! seen {
        ($i:expr, $name:literal) => {
            debug_assert_eq!(RARE_PATHS[$i].1, $name);
            if d.line.contains(RARE_PATHS[$i].0) {
                assert_reachable!($name, &details);
            }
        };
    }
    seen!(0, "an election times out without a winner");
    seen!(1, "a leader steps down after losing contact with a quorum");
    seen!(2, "a follower rejects entries whose previous log term mismatches");
    seen!(3, "a vote is refused because the candidate's last log term is behind");
    seen!(4, "a vote is refused because the candidate's log is shorter");
    seen!(5, "a leader learns from a follower that its term is stale");
}

pub struct Logs {
    pub states: Mutex<NodeStates>,
    pub model: Arc<Mutex<Model>>,
    pub active: AtomicBool,
}

impl Logs {
    /// Binds the socket and starts the receiving and recording threads.
    pub fn start(model: Arc<Mutex<Model>>) -> Arc<Logs> {
        let logs = Arc::new(Logs { states: Mutex::new(NodeStates::default()), model, active: AtomicBool::new(false) });
        let _ = std::fs::remove_file(SOCKET);
        let sock = match UnixDatagram::bind(SOCKET) {
            Ok(s) => s,
            Err(e) => {
                eprintln!("driver: cannot bind {SOCKET}: {e}; log checks disabled");
                return logs;
            }
        };
        let _ = std::fs::set_permissions(SOCKET, std::fs::Permissions::from_mode(0o777));
        set_rcvbuf(&sock, 8 << 20);
        let (tx, rx) = sync_channel::<Vec<u8>>(1000);
        std::thread::spawn(move || {
            let mut buf = vec![0u8; 65536];
            loop {
                match sock.recv(&mut buf) {
                    // Block when the recorder is behind: the forwarders hold
                    // their lines until the socket has room again. Dropping
                    // here would lose a line silently.
                    Ok(n) => {
                        if tx.send(buf[..n].to_vec()).is_err() {
                            return;
                        }
                    }
                    Err(e) => eprintln!("driver: log socket recv: {e}"),
                }
            }
        });
        let l = logs.clone();
        std::thread::spawn(move || {
            for d in rx {
                match serde_json::from_slice::<Datagram>(&d) {
                    Ok(d) => l.record(d),
                    Err(e) => eprintln!("driver: bad log datagram: {e}"),
                }
            }
        });
        logs
    }

    fn record(&self, d: Datagram) {
        let f = fields(&d.line);
        let msg = f.get("msg").copied().unwrap_or("");
        if msg.is_empty() {
            rare_path(&d);
        }
        let active = self.active.load(Ordering::Relaxed);

        // Node state first; never hold this lock and the model lock at once.
        let apply_or_restore = {
            let mut s = self.states.lock().unwrap_or_else(|e| e.into_inner());
            let st = s.nodes.entry(d.container.clone()).or_default();
            if st.boot == d.boot && st.boots > 0 {
                assert_always!(
                    d.seq == st.seq + 1,
                    "the driver receives every forwarded log line",
                    &json!({"container": d.container, "seq": d.seq, "last_seq": st.seq})
                );
            } else {
                let boots = st.boots + 1;
                *st = NodeState { boot: d.boot, boots, ..Default::default() };
            }
            st.seq = d.seq;

            match msg {
                "raft-state" => {
                    let (Some(role), Some(term)) = (f.get("role").copied(), num::<u64>(&f, "term")) else {
                        eprintln!("driver: unparsable state line from {}: {}", d.container, d.line);
                        return;
                    };
                    assert_reachable!("the driver reads a node's role and term from its logs", &json!({}));
                    st.role = role.to_string();
                    st.term = term;
                    let max = s.max_term.entry(d.container.clone()).or_default();
                    assert_always!(
                        term >= *max,
                        "a node's term never goes backwards, even across restarts",
                        &json!({"container": d.container, "term": term, "max_term_seen": *max})
                    );
                    *max = (*max).max(term);
                    if role == "leader" {
                        let first = s.leaders.entry(term).or_insert_with(|| d.container.clone()).clone();
                        assert_always!(
                            first == d.container,
                            "at most one node becomes leader in each term",
                            &json!({"term": term, "first_leader": first, "second_leader": d.container})
                        );
                    }
                    if active {
                        let terms: Vec<u64> = s.nodes.values().map(|n| n.term).collect();
                        let differ = terms.iter().any(|&t| t != terms[0]);
                        assert_sometimes!(
                            differ,
                            "nodes disagree on the current term",
                            &json!({"terms": terms})
                        );
                    }
                    None
                }
                "raft-apply" | "raft-restore" => {
                    let parsed = (
                        num::<u64>(&f, "index"),
                        num::<u64>(&f, "term"),
                        num::<i64>(&f, "sum"),
                        num::<u64>(&f, "count"),
                        num::<u64>(&f, "digest"),
                    );
                    let (Some(index), Some(term), Some(sum), Some(count), Some(digest)) = parsed else {
                        eprintln!("driver: unparsable line from {}: {}", d.container, d.line);
                        return;
                    };
                    st.applied = index;
                    let boots = st.boots;
                    if active {
                        let leader_applied =
                            s.nodes.values().filter(|n| n.role == "leader").map(|n| n.applied).max().unwrap_or(0);
                        let min_applied = s.nodes.values().map(|n| n.applied).min().unwrap_or(0);
                        if s.nodes.len() == 3 {
                            assert_sometimes_greater_than!(
                                leader_applied.saturating_sub(min_applied),
                                100u64,
                                "a node falls more than 100 entries behind the leader",
                                &json!({"leader_applied": leader_applied, "min_applied": min_applied})
                            );
                        }
                    }
                    Some((index, term, sum, count, digest, boots))
                }
                _ => None,
            }
        };

        let Some((index, term, sum, count, digest, boots)) = apply_or_restore else { return };
        let mut m = self.model.lock().unwrap_or_else(|e| e.into_inner());
        if msg == "raft-apply" {
            let (Some(op), Some(value)) = (num::<u64>(&f, "op"), num::<i64>(&f, "value")) else {
                // A malformed op is one the workload never wrote.
                assert_always!(false, "nodes apply only commands the workload sent", &json!({"line": d.line}));
                return;
            };
            assert_reachable!("the driver reads applied commands from a node's logs", &json!({}));
            if active && boots > 1 {
                assert_reachable!(
                    "a restarted node applies commands",
                    &json!({"container": d.container, "index": index})
                );
            }
            m.record_apply(index, Applied { term, op, value, sum, count, digest, node: d.container.clone() });
        } else {
            m.observe_state(
                StateAt { index, term, sum, count, digest, node: d.container.clone() },
                StateSource::Restore,
            );
        }
    }
}
