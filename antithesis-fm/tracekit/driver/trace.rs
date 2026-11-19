//! Trace collector and stream check runner. Independent of the system under
//! test except for the default manifest path and the separately named
//! CommitBeyondConfirmed violation.
//!
//! Programs report steps as datagrams on a Unix socket (tracekit.Sink):
//!
//!   {"container": "raft1", "boot": "<start nanos>", "seq": 7, "ev": {...}}
//!
//! `ev`, with `boot`, `seq` and `node` added, is appended to
//! `<dir>/stream.ndjson` in arrival order and to `<dir>/<container>.ndjson`.
//! Senders block until their datagram is queued, so stream order is a
//! possible order of the steps. A hole in `seq` within one boot is written as
//! a `Gap` event, which no model action matches.
//!
//! If TRACEKIT_CHECK names the stream checker, it runs for the life of the
//! driver; its verdict becomes assertions when it stops (only on a mismatch).
//! `Trace::new_notes` returns the trace spec's Notes as they are made.
//!
//! Environment: TRACEKIT_SOCKET (default /logs/kit.sock), TRACEKIT_DIR
//! (/trace-kit), TRACEKIT_CHECK, TRACEKIT_MANIFEST, and DRIVER_PRINT_TRACE=1
//! to print the stream as `trace-kit {...}` lines.

use serde_json::{json, Value};
use std::collections::HashMap;
use std::fs::{File, OpenOptions};
use std::io::Write;
use std::os::unix::fs::PermissionsExt;
use std::os::unix::net::UnixDatagram;
use antithesis_sdk::assert_always_or_unreachable;
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use std::sync::Arc;

/// Handle on the collector and on the streaming check.
#[derive(Clone, Default)]
pub struct Trace {
    /// Events written so far, over all nodes.
    pub events: Arc<AtomicU64>,
    /// A streaming check was started.
    pub checking: bool,
    stopped: Arc<AtomicBool>,
    progress: String,
    notes_read: Arc<AtomicU64>,
}

impl Trace {
    /// Events the model has matched so far.
    pub fn matched(&self) -> u64 {
        // The checker's progress file holds the index it is waiting for.
        std::fs::read_to_string(&self.progress)
            .ok()
            .and_then(|s| s.trim().parse::<u64>().ok())
            .map_or(0, |next| next.saturating_sub(1))
    }

    /// (event index, name) of each Note made since the last call.
    pub fn new_notes(&self) -> Vec<(u64, String)> {
        let text = std::fs::read_to_string(format!("{}.notes", self.progress)).unwrap_or_default();
        // Only whole lines: the checker may be in the middle of writing one.
        let lines: Vec<&str> = text.split_inclusive('\n').filter(|l| l.ends_with('\n')).collect();
        let from = self.notes_read.swap(lines.len() as u64, Ordering::Relaxed) as usize;
        lines.iter().skip(from).filter_map(|l| {
            let (k, name) = l.trim().split_once(' ')?;
            Some((k.parse().ok()?, name.to_string()))
        }).collect()
    }

    /// The streaming check has ended; nothing after its verdict is checked.
    pub fn stopped(&self) -> bool {
        self.stopped.load(Ordering::Relaxed)
    }
}

/// Runs the streaming check (TLC, blocked on the stream file) for the life of
/// the driver and reports its verdict when it stops.
fn check_stream(stream: String, trace: Trace) {
    let Ok(checker) = std::env::var("TRACEKIT_CHECK") else { return };
    let manifest = std::env::var("TRACEKIT_MANIFEST").unwrap_or_else(|_| "/opt/kit/spec/manifest.json".into());
    std::thread::spawn(move || {
        let out = std::process::Command::new("python3").arg(&checker).arg(&manifest).arg(&stream).output();
        trace.stopped.store(true, Ordering::Relaxed);
        let text = match out {
            Ok(o) => String::from_utf8_lossy(&o.stdout).trim().to_string(),
            Err(e) => format!("ERROR cannot run {checker}: {e}"),
        };
        eprintln!("driver: stream check stopped: {}", text.chars().take(2000).collect::<String>());
        let mut parts = text.splitn(3, ' ');
        let verdict = parts.next().unwrap_or("");
        let index = parts.next().and_then(|s| s.parse::<u64>().ok()).unwrap_or(0);
        let rest = parts.next().unwrap_or("");
        let event: Value = serde_json::from_str(rest).unwrap_or(json!(rest));
        // The checker stops only on a mismatch, hence "always, or unreachable".
        let details = json!({"event_index": index, "event": event, "written": trace.events.load(Ordering::Relaxed)});
        assert_always_or_unreachable!(
            verdict == "REJECTED" || verdict == "VIOLATED",
            "the stream check runs until it has a verdict",
            &json!({"output": text.chars().take(4000).collect::<String>()})
        );
        // Rejection at a restart: the recovered state is neither the model's
        // nor the one before the last announced write. Reported separately.
        let at_restart = verdict == "REJECTED" && event["e"] == "boot";
        assert_always_or_unreachable!(
            !(verdict == "REJECTED" && !at_restart),
            "the nodes' reported steps are a behaviour of the model",
            &details
        );
        assert_always_or_unreachable!(!at_restart, "a restarted node recovers the state the model expects", &details);
        // Committing beyond what the leader confirmed is reported separately.
        let beyond = verdict == "VIOLATED" && rest.contains("CommitBeyondConfirmed");
        assert_always_or_unreachable!(
            !beyond,
            "a follower commits only what its leader has confirmed",
            &json!({"event_index": index, "violated": rest})
        );
        assert_always_or_unreachable!(
            !(verdict == "VIOLATED" && !beyond),
            "a run that follows the model keeps the model's safety properties",
            &json!({"event_index": index, "violated": rest})
        );
    });
}

struct Node {
    file: File,
    boot: String,
    seq: u64,
}

/// Starts the collector. `observe` is called with every event, in stream
/// order, after it is written; a driver can check its own properties there.
pub fn start(mut observe: impl FnMut(&Value) + Send + 'static) -> Trace {
    let socket = std::env::var("TRACEKIT_SOCKET").unwrap_or_else(|_| "/logs/kit.sock".into());
    let dir = std::env::var("TRACEKIT_DIR").unwrap_or_else(|_| "/trace-kit".into());
    let stream_path = format!("{dir}/stream.ndjson");
    let trace = Trace {
        checking: std::env::var("TRACEKIT_CHECK").is_ok(),
        progress: format!("{stream_path}.progress"),
        ..Default::default()
    };
    let handle = trace.clone();
    // With DRIVER_PRINT_TRACE=1 the stream is also printed, so a timeline's
    // trace can be recovered from the run's logs and checked again offline.
    let print = std::env::var("DRIVER_PRINT_TRACE").is_ok_and(|v| v == "1");
    if let Err(e) = std::fs::create_dir_all(&dir) {
        eprintln!("driver: cannot create {dir}: {e}; trace collection disabled");
        return handle;
    }
    let _ = std::fs::remove_file(&socket);
    let sock = match UnixDatagram::bind(&socket) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("driver: cannot bind {socket}: {e}; trace collection disabled");
            return handle;
        }
    };
    let _ = std::fs::set_permissions(&socket, std::fs::Permissions::from_mode(0o777));
    std::thread::spawn(move || {
        let mut nodes: HashMap<String, Node> = HashMap::new();
        let mut stream = OpenOptions::new().create(true).append(true).open(&stream_path).ok();
        check_stream(stream_path.clone(), trace.clone());
        let mut buf = vec![0u8; 1 << 20];
        loop {
            let n = match sock.recv(&mut buf) {
                Ok(n) => n,
                Err(e) => {
                    eprintln!("driver: trace socket recv: {e}");
                    continue;
                }
            };
            let Ok(d) = serde_json::from_slice::<Value>(&buf[..n]) else {
                eprintln!("driver: bad trace datagram");
                continue;
            };
            let (Some(container), Some(boot), Some(seq)) =
                (d["container"].as_str(), d["boot"].as_str(), d["seq"].as_u64())
            else {
                eprintln!("driver: trace datagram without container/boot/seq");
                continue;
            };
            let node = match nodes.get_mut(container) {
                Some(n) => n,
                None => {
                    let path = format!("{dir}/{container}.ndjson");
                    let file = match OpenOptions::new().create(true).append(true).open(&path) {
                        Ok(f) => f,
                        Err(e) => {
                            eprintln!("driver: cannot open {path}: {e}");
                            continue;
                        }
                    };
                    nodes.entry(container.to_string()).or_insert(Node { file, boot: String::new(), seq: 0 })
                }
            };
            let expected = if node.boot == boot { node.seq + 1 } else { 1 };
            // k numbers the stream's lines from 1, so a reader of the printed
            // stream can tell that it has every line, in order.
            let k = trace.events.load(Ordering::Relaxed) + 1;
            if seq != expected {
                let gap = json!({"e": "Gap", "node": container, "boot": boot, "expected": expected, "got": seq, "k": k});
                let _ = writeln!(node.file, "{gap}");
                if let Some(f) = stream.as_mut() {
                    let _ = writeln!(f, "{gap}");
                }
            }
            node.boot = boot.to_string();
            node.seq = seq;
            let mut ev = d["ev"].clone();
            ev["boot"] = json!(boot);
            ev["seq"] = json!(seq);
            if let Err(e) = writeln!(node.file, "{ev}") {
                eprintln!("driver: trace write: {e}");
            }
            ev["node"] = json!(container);
            ev["k"] = json!(k);
            if let Some(f) = stream.as_mut() {
                let _ = writeln!(f, "{ev}");
            }
            if print {
                println!("trace-kit {ev}");
            }
            trace.events.fetch_add(1, Ordering::Relaxed);
            observe(&ev);
        }
    });
    handle
}
