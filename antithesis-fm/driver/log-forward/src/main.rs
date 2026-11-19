//! Copies stdin to stdout line by line, and sends every line that contains
//! one of the substrings in LOG_FORWARD_MATCH to the Unix datagram socket at
//! LOG_FORWARD_SOCKET, as {"container","boot","seq","line"} JSON.
//!
//! Sends never block the system: a separate thread sends non-blocking. When
//! the driver's socket queue is full (EAGAIN) it keeps the line in a bounded
//! backlog and retries shortly; the kernel queues only 10 datagrams per Unix
//! socket by default, so dropping on the first EAGAIN loses lines whenever the
//! driver stalls briefly. Lines are dropped (leaving a seq gap) only when the
//! backlog is full or the send fails for another reason, such as the driver
//! not having bound its socket yet.
use std::collections::VecDeque;
use std::io::{self, BufRead, Write};
use std::os::unix::net::UnixDatagram;
use std::sync::{Arc, Condvar, Mutex};
use std::time::{Duration, SystemTime, UNIX_EPOCH};

const MAX_BACKLOG: usize = 20_000;

struct Backlog {
    q: Mutex<VecDeque<Vec<u8>>>,
    cv: Condvar,
}

fn sender(sock: UnixDatagram, path: String, backlog: Arc<Backlog>) {
    loop {
        let msg = {
            let mut q = backlog.q.lock().unwrap_or_else(|e| e.into_inner());
            while q.is_empty() {
                q = backlog.cv.wait(q).unwrap_or_else(|e| e.into_inner());
            }
            q.pop_front().unwrap()
        };
        loop {
            match sock.send_to(&msg, &path) {
                Err(e) if e.kind() == io::ErrorKind::WouldBlock => std::thread::sleep(Duration::from_millis(2)),
                _ => break, // Sent, or failed for good: drop it.
            }
        }
    }
}

const MAX_DATAGRAM: usize = 16 * 1024;
const MAX_LINE: usize = 15 * 1024;

fn json_escape(s: &str, out: &mut String) {
    out.push('"');
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if (c as u32) < 0x20 => out.push_str(&format!("\\u{:04x}", c as u32)),
            c => out.push(c),
        }
    }
    out.push('"');
}

fn truncate(s: &str, max: usize) -> &str {
    if s.len() <= max {
        return s;
    }
    let mut end = max;
    while !s.is_char_boundary(end) {
        end -= 1;
    }
    &s[..end]
}

fn main() {
    let socket_path = std::env::var("LOG_FORWARD_SOCKET").unwrap_or_default();
    let patterns: Vec<String> = std::env::var("LOG_FORWARD_MATCH")
        .unwrap_or_default()
        .split(',')
        .filter(|s| !s.is_empty())
        .map(String::from)
        .collect();
    let container = std::env::var("HOSTNAME").unwrap_or_else(|_| "unknown".into());
    let boot = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map(|d| d.as_nanos())
        .unwrap_or(0);

    let backlog = if socket_path.is_empty() || patterns.is_empty() {
        None
    } else {
        UnixDatagram::unbound().ok().and_then(|s| {
            s.set_nonblocking(true).ok()?;
            let b = Arc::new(Backlog { q: Mutex::new(VecDeque::new()), cv: Condvar::new() });
            let (b2, path) = (b.clone(), socket_path.clone());
            std::thread::spawn(move || sender(s, path, b2));
            Some(b)
        })
    };

    let stdin = io::stdin();
    let mut stdin = stdin.lock();
    let stdout = io::stdout();
    let mut seq: u64 = 0;
    let mut buf = Vec::with_capacity(4096);
    let mut container_json = String::new();
    json_escape(&container, &mut container_json);

    loop {
        buf.clear();
        match stdin.read_until(b'\n', &mut buf) {
            Ok(0) => break,
            Ok(_) => {}
            Err(e) if e.kind() == io::ErrorKind::Interrupted => continue,
            Err(_) => break,
        }
        {
            let mut out = stdout.lock();
            let _ = out.write_all(&buf);
            let _ = out.flush();
        }
        let Some(backlog) = backlog.as_ref() else { continue };
        let line = String::from_utf8_lossy(&buf);
        let line = line.trim_end_matches(['\n', '\r']);
        if !patterns.iter().any(|p| line.contains(p.as_str())) {
            continue;
        }
        let this_seq = seq;
        seq += 1;
        let mut msg = String::with_capacity(line.len() + 128);
        msg.push_str("{\"container\":");
        msg.push_str(&container_json);
        msg.push_str(&format!(",\"boot\":{boot},\"seq\":{this_seq},\"line\":"));
        json_escape(truncate(line, MAX_LINE), &mut msg);
        msg.push('}');
        if msg.len() > MAX_DATAGRAM {
            continue;
        }
        let mut q = backlog.q.lock().unwrap_or_else(|e| e.into_inner());
        if q.len() < MAX_BACKLOG {
            q.push_back(msg.into_bytes());
            backlog.cv.notify_one();
        }
    }
    // stdin closed: the system exited. Give the backlog up to 3 s to drain.
    if let Some(b) = backlog {
        for _ in 0..300 {
            if b.q.lock().unwrap_or_else(|e| e.into_inner()).is_empty() {
                break;
            }
            std::thread::sleep(Duration::from_millis(10));
        }
    }
}
