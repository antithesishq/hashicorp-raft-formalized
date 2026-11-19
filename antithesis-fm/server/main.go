// A tiny replicated service built on hashicorp/raft (binary name raft-sum): three nodes
// keep a running sum of integers sent by clients. It exists to be tested in
// Antithesis. Raft is given wrapped stores, a wrapped transport and a wrapped
// state machine that report its steps (wrap.go).
//
// It logs one line per state transition (msg=raft-state) and per applied
// command (msg=raft-apply). The harness forwards those lines, and raft's own
// warnings for fault-only paths, to the driver.
package main

import (
	"context"
	"encoding/json"
	"errors"
	"fmt"
	"net"
	"net/http"
	"os"
	"os/signal"
	"path/filepath"
	"strconv"
	"strings"
	"sync"
	"sync/atomic"
	"syscall"
	"time"

	"github.com/hashicorp/go-hclog"
	"github.com/hashicorp/raft"
	raftboltdb "github.com/hashicorp/raft-boltdb/v2"

	"tracekit"
)

var stderrMu sync.Mutex

// logLine writes one structured line to stderr in a single write.
func logLine(format string, args ...any) {
	s := fmt.Sprintf(format, args...) + "\n"
	stderrMu.Lock()
	_, _ = os.Stderr.WriteString(s)
	stderrMu.Unlock()
}

type lockedWriter struct{}

func (lockedWriter) Write(p []byte) (int, error) {
	stderrMu.Lock()
	defer stderrMu.Unlock()
	return os.Stderr.Write(p)
}

func env(key, def string) string {
	if v := os.Getenv(key); v != "" {
		return v
	}
	return def
}

func envDuration(key string, def time.Duration) time.Duration {
	if v := os.Getenv(key); v != "" {
		d, err := time.ParseDuration(v)
		if err != nil {
			fatal("bad %s: %v", key, err)
		}
		return d
	}
	return def
}

func envUint(key string, def uint64) uint64 {
	if v := os.Getenv(key); v != "" {
		n, err := strconv.ParseUint(v, 10, 64)
		if err != nil {
			fatal("bad %s: %v", key, err)
		}
		return n
	}
	return def
}

func fatal(format string, args ...any) {
	logLine("fatal: "+format, args...)
	os.Exit(1)
}

// hostAddr is a net.Addr whose String is a host:port name, so the address the
// node advertises survives the container coming back with a new IP.
type hostAddr string

func (a hostAddr) Network() string { return "tcp" }
func (a hostAddr) String() string  { return string(a) }

type streamLayer struct {
	net.Listener
	advertise hostAddr
}

func (s *streamLayer) Addr() net.Addr { return s.advertise }

func (s *streamLayer) Dial(addr raft.ServerAddress, timeout time.Duration) (net.Conn, error) {
	return net.DialTimeout("tcp", string(addr), timeout)
}

type server struct {
	id   string
	raft *raft.Raft
	fsm  *sumFSM
}

func main() {
	id := env("NODE_ID", "")
	if id == "" {
		fatal("NODE_ID is required")
	}
	raftAddr := env("RAFT_ADDR", id+":7000")
	raftBind := env("RAFT_BIND", "0.0.0.0:7000")
	httpBind := env("HTTP_BIND", "0.0.0.0:8000")
	dataDir := env("DATA_DIR", "/data")
	peers := env("PEERS", "")

	if err := os.MkdirAll(dataDir, 0o755); err != nil {
		fatal("mkdir: %v", err)
	}

	logger := hclog.New(&hclog.LoggerOptions{
		Name:   "raft",
		Level:  hclog.LevelFromString(env("RAFT_LOG_LEVEL", "info")),
		Output: lockedWriter{},
	})

	// Every step raft takes at its interfaces is reported through one sink:
	// to the logger at trace level, and to a checker if one is listening.
	tr := &tracer{addrs: map[string]string{}}
	for _, p := range strings.Split(peers, ",") {
		if kv := strings.SplitN(p, "=", 2); len(kv) == 2 {
			tr.addrs[kv[1]] = kv[0]
		}
	}
	tr.sink = tracekit.New(func(msg string, kv ...any) { logger.Trace(msg, kv...) })

	conf := raft.DefaultConfig()
	conf.LocalID = raft.ServerID(id)
	conf.Logger = logger
	// Defaults are the feature subset the TLA+ model covers (see spec/README.md):
	// slow timers keep the trace small, snapshots never trigger, and batches
	// are small so batching is exercised. Pre-votes are on, as in raft's own
	// defaults, unless PREVOTE_DISABLED=1.
	conf.HeartbeatTimeout = envDuration("HEARTBEAT_TIMEOUT", 2*time.Second)
	conf.ElectionTimeout = envDuration("ELECTION_TIMEOUT", 2*time.Second)
	conf.LeaderLeaseTimeout = envDuration("LEADER_LEASE_TIMEOUT", time.Second)
	conf.CommitTimeout = envDuration("COMMIT_TIMEOUT", 500*time.Millisecond)
	conf.SnapshotInterval = envDuration("SNAPSHOT_INTERVAL", 1000*time.Hour)
	conf.SnapshotThreshold = envUint("SNAPSHOT_THRESHOLD", 1<<40)
	conf.TrailingLogs = envUint("TRAILING_LOGS", 1<<40)
	conf.MaxAppendEntries = int(envUint("MAX_APPEND_ENTRIES", 4))
	conf.PreVoteDisabled = env("PREVOTE_DISABLED", "0") == "1"

	store, err := raftboltdb.NewBoltStore(filepath.Join(dataDir, "raft.db"))
	if err != nil {
		fatal("bolt store: %v", err)
	}
	snaps, err := raft.NewFileSnapshotStoreWithLogger(dataDir, 3, logger)
	if err != nil {
		fatal("snapshot store: %v", err)
	}

	ln, err := net.Listen("tcp", raftBind)
	if err != nil {
		fatal("listen raft: %v", err)
	}
	// Replication is pipelined as in raft's defaults (MAX_RPCS_IN_FLIGHT=1
	// turns pipelining off). The RPC timeout is shorter than the election
	// timeout, so an election's vote requests have returned or failed before
	// the next election starts.
	netTrans := raft.NewNetworkTransportWithConfig(&raft.NetworkTransportConfig{
		Stream:          &streamLayer{Listener: ln, advertise: hostAddr(raftAddr)},
		MaxPool:         3,
		Timeout:         envDuration("RPC_TIMEOUT", 800*time.Millisecond),
		Logger:          logger,
		MaxRPCsInFlight: int(envUint("MAX_RPCS_IN_FLIGHT", raft.DefaultMaxRPCsInFlight)),
	})
	trans := newTracedTransport(netTrans, tr, env("HEARTBEAT_FASTPATH", "") != "1")

	tr.boot(store, store, snaps)
	fsm := &sumFSM{node: id}
	atomic.StoreInt64(&tr.builder, goid())
	r, err := raft.NewRaft(conf, tracedFSM{fsm, tr}, tracedLogs{store, tr}, tracedStable{store, tr}, tracedSnaps{snaps, tr}, trans)
	if err != nil {
		fatal("new raft: %v", err)
	}
	tr.attach(r)

	// The filter runs synchronously on raft's main goroutine when the node
	// changes state, so the term it reads is the term of the transition.
	r.RegisterObserver(raft.NewObserver(nil, false, func(o *raft.Observation) bool {
		if st, ok := o.Data.(raft.RaftState); ok {
			logLine("msg=raft-state role=%s term=%d", strings.ToLower(st.String()), o.Raft.CurrentTerm())
		}
		return false
	}))

	existing, err := raft.HasExistingState(store, store, snaps)
	if err != nil {
		fatal("existing state: %v", err)
	}
	if !existing && peers != "" {
		var cfg raft.Configuration
		for _, p := range strings.Split(peers, ",") {
			kv := strings.SplitN(p, "=", 2)
			if len(kv) != 2 {
				fatal("bad PEERS entry %q", p)
			}
			cfg.Servers = append(cfg.Servers, raft.Server{
				Suffrage: raft.Voter, ID: raft.ServerID(kv[0]), Address: raft.ServerAddress(kv[1]),
			})
		}
		if err := r.BootstrapCluster(cfg).Error(); err != nil && !errors.Is(err, raft.ErrCantBootstrap) {
			fatal("bootstrap: %v", err)
		}
	}

	s := &server{id: id, raft: r, fsm: fsm}
	mux := http.NewServeMux()
	mux.HandleFunc("POST /add", s.handleAdd)
	mux.HandleFunc("GET /sum", s.handleSum)
	mux.HandleFunc("GET /status", s.handleStatus)
	mux.HandleFunc("POST /transfer", s.handleTransfer)
	mux.HandleFunc("POST /snapshot", s.handleSnapshot)
	srv := &http.Server{Addr: httpBind, Handler: mux, ReadHeaderTimeout: 5 * time.Second}

	go func() {
		if err := srv.ListenAndServe(); err != nil && !errors.Is(err, http.ErrServerClosed) {
			fatal("http: %v", err)
		}
	}()
	logLine("msg=raft-server-started node=%s", id)

	sig := make(chan os.Signal, 1)
	signal.Notify(sig, syscall.SIGTERM, syscall.SIGINT)
	<-sig
	logLine("msg=raft-server-stopping node=%s", id)
	ctx, cancel := context.WithTimeout(context.Background(), 2*time.Second)
	defer cancel()
	_ = srv.Shutdown(ctx)
	_ = r.Shutdown().Error()
	_ = store.Close()
}

func writeJSON(w http.ResponseWriter, code int, v any) {
	w.Header().Set("Content-Type", "application/json")
	w.WriteHeader(code)
	_ = json.NewEncoder(w).Encode(v)
}

func (s *server) leaderID() string {
	_, id := s.raft.LeaderWithID()
	return string(id)
}

// Error responses. "not_leader" and "enqueue_timeout" are definite: the
// command was never appended to the log. Everything else is "unknown": the
// command may or may not be committed, now or later.
func (s *server) applyError(w http.ResponseWriter, err error) {
	switch {
	case errors.Is(err, raft.ErrNotLeader):
		writeJSON(w, http.StatusMisdirectedRequest, map[string]any{"error": "not_leader", "leader": s.leaderID()})
	case errors.Is(err, raft.ErrEnqueueTimeout):
		writeJSON(w, http.StatusServiceUnavailable, map[string]any{"error": "enqueue_timeout"})
	default:
		writeJSON(w, http.StatusInternalServerError, map[string]any{"error": "unknown", "detail": err.Error()})
	}
}

const applyWait = 2 * time.Second

func (s *server) handleAdd(w http.ResponseWriter, req *http.Request) {
	q := req.URL.Query()
	op, err1 := strconv.ParseUint(q.Get("op"), 10, 64)
	val, err2 := strconv.ParseInt(q.Get("value"), 10, 64)
	if err1 != nil || err2 != nil {
		writeJSON(w, http.StatusBadRequest, map[string]any{"error": "bad_request"})
		return
	}
	if s.raft.State() != raft.Leader {
		writeJSON(w, http.StatusMisdirectedRequest, map[string]any{"error": "not_leader", "leader": s.leaderID()})
		return
	}
	f := s.raft.Apply(encodeCommand(command{Op: op, Value: val}), 500*time.Millisecond)
	done := make(chan error, 1)
	go func() { done <- f.Error() }()
	select {
	case err := <-done:
		if err != nil {
			s.applyError(w, err)
			return
		}
		switch res := f.Response().(type) {
		case applyResult:
			writeJSON(w, http.StatusOK, map[string]any{"index": res.Index, "sum": res.Sum, "log_index": f.Index()})
		case error:
			writeJSON(w, http.StatusInternalServerError, map[string]any{"error": "fsm", "detail": res.Error()})
		default:
			writeJSON(w, http.StatusInternalServerError, map[string]any{"error": "fsm", "detail": fmt.Sprint(res)})
		}
	case <-time.After(applyWait):
		writeJSON(w, http.StatusGatewayTimeout, map[string]any{"error": "unknown", "detail": "timeout"})
	}
}

// GET /sum?mode=linear (default) runs a barrier through the log first, so it
// is linearizable and only works on the leader. mode=stale reads the local
// state machine on any node.
func (s *server) handleSum(w http.ResponseWriter, req *http.Request) {
	mode := req.URL.Query().Get("mode")
	if mode == "" {
		mode = "linear"
	}
	switch mode {
	case "linear":
		if s.raft.State() != raft.Leader {
			writeJSON(w, http.StatusMisdirectedRequest, map[string]any{"error": "not_leader", "leader": s.leaderID()})
			return
		}
		f := s.raft.Barrier(500 * time.Millisecond)
		done := make(chan error, 1)
		go func() { done <- f.Error() }()
		select {
		case err := <-done:
			if err != nil {
				s.applyError(w, err)
				return
			}
		case <-time.After(applyWait):
			writeJSON(w, http.StatusGatewayTimeout, map[string]any{"error": "unknown", "detail": "timeout"})
			return
		}
	case "stale":
	default:
		writeJSON(w, http.StatusBadRequest, map[string]any{"error": "bad_mode"})
		return
	}
	st := s.fsm.state()
	writeJSON(w, http.StatusOK, map[string]any{
		"node": s.id, "index": st.Index, "term": st.Term, "sum": st.Sum, "count": st.Count, "digest": strconv.FormatUint(st.Digest, 10),
	})
}

func (s *server) handleStatus(w http.ResponseWriter, req *http.Request) {
	writeJSON(w, http.StatusOK, map[string]any{
		"node":       s.id,
		"state":      strings.ToLower(s.raft.State().String()),
		"term":       s.raft.CurrentTerm(),
		"leader":     s.leaderID(),
		"commit":     s.raft.CommitIndex(),
		"applied":    s.raft.AppliedIndex(),
		"last_index": s.raft.LastIndex(),
	})
}

func (s *server) handleTransfer(w http.ResponseWriter, req *http.Request) {
	if s.raft.State() != raft.Leader {
		writeJSON(w, http.StatusMisdirectedRequest, map[string]any{"error": "not_leader", "leader": s.leaderID()})
		return
	}
	f := s.raft.LeadershipTransfer()
	done := make(chan error, 1)
	go func() { done <- f.Error() }()
	select {
	case err := <-done:
		if err != nil {
			writeJSON(w, http.StatusInternalServerError, map[string]any{"error": "transfer", "detail": err.Error()})
			return
		}
		writeJSON(w, http.StatusOK, map[string]any{"ok": true})
	case <-time.After(applyWait):
		writeJSON(w, http.StatusGatewayTimeout, map[string]any{"error": "unknown", "detail": "timeout"})
	}
}

func (s *server) handleSnapshot(w http.ResponseWriter, req *http.Request) {
	f := s.raft.Snapshot()
	done := make(chan error, 1)
	go func() { done <- f.Error() }()
	select {
	case err := <-done:
		if err != nil && !errors.Is(err, raft.ErrNothingNewToSnapshot) {
			writeJSON(w, http.StatusInternalServerError, map[string]any{"error": "snapshot", "detail": err.Error()})
			return
		}
		writeJSON(w, http.StatusOK, map[string]any{"ok": true, "nothing_new": err != nil})
	case <-time.After(applyWait):
		writeJSON(w, http.StatusGatewayTimeout, map[string]any{"error": "unknown", "detail": "timeout"})
	}
}
