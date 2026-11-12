package main

// Reports raft's steps at the interfaces raft is given: its stores, its
// transport and its observer hook. Nothing here needs code inside raft.
//
// Every report goes through one tracekit.Sink, which orders them and, when a
// checker is listening, delivers them synchronously. Event names and fields:
//
//	boot         term, voteTerm, voteFor, lastIndex, lastTerm   (what was recovered)
//	stable.set   key, value                                     (before the write)
//	log.store    first, entries                                 (before the write)
//	log.delete   from, to[, commit, applied]                    (before the write)
//	role         role
//	rpc.send     kind, peer, req
//	rpc.recv     kind, src, req                                 (append requests, as raft is handed them)
//	rpc.reply    kind, src, req, resp, commit
//	rpc.return   kind, peer, req, resp
//	rpc.fail     kind, peer, req

import (
	"bytes"
	"encoding/hex"
	"runtime"
	"strconv"
	"strings"
	"sync"
	"sync/atomic"
	"time"

	"github.com/hashicorp/raft"

	"tracekit"
)

// tracer holds what the wrappers share.
type tracer struct {
	sink  *tracekit.Sink
	addrs map[string]string // server address -> server ID
	raft  atomic.Pointer[raft.Raft]

	// builder is the goroutine that calls raft.NewRaft. NewRaft starts
	// raft's goroutines before it returns the *Raft the wrappers need (to
	// read the role and the commit index). Until attach has run, a call
	// from any other goroutine waits; calls NewRaft makes itself go through.
	builder  int64
	roleMu   sync.Mutex
	lastRole string
}

func goid() int64 {
	var buf [64]byte
	f := bytes.Fields(buf[:runtime.Stack(buf[:], false)])
	id, _ := strconv.ParseInt(string(f[1]), 10, 64)
	return id
}

// await returns once the wrappers have the *Raft, unless the caller is
// NewRaft itself.
func (t *tracer) await() {
	for t.raft.Load() == nil && goid() != atomic.LoadInt64(&t.builder) {
		time.Sleep(time.Millisecond)
	}
}

// syncRole reports the node's role if it is not the one last reported. The
// observer calls it at every change; the store wrappers call it before a
// write, which covers a change made before the observer was registered.
func (t *tracer) syncRole() {
	r := t.raft.Load()
	if r == nil {
		return
	}
	t.roleMu.Lock()
	defer t.roleMu.Unlock()
	if role := strings.ToLower(r.State().String()); role != t.lastRole {
		t.lastRole = role
		t.sink.Emit("role", "role", role)
	}
}

// attach is called with the *Raft as soon as NewRaft returns.
func (t *tracer) attach(r *raft.Raft) {
	t.lastRole = "follower"
	r.RegisterObserver(raft.NewObserver(nil, false, func(o *raft.Observation) bool {
		if _, ok := o.Data.(raft.RaftState); ok {
			t.syncRole()
		}
		return false
	}))
	t.raft.Store(r)
	t.syncRole()
}

func (t *tracer) id(addr string) string {
	if id, ok := t.addrs[addr]; ok {
		return id
	}
	return addr
}

func entryOf(l *raft.Log) map[string]any {
	e := map[string]any{"term": l.Term, "type": strings.ToLower(strings.TrimPrefix(l.Type.String(), "Log")), "value": ""}
	switch l.Type {
	case raft.LogCommand:
		e["type"], e["value"] = "command", hex.EncodeToString(l.Data)
	case raft.LogNoop:
		e["type"] = "noop"
	case raft.LogBarrier:
		e["type"] = "barrier"
	case raft.LogConfiguration:
		e["type"] = "config"
	}
	return e
}

func entriesOf(logs []*raft.Log) []map[string]any {
	out := make([]map[string]any, 0, len(logs))
	for _, l := range logs {
		out = append(out, entryOf(l))
	}
	return out
}

func appendReq(a *raft.AppendEntriesRequest) map[string]any {
	return map[string]any{
		"term": a.Term, "prevLogIndex": a.PrevLogEntry, "prevLogTerm": a.PrevLogTerm,
		"entries": entriesOf(a.Entries), "commit": a.LeaderCommitIndex,
	}
}

func voteReq(v *raft.RequestVoteRequest) map[string]any {
	return map[string]any{"term": v.Term, "lastLogIndex": v.LastLogIndex, "lastLogTerm": v.LastLogTerm}
}

// isHeartbeat is the transport's own test for a heartbeat.
func isHeartbeat(a *raft.AppendEntriesRequest) bool {
	return a.Term != 0 && a.PrevLogEntry == 0 && a.PrevLogTerm == 0 && len(a.Entries) == 0 && a.LeaderCommitIndex == 0
}

// ---- stable store: every write is announced before it is made.

type tracedStable struct {
	raft.StableStore
	t *tracer
}

func (s tracedStable) Set(key, val []byte) error {
	s.t.await()
	s.t.syncRole()
	return s.t.sink.Do(func() error { return s.StableStore.Set(key, val) },
		"stable.set", "key", string(key), "value", s.t.id(string(val)))
}

func (s tracedStable) SetUint64(key []byte, val uint64) error {
	s.t.await()
	s.t.syncRole()
	return s.t.sink.Do(func() error { return s.StableStore.SetUint64(key, val) },
		"stable.set", "key", string(key), "value", val)
}

// ---- log store.

type tracedLogs struct {
	raft.LogStore
	t *tracer
}

func (s tracedLogs) StoreLog(l *raft.Log) error { return s.StoreLogs([]*raft.Log{l}) }

func (s tracedLogs) StoreLogs(logs []*raft.Log) error {
	if len(logs) == 0 {
		return s.LogStore.StoreLogs(logs)
	}
	s.t.await()
	s.t.syncRole()
	return s.t.sink.Do(func() error { return s.LogStore.StoreLogs(logs) },
		"log.store", "first", logs[0].Index, "entries", entriesOf(logs))
}

func (s tracedLogs) DeleteRange(min, max uint64) error {
	s.t.await()
	s.t.syncRole()
	kv := []any{"from", min, "to", max}
	// When the end of the log is deleted, say how far the node has committed
	// and applied, so a reader can check that nothing committed is lost.
	if r := s.t.raft.Load(); r != nil {
		if last, err := s.LogStore.LastIndex(); err == nil && max >= last {
			kv = append(kv, "commit", r.CommitIndex(), "applied", r.AppliedIndex())
		}
	}
	return s.t.sink.Do(func() error { return s.LogStore.DeleteRange(min, max) }, "log.delete", kv...)
}

// ---- transport.

type tracedTransport struct {
	*raft.NetworkTransport
	t        *tracer
	serial   bool // hide the heartbeat fast path (hashicorp/raft#695)
	consumer chan raft.RPC
}

func newTracedTransport(inner *raft.NetworkTransport, t *tracer, serial bool) *tracedTransport {
	tt := &tracedTransport{NetworkTransport: inner, t: t, serial: serial, consumer: make(chan raft.RPC)}
	go tt.deliver()
	return tt
}

func (tt *tracedTransport) SetHeartbeatHandler(cb func(raft.RPC)) {
	if !tt.serial {
		tt.NetworkTransport.SetHeartbeatHandler(cb)
	}
}

func (tt *tracedTransport) Consumer() <-chan raft.RPC { return tt.consumer }

// deliver hands raft one request at a time and reports raft's reply before
// the reply leaves and before the next request goes in. The handler's own
// writes are thereby bracketed by the previous reply and this one.
func (tt *tracedTransport) deliver() {
	for rpc := range tt.NetworkTransport.Consumer() {
		tt.t.await()
		out := rpc.RespChan
		in := make(chan raft.RPCResponse, 1)
		rpc.RespChan = in
		if req, ok := rpc.Command.(*raft.AppendEntriesRequest); ok {
			// The reply is reported by this goroutine, which can run long
			// after the handler; the checker must know meanwhile that the
			// request is being handled.
			tt.t.sink.Emit("rpc.recv", "kind", "append", "src", string(req.ID), "req", appendReq(req))
		}
		tt.consumer <- rpc
		resp := <-in
		var commit uint64
		if r := tt.t.raft.Load(); r != nil {
			commit = r.CommitIndex()
		}
		switch req := rpc.Command.(type) {
		case *raft.AppendEntriesRequest:
			if a, ok := resp.Response.(*raft.AppendEntriesResponse); ok && resp.Error == nil {
				tt.t.sink.Emit("rpc.reply", "kind", "append", "src", string(req.ID), "req", appendReq(req),
					"resp", map[string]any{"term": a.Term, "success": a.Success, "lastLog": a.LastLog},
					"commit", commit)
			}
		case *raft.RequestVoteRequest:
			if v, ok := resp.Response.(*raft.RequestVoteResponse); ok && resp.Error == nil {
				tt.t.sink.Emit("rpc.reply", "kind", "vote", "src", string(req.ID), "req", voteReq(req),
					"resp", map[string]any{"term": v.Term, "granted": v.Granted}, "commit", commit)
			}
		}
		out <- resp
	}
}

func (tt *tracedTransport) AppendEntries(id raft.ServerID, target raft.ServerAddress,
	args *raft.AppendEntriesRequest, resp *raft.AppendEntriesResponse) error {
	kind := "append"
	if isHeartbeat(args) {
		kind = "heartbeat"
	}
	// The request was built some time ago, from the log and commit index of
	// this node as leader of args.Term; the report can come after the node
	// has moved on. The model's send allows that.
	req := appendReq(args)
	tt.t.sink.Emit("rpc.send", "kind", kind, "peer", string(id), "req", req)
	if err := tt.NetworkTransport.AppendEntries(id, target, args, resp); err != nil {
		tt.t.sink.Emit("rpc.fail", "kind", kind, "peer", string(id), "req", req)
		return err
	}
	tt.t.sink.Emit("rpc.return", "kind", kind, "peer", string(id), "req", req,
		"resp", map[string]any{"term": resp.Term, "success": resp.Success, "lastLog": resp.LastLog})
	return nil
}

func (tt *tracedTransport) RequestVote(id raft.ServerID, target raft.ServerAddress,
	args *raft.RequestVoteRequest, resp *raft.RequestVoteResponse) error {
	req := voteReq(args)
	tt.t.sink.Emit("rpc.send", "kind", "vote", "peer", string(id), "req", req)
	if err := tt.NetworkTransport.RequestVote(id, target, args, resp); err != nil {
		tt.t.sink.Emit("rpc.fail", "kind", "vote", "peer", string(id), "req", req)
		return err
	}
	tt.t.sink.Emit("rpc.return", "kind", "vote", "peer", string(id), "req", req,
		"resp", map[string]any{"term": resp.Term, "granted": resp.Granted})
	return nil
}

// ---- startup.

// boot reports what the node recovered from disk.
func (t *tracer) boot(stable raft.StableStore, logs raft.LogStore) {
	term, _ := stable.GetUint64([]byte("CurrentTerm"))
	voteTerm, _ := stable.GetUint64([]byte("LastVoteTerm"))
	voteFor, _ := stable.Get([]byte("LastVoteCand"))
	last, _ := logs.LastIndex()
	var lastTerm uint64
	if last > 0 {
		var l raft.Log
		if err := logs.GetLog(last, &l); err == nil {
			lastTerm = l.Term
		}
	}
	t.sink.Emit("boot", "term", term, "voteTerm", voteTerm, "voteFor", t.id(string(voteFor)),
		"lastIndex", last, "lastTerm", lastTerm)
}
