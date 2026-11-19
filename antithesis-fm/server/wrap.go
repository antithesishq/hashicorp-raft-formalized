package main

// Reports raft's steps at the interfaces raft is given: its stores, its
// transport and its observer hook. Nothing here needs code inside raft.
//
// Every report goes through one tracekit.Sink, which orders them and, when a
// checker is listening, delivers them synchronously. Event names and fields:
//
//	boot         term, voteTerm, voteFor, firstIndex, lastIndex, lastTerm, snapIndex, snapTerm
//	                                                            (what was recovered: the log store's
//	                                                            first and last entries, the newest snapshot)
//	stable.set   key, value                                     (before the write)
//	log.store    first, entries                                 (before the write)
//	log.delete   from, to, first[, commit, applied]             (before the write; first is the
//	                                                            log store's first index)
//	snap.store   index, term, kind, commit                      (before the snapshot is made durable;
//	                                                            kind is take or install)
//	role         role
//	rpc.send     kind, peer, req
//	rpc.recv     kind, src, req                                 (append and timeoutnow requests, as raft is handed them)
//	rpc.reply    kind, src, req, resp, commit
//
// kind is append, heartbeat, vote, prevote, timeoutnow or snapshot. A TimeoutNow
// request has nothing in it (req is empty) and its reply carries no commit
// index. A request to install a snapshot is reported as its term and the
// index and term of the snapshot's last entry.
//	rpc.return   kind, peer, req, resp                          (before raft acts on the reply)
//	rpc.fail     kind, peer, req
//	fsm.apply    index, entry, commit                           (before the state machine applies it)

import (
	"bytes"
	"encoding/hex"
	"io"
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
	builder int64
	// mainLoop is the goroutine of raft's main loop, known from its first
	// write of a term, a vote or a log entry after NewRaft has returned.
	// Raft installs a snapshot on it and takes its own on another.
	mainLoop int64
	roleMu   sync.Mutex
	lastRole string

	// The request raft is handling, if any. Raft answers it from its main
	// loop, and the model requires the reply to be reported in the state
	// raft answered in: before the node's next durable write. So the reply
	// is reported by whichever comes first, the transport wrapper's
	// goroutine or the next write, which is made by the main loop too.
	replyMu sync.Mutex
	flight  *inFlight
}

// inFlight is a request handed to raft whose reply has not been reported.
type inFlight struct {
	rpc raft.RPC                // as the transport delivered it
	in  chan raft.RPCResponse   // where raft puts its answer
	out chan<- raft.RPCResponse // where the transport expects it
}

// flushReply reports the reply of the request in flight if raft has answered
// it, and passes the answer on. It reports whether there is no longer a
// request in flight.
func (t *tracer) flushReply() bool {
	t.replyMu.Lock()
	defer t.replyMu.Unlock()
	f := t.flight
	if f == nil {
		return true
	}
	select {
	case resp := <-f.in:
		t.reportReply(f.rpc, resp)
		f.out <- resp
		t.flight = nil
		return true
	default:
		return false
	}
}

func (t *tracer) reportReply(rpc raft.RPC, resp raft.RPCResponse) {
	var commit uint64
	if r := t.raft.Load(); r != nil {
		commit = r.CommitIndex()
	}
	switch req := rpc.Command.(type) {
	case *raft.AppendEntriesRequest:
		if a, ok := resp.Response.(*raft.AppendEntriesResponse); ok && resp.Error == nil {
			t.sink.Emit("rpc.reply", "kind", "append", "src", string(req.ID), "req", appendReq(req),
				"resp", map[string]any{"term": a.Term, "success": a.Success, "lastLog": a.LastLog},
				"commit", commit)
		}
	case *raft.RequestVoteRequest:
		if v, ok := resp.Response.(*raft.RequestVoteResponse); ok && resp.Error == nil {
			t.sink.Emit("rpc.reply", "kind", "vote", "src", string(req.ID), "req", voteReq(req),
				"resp", map[string]any{"term": v.Term, "granted": v.Granted}, "commit", commit)
		}
	case *raft.RequestPreVoteRequest:
		if v, ok := resp.Response.(*raft.RequestPreVoteResponse); ok && resp.Error == nil {
			t.sink.Emit("rpc.reply", "kind", "prevote", "src", string(req.ID), "req", preVoteReq(req),
				"resp", map[string]any{"term": v.Term, "granted": v.Granted}, "commit", commit)
		}
	case *raft.TimeoutNowRequest:
		if _, ok := resp.Response.(*raft.TimeoutNowResponse); ok && resp.Error == nil {
			t.sink.Emit("rpc.reply", "kind", "timeoutnow", "src", string(req.ID), "req", map[string]any{})
		}
	case *raft.InstallSnapshotRequest:
		if v, ok := resp.Response.(*raft.InstallSnapshotResponse); ok && resp.Error == nil {
			t.sink.Emit("rpc.reply", "kind", "snapshot", "src", string(req.ID), "req", snapReq(req),
				"resp", map[string]any{"term": v.Term, "success": v.Success}, "commit", commit)
		}
	}
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

// onMainLoop notes the calling goroutine as raft's main loop, unless it is
// NewRaft's.
func (t *tracer) onMainLoop() {
	if t.raft.Load() != nil && atomic.LoadInt64(&t.mainLoop) == 0 {
		if id := goid(); id != atomic.LoadInt64(&t.builder) {
			atomic.StoreInt64(&t.mainLoop, id)
		}
	}
}

// reportRole reports a role if it is not the one last reported.
func (t *tracer) reportRole(role string) {
	t.roleMu.Lock()
	defer t.roleMu.Unlock()
	if role != t.lastRole {
		t.lastRole = role
		t.sink.Emit("role", "role", role)
	}
}

// syncRole reports the node's role as it is now. The store wrappers call it
// before a write, which covers a change made before the observer was
// registered.
func (t *tracer) syncRole() {
	if r := t.raft.Load(); r != nil {
		t.reportRole(strings.ToLower(r.State().String()))
	}
}

// attach is called with the *Raft as soon as NewRaft returns.
func (t *tracer) attach(r *raft.Raft) {
	t.lastRole = "follower"
	// Raft announces a change of role from the goroutine that makes it, before
	// that goroutine goes on. The role reported is the one announced, not the
	// one the node has by the time the report is made: a node that is being
	// stopped has its role overwritten from outside the main loop, and a
	// role the main loop has just taken (follower, on a request of a later
	// term) must still be reported before the write that follows it.
	r.RegisterObserver(raft.NewObserver(nil, false, func(o *raft.Observation) bool {
		if st, ok := o.Data.(raft.RaftState); ok {
			// A reply raft has given is reported before the change: the
			// node answered in the role it had.
			t.flushReply()
			t.reportRole(strings.ToLower(st.String()))
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
	return map[string]any{"term": v.Term, "lastLogIndex": v.LastLogIndex, "lastLogTerm": v.LastLogTerm,
		"transfer": v.LeadershipTransfer}
}

func snapReq(a *raft.InstallSnapshotRequest) map[string]any {
	return map[string]any{"term": a.Term, "index": a.LastLogIndex, "lastTerm": a.LastLogTerm}
}

func preVoteReq(v *raft.RequestPreVoteRequest) map[string]any {
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
	s.t.onMainLoop()
	s.t.flushReply()
	s.t.syncRole()
	return s.t.sink.Do(func() error { return s.StableStore.Set(key, val) },
		"stable.set", "key", string(key), "value", s.t.id(string(val)))
}

func (s tracedStable) SetUint64(key []byte, val uint64) error {
	s.t.await()
	s.t.onMainLoop()
	s.t.flushReply()
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
	s.t.onMainLoop()
	s.t.flushReply()
	s.t.syncRole()
	return s.t.sink.Do(func() error { return s.LogStore.StoreLogs(logs) },
		"log.store", "first", logs[0].Index, "entries", entriesOf(logs))
}

func (s tracedLogs) DeleteRange(min, max uint64) error {
	s.t.await()
	s.t.flushReply()
	s.t.syncRole()
	first, _ := s.LogStore.FirstIndex()
	kv := []any{"from", min, "to", max, "first", first}
	// When the end of the log is deleted, say how far the node has committed
	// and applied, so a reader can check that nothing committed is lost.
	if r := s.t.raft.Load(); r != nil {
		if last, err := s.LogStore.LastIndex(); err == nil && max >= last {
			kv = append(kv, "commit", r.CommitIndex(), "applied", r.AppliedIndex())
		}
	}
	return s.t.sink.Do(func() error { return s.LogStore.DeleteRange(min, max) }, "log.delete", kv...)
}

// ---- snapshot store: a snapshot is announced before it is made durable.

type tracedSnaps struct {
	raft.SnapshotStore
	t *tracer
}

func (s tracedSnaps) Create(version raft.SnapshotVersion, index, term uint64, configuration raft.Configuration,
	configurationIndex uint64, trans raft.Transport) (raft.SnapshotSink, error) {
	sink, err := s.SnapshotStore.Create(version, index, term, configuration, configurationIndex, trans)
	if err != nil {
		return nil, err
	}
	return &tracedSink{SnapshotSink: sink, t: s.t, index: index, term: term}, nil
}

// tracedSink reports the snapshot when raft closes it, which is what makes
// it the node's newest snapshot.
type tracedSink struct {
	raft.SnapshotSink
	t           *tracer
	index, term uint64
	closed      bool
}

// installing reports whether the request raft is handling is one to install
// the snapshot (index, term).
func (t *tracer) installing(index, term uint64) bool {
	t.replyMu.Lock()
	defer t.replyMu.Unlock()
	if t.flight == nil {
		return false
	}
	req, ok := t.flight.rpc.Command.(*raft.InstallSnapshotRequest)
	return ok && req.LastLogIndex == index && req.LastLogTerm == term
}

func (k *tracedSink) Close() error {
	// The state machine's Persist closes the sink and raft closes it again.
	if k.closed {
		return k.SnapshotSink.Close()
	}
	k.closed = true
	k.t.await()
	// A snapshot the node was sent is stored by the main loop while it
	// handles the request. One the node takes itself is stored by another
	// goroutine, possibly at that moment and of the same index.
	kind := "take"
	if main := atomic.LoadInt64(&k.t.mainLoop); k.t.installing(k.index, k.term) && (main == 0 || goid() == main) {
		kind = "install"
	}
	k.t.flushReply()
	k.t.syncRole()
	var commit uint64
	if r := k.t.raft.Load(); r != nil {
		commit = r.CommitIndex()
	}
	return k.t.sink.Do(func() error { return k.SnapshotSink.Close() },
		"snap.store", "index", k.index, "term", k.term, "kind", kind, "commit", commit)
}

// ---- state machine: every entry raft hands to it is reported first.

// tracedFSM is a raft.FSM and nothing more. It does not implement
// raft.BatchingFSM or raft.ConfigurationStore, so raft calls Apply once per
// command entry, in the order it hands them over, and never passes it a
// configuration entry.
type tracedFSM struct {
	raft.FSM
	t *tracer
}

func (f tracedFSM) Apply(l *raft.Log) interface{} {
	f.t.await()
	// Raft applies on a goroutine of its own, after its main loop has moved
	// the commit index. The commit index is reported too, as with a reply:
	// the checker may not have seen it move yet.
	f.t.sink.Emit("fsm.apply", "index", l.Index, "entry", entryOf(l), "commit", f.t.raft.Load().CommitIndex())
	return f.FSM.Apply(l)
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
// the reply leaves, before the next request goes in, and before the node's
// next durable write (tracer.flushReply).
func (tt *tracedTransport) deliver() {
	for rpc := range tt.NetworkTransport.Consumer() {
		tt.t.await()
		f := &inFlight{rpc: rpc, in: make(chan raft.RPCResponse, 1), out: rpc.RespChan}
		handed := rpc
		handed.RespChan = f.in
		switch req := rpc.Command.(type) {
		case *raft.AppendEntriesRequest:
			// The checker must know that the request is being handled.
			tt.t.sink.Emit("rpc.recv", "kind", "append", "src", string(req.ID), "req", appendReq(req))
		case *raft.TimeoutNowRequest:
			// And this one: the change of role it causes is reported
			// before its reply.
			tt.t.sink.Emit("rpc.recv", "kind", "timeoutnow", "src", string(req.ID), "req", map[string]any{})
		case *raft.InstallSnapshotRequest:
			// And this one: the snapshot is stored before its reply.
			tt.t.sink.Emit("rpc.recv", "kind", "snapshot", "src", string(req.ID), "req", snapReq(req))
		}
		tt.t.replyMu.Lock()
		tt.t.flight = f
		tt.t.replyMu.Unlock()
		tt.consumer <- handed
		for !tt.t.flushReply() {
			time.Sleep(200 * time.Microsecond)
		}
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

// AppendEntriesPipeline is what a replicator sends on once a request to the
// peer has succeeded: requests go out without waiting for the replies to the
// ones before, and another goroutine of raft reads the replies.
func (tt *tracedTransport) AppendEntriesPipeline(id raft.ServerID, target raft.ServerAddress) (raft.AppendPipeline, error) {
	inner, err := tt.NetworkTransport.AppendEntriesPipeline(id, target)
	if err != nil {
		return nil, err
	}
	p := &tracedPipeline{AppendPipeline: inner, t: tt.t, peer: string(id),
		done: make(chan raft.AppendFuture), stop: make(chan struct{})}
	go p.relay()
	return p, nil
}

// tracedPipeline reports each request before it is written to the
// connection, and each reply before raft is handed it.
type tracedPipeline struct {
	raft.AppendPipeline
	t    *tracer
	peer string
	done chan raft.AppendFuture
	stop chan struct{}

	mu     sync.Mutex
	sent   []pipelined // reported as sent, no reply reported; replies come in this order
	closed bool
}

type pipelined struct {
	kind string
	req  map[string]any
}

func (p *tracedPipeline) AppendEntries(args *raft.AppendEntriesRequest, resp *raft.AppendEntriesResponse) (raft.AppendFuture, error) {
	q := pipelined{kind: "append", req: appendReq(args)}
	if isHeartbeat(args) {
		q.kind = "heartbeat"
	}
	// As in tracedTransport.AppendEntries: the request was built from the
	// log and commit index of this node as leader of args.Term.
	p.mu.Lock()
	p.t.sink.Emit("rpc.send", "kind", q.kind, "peer", p.peer, "req", q.req)
	p.sent = append(p.sent, q)
	p.mu.Unlock()
	f, err := p.AppendPipeline.AppendEntries(args, resp)
	if err != nil {
		// Not handed over for a reply, so it is still the last one.
		p.mu.Lock()
		if n := len(p.sent); n > 0 && !p.closed {
			p.sent = p.sent[:n-1]
			p.t.sink.Emit("rpc.fail", "kind", q.kind, "peer", p.peer, "req", q.req)
		}
		p.mu.Unlock()
		return nil, err
	}
	return f, nil
}

func (p *tracedPipeline) Consumer() <-chan raft.AppendFuture { return p.done }

// relay passes replies on to raft, reporting each first.
func (p *tracedPipeline) relay() {
	for {
		select {
		case f := <-p.AppendPipeline.Consumer():
			p.mu.Lock()
			if p.closed || len(p.sent) == 0 {
				p.mu.Unlock()
				return
			}
			q := p.sent[0]
			p.sent = p.sent[1:]
			// Raft reads the response whether or not the future has an
			// error; a response that failed to arrive is not a success.
			if resp := f.Response(); f.Error() != nil && !resp.Success {
				p.t.sink.Emit("rpc.fail", "kind", q.kind, "peer", p.peer, "req", q.req)
			} else {
				p.t.sink.Emit("rpc.return", "kind", q.kind, "peer", p.peer, "req", q.req,
					"resp", map[string]any{"term": resp.Term, "success": resp.Success, "lastLog": resp.LastLog})
			}
			p.mu.Unlock()
			select {
			case p.done <- f:
			case <-p.stop:
				return
			}
		case <-p.stop:
			return
		}
	}
}

// Close is called by the replicator when it leaves pipeline mode. Replies to
// the requests still out are not read.
func (p *tracedPipeline) Close() error {
	p.mu.Lock()
	if !p.closed {
		p.closed = true
		close(p.stop)
		for _, q := range p.sent {
			p.t.sink.Emit("rpc.fail", "kind", q.kind, "peer", p.peer, "req", q.req)
		}
		p.sent = nil
	}
	p.mu.Unlock()
	return p.AppendPipeline.Close()
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

// RequestPreVote makes the wrapper a raft.WithPreVote, as the transport it
// wraps is. The request was built by the main loop; the report can come
// after the node has given the attempt up.
func (tt *tracedTransport) RequestPreVote(id raft.ServerID, target raft.ServerAddress,
	args *raft.RequestPreVoteRequest, resp *raft.RequestPreVoteResponse) error {
	req := preVoteReq(args)
	tt.t.sink.Emit("rpc.send", "kind", "prevote", "peer", string(id), "req", req)
	if err := tt.NetworkTransport.RequestPreVote(id, target, args, resp); err != nil {
		tt.t.sink.Emit("rpc.fail", "kind", "prevote", "peer", string(id), "req", req)
		return err
	}
	tt.t.sink.Emit("rpc.return", "kind", "prevote", "peer", string(id), "req", req,
		"resp", map[string]any{"term": resp.Term, "granted": resp.Granted})
	return nil
}

// TimeoutNow is sent by a goroutine of the leadership transfer, which can
// outlive the leadership it was started in.
func (tt *tracedTransport) TimeoutNow(id raft.ServerID, target raft.ServerAddress,
	args *raft.TimeoutNowRequest, resp *raft.TimeoutNowResponse) error {
	req := map[string]any{}
	tt.t.sink.Emit("rpc.send", "kind", "timeoutnow", "peer", string(id), "req", req)
	if err := tt.NetworkTransport.TimeoutNow(id, target, args, resp); err != nil {
		tt.t.sink.Emit("rpc.fail", "kind", "timeoutnow", "peer", string(id), "req", req)
		return err
	}
	tt.t.sink.Emit("rpc.return", "kind", "timeoutnow", "peer", string(id), "req", req, "resp", map[string]any{})
	return nil
}

// InstallSnapshot is called by a replicator, which can outlive the
// leadership it was started in.
func (tt *tracedTransport) InstallSnapshot(id raft.ServerID, target raft.ServerAddress,
	args *raft.InstallSnapshotRequest, resp *raft.InstallSnapshotResponse, data io.Reader) error {
	req := snapReq(args)
	tt.t.sink.Emit("rpc.send", "kind", "snapshot", "peer", string(id), "req", req)
	if err := tt.NetworkTransport.InstallSnapshot(id, target, args, resp, data); err != nil {
		tt.t.sink.Emit("rpc.fail", "kind", "snapshot", "peer", string(id), "req", req)
		return err
	}
	tt.t.sink.Emit("rpc.return", "kind", "snapshot", "peer", string(id), "req", req,
		"resp", map[string]any{"term": resp.Term, "success": resp.Success})
	return nil
}

// ---- startup.

// boot reports what the node recovered from disk.
func (t *tracer) boot(stable raft.StableStore, logs raft.LogStore, snaps raft.SnapshotStore) {
	term, _ := stable.GetUint64([]byte("CurrentTerm"))
	voteTerm, _ := stable.GetUint64([]byte("LastVoteTerm"))
	voteFor, _ := stable.Get([]byte("LastVoteCand"))
	first, _ := logs.FirstIndex()
	last, _ := logs.LastIndex()
	var snapIndex, snapTerm uint64
	if list, err := snaps.List(); err == nil && len(list) > 0 {
		snapIndex, snapTerm = list[0].Index, list[0].Term
	}
	var lastTerm uint64
	if last > 0 {
		var l raft.Log
		if err := logs.GetLog(last, &l); err == nil {
			lastTerm = l.Term
		}
	}
	t.sink.Emit("boot", "term", term, "voteTerm", voteTerm, "voteFor", t.id(string(voteFor)),
		"firstIndex", first, "lastIndex", last, "lastTerm", lastTerm, "snapIndex", snapIndex, "snapTerm", snapTerm)
}
