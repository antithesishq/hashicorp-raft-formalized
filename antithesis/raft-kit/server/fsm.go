package main

import (
	"encoding/binary"
	"encoding/json"
	"fmt"
	"io"
	"sync"

	"github.com/antithesishq/antithesis-sdk-go/assert"
	"github.com/hashicorp/raft"
)

// A command adds Value to the running sum. Op is a unique id the client
// picked, so every applied entry can be attributed to exactly one request.
type command struct {
	Op    uint64
	Value int64
}

const commandLen = 16

func encodeCommand(c command) []byte {
	b := make([]byte, commandLen)
	binary.BigEndian.PutUint64(b[0:8], c.Op)
	binary.BigEndian.PutUint64(b[8:16], uint64(c.Value))
	return b
}

func decodeCommand(b []byte) (command, error) {
	if len(b) != commandLen {
		return command{}, fmt.Errorf("bad command length %d", len(b))
	}
	return command{
		Op:    binary.BigEndian.Uint64(b[0:8]),
		Value: int64(binary.BigEndian.Uint64(b[8:16])),
	}, nil
}

// fsmState is everything the FSM holds. Index is the log index of the last
// applied command; Digest chains every applied (index, term, op, value), so
// two nodes with the same digest at an index applied the same history.
type fsmState struct {
	Index  uint64 `json:"index"`
	Term   uint64 `json:"term"`
	Sum    int64  `json:"sum"`
	Count  uint64 `json:"count"`
	Digest uint64 `json:"digest"`
}

type applyResult struct {
	Index uint64
	Sum   int64
}

type sumFSM struct {
	node string
	mu   sync.Mutex
	st   fsmState
}

func mix(h, x uint64) uint64 {
	// splitmix64-style mixing, chained.
	h ^= x + 0x9e3779b97f4a7c15 + (h << 6) + (h >> 2)
	h ^= h >> 30
	h *= 0xbf58476d1ce4e5b9
	h ^= h >> 27
	h *= 0x94d049bb133111eb
	h ^= h >> 31
	return h
}

func (f *sumFSM) Apply(l *raft.Log) interface{} {
	c, err := decodeCommand(l.Data)
	if err != nil {
		assert.Unreachable("the state machine only receives well-formed commands",
			map[string]any{"node": f.node, "index": l.Index, "len": len(l.Data)})
		return err
	}
	f.mu.Lock()
	prev := f.st
	assert.Always(l.Index > prev.Index, "a node applies commands in strictly increasing log index order",
		map[string]any{"node": f.node, "index": l.Index, "prev_index": prev.Index})
	assert.Always(l.Term >= prev.Term, "a node applies commands in non-decreasing term order",
		map[string]any{"node": f.node, "index": l.Index, "term": l.Term, "prev_term": prev.Term})
	f.st.Index = l.Index
	f.st.Term = l.Term
	f.st.Sum += c.Value
	f.st.Count++
	f.st.Digest = mix(mix(mix(mix(prev.Digest, l.Index), l.Term), c.Op), uint64(c.Value))
	st := f.st
	f.mu.Unlock()

	logLine("msg=raft-apply index=%d term=%d op=%d value=%d sum=%d count=%d digest=%d",
		st.Index, st.Term, c.Op, c.Value, st.Sum, st.Count, st.Digest)
	return applyResult{Index: st.Index, Sum: st.Sum}
}

func (f *sumFSM) state() fsmState {
	f.mu.Lock()
	defer f.mu.Unlock()
	return f.st
}

func (f *sumFSM) Snapshot() (raft.FSMSnapshot, error) {
	return &sumSnapshot{st: f.state()}, nil
}

func (f *sumFSM) Restore(rc io.ReadCloser) error {
	defer rc.Close()
	var st fsmState
	if err := json.NewDecoder(rc).Decode(&st); err != nil {
		assert.Unreachable("a node can always decode a snapshot",
			map[string]any{"node": f.node, "error": err.Error()})
		return err
	}
	f.mu.Lock()
	prev := f.st
	f.st = st
	f.mu.Unlock()
	if st.Index < prev.Index {
		// Not a safety violation by itself (the node replays the same entries
		// afterwards), but worth knowing about.
		logLine("msg=raft-restore-backwards from=%d to=%d", prev.Index, st.Index)
	}
	logLine("msg=raft-restore index=%d term=%d sum=%d count=%d digest=%d",
		st.Index, st.Term, st.Sum, st.Count, st.Digest)
	return nil
}

type sumSnapshot struct{ st fsmState }

func (s *sumSnapshot) Persist(sink raft.SnapshotSink) error {
	err := json.NewEncoder(sink).Encode(s.st)
	if err != nil {
		_ = sink.Cancel()
		return err
	}
	return sink.Close()
}

func (s *sumSnapshot) Release() {}
