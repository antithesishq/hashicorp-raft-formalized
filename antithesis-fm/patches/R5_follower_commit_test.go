//go:build patchtest

// Reproducer for patch R5 (see README.md): fails on upstream raft and passes
// with the patch.
package patches

import (
	"io"
	"testing"
	"time"

	"github.com/hashicorp/raft"
)

type recordingFSM chan string

func (f recordingFSM) Apply(l *raft.Log) interface{}       { f <- string(l.Data); return nil }
func (f recordingFSM) Snapshot() (raft.FSMSnapshot, error) { return nil, io.EOF }
func (f recordingFSM) Restore(rc io.ReadCloser) error      { return rc.Close() }

// A follower holds an entry at index 2 from a term-2 leader that never
// committed it. The leader of term 3, elected with last index 1, has committed
// its own entry at index 2 through the third server, and sends the follower
// the request its replicator built at election time: previous entry 1, no
// entries, with the commit index read afterwards.
func TestFollowerDoesNotCommitStaleTail(t *testing.T) {
	conf := raft.DefaultConfig()
	conf.LocalID = "f"
	conf.HeartbeatTimeout, conf.ElectionTimeout = time.Minute, time.Minute
	store, snaps := raft.NewInmemStore(), raft.NewInmemSnapshotStore()
	addr, trans := raft.NewInmemTransport("f")
	servers := raft.Configuration{Servers: []raft.Server{{ID: "f", Address: addr}, {ID: "l", Address: "l"}, {ID: "g", Address: "g"}}}
	if err := raft.BootstrapCluster(conf, store, store, snaps, trans, servers); err != nil {
		t.Fatal(err)
	}
	fsm := make(recordingFSM, 8)
	r, err := raft.NewRaft(conf, fsm, store, store, snaps, trans)
	if err != nil {
		t.Fatal(err)
	}
	defer r.Shutdown()

	_, leader := raft.NewInmemTransport("l")
	leader.Connect(addr, trans)
	send := func(term, commit uint64, entries ...*raft.Log) {
		t.Helper()
		req := &raft.AppendEntriesRequest{
			RPCHeader: raft.RPCHeader{ProtocolVersion: conf.ProtocolVersion, ID: []byte("l"), Addr: []byte("l")},
			Term:      term, PrevLogEntry: 1, PrevLogTerm: 1, Entries: entries, LeaderCommitIndex: commit,
		}
		var resp raft.AppendEntriesResponse
		if err := leader.AppendEntries("f", addr, req, &resp); err != nil || !resp.Success {
			t.Fatalf("append in term %d: success=%v err=%v", term, resp.Success, err)
		}
	}

	send(2, 1, &raft.Log{Index: 2, Term: 2, Type: raft.LogCommand, Data: []byte("stale")})
	send(3, 2)
	if c := r.CommitIndex(); c != 1 {
		t.Errorf("commit index %d after a request covering index 1: the follower committed its own entry at index 2", c)
	}
	send(3, 2, &raft.Log{Index: 2, Term: 3, Type: raft.LogCommand, Data: []byte("leader")})
	if c := r.CommitIndex(); c != 2 {
		t.Errorf("commit index %d, want 2", c)
	}
	select {
	case got := <-fsm:
		if got != "leader" {
			t.Errorf("state machine was handed %q at index 2; the committed entry is \"leader\"", got)
		}
	case <-time.After(5 * time.Second):
		t.Error("nothing applied")
	}
}
