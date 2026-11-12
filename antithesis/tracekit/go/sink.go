// Package tracekit records a program's steps so that a run can be checked
// against a model. It knows nothing about any particular program or model.
//
// A program reports a step as a message with key/value pairs, exactly as it
// would log it. The Sink does two things with a report:
//
//   - it hands it to the program's ordinary logger, so a run without any
//     checker just produces verbose logs;
//   - if TRACEKIT_SOCKET names a Unix datagram socket, it also sends it
//     there, in order, and waits until the receiver has it. A report is
//     therefore never lost when the process is killed right after the step,
//     and the order of reports at the receiver is the order they were made.
//
// Two rules make the reports a faithful record. The Sink provides the
// mechanism for each; the program has to use it at the right places.
//
//  1. Announce a durable write before making it (Do). After a kill, every
//     write but the last announced one is known to have happened.
//  2. Report a reply or a role change when it happens (Emit).
//
// A message that one goroutine builds from state another goroutine writes
// is reported when it is sent, which can be later than the read. The Sink
// does not hide that: the model must allow a message to be sent any time
// after the state it was built from existed, as a network delay would.
package tracekit

import (
	"encoding/json"
	"fmt"
	"net"
	"os"
	"strconv"
	"sync"
	"time"
)

// Sink orders and delivers reports. All methods are safe for concurrent use.
type Sink struct {
	mu   sync.Mutex
	log  func(msg string, kv ...any)
	path string
	conn *net.UnixConn
	host string
	boot string
	seq  uint64
}

// New returns a Sink. log receives every report (it may be nil); it is
// called with the Sink's lock held and must not call back into the Sink.
func New(log func(msg string, kv ...any)) *Sink {
	host, _ := os.Hostname()
	return &Sink{
		log:  log,
		path: os.Getenv("TRACEKIT_SOCKET"),
		host: host,
		boot: strconv.FormatInt(time.Now().UnixNano(), 10),
	}
}

// Emit reports one step.
func (s *Sink) Emit(msg string, kv ...any) {
	s.mu.Lock()
	defer s.mu.Unlock()
	s.emit(msg, kv)
}

// Do announces a step and then performs it, as one unit with respect to
// every other report. Use it for durable writes.
func (s *Sink) Do(fn func() error, msg string, kv ...any) error {
	s.mu.Lock()
	defer s.mu.Unlock()
	s.emit(msg, kv)
	return fn()
}

func (s *Sink) emit(msg string, kv []any) {
	if s.log != nil {
		s.log(msg, kv...)
	}
	if s.path == "" {
		return
	}
	ev := map[string]any{"e": msg}
	for i := 0; i+1 < len(kv); i += 2 {
		ev[fmt.Sprint(kv[i])] = kv[i+1]
	}
	s.seq++
	data, err := json.Marshal(map[string]any{
		"container": s.host, "boot": s.boot, "seq": s.seq, "ev": ev,
	})
	if err != nil {
		panic(fmt.Errorf("tracekit: cannot encode %q: %v", msg, err))
	}
	s.send(data)
}

// send waits for the receiver if it is not there yet or its queue is full.
// After a minute without a receiver it stops sending, loudly: a record with
// a hole must not look complete.
func (s *Sink) send(data []byte) {
	deadline := time.Now().Add(time.Minute)
	for {
		if s.conn == nil {
			c, err := net.DialUnix("unixgram", nil, &net.UnixAddr{Name: s.path, Net: "unixgram"})
			if err == nil {
				s.conn = c
			}
		}
		if s.conn != nil {
			if _, err := s.conn.Write(data); err == nil {
				return
			}
			_ = s.conn.Close()
			s.conn = nil
		}
		if time.Now().After(deadline) {
			fmt.Fprintf(os.Stderr, "tracekit: receiver %s unreachable, reporting stopped\n", s.path)
			s.path = ""
			return
		}
		time.Sleep(20 * time.Millisecond)
	}
}
