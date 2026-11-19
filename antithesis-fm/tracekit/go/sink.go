// Package tracekit records a program's steps so that a run can be checked
// against a model. It is independent of the program and the model.
//
// A report is a message with key/value pairs. The Sink passes it to the
// program's logger and, if TRACEKIT_SOCKET names a Unix datagram socket,
// sends it there in order and waits until it is delivered, so a report is
// not lost if the process is killed right after the step.
//
// The program must announce each durable write before making it (Do), and
// report replies and role changes when they happen (Emit). A message is
// reported when sent, which may be after the state it was built from was
// read; the model must allow that, as for a network delay.
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

// send retries while the receiver is absent or full. After a minute it stops
// reporting and says so on stderr, so an incomplete record is not mistaken
// for a complete one.
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
