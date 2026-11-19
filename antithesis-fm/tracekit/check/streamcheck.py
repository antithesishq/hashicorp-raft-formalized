#!/usr/bin/env python3
"""Check a trace stream against a TLA+ stream spec, in step with its writer.

    streamcheck.py MANIFEST STREAM_FILE

MANIFEST (JSON, paths relative to it) names the stream spec:
    {"stream_spec": "Binding.tla", "stream_config": "Binding.cfg",
     "tools": "../tracekit/tools", "classes": "../tracekit/stream/classes",
     "library": ["../tracekit/tla"]}
TRACEKIT_STREAM_CONFIG, if set, names another configuration file for the same
spec (for example one that sets a constant of the model differently).
STREAM_FILE is an ndjson file that something is appending to: every node's
events in one order. TLC blocks on each next line (stream/TraceKit.java). The
writer signals the end by creating STREAM_FILE.eof.

One line is printed when TLC stops:
    ACCEPTED n          the stream ended and all n events matched the model
    REJECTED k <event>  no model state can take event k (k-1 events matched)
    VIOLATED k <names>  the model's safety properties broke at event k
    ERROR <text>        TLC failed
While it runs, STREAM_FILE.progress holds the index of the event TLC is
waiting for or working on.

TLC_HEAP and TLC_STACK set the JVM's heap (default 2g) and thread stack
(default 256m).

Exit status: 0 accepted, 1 rejected or violated, 2 error.
"""
import json
import os
import re
import subprocess
import sys
import tempfile


def main():
    if len(sys.argv) != 3:
        sys.exit(__doc__)
    manifest, stream = sys.argv[1], os.path.abspath(sys.argv[2])
    base = os.path.dirname(os.path.abspath(manifest))
    m = json.load(open(manifest))
    tools = os.path.join(base, m.get("tools", "../tools"))
    cp = os.pathsep.join([os.path.join(base, m.get("classes", "../stream/classes")),
                          os.path.join(tools, "tla2tools.jar"),
                          os.path.join(tools, "CommunityModules-deps.jar")])
    libs = os.pathsep.join(os.path.join(base, d) for d in m.get("library", []))
    progress = stream + ".progress"
    env = dict(os.environ, TRACE_STREAM=stream, TRACE_PROGRESS=progress)
    with tempfile.TemporaryDirectory(prefix="streamcheck-") as meta:
        # Large stack: TLC's recursive evaluation goes as deep as the number of
        # point updates to a value over a long run, and as deep as the step formula.
        cmd = ["java", "-XX:+UseSerialGC", "-Xmx" + os.environ.get("TLC_HEAP", "2g"),
               "-Xss" + os.environ.get("TLC_STACK", "256m"),
               "-DTLA-Library=" + libs, "-cp", cp,
               "tlc2.TLC", "-workers", "1", "-metadir", meta, "-noGenerateSpecTE",
               "-config", os.environ.get("TRACEKIT_STREAM_CONFIG") or m["stream_config"], m["stream_spec"]]
        p = subprocess.run(cmd, cwd=base, env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
    out = p.stdout
    open(stream + ".tlc.out", "w").write(out)
    at = int(open(progress).read()) if os.path.exists(progress) else 0
    lines = [l for l in open(stream) if l.strip()] if os.path.exists(stream) else []
    event = lines[at - 1].strip()[:1500] if 0 < at <= len(lines) else ""
    violated = [v for v in re.findall(r"(?:Invariant|Action property|Temporal property) (\w+) (?:is|was) violated", out)]
    if violated:
        names = sorted(set(violated))
        if "Safe" in names:
            # Names of broken properties: from `viol` in the last state TLC
            # prints or, when TLC cannot print it (events not buffered), from
            # Note(name, i) at the violating step.
            found = re.search(r"viol = (\{[^}]*\})", out.split("State ")[-1])
            if found:
                broken = re.findall(r'"(\w+)"', found.group(1))
            else:
                notes = [l.split() for l in open(progress + ".notes")] if os.path.exists(progress + ".notes") else []
                last = max((int(l[0]) for l in notes if len(l) == 2), default=0)
                broken = sorted({l[1] for l in notes if len(l) == 2 and int(l[0]) == last and re.fullmatch(r"[A-Z][A-Za-z]+", l[1])})
            names = [n for n in names if n != "Safe"] + (broken or ["Safe"])
        # TLC checks a state when it makes it, so event `at` broke the property.
        print(f"VIOLATED {at} {','.join(names)}")
        return 1
    if "Model checking completed" not in out:
        # TLC's error lines and any Java exception's name and message.
        err = " ".join(l.strip() for l in out.splitlines()
                       if "rror" in l or "xception" in l or l.startswith(": "))[:1500]
        print(f"ERROR {err or 'TLC stopped without a result'}")
        return 2
    if os.path.exists(stream + ".eof") and at == len(lines) + 1:
        print(f"ACCEPTED {len(lines)}")
        return 0
    print(f"REJECTED {at} {event}")
    return 1


if __name__ == "__main__":
    sys.exit(main())
