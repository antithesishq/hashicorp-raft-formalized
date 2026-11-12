#!/usr/bin/env node
// Runs the reducer over a recorded stream, as the search query would.
//
//   check.js STREAM.ndjson
//
// Prints one line, in the stream checker's format:
//   ACCEPTED n | REJECTED k why | VIOLATED k name
// Exit status: 0 accepted, 1 rejected or violated.
const fs = require("fs");
const path = require("path");
const step = eval(fs.readFileSync(path.join(__dirname, "reducer.js"), "utf8"));
let s = JSON.parse(fs.readFileSync(path.join(__dirname, "init.json"), "utf8"));
const lines = fs.readFileSync(process.argv[2], "utf8").split("\n").filter((l) => l.trim());
let k = 0;
for (const line of lines) {
  const ev = JSON.parse(line);
  k++;
  if (ev.k === undefined) ev.k = k;   // streams recorded before lines were numbered
  const [found, next] = step(s, ev);
  s = next;
  if (found.length) {
    const f = found[0];
    console.log((f.kind === "violated" ? "VIOLATED " : "REJECTED ") + ev.k + " " + f.why);
    process.exit(1);
  }
}
console.log("ACCEPTED " + lines.length);
