import Lake
open Lake DSL

-- Veil at a pinned commit (Lean 4.35.0), fetched by Lake into .lake/packages.
require veil from git "https://github.com/verse-lab/veil.git" @ "1287c31d0d62e7ae069993845fe7e5d9736b8fba"

package raftveil

@[default_target]
lean_lib RaftVeil
