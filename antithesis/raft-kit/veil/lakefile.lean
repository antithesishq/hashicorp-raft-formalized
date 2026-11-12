import Lake
open Lake DSL

-- Veil is used from a local checkout (commit 1287c31d, Lean 4.35.0), built
-- once there. To fetch it instead:
--   require veil from git "https://github.com/verse-lab/veil.git" @ "1287c31d"
require veil from "../../../../../veil"

package raftveil

@[default_target]
lean_lib RaftVeil
