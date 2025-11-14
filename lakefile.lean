import Lake
open Lake DSL

package «qkd» where
  srcDir := "."

@[default_target]
lean_lib «QKD» where
  srcDir := "."

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

require checkdecls from git "https://github.com/PatrickMassot/checkdecls.git"

meta if get_config? env = some "dev" then
require «doc-gen4» from git
  "https://github.com/leanprover/doc-gen4" @ "main"