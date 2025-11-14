import Lake
open Lake DSL

package «qkd» where
  srcDir := "."

@[default_target]
lean_lib «QKD» where
  srcDir := "."

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"
