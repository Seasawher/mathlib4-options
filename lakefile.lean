import Lake
open Lake DSL

package «options» {
  -- add any package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "3ce43c18f614b76e161f911b75a3e1ef641620ff"

@[default_target]
lean_lib «Options» {
  -- add any library configuration options here
}
