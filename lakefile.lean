import Lake
open Lake DSL

package «options» {
  -- add any package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "33e0d3e665fb66f3a41f40e5033e75f8750b9389"

@[default_target]
lean_lib «Options» {
  -- add any library configuration options here
}
