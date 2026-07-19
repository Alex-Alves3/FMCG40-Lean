import Lake
open Lake DSL

package «FMCG40-Lean» where
  -- add package configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "master"

@[default_target]
lean_lib «FMCG40» where
  -- add library configuration options here
