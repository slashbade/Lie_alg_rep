import Lake
open Lake DSL

package «Lie_alg_rep» where
  -- add package configuration options here

@[default_target]
lean_lib «LieAlgRep» where
  -- add library configuration options here


require mathlib from git
  "https://github.com/leanprover-community/mathlib4"
