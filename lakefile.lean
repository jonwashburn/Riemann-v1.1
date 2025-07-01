import Lake
open Lake DSL

package «RiemannHypothesis» where
  -- add package configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «RiemannHypothesis» where
  srcDir := "src"
  roots := #[`RiemannHypothesis]
