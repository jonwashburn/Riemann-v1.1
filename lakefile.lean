import Lake
open Lake DSL

package «RiemannHypothesis» where
  -- add package configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.8.0"

-- Temporarily disable foundation_repo dependency
-- require «RecognitionScience» from "foundation_repo"

@[default_target]
lean_lib «RiemannHypothesis» where
  srcDir := "src"
  roots := #[`RiemannHypothesis]
