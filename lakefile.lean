import Lake
open Lake DSL

package «RiemannHypothesis» where
  -- add package configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.3.0"

-- Local dependency: RecognitionScience foundation library
-- Pin ProofWidgets to a specific release tag so we don't accidentally pull `main`.
-- Lean 4.3 pairs with ProofWidgets4 v0.0.67.
-- (ProofWidgets removed for now to avoid incompatibility with Lean 4.3)
require «RecognitionScience» from "foundation_repo"

@[default_target]
lean_lib «RiemannHypothesis» where
  srcDir := "src"
  roots := #[`RiemannHypothesis]
