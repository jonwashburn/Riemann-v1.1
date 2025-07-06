import Lake
open Lake DSL

package «RiemannHypothesis» where
  -- add package configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

-- Local dependency: RecognitionScience foundation library
-- Pin ProofWidgets to a specific release tag so we don't accidentally pull `main` (which
-- might depend on a newer Lean/nightly and require an `npm` build).  Lean 4.22 works with
-- ProofWidgets4 v0.0.66.
require proofwidgets from git "https://github.com/leanprover-community/ProofWidgets4" @ "v0.0.66"
require «RecognitionScience» from "foundation_repo"

@[default_target]
lean_lib «RiemannHypothesis» where
  srcDir := "src"
  roots := #[`RiemannHypothesis]
