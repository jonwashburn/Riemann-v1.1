import Lake
open Lake DSL

package «RiemannHypothesis» where
  -- add package configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.8.0"

-- Local dependency: RecognitionScience foundation library
require «RecognitionScience» from "foundation_repo"

@[default_target]
lean_lib «RiemannHypothesis» where
  srcDir := "src"
  roots := #[`RiemannHypothesis]
