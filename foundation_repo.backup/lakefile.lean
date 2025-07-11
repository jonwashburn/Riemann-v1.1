import Lake
open Lake DSL

package «RecognitionScience» where
  -- Minimal package configuration

lean_lib «RecognitionScience» where
  srcDir := "."
  roots := #[`RecognitionScience]
