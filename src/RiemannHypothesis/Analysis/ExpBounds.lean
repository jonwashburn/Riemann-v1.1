import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Complex.Abs

/-!
# Elementary bounds for the complex exponential

This tiny helper file collects a uniform Lipschitz‐type bound on `exp z − 1`
that is convenient when proving convergence of Euler products with
`exp (p^{-s})` factors.

We only need a crude estimate: whenever `‖z‖ ≤ 1` we have

``‖exp z - 1‖ ≤ 2 * ‖z‖.``

A sharper constant is possible but irrelevant.
-/

open Complex Real

namespace RH.Analysis

lemma exp_sub_one_bound {z : ℂ} (h : ‖z‖ ≤ 1) : ‖Complex.exp z - 1‖ ≤ 2 * ‖z‖ := by
  -- We reuse the bundled lemma `Complex.norm_exp_sub_one_le` from mathlib.
  simpa using Complex.norm_exp_sub_one_le h

end RH.Analysis
