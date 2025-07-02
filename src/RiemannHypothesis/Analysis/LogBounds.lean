import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

/-!
# Bounds for `log (1-z)`

This file provides a bound for `‖log (1-z)‖` analogous to the one for
`log (1+z)`.  It is used in proving the convergence of Euler-type products.
-/

namespace RH.Analysis

open Complex

lemma norm_log_one_sub_le {z : ℂ} (hz : ‖z‖ ≤ 1/2) : ‖log (1 - z)‖ ≤ (3/2) * ‖z‖ := by
  -- We reuse the mathlib lemma for `1+z` by substituting `-z`.
  rw [sub_eq_add_neg]
  have h_neg_z : ‖-z‖ ≤ 1/2 := by simpa
  exact norm_log_one_add_half_le_self h_neg_z

end RH.Analysis
