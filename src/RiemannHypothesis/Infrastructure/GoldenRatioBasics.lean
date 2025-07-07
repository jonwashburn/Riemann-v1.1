import Mathlib.Data.Real.GoldenRatio
import Mathlib.Data.Complex.Basic

/-!
# Golden–ratio convenience definitions

This module defines the complex golden ratio `φ : ℂ` and the
`ε = φ - 1 = φ⁻¹` shift that cancels the exponential
factor in the 2-regularised Fredholm determinant.

These definitions live in their own file so that other parts of the
codebase can `open RH.GoldenRatioBasics` without pulling in any heavy
Fredholm machinery.
-/

namespace RH.GoldenRatioBasics

open Complex

/-- The (complex) golden ratio `φ = (1 + √5)/2`. We reuse the real
    definition from `Mathlib` and coerce it to `ℂ`. -/
noncomputable def φ : ℂ := Complex.ofReal goldenRatio

/-- The cancellation shift ε = φ - 1 = φ⁻¹. -/
noncomputable def ε : ℂ := φ - (1 : ℂ)

/- Core algebraic identity used in Section 2 of the paper.  A full proof will
be added later. -/
lemma epsilon_mul_phi : ε * φ = (1 : ℂ) := by
  -- Use the fundamental property of the golden ratio: φ² = φ + 1
  -- Therefore φ - 1 = φ⁻¹, so ε = φ⁻¹ and ε * φ = 1
  unfold ε φ
  simp only [Complex.ofReal_sub, Complex.ofReal_one]
  -- Use the golden ratio identity: φ² = φ + 1, so φ² - φ = 1, so φ(φ - 1) = 1
  have h_golden_identity : goldenRatio ^ 2 = goldenRatio + 1 := by
    exact goldenRatio_sq
  have h_rearrange : goldenRatio * (goldenRatio - 1) = 1 := by
    rw [mul_sub, mul_one]
    rw [← pow_two] at h_golden_identity
    linarith [h_golden_identity]
  -- Convert to complex numbers
  have h_complex : (goldenRatio : ℂ) * ((goldenRatio : ℂ) - 1) = 1 := by
    rw [← Complex.ofReal_mul, ← Complex.ofReal_sub, ← Complex.ofReal_one]
    exact congr_arg Complex.ofReal h_rearrange
  -- Rearrange to get the desired form
  rw [← h_complex]
  ring

end RH.GoldenRatioBasics
