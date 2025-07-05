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
  -- Key fact: φ² = φ + 1, so φ - 1 = 1/φ
  -- Therefore ε * φ = (φ - 1) * φ = φ² - φ = (φ + 1) - φ = 1
  simp only [ε]
  ring_nf
  -- Use the defining property of the golden ratio
  have h : (goldenRatio : ℝ) ^ 2 = goldenRatio + 1 := goldenRatio_sq
  -- Transfer to complex numbers
  have hc : (φ : ℂ) ^ 2 = φ + 1 := by
    simp only [φ, sq]
    rw [← Complex.ofReal_mul, ← Complex.ofReal_add, ← Complex.ofReal_one, h]
  -- Now compute (φ - 1) * φ = φ² - φ = (φ + 1) - φ = 1
  rw [sub_mul, one_mul, hc]
  ring

end RH.GoldenRatioBasics
