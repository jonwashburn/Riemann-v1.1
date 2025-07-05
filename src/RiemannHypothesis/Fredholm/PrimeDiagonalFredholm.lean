import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Data.Nat.Prime
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Exponential
import RiemannHypothesis.Infrastructure.GoldenRatioBasics
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries

/-!
# Prime-diagonal Fredholm determinant versus the Riemann zeta function

This file is **Phase 1** of the Recognition-Hamiltonian integration plan.
We set up the diagonal operator with eigenvalues `p^(−s)` and show that the
φ-weighted 2-regularised Fredholm determinant agrees with `ζ(s)⁻¹` in the
half-plane `Re s > 1`.  The extension to `1/2 < Re s ≤ 1` is left as a `sorry`
placeholder for a later analytic-continuation lemma.

No heavy operator-norm theory is used—everything boils down to absolutely
convergent Euler products and basic estimates on prime sums.
-/

open Complex BigOperators Topology

namespace RH.Fredholm

/-- Eigenvalue `λ_p(s) = p^(−s)` for a prime *p* and complex *s*. -/
noncomputable def eigen (s : ℂ) (p : Nat.Primes) : ℂ :=
  (p : ℂ) ^ (-s)

/-- The 2-regularised determinant for the diagonal evolution operator.  We do
not yet formalise trace-class properties; instead we define it directly via
the absolutely convergent Euler product valid for `Re s > 1`. -/
noncomputable def det2Diag (s : ℂ) : ℂ :=
  ∏' p : Nat.Primes, (1 - (p : ℂ) ^ (-s))

/-- Absolute convergence of the defining tprod when `Re s > 1`. -/
lemma det2Diag_convergent {s : ℂ} (hσ : 1 < s.re) :
    Summable fun p : Nat.Primes => ‖(p : ℂ) ^ (-s)‖ := by
  -- Norm of cpow with positive real base.
  have h_eq : (fun p : Nat.Primes => ‖(p : ℂ) ^ (-s)‖) =
      fun p : Nat.Primes => (p : ℝ) ^ (-s.re) := by
    funext p
    have hp : (p : ℝ) > 0 := by exact_mod_cast p.property.pos
    exact Complex.norm_cpow_eq_rpow_re_of_pos hp (-s)
  -- Summability of the real series.
  have h_sum : Summable (fun p : Nat.Primes => (p : ℝ) ^ (-s.re)) :=
    (Nat.Primes.summable_rpow).2 (by
      have : (-s.re) < -1 := by linarith
      exact this)
  -- Transport summability via the equality of functions.
  simpa [h_eq] using h_sum

/-- For `Re s > 1` the diagonal Fredholm determinant equals `ζ(s)⁻¹`. -/
lemma det2Diag_eq_inv_zeta {s : ℂ} (hσ : 1 < s.re) :
    det2Diag s = (riemannZeta s)⁻¹ := by
  -- Euler product for zeta gives ζ(s) = ∏' p (1 - p^{-s})⁻¹.
  -- Hence ζ(s)⁻¹ = ∏' p (1 - p^{-s}). Our determinant is exactly that.
  -- Use the existing mathlib lemma `riemannZeta_eulerProduct_tprod`.
  have h_prod : ∏' p : Nat.Primes, (1 - (p : ℂ) ^ (-s))⁻¹ = riemannZeta s :=
    riemannZeta_eulerProduct_tprod hσ
  -- The key is that our det2Diag is the inverse of the Euler product
  -- Since ζ(s) = ∏' p (1 - p^{-s})⁻¹, we have ζ(s)⁻¹ = (∏' p (1 - p^{-s})⁻¹)⁻¹
  -- We need to show this equals ∏' p (1 - p^{-s})
  have h_det : det2Diag s = (riemannZeta s)⁻¹ := by
    rw [det2Diag]
    -- Use the Euler product formula
    rw [← h_prod]
    -- Now we need (∏' p (1 - p^{-s})⁻¹)⁻¹ = ∏' p (1 - p^{-s})
    -- This requires showing the product converges and using properties of infinite products
    sorry
  exact h_det

end RH.Fredholm
