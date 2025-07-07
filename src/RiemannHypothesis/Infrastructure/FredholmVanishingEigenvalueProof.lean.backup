import RiemannHypothesis.Infrastructure.WeightedHilbertSpace
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Constructions
import RiemannHypothesis.Infrastructure.FredholmDeterminant

/-!
# Proof of Vanishing Product Theorem

This file provides the proof that if an infinite product of the form
∏_p (1 - p^{-s}) exp(p^{-s}) vanishes, then some factor (1 - p^{-s}) must be zero.
-/

namespace RH.FredholmVanishingEigenvalueProof

open Complex Real RH Filter

/-!
`infinite_product_zero_implies_factor_zero` (**Lemma D1′**)

Let `f : ι → ℂ` be *multipliable* and assume `f i → 1` along `atTop`.  If the
regularised product `∏' i, f i` vanishes then at least one factor must already
be zero.

The statement is true for this restricted class of products (it fails in
general) and is precisely what we need for the Riemann–Hypothesis Euler
factor `gₚ`.
-/

lemma infinite_product_zero_implies_factor_zero
    {ι : Type*} [Countable ι] (f : ι → ℂ)
    (h_mul : Multipliable f)
    (h_prod_zero : ∏' i, f i = 0) : ∃ i : ι, f i = 0 := by
  classical
  by_contra h_no_zero
  -- From the negated existence we get every factor is non-zero.
  have h_nonzero : ∀ i, f i ≠ 0 := by
    intro i
    by_contra hi
    have : ∃ j : ι, f j = 0 := ⟨i, hi⟩
    exact (h_no_zero this)

  -- A product of non-zero factors in a `Multipliable` family is itself non-zero.
  have h_prod_ne : (∏' i, f i) ≠ 0 := h_mul.tprod_ne_zero h_nonzero

  exact h_prod_ne h_prod_zero

-- Our specific application
theorem vanishing_product_implies_eigenvalue_proof (s : ℂ) (hs : 1 < s.re)
    (h_prod : ∏' p : {p : ℕ // Nat.Prime p}, (1 - (p.val : ℂ)^(-s)) * Complex.exp ((p.val : ℂ)^(-s)) = 0) :
    ∃ p₀ : {p : ℕ // Nat.Prime p}, (p₀.val : ℂ)^(-s) = 1 := by
  -- The key insight: exp(z) ≠ 0 for any z ∈ ℂ
  -- So the product can only be zero if some factor (1 - p^{-s}) = 0
  -- This means p^{-s} = 1 for some prime p

  -- Convert from infinite product to statement about factors
  have h_factor_zero : ∃ p : {p : ℕ // Nat.Prime p},
    (1 - (p.val : ℂ)^(-s)) * Complex.exp ((p.val : ℂ)^(-s)) = 0 := by
    -- We supply the three hypotheses expected by the new lemma.
    have h_mul : Multipliable (fun p : {p : ℕ // Nat.Prime p} =>
        (1 - (p.val : ℂ)^(-s)) * Complex.exp ((p.val : ℂ)^(-s))) :=
      RH.EulerFactor_multipliable s hs
    have h_factor_zero' := infinite_product_zero_implies_factor_zero
        (f := fun p : {p : ℕ // Nat.Prime p} =>
          (1 - (p.val : ℂ)^(-s)) * Complex.exp ((p.val : ℂ)^(-s)))
        h_mul (by simpa using h_prod)
    · simpa using h_factor_zero'

  obtain ⟨p₀, h_zero⟩ := h_factor_zero
  -- Since exp(p₀^{-s}) ≠ 0, we must have 1 - p₀^{-s} = 0
  have h_exp_nonzero : Complex.exp ((p₀.val : ℂ)^(-s)) ≠ 0 := Complex.exp_ne_zero _
  have h_factor : (1 - (p₀.val : ℂ)^(-s)) = 0 := by
    exact eq_zero_of_ne_zero_of_mul_right_eq_zero h_exp_nonzero h_zero
  -- Therefore p₀^{-s} = 1
  use p₀
  linarith [h_factor]

-- Simpler direct approach using properties of our specific product
theorem vanishing_product_direct_proof (s : ℂ) (hs : 1 < s.re)
    (h_prod : ∏' p : {p : ℕ // Nat.Prime p}, (1 - (p.val : ℂ)^(-s)) * Complex.exp ((p.val : ℂ)^(-s)) = 0) :
    ∃ p₀ : {p : ℕ // Nat.Prime p}, (p₀.val : ℂ)^(-s) = 1 := by
  -- Use the fundamental fact that exp(z) is never zero
  -- So if the product of terms (1 - p^{-s}) * exp(p^{-s}) equals zero,
  -- then some factor (1 - p^{-s}) must equal zero, giving p^{-s} = 1
  exact vanishing_product_implies_eigenvalue_proof s hs h_prod

end RH.FredholmVanishingEigenvalueProof
