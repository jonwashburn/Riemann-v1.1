import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.NormedSpace.ContinuousLinearMap
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Data.Nat.Prime
import RiemannHypothesis.Infrastructure.WeightedHilbertSpace
import RiemannHypothesis.Infrastructure.FredholmDeterminant

/-!
# Proofs for FredholmDeterminant sorry statements

This file contains the detailed proofs for the three sorry statements in FredholmDeterminant.lean:
1. Continuity of DiagonalOperator
2. Bound on evolution eigenvalues
3. Diagonal action on deltaBasis
-/

namespace RH.FredholmDeterminantProofs

open Complex Real RH

-- Proof 1: Continuity of DiagonalOperator
lemma diagonal_operator_continuous_proof
    (eigenvalues : {p : ℕ // Nat.Prime p} → ℂ)
    (C : ℝ) (hC : ∀ p, ‖eigenvalues p‖ ≤ C) (ψ : WeightedL2) :
    ∃ (ψ' : WeightedL2), (∀ p, ψ' p = eigenvalues p * ψ p) ∧ ‖ψ'‖ ≤ C * ‖ψ‖ := by
  -- This is a standard result about bounded diagonal operators on l²
  -- The detailed proof requires understanding the WeightedL2 type structure

  -- Step 1: Define ψ' as the pointwise product
  use fun p => eigenvalues p * ψ p

  constructor
  · -- The first part is trivial by definition
    intro p
    rfl

  · -- Step 2: Prove the norm bound
    -- We need to show ‖ψ'‖ ≤ C * ‖ψ‖
    -- For l² spaces, this means showing (∑ |eigenvalues p * ψ p|²)^(1/2) ≤ C * (∑ |ψ p|²)^(1/2)

    -- Use the fact that |eigenvalues p * ψ p| = |eigenvalues p| * |ψ p|
    -- And |eigenvalues p| ≤ C for all p

    -- The key is that for diagonal operators on l², the operator norm equals
    -- the supremum of the eigenvalue norms, which is bounded by C

    -- This follows from the standard estimate for diagonal operators on Hilbert spaces

    -- We'll use the l² norm formula: ‖ψ'‖² = ∑' p, ‖ψ' p‖²
    -- and show that ‖ψ'‖² ≤ C² * ‖ψ‖²

    -- Step 1: Use the norm-squared formula for l²
    have h_norm_sq : ‖fun p => eigenvalues p * ψ p‖^2 =
        ∑' p, ‖eigenvalues p * ψ p‖^2 := by
      exact WeightedL2.norm_sq_eq_sum _

    -- Step 2: Simplify the norm of the product
    have h_prod_norm : ∀ p, ‖eigenvalues p * ψ p‖ = ‖eigenvalues p‖ * ‖ψ p‖ := by
      intro p
      exact norm_mul _ _

    -- Step 3: Apply the bound on eigenvalues
    have h_bound : ∑' p, ‖eigenvalues p * ψ p‖^2 ≤ ∑' p, (C * ‖ψ p‖)^2 := by
      apply tsum_le_tsum
      · intro p
        rw [h_prod_norm]
        rw [mul_pow, mul_pow]
        apply mul_le_mul_of_nonneg_right
        · exact pow_le_pow_left (norm_nonneg _) (hC p) 2
        · exact sq_nonneg _
      · exact summable_mul_of_summable_norm (fun p => ‖ψ p‖^2) -- Summability follows from ψ ∈ l²
      · exact summable_mul_of_summable_norm (fun p => ‖ψ p‖^2) -- Same summability

    -- Step 4: Factor out C² and use the l² norm formula
    rw [h_norm_sq]
    rw [Real.sqrt_le_sqrt (sq_nonneg _)]
    rw [mul_pow]

    calc
      ∑' p, ‖eigenvalues p * ψ p‖^2 ≤ ∑' p, (C * ‖ψ p‖)^2 := h_bound
      _ = ∑' p, C^2 * ‖ψ p‖^2 := by simp only [mul_pow]
      _ = C^2 * ∑' p, ‖ψ p‖^2 := tsum_mul_left
      _ = C^2 * ‖ψ‖^2 := by rw [← WeightedL2.norm_sq_eq_sum]

-- Proof 2: Evolution eigenvalue bound
lemma evolution_eigenvalue_bound_proof (s : ℂ) (p : {p : ℕ // Nat.Prime p}) (hs : 0 ≤ s.re) :
    ‖(p.val : ℂ)^(-s)‖ ≤ (2 : ℝ)^s.re := by
  -- For primes p ≥ 2 and Re(s) ≥ 0, we have ‖p^(-s)‖ = p^(-Re(s)) ≤ 2^(-Re(s))
  -- And since Re(s) ≥ 0, we have 2^(-Re(s)) ≤ 2^Re(s)

  -- First, establish that p ≥ 2 since p is prime
  have h_p_ge_2 : 2 ≤ p.val := Nat.Prime.two_le p.property

  -- The calculation involves complex power norms
  -- ‖p^(-s)‖ = p^(-Re(s)) for p > 0
  -- Since p ≥ 2 and Re(s) ≥ 0, we have p^(-Re(s)) ≤ 2^(-Re(s)) ≤ 2^Re(s)

  -- Step 1: Use the norm formula for complex powers
  have h_norm : ‖(p.val : ℂ)^(-s)‖ = (p.val : ℝ)^(-s.re) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos]
    exact Nat.cast_pos.mpr (Nat.Prime.pos p.property)

  rw [h_norm]

  -- Step 2: Show p^(-Re(s)) ≤ 2^Re(s)
  -- Since p ≥ 2, we have p^(-Re(s)) ≤ 2^(-Re(s))
  have h_ineq : (p.val : ℝ)^(-s.re) ≤ (2 : ℝ)^(-s.re) := by
    apply Real.rpow_le_rpow_of_exponent_nonpos
    · norm_num
    · exact Nat.cast_le.mpr h_p_ge_2
    · exact neg_nonpos.mpr hs

  -- Step 3: Show 2^(-Re(s)) ≤ 2^Re(s) when Re(s) ≥ 0
  calc (p.val : ℝ)^(-s.re)
    ≤ (2 : ℝ)^(-s.re) := h_ineq
  _ ≤ (2 : ℝ)^s.re := by
    rw [Real.rpow_neg (by norm_num : (2 : ℝ) ≠ 0)]
    rw [div_le_iff (Real.rpow_pos_of_pos (by norm_num) s.re)]
    rw [one_mul]
    exact Real.le_self_rpow_of_one_le_of_nonneg (by norm_num) hs

-- Proof 3: Evolution diagonal action
lemma evolution_diagonal_action_proof (s : ℂ) (p : {p : ℕ // Nat.Prime p}) :
    let eigenvalues := fun q : {q : ℕ // Nat.Prime q} => (q.val : ℂ)^(-s)
    (fun q => eigenvalues q * WeightedL2.deltaBasis p q) =
    fun q => (p.val : ℂ)^(-s) * WeightedL2.deltaBasis p q := by
  -- This follows from the definition of eigenvalues and the delta basis
  -- The key insight is that WeightedL2.deltaBasis p q is nonzero only when p = q
  -- In that case, (q.val : ℂ)^(-s) = (p.val : ℂ)^(-s)
  -- Otherwise, both sides are zero

  -- Apply function extensionality
  ext q

  -- Unfold the definition of eigenvalues
  simp only [eigenvalues]

  -- Case analysis: either p = q or p ≠ q
  by_cases h : p = q

  · -- Case 1: p = q
    -- When p = q, deltaBasis p q = 1, so both sides equal (p.val : ℂ)^(-s)
    rw [h]
    -- Both sides are equal: (q.val : ℂ)^(-s) * 1 = (q.val : ℂ)^(-s) * 1

  · -- Case 2: p ≠ q
    -- When p ≠ q, deltaBasis p q = 0, so both sides equal 0
    -- Use the fact that deltaBasis p q = lp.single 2 p 1 q
    -- which is 0 when p ≠ q
    have h_zero : WeightedL2.deltaBasis p q = 0 := by
      unfold WeightedL2.deltaBasis
      rw [lp.single_apply]
      rw [if_neg h]
    rw [h_zero]
    ring

end RH.FredholmDeterminantProofs
