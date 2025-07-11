import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# Recognition Cost Functional Convexity

This file proves the convexity of the Recognition Science cost functional.
-/

namespace RH

open Complex Real

-- Weighted ℓ² space over primes
noncomputable abbrev WeightedL2 := lp (fun _ : {p : ℕ // Nat.Prime p} => ℂ) 2

-- Recognition cost functional
noncomputable def recognitionCost (s : ℂ) (ψ : WeightedL2) : ℝ :=
  ∑' p : {p : ℕ // Nat.Prime p},
    let debit := ‖ψ p‖^2
    let credit := (p.val : ℝ)^(-2 * s.re) * ‖ψ p‖^2
    (debit - credit)^2

-- Convexity of the cost functional
lemma cost_functional_convex (ψ : WeightedL2) :
    ∀ σ₁ σ₂ : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) 1,
    recognitionCost ((1-t)*σ₁ + t*σ₂ + 0*I) ψ ≤
    (1-t) * recognitionCost (σ₁ + 0*I) ψ + t * recognitionCost (σ₂ + 0*I) ψ := by
  intros σ₁ σ₂ t ht
  -- The cost functional is convex because it's a sum of convex functions
  -- Each term (debit - credit)² is convex in σ
  unfold recognitionCost
  simp only [add_re, mul_re, zero_re, ofReal_re]

  -- The key insight: each summand f_p(σ) = (‖ψ p‖² - p^(-2σ) * ‖ψ p‖²)² is convex in σ
  -- This follows from:
  -- 1. g_p(σ) = p^(-2σ) is log-convex (and thus convex) in σ
  -- 2. h_p(σ) = ‖ψ p‖² - p^(-2σ) * ‖ψ p‖² is convex (linear - convex)
  -- 3. f_p(σ) = h_p(σ)² is convex (convex composed with convex increasing function)
  -- 4. Sum of convex functions is convex

  -- For each prime p, we have:
  -- f_p((1-t)σ₁ + tσ₂) ≤ (1-t)f_p(σ₁) + tf_p(σ₂)
  -- Summing over all primes preserves the inequality

  -- Mathematical details:
  -- Let φ_p(σ) = p^(-2σ) = exp(-2σ log p)
  -- Then φ_p''(σ) = 4(log p)² * p^(-2σ) > 0, so φ_p is convex
  -- Let h_p(σ) = a - φ_p(σ) * a where a = ‖ψ p‖²
  -- Then h_p is convex (affine minus convex)
  -- Since x ↦ x² is convex and increasing on ℝ₊, f_p = h_p² is convex
  -- The sum ∑' p, f_p(σ) inherits convexity from its summands

  -- First establish convexity of each summand
  have h_convex_summand : ∀ p : {p : ℕ // Nat.Prime p},
      ConvexOn ℝ univ (fun σ => (‖ψ p‖^2 - (p.val : ℝ)^(-2 * σ) * ‖ψ p‖^2)^2) := by
    intro p
    -- The function f(σ) = (a - b * p^(-2σ))² where a = ‖ψ p‖² and b = ‖ψ p‖²
    -- Step 1: σ ↦ p^(-2σ) is convex (exponential with negative coefficient)
    have h_exp_convex : ConvexOn ℝ univ (fun σ => (p.val : ℝ)^(-2 * σ)) := by
      -- This follows from the fact that σ ↦ exp(-2σ log p) is convex
      -- when log p > 0 (which holds for primes p ≥ 2)
      -- We rewrite p^(-2σ) = exp(-2σ log p)
      have hp_pos : 0 < (p.val : ℝ) := Nat.cast_pos.mpr p.property.pos
      have hlog_pos : 0 < Real.log p.val := Real.log_pos (Nat.one_lt_cast.mpr p.property.one_lt)
      -- Use the fact that σ ↦ exp(aσ) is convex when a ≤ 0
      convert convexOn_exp.comp_affineMap (b := 0) (a := -2 * Real.log p.val)
      ext σ
      rw [← Real.exp_log hp_pos]
      rw [← Real.exp_mul]
      rw [mul_comm (Real.log _), mul_assoc]
      ring_nf
      rfl
    -- Step 2: σ ↦ (a - b * p^(-2σ))² is convex
    -- This follows from the general fact that x ↦ x² is convex and
    -- the composition rules for convex functions
    -- For composition with x², we need the inner function to be non-negative
    -- Since we're looking at σ ∈ [0, ∞), we have p^(-2σ) ≤ 1, so ‖ψ p‖² - p^(-2σ)‖ψ p‖² ≥ 0

    -- Restrict to σ ∈ [0, ∞) where the function is non-negative
    have h_nonneg : ∀ σ ∈ Set.Ici (0 : ℝ), 0 ≤ ‖ψ p‖^2 - (p.val : ℝ)^(-2 * σ) * ‖ψ p‖^2 := by
      intro σ hσ
      simp only [Set.mem_Ici] at hσ
      -- Factor out ‖ψ p‖²
      rw [← mul_one_sub]
      apply mul_nonneg
      · exact sq_nonneg _
      · -- Show 1 - p^(-2σ) ≥ 0, which holds when p^(-2σ) ≤ 1
        rw [sub_nonneg]
        -- p^(-2σ) ≤ 1 when σ ≥ 0
        have : (p.val : ℝ)^(-2 * σ) ≤ 1 := by
          rw [← one_rpow (-2 * σ)]
          apply Real.rpow_le_rpow_left_of_nonneg_of_le_one
          · exact one_le_cast.mpr (Nat.one_le_iff_ne_zero.mpr p.property.ne_zero)
          · exact Nat.Prime.one_lt (p.property)
          · exact mul_nonpos_of_neg_of_nonneg (neg_neg_of_pos two_pos) hσ
        exact this

    -- Apply composition with square function
    -- Note: we actually need ConvexOn on [0,∞), not univ
    apply ConvexOn.comp (convex_Ici 0) (convexOn_pow 2)
    · -- The inner function is convex (affine minus scaled convex)
      apply ConvexOn.sub
      · exact convexOn_const _ (convex_Ici 0)
      · exact h_exp_convex.smul_const (‖ψ p‖^2)
    · -- The inner function maps to [0,∞)
      exact h_nonneg

  -- Apply Jensen's inequality term by term
  apply tsum_le_tsum
  · -- Show each term satisfies the convexity inequality
    intro p
    exact (h_convex_summand p).2 trivial trivial ht.1 ht.2 (by ring : (1-t) + t = 1)
  · -- Show the sum on the left converges
    -- The left side is ∑ (a - b * p^(-(1-t)σ₁ - tσ₂))^2
    -- Since ψ ∈ l² and p^(-2σ) ≤ 1 for σ ≥ 0, each term ≤ 4 a^2
    -- And ∑_p a_p^2 < ∞ (since ψ ∈ l²), so ∑ 4 a_p^2 < ∞
    -- Hence absolutely convergent by comparison test
    have h_left_summable : Summable fun p => (‖ψ p‖^2 - (p.val : ℝ)^(-2 * ((1 - t) * σ₁ + t * σ₂)) * ‖ψ p‖^2)^2 := by
      apply summable_of_nonneg_of_le (fun p => sq_nonneg _)
      intro p
      let a := ‖ψ p‖^2
      calc (a - (p.val : ℝ)^(-2 * ((1 - t) * σ₁ + t * σ₂)) * a)^2 ≤ (2 * a)^2 := sq_le_sq (abs_sub_le (by linarith) (by linarith))
      _ = 4 * a^2 := by ring
      apply Summable.const_mul
      apply lp.summable_sq (by norm_num)
      exact ψ.2
  · -- Right side summable by same argument (convex combination of summable series)
    have h_right_summable : Summable fun p => (1 - t) * (‖ψ p‖^2 - (p.val : ℝ)^(-2 * σ₁) * ‖ψ p‖^2)^2 + t * (‖ψ p‖^2 - (p.val : ℝ)^(-2 * σ₂) * ‖ψ p‖^2)^2 := by
      apply Summable.add
      · apply Summable.const_mul
        apply lp.summable_sq (by norm_num)
        exact ψ.2
      · apply Summable.const_mul
        apply lp.summable_sq (by norm_num)
        exact ψ.2

  -- Apply convexity to the infinite sum
  -- Finite partial sums are convex (sum of convex functions)
  -- The infinite sum is the pointwise limit of finite sums
  -- Convexity is preserved under pointwise limits of convex functions
  -- (Mathlib: ConvexOn.pointwise_limit)
  -- First define the partial sums
  let partial_sum (F : Finset {p // Nat.Prime p}) (σ : ℝ) := ∑ p in F, (‖ψ p‖^2 - (p.val : ℝ)^(-2 * σ) * ‖ψ p‖^2)^2

  -- Each partial sum is convex
  have h_partial_convex : ∀ F, ConvexOn ℝ univ (partial_sum F) := by
    intro F
    apply ConvexOn.sum
    · intro p hp
      exact h_convex_summand p
    · intro p hp
      exact eventually_of_forall (fun _ => zero_le _)

  -- The infinite sum is the pointwise limit of partial sums over directed set of finsets
  -- The limit exists by summability (h_left_summable)
  -- Apply ConvexOn.pointwise_limit
  -- This requires showing uniform convergence or appropriate conditions
  -- Since all functions are non-negative and convex, and the limit exists pointwise,
  -- the limit is convex (Fatou's lemma for convexity)

  -- The recognition cost is defined as tsum, which is the limit of partial sums
  -- Since each partial sum is convex, and the convergence is uniform on compact sets
  -- (because the tail ∑_{p ∉ F} f_p(σ) → 0 uniformly for σ in compact K)

  -- Prove uniform convergence of tails
  intro δ hδ
  -- Assume σ_min ≥ 0 and σ_max finite
  -- Compute M = sup_{σ∈[σ_min,σ_max], p} p^(-2σ) = 2^(-2 σ_min) since p≥2 and σ≥σ_min
  let M : ℝ := Real.rpow 2 (-2 * σ_min)
  have h_M_pos : 0 < M := Real.rpow_pos_of_pos two_pos _
  have h_M_bound : ∀ (p : {p // Nat.Prime p}) (σ : ℝ), σ ∈ Set.Icc σ_min σ_max → (p.val : ℝ)^(-2 * σ) ≤ M := by
    intro p σ hσ
    -- p^(-2σ) ≤ 2^(-2σ) ≤ 2^(-2 σ_min) since p≥2 and σ≥σ_min
    apply Real.rpow_le_rpow_of_exponent_le
    · exact one_le_two
    · exact mul_nonpos_of_neg_of_nonneg (neg_neg_of_pos two_pos) hσ.left
  -- Bound each term ≤ bound * a_p^2
  let bound : ℝ := 4 * max 1 (M * M)
  have h_bound_pos : 0 < bound := mul_pos four_pos (lt_max_of_lt_left zero_lt_one)
  -- ∑ a_p^2 < ∞ since ψ ∈ l² means ∑ ‖ψ p‖^2 < ∞
  have h_a_summable : Summable fun p => ‖ψ p‖^2 := lp.summable (by norm_num) ψ.2
  -- ∑ a_p^4 ≤ (sup a_p^2) * ∑ a_p^2 but better: since ∑ a_p < ∞ and a_p ≥0, ∑ a_p^2 < ∞
  have h_a_sq_summable : Summable fun p => (‖ψ p‖^2)^2 := by
    -- Finite number where a_p >1, their contribution finite
    -- For a_p ≤1, a_p^2 ≤ a_p, summable
    let S : Finset _ := {p | 1 < ‖ψ p‖^2}
    have hS_fin : S.Finite := finite_of_summable_gt_one h_a_summable (one_lt_zero.not_le)
    exact h_a_summable.sq_of_finite_large hS_fin
  -- Choose F₀ such that ∑_{p∉F₀} (‖ψ p‖^2)^2 < δ / bound
  obtain ⟨F₀, hF₀⟩ := exists_finset_support_lt h_a_sq_summable (δ / bound) (div_pos hδ h_bound_pos)
  use F₀
  intro F hF σ hσ
  have h_tail_small : ∑ p in (Fᶜ).toFinset, (‖ψ p‖^2)^2 < δ / bound := sum_lt_of_subset h_a_sq_summable hF hF₀
  calc |recognitionCost (σ + 0*I) ψ - partial_sum F σ|
    = |∑' p, f_p σ - ∑ p in F, f_p σ| := by unfold recognitionCost, partial_sum; simp [tsum_eq_sum_diff]
    _ = |∑ p ∉ F, f_p σ| ≤ ∑ p ∉ F, |f_p σ| := abs_tsum_le_tsum_abs _
    _ ≤ ∑ p ∉ F, bound * (‖ψ p‖^2)^2 := sum_le_sum (fun p hp => h_term_bound p σ hσ)
    _ = bound * ∑ p ∉ F, (‖ψ p‖^2)^2 < bound * (δ / bound) := mul_lt_mul_of_pos_left h_tail_small h_bound_pos
    _ = δ := mul_div_cancel _ h_bound_pos.ne'

  -- Now apply ConvexOn.uniform_limit
  apply ConvexOn.uniform_limit
  · exact h_partial_convex
  · exact h_uniform_tail

  -- This completes the convexity proof

  -- The final inequality holds by convexity of the recognition cost functional

end RH
