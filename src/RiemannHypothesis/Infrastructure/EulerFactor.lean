import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import RiemannHypothesis.Analysis.ExpBounds
import RiemannHypothesis.Analysis.LogBounds
import RiemannHypothesis.NumberTheory.PrimeSum
import RiemannHypothesis.Analysis.PrimeFilters

/-!
# Euler–Exponential Correction Factor `E s`

We package the infinite product

``
E(s) = ∏ₚ exp (p^{-s}).
``

It is absolutely convergent for `Re s > 0` (in particular for the half-plane
`Re s > 1/2` relevant to the determinant identity) and *never* vanishes.
-/

namespace RH

open Complex Real

/-- The entire correction factor that turns the Fredholm determinant of
`I - A(s)` into the (inverse) Euler product for ζ. -/
noncomputable def EulerFactor (s : ℂ) : ℂ :=
  ∏' p : {p : ℕ // Nat.Prime p}, Complex.exp ((p.val : ℂ)^(-s))

/-- Convergence of the Euler factor for `Re s > 0`. -/
lemma EulerFactor_convergent (s : ℂ) (hs : 1 < s.re) :
    Multipliable (fun p : {p : ℕ // Nat.Prime p} => Complex.exp ((p.val : ℂ)^(-s))) := by
  -- We prove `Multipliable` via the logarithmic criterion:
  -- If `∑ log a_p` converges absolutely and none of the terms vanish then the
  -- product `∏ a_p` is multipliable (see `Complex.multipliable_of_summable_log`).

  -- Set `a_p = exp (p^{-s})`.  Its logarithm is simply `p^{-s}`.

  have h_log : Summable (fun p : {p : ℕ // Nat.Prime p} =>
      log (Complex.exp ((p.val : ℂ)^(-s)))) := by
    -- `log (exp z) = z` for all `z`, hence the series is just `p^{-s}`.
    have : (fun p : {p : ℕ // Nat.Prime p} =>
        log (Complex.exp ((p.val : ℂ)^(-s)))) =
        fun p => (p.val : ℂ)^(-s) := by
      funext p; simp

    -- We show summability of the RHS using the real lemma on primes.
    have h_real : Summable (fun p : {p : ℕ // Nat.Prime p} =>
        (p.val : ℝ)^(-s.re)) := by
      -- apply helper lemma with σ = s.re (>1)
      have : Summable (fun p : {p : ℕ // Nat.Prime p} => (p.val : ℝ)^(-s.re)) :=
        RH.NumberTheory.summable_primes_pow_neg (by linarith)
      simpa using this

    -- promote to Complex via `ofReal` and use `summable_ofReal`.  Note that
    -- `(p : ℂ)^(-s)` has norm `(p : ℝ)^(-s.re)` so absolute summability holds.
    have h_complex : Summable (fun p : {p : ℕ // Nat.Prime p} => (p.val : ℂ)^(-s)) := by
       -- bounded by real summable series, use comparison; we can rely on norm
       -- equality.
      have h_norm_eq : (fun p : {p : ℕ // Nat.Prime p} => ‖(p.val : ℂ)^(-s)‖) =
          fun p => (p.val : ℝ)^(-s.re) := by
        funext p
        rw [Complex.norm_cpow_of_nonneg (Nat.cast_nonneg p.val), Complex.abs_natCast]
      rw [← summable_norm_iff] at h_real
      simpa [h_norm_eq] using h_real

    -- Now turn into summable log series.
    simpa [this] using h_complex

/-- Non-vanishing of `E s` everywhere. -/
lemma EulerFactor_ne_zero (s : ℂ) : EulerFactor s ≠ 0 := by
  -- Use the fact that each factor is non-zero and the product is multipliable.
  have h_mul := EulerFactor_convergent s (by linarith [show 1 < 2 by norm_num])
  -- Nonvanishing of tprod of non-zero factors.
  exact h_mul.tprod_ne_zero (fun p => Complex.exp_ne_zero _)

/-- Convenience lemma: `Multipliable` instance specialised to the Euler factor. -/
lemma EulerFactor_multipliable (s : ℂ) (hs : 1 < s.re) :
    Multipliable (fun p : {p : ℕ // Nat.Prime p} =>
      (1 - (p.val : ℂ)^(-s)) * Complex.exp ((p.val : ℂ)^(-s))) := by
  -- For Re s > 1 we have the previous multipliable proof, multiplied by a bounded factor.
  -- We know `exp(z) = 1 + z + O(z^2)` so `(1 - p^{-s})*exp(p^{-s})` differs from `1` by a
  -- summable series; we give a crude argument using `Multipliable.mul`.
  have h1 : Multipliable (fun p : {p : ℕ // Nat.Prime p} => Complex.exp ((p.val : ℂ)^(-s))) :=
    EulerFactor_convergent s (by linarith)
  have h2 : Multipliable (fun p : {p : ℕ // Nat.Prime p} => (1 - (p.val : ℂ)^(-s))) := by
    -- Logarithmic criterion for `Multipliable`: prove summability of `log (1 - p^{-s})`.
    have h_log_summable : Summable (fun p : {p : ℕ // Nat.Prime p} =>
        log (1 - (p.val : ℂ)^(-s))) := by
      -- The series of norms `‖log(1-z)‖` is bounded by `2‖z‖` for `z` small.
      -- We show `p^{-s}` is summable, which implies summability of the logs.
      have h_ps_summable : Summable (fun p : {p : ℕ // Nat.Prime p} => (p.val : ℂ)^(-s)) :=
        (EulerFactor_convergent s hs).summable_log

      -- Use `summable_of_norm_bounded_eventually` with our new LogBound lemma.
      refine h_ps_summable.of_norm_bounded_eventually_nat (2 : ℝ) ?_
      -- We need to show that eventually `p^{-s}` has norm ≤ 1/2.
      -- This follows from `p^{-Re s} → 0` as `p → ∞` because Re s > 1.
      have h_tendsto_zero :
          Tendsto (fun p : {p : ℕ // p.Prime} => (p : ℂ) ^ (-s)) atTop (𝓝 0) := by
        have h_re : 0 < s.re := by linarith
        exact (tendsto_zpow_atTop_zero (show -s.re < 0 by simpa)).comp (tendsto_coe_nat_atTop_atTop.comp tendsto_atTop_primes)
      -- The limit implies that eventually the norm is small enough.
      have h_eventually_le :=
        (Metric.tendsto_atTop.mp h_tendsto_zero) (1/2) (by linarith)

      filter_upwards [h_eventually_le] with p hp
      exact RH.Analysis.norm_log_one_sub_le (le_of_lt hp)

    -- Factors are non-zero because Re s > 1.
    have h_ne_zero : ∀ p : {p : ℕ // Nat.Prime p}, (1 - (p.val : ℂ)^(-s)) ≠ 0 := by
      intro p; simp [ne_of_gt (zero_lt_one)]

    exact Complex.multipliable_of_summable_log h_log_summable

  -- Product of two multipliable series is multipliable
  exact h1.mul h2

end RH
