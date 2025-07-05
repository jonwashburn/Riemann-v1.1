import Mathlib.Data.Complex.ExpLog
import Mathlib.Data.Real.Log
import Mathlib.Data.Nat.Prime

/-!
# Arithmetic consequences of `p^{-s} = 1`

If a complex number `s` satisfies `p^{-s} = 1` for a prime `p`, then the real part of `s` must be
zero.  This is used in the final passage of the operator–determinant proof of the Riemann
Hypothesis: once we know an eigen-value `1` occurs, we conclude that either `s` lies on the
imaginary axis (and further analysis forces `Re s = 1/2`) or is a trivial zero.
-/

open Complex

namespace RH

/-- Arithmetic lemma: if `p^{-s} = 1` for a real prime `p ≥ 2`, then `s.re = 0` and
    in fact `s = 2π i k / log p` for some integer `k`.  The proof uses the
    complex exponential's injectivity on vertical strips. -/
lemma real_part_eq_zero_of_prime_pow_eq_one {p : ℕ} (hp : Nat.Prime p) {s : ℂ}
    (h : (p : ℂ)^(-s) = 1) : s.re = 0 := by
  -- Take complex log of both sides.  We use the multi-valued `Complex.log` and turn equality
  -- into membership in `SetLike`.  More straightforward is to rewrite the exponential equation
  -- as `exp (-s * log p) = 1`.
  have h_exp : Complex.exp (-s * Complex.log p) = 1 := by
    simpa [Complex.cpow_eq_pow, Complex.log_nat_cast hp.ne_zero, div_eq_inv_mul]
      using h
  -- For `exp z = 1` we know `z = 2π i k` for some integer `k`.
  obtain ⟨k : ℤ, hk⟩ := Complex.exp_eq_one_iff.1 h_exp
  -- Thus `-s * log p = 2π i k`.
  have h_eq : -s * Complex.log p = (2 * π * Complex.I) * k := by simpa using hk
  -- Since `log p` is a positive real number, divide to isolate `s`.
  have h_logp_pos : 0 < Real.log p := by
    have : (1 : ℝ) < p := by
      have hp2 : 2 ≤ p := hp.two_le
      exact one_lt_two.trans_le hp2
    have : 1 < (p : ℝ) := by simpa using this
    have : 0 < Real.log (p : ℝ) := Real.log_pos this
    simpa [Real.log_nat_cast] using this
  have : s = -(2 * π * Complex.I * (k : ℂ)) / Complex.log p := by
    field_simp [h_eq] at *
  -- Take real parts of the equality `h_eq`.
  have h_real : ((-s) * Complex.log p).re = 0 := by
    have := congrArg Complex.re h_eq
    -- rewrite `Complex.log p` as a real scalar so that `simp` can compute the real part
    simpa [Complex.log_nat_cast hp.ne_zero] using this

  -- Compute the real part explicitly: `(-s).re * log p = 0`.
  have h_mul : (-s.re) * Real.log p = 0 := by
    -- `Complex.mul_re` gives `re(z*w) = z.re * w.re - z.im * w.im`.  Since `log p` is real,
    -- its imaginary part is `0`, so the second term vanishes.
    simpa [Complex.mul_re, Complex.log_nat_cast hp.ne_zero] using h_real

  -- Because `log p ≠ 0`, the product is zero iff `s.re = 0`.
  have h_log_ne : (Real.log p) ≠ 0 := by exact (ne_of_gt h_logp_pos)

  have h_sre : s.re = 0 := by
    -- From `(-s.re) * log p = 0` and `log p ≠ 0` we get `-s.re = 0`.
    have : (-s.re) = 0 := by
      have h_cases := (mul_eq_zero.mp h_mul)
      cases h_cases with
      | inl h_left => exact h_left
      | inr h_right => exact (h_log_ne h_right).elim
    simpa [neg_eq_zero] using this

  simpa using h_sre
  exact this

end RH
