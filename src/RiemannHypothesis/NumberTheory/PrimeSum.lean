import Mathlib.NumberTheory.ZetaFunction
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Data.Nat.Prime

/-!
# Summability of `p^{-σ}` over primes

For any real `σ > 1` the series `∑_{p prime} p^{-σ}` converges.  This is a
standard corollary of the comparison with the Riemann zeta function.
-/

open Real Filter Set Nat

namespace RH.NumberTheory

lemma summable_primes_pow_neg {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun p : {p : ℕ // Nat.Prime p} => (p.val : ℝ)^(-σ)) := by
  -- Step 1: summability over `Nat.Primes` using the ready-made lemma.
  have hneg : (-σ) < -1 := by linarith
  have hNat : Summable (fun p : Nat.Primes => (p : ℝ) ^ (-σ)) :=
    (Nat.Primes.summable_rpow).mpr hneg

  -- Step 2: translate to a sum over ℕ with an indicator of primality.
  have h_indicator :
      Summable (indicator {n : ℕ | Nat.Prime n} fun n : ℕ => (n : ℝ) ^ (-σ)) := by
    -- `summable_subtype_iff_indicator` works for *any* subtype of ℕ.
    simpa using
      (summable_subtype_iff_indicator
            (s := {n : ℕ | Nat.Prime n})
            (f := fun n : ℕ => (n : ℝ) ^ (-σ))).mp
        (by
          -- `Nat.Primes` is definitionally the same subtype, so we can cast.
          simpa using hNat)

  -- Step 3: apply the same equivalence in the opposite direction to obtain the desired form.
  simpa using
    (summable_subtype_iff_indicator
          (s := {n : ℕ | Nat.Prime n})
          (f := fun n : ℕ => (n : ℝ) ^ (-σ))).mpr h_indicator

end RH.NumberTheory
