import Mathlib.Topology.Basic
import Mathlib.Data.Nat.Prime

/-!
# Filter results for primes

This file contains a small helper lemma establishing that the primes `p` tend to
infinity (`atTop`) as a sub-filter of `ℕ`. This allows us to reuse limit
theorems for `ℕ` when working with sums or products over primes.
-/

namespace RH.Analysis

open Filter

lemma tendsto_atTop_primes : Tendsto (fun p : {p : ℕ // Nat.Prime p} => (p : ℕ)) atTop atTop := by
  -- The primes are cofinal in `ℕ`; this is a standard mathlib argument.
  -- `tendsto_atTop_atTop` requires `∀ N, ∃ p, N ≤ p`.
  rw [tendsto_atTop_atTop]
  intro N
  obtain ⟨p, hp, hpN⟩ := Nat.exists_prime_ge N
  use ⟨p, hp⟩
  simpa

end RH.Analysis
