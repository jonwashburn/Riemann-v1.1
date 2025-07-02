import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Data.Real.GoldenRatio
import Mathlib.Topology.Instances.ENNReal
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# Weighted Hilbert space used in the operator–theoretic RH proof

We import the fully-featured `lp`-based ℓ² space over primes from the RH
academic framework and re-export it under the old name `WeightedHilbertSpace`
so existing files continue to compile.
-/

namespace RH

open Complex Real BigOperators

/-- The weighted ℓ² space over primes.  We simply take the standard `lp`
    construction with exponent 2 and coordinate type ℂ. -/
noncomputable abbrev WeightedL2 := lp (fun _ : {p : ℕ // Nat.Prime p} => ℂ) 2

namespace WeightedL2

instance : Fact (1 ≤ (2 : ℝ)) := ⟨by norm_num⟩

/-- Basis vector δₚ (1 at index `p`, 0 elsewhere). -/
noncomputable def deltaBasis (p : {p : ℕ // Nat.Prime p}) : WeightedL2 :=
  lp.single 2 p 1

/-- Domain of the arithmetic Hamiltonian H. -/
noncomputable def domainH : Set WeightedL2 :=
  {ψ | Summable fun p => ‖ψ p‖ ^ 2 * (Real.log p.val) ^ 2}

/-- Norm-squared equals the ℓ² sum of component norms squared. -/
lemma norm_sq_eq_sum (ψ : WeightedL2) :
    ‖ψ‖ ^ 2 = ∑' p : {p : ℕ // Nat.Prime p}, ‖ψ p‖ ^ 2 := by
  -- `lp` furnishes the requisite identity
  simpa [ENNReal.toReal_ofNat] using
    lp.norm_rpow_eq_tsum (p := (2 : ℝ≥0∞)) (by norm_num) ψ

end WeightedL2

/-- Provide the legacy name used elsewhere in the code-base. -/
noncomputable abbrev WeightedHilbertSpace := WeightedL2

/-- Re-export the delta basis and domain under the legacy namespace so that
    existing `open WeightedHilbertSpace` lines still work. -/
namespace WeightedHilbertSpace
  export RH.WeightedL2 (deltaBasis domainH)
end WeightedHilbertSpace

end RH
