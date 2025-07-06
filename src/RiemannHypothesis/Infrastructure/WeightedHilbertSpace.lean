import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Data.Real.GoldenRatio
import Mathlib.Topology.Instances.ENNReal.Lemmas
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

/-- Weighted ℓ² space over primes (compact docstring).

We simply take the standard `lp`
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
  -- Use the lp norm formula for p = 2
  rw [← Real.rpow_two]
  -- For lp with p = 2, we have ‖f‖^p = Σᵢ ‖f i‖^p
  have h_norm : ‖ψ‖ ^ (2 : ℝ) = (∑' p : {p : ℕ // Nat.Prime p}, ‖ψ p‖ ^ (2 : ℝ) : ℝ) := by
    -- This is the standard lp norm formula for p = 2
    rw [lp.norm_rpow_eq_tsum (by norm_num : (0 : ℝ) < 2)]
    simp only [ENNReal.toReal_ofReal, zero_lt_two]
  rw [h_norm]
  -- Convert back to squared notation
  congr 1
  ext p
  rw [Real.rpow_two]

end WeightedL2

/-- Provide the legacy name used elsewhere in the code-base. -/
noncomputable abbrev WeightedHilbertSpace := WeightedL2

-- Re-export delta basis & domain for compatibility
namespace WeightedHilbertSpace
  export RH.WeightedL2 (deltaBasis domainH)
end WeightedHilbertSpace

end RH
