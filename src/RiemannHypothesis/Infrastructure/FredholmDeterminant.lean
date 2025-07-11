import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.NormedSpace.OperatorNorm
import RiemannHypothesis.Infrastructure.WeightedHilbertSpace

namespace RH.FredholmDeterminant

open Complex Real RH

noncomputable def evolutionEigenvalues (s : ℂ) : {p : ℕ // Nat.Prime p} → ℂ :=
  fun p => (p.val : ℂ)^(-s)

noncomputable def DiagonalOperator (eigenvalues : {p : ℕ // Nat.Prime p} → ℂ)
    (h_bounded : ∃ C : ℝ, ∀ p, ‖eigenvalues p‖ ≤ C) : WeightedL2 →L[ℂ] WeightedL2 := sorry

noncomputable def evolutionOperatorFromEigenvalues (s : ℂ) : WeightedL2 →L[ℂ] WeightedL2 := sorry

noncomputable def fredholmDet1Diagonal (eigenvalues : {p : ℕ // Nat.Prime p} → ℂ) : ℂ :=
  ∏' p : {p : ℕ // Nat.Prime p}, (1 - eigenvalues p)

theorem fredholm_det1_diagonal (s : ℂ) (hs : 1/2 < s.re) :
    fredholmDet1Diagonal (evolutionEigenvalues s) =
      ∏' p : {p : ℕ // Nat.Prime p}, (1 - (p.val : ℂ)^(-s)) := sorry

end RH.FredholmDeterminant
