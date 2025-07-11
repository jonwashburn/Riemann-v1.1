import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.Complex.Basic
import RiemannHypothesis.Infrastructure.FredholmDeterminant
import RiemannHypothesis.Infrastructure.WeightedHilbertSpace

namespace RH

open Complex Real BigOperators

theorem determinant_identity (s : ℂ) (hs : s.re > 1) :
    FredholmDeterminant.fredholmDet1Diagonal (FredholmDeterminant.evolutionEigenvalues s) = (riemannZeta s)⁻¹ := sorry

theorem determinant_identity_analytic (s : ℂ) (hs : s.re > 1/2) (hs_ne : riemannZeta s ≠ 0) :
    FredholmDeterminant.fredholmDet1Diagonal (FredholmDeterminant.evolutionEigenvalues s) = (riemannZeta s)⁻¹ := sorry

theorem spectrum_cost_connection (s : ℂ) (hs : s.re = 1/2) :
    (∃ lam : ℂ, lam ∈ spectrum (FredholmDeterminant.evolutionOperatorFromEigenvalues s) ∧ lam = 1) ↔
    (∀ ψ : WeightedL2, recognitionCost s ψ = 0) := sorry

theorem fredholmDet1Diagonal_holomorphic (s : ℂ) (hs : s.re > 1/2) :
    AnalyticAt ℂ (fun z => FredholmDeterminant.fredholmDet1Diagonal (FredholmDeterminant.evolutionEigenvalues z)) s := sorry

end RH
