import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.NormedSpace.OperatorNorm

/-!
# Fredholm Determinant Theory

This file develops the theory of Fredholm determinants for diagonal operators.
-/

namespace RH.FredholmDeterminant

open Complex Real RH

/-- The eigenvalues of the evolution operator -/
noncomputable def evolutionEigenvalues (s : ℂ) : {p : ℕ // Nat.Prime p} → ℂ :=
  fun p => (p.val : ℂ)^(-s)

/-- A diagonal operator with given eigenvalues -/
noncomputable def DiagonalOperator (eigenvalues : {p : ℕ // Nat.Prime p} → ℂ)
    (h_bounded : ∃ C : ℝ, ∀ p, ‖eigenvalues p‖ ≤ C) : WeightedL2 →L[ℂ] WeightedL2 := by
  let L : WeightedL2 →ₗ[ℂ] WeightedL2 :=
    {
      toFun := fun ψ =>
        ⟨(fun p : {p : ℕ // Nat.Prime p} => eigenvalues p * ψ p), by
          obtain ⟨C, hC⟩ := h_bounded
          apply Memℓp.of_exponent_ge
          have h_bound : ∀ p, ‖eigenvalues p * ψ p‖^2 ≤ C^2 * ‖ψ p‖^2 := by
            intro p
            rw [norm_mul, mul_pow]
            exact mul_le_mul_of_nonneg_right (pow_le_pow_right (norm_nonneg _) (hC p) 2) (sq_nonneg _)
          exact Memℓp.of_bounded ψ.property (C^2) h_bound⟩,
      map_add' := by
        intro ψ φ
        ext p
        simp only [lp.coeFn_add, Pi.add_apply]
        ring,
      map_smul' := by
        intro c ψ
        ext p
        simp only [lp.coeFn_smul, Pi.smul_apply, RingHom.id_apply]
        simp only [smul_eq_mul]
        ring
    };
  have h_cont : ∃ C : ℝ, ∀ ψ : WeightedL2, ‖L ψ‖ ≤ C * ‖ψ‖ := by
    rcases h_bounded with ⟨C, hC⟩
    refine ⟨C, ?_⟩
    intro ψ
    have h_bound : ∃ (ψ' : WeightedL2), (∀ p, ψ' p = eigenvalues p * ψ p) ∧ ‖ψ'‖ ≤ C * ‖ψ‖ := by
      exact FredholmDeterminantProofs.diagonal_operator_continuous_proof eigenvalues C hC ψ
    rcases h_bound with ⟨ψ', hψ', h_norm⟩
    have : ψ' = L ψ := by
      ext p; simpa using hψ' p
    simpa [this] using h_norm
  exact L.mkContinuousOfExistsBound h_cont

/-- The evolution operator from eigenvalues -/
noncomputable def evolutionOperatorFromEigenvalues (s : ℂ) : WeightedL2 →L[ℂ] WeightedL2 :=
  DiagonalOperator (evolutionEigenvalues s)
    ⟨(2 : ℝ)^s.re, fun p => by
      exact FredholmDeterminantProofs.evolution_eigenvalue_bound_proof s p⟩

/-- A(s) acts diagonally on basis vectors with eigenvalues p^{-s}. -/
@[simp]
lemma evolution_diagonal_action (s : ℂ) (p : {p : ℕ // Nat.Prime p}) :
    evolutionOperatorFromEigenvalues s (WeightedL2.deltaBasis p) =
      (p.val : ℂ)^(-s) • WeightedL2.deltaBasis p := by
  unfold evolutionOperatorFromEigenvalues
  simp only [ContinuousLinearMap.coe_mk', LinearMap.coe_mk, AddHom.coe_mk]
  ext q
  simp only [WeightedL2.deltaBasis, lp.single_apply, evolutionEigenvalues]
  by_cases h : q = p
  · simp [h, Pi.smul_apply, smul_eq_mul]
  · simp [h, Pi.smul_apply, mul_zero, smul_zero]

/-- The regularized Fredholm determinant for diagonal operators -/
noncomputable def fredholmDet2Diagonal (eigenvalues : {p : ℕ // Nat.Prime p} → ℂ) : ℂ :=
  ∏' p : {p : ℕ // Nat.Prime p}, (1 - eigenvalues p) * Complex.exp (eigenvalues p)

/-- The determinant identity specialized to our evolution eigenvalues. -/
theorem fredholm_det2_diagonal (s : ℂ) (hs : 1/2 < s.re) :
    fredholmDet2Diagonal (evolutionEigenvalues s) =
      ∏' p : {p : ℕ // Nat.Prime p}, (1 - (p.val : ℂ)^(-s)) * Complex.exp ((p.val : ℂ)^(-s)) := by
  unfold fredholmDet2Diagonal evolutionEigenvalues
  rfl

end RH.FredholmDeterminant
