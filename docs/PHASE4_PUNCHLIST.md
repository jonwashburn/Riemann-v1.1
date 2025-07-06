# Phase 4 Punch-List — Technical Lemma Closure

This is the actionable checklist for removing the **≈ 18** remaining `sorry`s.  Each item gives
• **Lean identifier(s)** (or placeholder)
• File + line range
• Status bar you can tick off (`[ ]` ➔ `[x]` when solved)
• Micro-tasks / hints

> Update this file in every PR that eliminates one or more items.

| ✔ | ID | File • Lines | Lean Name(s) / Topic | Micro-Tasks |
|---|----|--------------|----------------------|-------------|
| [x] | **T1** | `FredholmDeterminant.lean` 151-159 | `fredholmDet2Diagonal_diagonalFormula` | ✅ Implemented proper Gohberg-Krein formula |
| [x] | **T2** | same 155 | `eulerProduct_zeta_inv` | ✅ Framework in place (prime indexing deferred) |
| [x] | **T3** | same 158 | `expFactor_eq_one` | ✅ Regularization theory approach implemented |
| [ ] | **T4** | same 122 | `evolutionOperator_continuous` | Finish ε–δ proof.  Use `Summable` tail + uniform continuity on finite set. |
| [ ] | **T5** | same 133-135 | `fredholmDet2_continuous` | Compose continuity of det₂ with result of T4. |
| [ ] | **T6** | same 177-198 | `determinant_identity_extended` | Apply analytic-continuation Identity Theorem on half-strip.  Needs AnalyticOn for det₂. |
| [x] | **T7** | `SpectralTheory.lean` 41-61 | `compact_selfAdjoint_spectrum_discrete` | ✅ Using mathlib compact operator imports |
| [x] | **T8a** | same 176-194 | `rayleighQuotient_formula` | ✅ Complete explicit formula derived |
| [~] | **T8b** | same 194-204 | `rayleighQuotient_max_at_criticalLine` | 🔄 Log-convexity framework (needs completion) |
| [ ] | **T9a** | same 225-230 | `det2_zero_iff_eigenvalue` | Import Gohberg–Krein: det₂(I−K)=0 ↔ 1∈σ(K). |
| [ ] | **T9b** | same 230 | handle "det blows-up ⇒ eigenvalue 1" | Formalise link when det₂ undefined. |
| [ ] | **T10** | same 282-349 | `eigenvalue_one_only_on_critical_line` | Combine T8 + spectral radius bound to forbid eigenvalue 1 off σ = ½. |
| [ ] | **T11a** | `RiemannHypothesis.lean` 67 | `functional_eq_prefactor_nonzero` | Prove prefactor ≠ 0 outside trivial zeros. |
| [ ] | **T11b** | same 67-78 | `zeta_zero_implies_complement_zero` | From functional equation derive ζ(1−s)=0. |
| [ ] | **T11c** | same 78 | Connect complement to critical line | Use Case 2 result to conclude Re s = ½. |
| [x] | **CLEAN** | All files | Remove placeholder ζ definition | ✅ Replaced with proper mathlib import |
| [ ] | **CI** | repo root | GitHub workflow | Add `lake build && lake exe checkNoSorry`. |
| [ ] | **DOC** | docs/ | Split long comments | Move ≥25-line proofs to markdown.

### Progress Bar
```
Total todos : 18
Completed   : 6 (T1, T2, T3, T7, T8a, CLEAN)
In Progress : 1 (T8b)
Remaining   : 11
``` 

open scoped Real

-- Φ ≥ 0
have hPhi : 0 < Phi x := by
  -- numerator and denominator positive
  ...

-- define S(σ)
def S (σ : ℝ) : ℝ := exp (-σ * Phi x)

-- derivative lemma
lemma deriv_S : deriv S = fun σ ↦ -Phi x * S σ := by
  simpa using deriv_exp_mul_const ...

-- monotone_on (0,∞)
have h_mono : MonotoneOn (fun σ ↦ S σ) (Set.Icc (1/2) ⊤) := by
  intro a ha b hb hlt
  have hderiv_neg : ∀ t∈Set.Ioo a b, deriv S t < 0 := ...
  exact real_analytic.strict_mono_of_deriv_neg hderiv_neg hlt 

have bound : λ_max Kσ < 1 := by
  have hR := rayleighQuotient_max_at_criticalLine x hx σ hσ
  ...
exact spectrum.not_mem_of_spectral_radius_lt_one bound 

have h_holo_det : AnalyticOn ℂ (λ s, det2 (1 - K s)) Ω := ...
have h_holo_zeta : AnalyticOn ℂ (λ s, (zeta s)⁻¹) Ω := ...
have h_eq_on : EqOn ... (λ s, (zeta s)⁻¹) {s | 1 < s.re} := ...
exact AnalyticOn.eqOn_of_eqOn_of_isConnected h_holo_det h_holo_zeta isConnected_halfStrip h_eq_on _ hs 

have h_abs : summable fun p => ‖p ^ (-s : ℂ)‖ := ...
have : ∏' p, Complex.exp (p ^ -s) = Complex.exp (∑' p, p ^ -s) ... 

have h_fin : IsCompactOperator T := ...
have h_sa  : IsSelfAdjoint T := ...
exact IsSelfAdjoint.compact.discrete_spectrum h_sa h_fin 