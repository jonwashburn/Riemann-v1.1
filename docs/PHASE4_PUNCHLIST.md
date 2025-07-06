# Phase 4 Punch-List — Technical Lemma Closure

This is the actionable checklist for removing the **≈ 18** remaining `sorry`s.  Each item gives
• **Lean identifier(s)** (or placeholder)
• File + line range
• Status bar you can tick off (`[ ]` ➔ `[x]` when solved)
• Micro-tasks / hints

> Update this file in every PR that eliminates one or more items.

| ✔ | ID | File • Lines | Lean Name(s) / Topic | Micro-Tasks |
|---|----|--------------|----------------------|-------------|
| [ ] | **T1** | `FredholmDeterminant.lean` 151-159 | `fredholmDet2Diagonal_diagonalFormula` | Implement det₂ formula for diagonal operator (Gohberg–Krein).  Use mathlib's `TraceClass.det2_diagonal`. |
| [ ] | **T2** | same 155 | `eulerProduct_zeta_inv` | Import `zeta_function.euler_product_inv` for Re s > 1.  Connect to λₚ. |
| [ ] | **T3** | same 158 | `expFactor_eq_one` | Show `∏ₚ exp(λₚ) = 1`; prove Σλₚ absolutely convergent ⇒ log of product = 0. |
| [ ] | **T4** | same 122 | `evolutionOperator_continuous` | Finish ε–δ proof.  Use `Summable` tail + uniform continuity on finite set. |
| [ ] | **T5** | same 133-135 | `fredholmDet2_continuous` | Compose continuity of det₂ with result of T4. |
| [ ] | **T6** | same 177-198 | `determinant_identity_extended` | Apply analytic-continuation Identity Theorem on half-strip.  Needs AnalyticOn for det₂. |
| [ ] | **T7** | `SpectralTheory.lean` 41-61 | `compact_selfAdjoint_spectrum_discrete` | Replace sketch by importing `IsCompactOperator.hasEigenvalues` + discrete-spectrum lemma. |
| [ ] | **T8a** | same 176-194 | `rayleighQuotient_formula` | Derive explicit Σ formula for R(σ). |
| [ ] | **T8b** | same 194-204 | `rayleighQuotient_max_at_criticalLine` | Use min-max or derivative-free monotonicity to prove max at σ = ½. |
| [ ] | **T9a** | same 225-230 | `det2_zero_iff_eigenvalue` | Import Gohberg–Krein: det₂(I−K)=0 ↔ 1∈σ(K). |
| [ ] | **T9b** | same 230 | handle "det blows-up ⇒ eigenvalue 1" | Formalise link when det₂ undefined. |
| [ ] | **T10** | same 282-349 | `eigenvalue_one_only_on_critical_line` | Combine T8 + spectral radius bound to forbid eigenvalue 1 off σ = ½. |
| [ ] | **T11a** | `RiemannHypothesis.lean` 67 | `functional_eq_prefactor_nonzero` | Prove prefactor ≠ 0 outside trivial zeros. |
| [ ] | **T11b** | same 67-78 | `zeta_zero_implies_complement_zero` | From functional equation derive ζ(1−s)=0. |
| [ ] | **T11c** | same 78 | Connect complement to critical line | Use Case 2 result to conclude Re s = ½. |
| [ ] | **CLEAN** | All files | Remove placeholder ζ definition | Replace with `open ZetaFunction` import; adjust calls. |
| [ ] | **CI** | repo root | GitHub workflow | Add `lake build && lake exe checkNoSorry`. |
| [ ] | **DOC** | docs/ | Split long comments | Move ≥25-line proofs to markdown.

### Progress Bar
```
Total todos : 18
Completed   : 0
Remaining   : 18
``` 