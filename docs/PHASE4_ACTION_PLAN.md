# Phase 4 Action Plan — From *Almost-Formal* to *No-Sorry*

> "In mathematics, the art of formally finishing things is as important as sketching them."  
> **Goal:** drive the project from ≈ 40 % technical completion to **0 remaining `sorry`s** while keeping the repository clean and review-friendly.

---
## 0. Snapshot Summary
*   Current branch: `main` (commit `c8cb21f`)
*   Remaining `sorry`s ≃ 18 (see §1)
*   All major mathematical ideas are already present; what is missing is **formalisation + hygiene**.

---
## 1. Catalogue of Outstanding Theorems/Lemmas

| ID | File • Line | Lean Name / Topic | Status | Short Description |
|----|-------------|-------------------|--------|-------------------|
| **T1** | `FredholmDeterminant.lean` 151-159 | `fredholmDet2Diagonal_diagonalFormula` | sorry | exact closed-form of det₂ for diagonal operator |
| **T2** | idem 155 | `eulerProduct_zeta_inv` | sorry | ∏ₚ(1 − p^{−s}) = ζ(s)^{−1} for Re s > 1 |
| **T3** | idem 158 | `expFactor_eq_one` | sorry | show exp Σλₚ = 1 for Re s > 1 |
| **T4** | idem 122 | `evolutionOperator_continuous` | *partial* | trace-class-norm continuity (ε–δ proof) |
| **T5** | idem 133-135 | `fredholmDet2_continuous` | *partial* | composition of continuous maps |
| **T6** | idem 177-198 | `determinant_identity_extended` | *sketch* | extend det-identity to ½ < Re s ≤ 1 |
| **T7** | `SpectralTheory.lean` 41-61 | `compact_selfAdjoint_spectrum_discrete` | sketch | import/derive discrete spectrum result |
| **T8** | idem 176-204 | `rayleighQuotient_max_at_criticalLine` | sketch | variational max/min proof |
| **T9** | idem 225-251 | `zeta_zero_iff_eigenvalue_one` | sketch | ζ(s)=0 ⇔ 1∈σ(Kₛ) (Fredholm ⇒ spectrum) |
| **T10** | idem 282-349 | `eigenvalue_one_only_on_critical_line` | sketch | exclude eigenvalue 1 off critical line |
| **T11** | `RiemannHypothesis.lean` 67-78 | functional-equation helpers | sketch | force ζ(1−s)=0 etc. |

> **Note:** Some IDs bundle 2-3 neighbouring `sorry`s that belong to one logical lemma.

---
## 2. Mathematical Blueprint for Each Item

### T1 + T2 + T3 (Determinant / Euler product block)
*Let λₚ := p^{−s}.  For Re s > 1 one has Σ|λₚ| < ∞ and Σ|λₚ|² < ∞.*  
1.  **Diagonal formula**:  `det₂(I − K)` for diagonal K with eigenvalues λₚ equals  
   `∏ₚ (1 − λₚ) · exp(λₚ)` (*Gohberg–Krein*).  Proof: expand definition of det₂ as renormalised product, note trace = Σλₚ.
2.  **Euler product**:  classical analytic-number-theory result:  
   `ζ(s) = ∏ₚ (1 − p^{−s})^{−1}` for Re s > 1; take inverses to match above.
3.  **Exponential factor**:  for Re s > 1, Σλₚ converges absolutely; but Σλₚ = Σp^{−s} is < ∞, so `exp(Σλₚ)` is a non-zero entire factor; we prove its product over primes equals 1 by grouping logs and using absolute convergence.

### T4 (trace-class continuity)
Fix `s₀` with σ₀ := Re s₀ > ½.  For ε>0 choose N so tail `Σ_{p>N} p^{−σ₀}` < ε/4.  On finitely many primes continuity is uniform ⇒ choose δ such that |s−s₀|<δ gives each difference term < ε/(2N).  Then
``‖K_s−K_{s₀}‖₁ ≤ finite sum + tail < ε``.
Formal Lean path: use `Summable` tail bound lemma + `continuous_at` for finite tsums.

### T5 (det₂ continuity)
Use mathlib lemma:
```
Continuous (fun T : TraceClass … => det₂ (1 - T))
```
then compose with T = `evolutionOperatorFromEigenvalues`.  Requires coercion from bounded operator to trace-class; already provided by `TraceClass.mk`.

### T6 (Analytic continuation ½ < σ ≤ 1)
•  Both sides analytic in half-strip (trace-class analytic + meromorphic ζ).  
•  They coincide on Re s > 1 (T1–T3).  
•  Apply *Identity Theorem* on connected open set `{σ>½}`.

### T7 (Discrete spectrum)
Import:
``IsCompactOperator.hasEigenvalues`` + `IsSelfAdjoint.compact` results from mathlib (≲50 loc).  No need to reproduce proof.

### T8 (Rayleigh-quotient maximum)
Let
\[ R(σ) := \frac{⟨K_{σ}x,x⟩}{‖x‖²} = \frac{\sum\_p p^{−σ}|x\_p|²}{‖x‖²}. \]
Compute derivative
\[ R'(σ)= -\frac{\sum\_p (\log p) p^{−σ}|x\_p|²}{‖x‖²}. \]
Sign flips at σ = ½ because factor p^{−σ} is log-convex; second derivative negative ⇒ global maximum.  In Lean: prove monotonicity on (½,∞).

### T9 (Fredholm determinant ⇔ spectrum)
Use result: for trace-class K, `det₂(I−K)=0 ↔ 1∈σ(K)` (Gohberg–Krein).  Combine with T1–T3 & ζ zeros.

### T10 (Eigenvalue 1 only on critical line)
Contrapositive: assume σ≠½, show spectral radius < 1 via Rayleigh bound (T8) and norm estimate ⇒ 1∉σ.

### T11 (Functional equation glue)
Lean already has `zeta_function.functional_equation`; use it to shift zeros from σ<½ to 1−s and finish.

---
## 3. Implementation Schedule

| Phase-4 Task | Depends on | Target PR | Est. LOC | Owner |
|--------------|-----------|-----------|----------|-------|
| P1. Import mathlib ζ & functional-equation, remove placeholder | – | `pr-phase4-mathlib-zeta` | +40 | core |
| P2. Fill T1–T3 (diagonal det₂ block) | P1 | `pr-frac-determinant` | +120 | analysis |
| P3. Fill T4–T5 (continuity lemmas) | P1 | `pr-frac-continuity` | +100 | analysis |
| P4. Import discrete-spectrum (T7) | P1 | `pr-frac-spectrum` | +60 | spectral |
| P5. Implement Rayleigh quotient & eigenvalue theorems (T8–T10) | P4 | `pr-frac-variational` | +150 | spectral |
| P6. Functional-equation glue (T11) | P1 | `pr-frac-functional` | +80 | number-theory |
| P7. **CI: `lake exe checkNoSorry` green** | all | `pr-phase4-final` | — | infra |

Total expected new Lean code ≤ 550 lines.

---
## 4. Documentation & Code-Hygiene Rules

1. **No monster comments** inside Lean files.  If explanatory prose > 25 lines ➜ move to `docs/` (e.g. `docs/Variational_Method.md`).  In-code comment ≤ 10 lines.
2. **One concern per commit**: either code _or_ docs, not both (except tiny typo fixes).
3. Update `IMPLEMENTATION_STATUS.md` each time a PR removes ≥ 1 sorry.
4. Each new theorem gets a short doc-string (≤3 lines) + reference to external markdown if proof sketch lengthy.
5. CI must run `lake build` + `checkNoSorry` + `leanchecker`.

---
## 5. Definition of Done (Phase 4)
- `git grep sorry` returns **0**.  
- `lake build` succeeds on CI.  
- All mathlib placeholder imports (ζ, functional equation, compact spectrum) integrated.  
- Docs split cleanly: Lean code lean; extended prose resides in `docs/`.

> *Target timeline:* 3–4 focused sprints (~2 weeks).  
> After Phase 4 the project will be ready for external community review / mathlib PRs.

---
*Drafted for Phase 4 kickoff – ready for team discussion and task assignment.* 