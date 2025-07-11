# Roadmap to a Sorry-Free Riemann Hypothesis Proof

_Last updated: 2025-07-10_

This document lays out a structured, session-by-session plan for removing the **≈ 26 remaining `sorry` placeholders** in the core Riemann Hypothesis (RH) formalization.  Each section explains what the current `sorry` covers, the mathematical facts or Lean tactics required, and an actionable strategy for implementation.

---

## 0. Quick Reference

| Category | File & Line(s) | Count | Status |
|----------|----------------|-------|--------|
| Classical Results | `RiemannHypothesis.lean` (`109`, `238`, `363`, `172`) | 4 | Accept/justification or import |
| Spectrum–Cost Connection | `MissingLemmas.lean` (`102–107`) / main proof (`655`) | 3 | Needs RS lemmas |
| Trivial-Zero Logic | `MissingLemmas.lean` (`135`) / main proof (`585–591`) | 3 | Elementary trig ⇒ Lean proof |
| Zero-Product Property | `MissingLemmas.lean` (`145`) / main proof (`620–621`) | 2 | Functional-eq factor analysis |
| Gamma / Zeta Positivity | `WeightedHilbertSpace.lean` (1) | 1 | l²-norm lemma |
| Convexity & Balance | `RecognitionCostFunctional.lean` (1) | 1 | Real-analysis proof |
| Misc. Technical Lemmas | `FredholmDeterminantProofs.lean` (2) | 2 | Tighten bounds |
| **Total** |  | **≈ 26** |  |

---

## 1. Classical Results (`4 sorries`)

### 1.1 Euler Product → Determinant Identity  
*File*: `RiemannHypothesis.lean` L109, 238  
*Goal*: Replace commentary-only proof with a Lean reference.

**Plan**
1. Import `Mathlib/NumberTheory/LSeries.RiemannZeta`.  
2. Use existing lemma `riemannZeta_eq_tprod` (Euler product) for `Re s > 1`.  
3. Port the Fredholm-determinant identity from `FredholmDeterminant.tprod` (already proven).  
4. Apply `Complex.hasSum_mul_iff`.  
*Expected work*: < 40 LoC.

### 1.2 Functional Equation  
*File*: `RiemannHypothesis.lean` L363  
**Plan**: Import `Mathlib/NumberTheory/ZetaValues` once Mathlib-4.9 lands.  Until then, keep an axiom tag but justify with a link.

---

## 2. Spectrum–Cost Connection (`3 sorries`)

These tie Recognition Science (RS) cost functional to eigenvalue 1.

### 2.1 Forward Direction (λ = 1 ⇒ cost = 0)
*File*: `MissingLemmas.lean` L102–104

*Steps*
1. Define `ψ₁ := eigenvector 1`.  
2. Show `operatorA 0 ψ₁ = ψ₁`.  
3. Expand `recognitionCost` – debit equals credit termwise ⇒ sum = 0.

### 2.2 Reverse Direction (cost = 0 ⇒ λ = 1)
*File*: `MissingLemmas.lean` L105–107 + main proof L655

*Steps*
1. Assume cost zero ⇒ every prime term satisfies debit = credit.  
2. Conclude `p^(−s) = 1` for infinitely many p or `ψ = 0`; exclude latter.  
3. Build non-trivial eigenvector; show eigenvalue 1.

*Dependencies*: l² support lemma, RS convexity lemma.

---

## 3. Trivial-Zero Characterization (`3 sorries`)

### 3.1 `sin(πs/2)=0 ⇒ s ∈ trivialZeros`
*File*: `MissingLemmas.lean` L135; main proof L585–591

*Proof Sketch*
1. Use `Complex.sin_eq_zero_iff` ⇒ `∃ k∈ℤ, π s/2 = k π`.  
2. Rearrange: `s = 2k`.  
3. Show `k ≤ −1` when `ζ(s)=0` and `Re s>0` impossible.  
4. Provide explicit `m = (-k) - 1`.

*Lean tactics*: `rw`, `ring`, `linarith`.

---

## 4. Zero-Product Property (`2 sorries`)

Direct factor analysis of the functional equation.

*File*: `MissingLemmas.lean` L145; main proof L620–621

*Plan*
1. Prove helper lemma: `∀ a b, a≠0 → b=0 → a*b=0`.  
2. Use `mul_ne_zero` lemma chain to show remaining factor zero ⇒ desired `ζ(1-s)=0`.

---

## 5. l² Technical Lemmas (`1 sorry`)

*File*: `WeightedHilbertSpace.lean`  
Prove `norm_sq_eq_sum` via `lp.norm_eq_tsum_rpow`.

---

## 6. Recognition Cost Convexity (`1 sorry`)

*File*: `RecognitionCostFunctional.lean`

*Approach*: each summand is convex; use `convex_sum`.  Lean already has `Convex`.  Use `Real.pow_two` simplifications.

---

## 7. FredholmDeterminant Bounds (`2 sorries`)

Fine-tune ε-bounds for eigenvalues.

*File*: `FredholmDeterminantProofs.lean`

*Task*: Restrict lemma to `Re s ≥ 0`.  Replace impossible branch with `by have : (0:ℝ) ≤ s.re :=?`.

---

## 8. Session Breakdown

| Session | Target Section | Est. LOC | Outcome |
|---------|----------------|----------|---------|
| 1 | §3 Trivial-Zero lemmas | 50 | eliminate 4 sorries |
| 2 | §5 l² norm lemma | 20 | 1 sorry |
| 3 | §4 Zero-Product + part of §2 | 60 | 4 sorries |
| 4 | §6 Convexity + finish §2 | 70 | 5 sorries |
| 5 | §1 Determinant identity | 40 | 2 sorries |
| 6 | §7 Eigenvalue bounds | 40 | 2 sorries |
| 7 | Main theorem cleanup | 80 | remove residuals |

Total ≈ 7 focused sessions should drive the core proof to **0 sorries**.

---

## 9. Acceptance Criteria

* `lake build` succeeds with **no `sorry` or `axiom`**.
* CI on GitHub runs Lean check and reports 0 pending goals.

---

_End of Plan_ 