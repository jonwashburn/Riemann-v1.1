# Formal-Proof Checklist for `RiemannHypothesis.lean`

This document records **every mathematical ingredient** still needed to turn the high-level
skeleton in `src/RiemannHypothesis/RiemannHypothesis.lean` into a fully verified proof.
The list follows the six annotated steps already present in the file.

---
## 0  Notation & basic objects

* **Weighted Hilbert space** `WeightedL2`               — already defined in
  `Infrastructure/WeightedHilbertSpace.lean`.
* **Evolution operator**   `A s : WeightedL2 →L[ℂ] WeightedL2`    — diagonal with
  eigenvalues `p⁻ˢ`.  Implemented via `evolutionOperatorFromEigenvalues` in
  `FredholmDeterminant.lean`.
* **Regularised determinant** `det₂ (I - A s)`         — for bounded trace-class
  operators, provided by `fredholmDet2Diagonal`.
* **Regularised Euler factor already inside determinant**
  The determinant identity uses the product `(1 − p^{-s})·exp(p^{-s})`, which
  converges for `Re s > 1/2`.  No additional correction factor is required.
* **Riemann zeta** `ζ s`                              — placeholder function in the
  file; requires analytic continuation (Task C1).

---
## 1  Fredholm determinant identity

**Goal**   `∀ s, ½ < Re s → det₂ (I - A s) = ζ s ⁻¹`

| ID | Lemma / definition | File | Status |
|----|--------------------|------|--------|
| A1 | Proof that `A s` is trace-class for Re s > ½ | `FredholmDeterminantProofs` | **done** |
| A2 | (No longer needed) | — | **removed** |
| A3 | Prove determinant identity  `det₂ (I - A s) = ζ s ⁻¹`  | **new** | 🛠 |

Dependencies: Dirichlet series of `log ζ`, classical Euler product; uses the
built-in quadratic regularisation inside the determinant.

---
## 2  Zero of ζ ⇒ zero of determinant

**Lemma B1**  If `ζ s = 0` then `det₂ (I - A s) = 0` (since they are inverses).
Status 🛠 — becomes immediate once A3 is proved.

---
## 3  Determinant = regularised product

Already provided: `fredholmDet2Diagonal` gives
``det₂ (I - A s) = ∏ₚ (1 - p⁻ˢ)·exp (p⁻ˢ)``
for Re s > ½.

No extra work.

---
## 4  Vanishing product ⇒ p⁻ˢ = 1 for some prime

`FredholmVanishingEigenvalueProof.lean` contains a partial proof.  Outstanding:

| ID | Lemma | Status |
|----|-------|--------|
| D1 | `infinite_product_zero_implies_factor_zero` for complex products | **sorry** in file |
| D2 | Finish `vanishing_product_implies_eigenvalue_proof` | **sorry** placeholders |

Once D1/D2 are completed we obtain an eigenvalue 1 of `A s`.

---
## 5  From p⁻ˢ = 1 to Re s = ½ or trivial

Arithmetic manipulation gives `s = 2π i k / log p`.
Need to rule out `k ≠ 0` when `Re s > 0`, and then analyse real part:

| ID | Lemma | File | Status |
|----|-------|------|--------|
| E1 | If `p⁻ˢ = 1` and `Re s > 0` then `s.re = 0` | **new** | 🛠 |
| E2 | Show ζ(0) ≠ 0 (classical) to derive contradiction | **new** | 🛠 |

Alternate route: Use analytic continuation and functional equation to move
zeros to the critical line.

---
## 6  Analytic continuation & functional equation

| ID | Lemma | File | Status |
|----|-------|------|--------|
| F1 | Define ζ on ℂ via analytic continuation | `Placeholders` | **sorry** |
| F2 | Functional equation ξ(s) = ξ(1 − s) | `Placeholders` | **sorry** |

These results allow the final step: any non-trivial zero with Re s > 0 must have
Re s = ½.

---
## 7  Summary of outstanding work

1. **Determinant identity**: A3, F1, F2.
2. **Infinite-product lemma**: D1, complete D2.
3. **Arithmetic clean-up**: E1, E2.
4. Remove any lingering comments referring to a separate `E s`.

---
### How to proceed
1. Finish D1 in `FredholmVanishingEigenvalueProof.lean` (pure analysis, lowest hanging fruit).
2. Implement `E s` (bounded exponential Euler factor) and prove A3; this will also settle B1.
3. Port analytic-continuation results from mathlib (ζ and Γ) into F1/F2.
4. Finally stitch the steps in `RiemannHypothesis.lean`, replacing the big `sorry` with calls to the completed lemmas. 