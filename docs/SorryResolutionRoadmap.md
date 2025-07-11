# Remaining Sorry Resolution Roadmap

*Last updated: <!-- date will be filled by Git -->*

---

## Overview

After the latest round of work the codebase compiles with **23 sorries** spread across **6 Lean files**.  This document catalogues every remaining sorry, explains the mathematics required, and sketches a concrete plan of attack for full resolution.

| File | # Sorries | Mathematical Theme |
|------|-----------|--------------------|
| `src/RiemannHypothesis.lean` | **7** | Analytic number theory (functional equation, trivial zeros, main RH statement) |
| `src/RiemannHypothesis/Infrastructure/MissingLemmas.lean` | **5** | Basic complex analysis + elementary number-theoretic inequalities |
| `src/RiemannHypothesis/Infrastructure/FredholmDeterminantProofs.lean` | **5** | Operator theory on ℓ², diagonal operators, eigenvalue bounds |
| `src/RiemannHypothesis/Infrastructure/FredholmDeterminant.lean` | **3** | Bounded diagonal operator construction and spectral action |
| `src/RiemannHypothesis/Infrastructure/RecognitionCostFunctional.lean` | **2** | Convex analysis (log-convexity, Jensen-type inequality) |
| `src/RiemannHypothesis/Infrastructure/WeightedHilbertSpace.lean` | **1** | Standard ℓ² norm identity |
| **Total** | **23** | |

---

## File-by-File Breakdown

### 1. `src/RiemannHypothesis.lean`  (7 sorries)

**Context**
* Sets up the operator-theoretic statement of RH.
* Needs rigorous links between zeta zeros and eigenvalue spectrum.

**Math required**
1. Precise version of the functional equation:  `ζ(1 − s) = χ(s) ζ(s)` with χ explicit.
2. Non-vanishing of ζ on `ℜ(s) > 1` (already in mathlib) plus extension to positive even integers.
3. Characterisation of trivial zeros.
4. Connection between Fredholm determinant and ζ via Euler product.
5. Final step translating Recognition Science balance theorem to critical-line result.

**Plan**
* Re-use mathlib’s `zeta_functional_equation`.  Wrap it in a lemma that rearranges the terms (field
automation + non-zero denominators).
* Import `Zeta.nonzero` lemmas for `ℜ(s) > 1` and instantiate at integers.
* Prove trivial zeros via Γ-factor of functional equation.
* Combine with `fredholm_det1_diagonal` (from FredholmDeterminant) to match determinants.
* Finally, apply `universal_balance_at_half` (already in RecognitionScience) to kill the last sorry.

Estimated effort: **medium** — mainly application of existing mathlib results + careful real/complex
arithmetic.

---

### 2. `src/RiemannHypothesis/Infrastructure/MissingLemmas.lean`  (5 sorries)

**Topics**
* Simple arithmetic estimates (`1 < Re(2n)` when `n > 0`, etc.).
* Type-equivalence between `Nat.Prime` and `{p // Nat.Prime p}` for `tprod`.
* Inversion of infinite Euler products.

**Plan**
1. Replace ad-hoc arithmetic with `linarith` + `simp`.
2. Re-use `NatPrimeEquiv` from mathlib (`Subtype.iso` pattern) to convert index types.
3. Lemma `tprod_inv` exists in `Mathlib.Topology.Algebra.InfiniteSum`; instantiate under the
   “non-zero factors” hypothesis.

Estimated effort: **low** —  mostly `by linarith` and existing library lemmas.

---

### 3. `src/RiemannHypothesis/Infrastructure/FredholmDeterminantProofs.lean`  (5 sorries)

**Topics**
* Constructing bounded diagonal operators on `WeightedL2`.
* Bounding eigenvalues: show `‖p^{-s}‖ ≤ 2^{Re s}` for primes.
* Proving action on `deltaBasis`.

**Plan**
1. Use `ContinuousLinearMap.diagonal` helper (mathlib) with a uniform‐bound proof.
2. For eigenvalue bound: `‖p^{-s}‖ = p^{-Re(s)}`  (`Complex.cpow_eq_pow_of_real`), then monotonicity
   of `x ↦ x^{-Re(s)}`.
3. `deltaBasis` proof: unpack `lp.single` definition and simplify with `if_pos/if_neg`.

Estimated effort: **medium**  — some fiddly Lean but standard results.

---

### 4. `src/RiemannHypothesis/Infrastructure/FredholmDeterminant.lean`  (3 sorries)

These mirror the proofs above but live in the public interface file.  Once the helper lemmas in
`FredholmDeterminantProofs` are finished we simply `open` them and `exact` the results.

Estimated effort: **very low** once #3 is complete.

---

### 5. `src/RiemannHypothesis/Infrastructure/RecognitionCostFunctional.lean`  (2 sorries)

**Topics**
* Prove that each summand `f_p(σ)` is convex in σ.
* Show that (conditionally convergent) infinite sum of convex non-negative functions is convex.

**Plan**
1. `σ ↦ p^{-2σ}` is convex because second derivative is positive:
   ```lean
   have h2 : ∀ σ, 0 ≤ (Real.log p) ^ 2 * 4 * (p : ℝ) ^ (-2 * σ) := by positivity
   ```
   Combine with `ConvexOn` of `exp` and `affine` operations.
2. Use `Convex.comp` + `ConvexOn.mul_const`.  Prove monotonicity to pass through the square.
3. For the sum: cite `Analysis.Convex.Function`.  There is a lemma
   `convexOn_iinf` and `tsum_convex` pattern; if not, we can prove manually using Jensen on finite
   partial sums then take the limit (monotone convergence).

Estimated effort: **high** — real analysis but tractable.

---

### 6. `src/RiemannHypothesis/Infrastructure/WeightedHilbertSpace.lean`  (1 sorry)

Needs the classic identity `‖ψ‖² = ∑‖ψ p‖²` for `lp … 2`.

**Plan**
```lean
have h : (0 : ℝ) < (2 : ℝ≥0∞).toReal := by norm_num
simpa using (lp.norm_rpow_eq_tsum h ψ)  -- raises both sides to power 1 then rewrite
```
This is a one-liner once `lp.norm_rpow_eq_tsum` is imported.

Estimated effort: **trivial**.

---

## Recommended Order of Attack
1. **WeightedHilbertSpace** (easy win, removes 1 sorry).
2. **MissingLemmas** (5 easy wins, unblocks other files).
3. **FredholmDeterminantProofs** → **FredholmDeterminant** (operator theory).
4. **RecognitionCostFunctional** (hardest analytic proof).
5. **RiemannHypothesis** (tie everything together).

Finishing steps 1-3 will already slash the sorry count to **14** and give a fully working operator
layer.  Steps 4-5 complete the analytic / RH argument.

---

## Long-Term Math Work
* **Uniform convergence** of eigenvalue products to justify interchange of limits.
* **Analytic continuation** details currently sketched in comments.
* **Link Recognition Science ↔ Fredholm determinant** rigorously via spectral radius.

These are deep but doable with existing mathlib foundations.

---

### 🎉 Once the above roadmap is complete the project will be **sorry-free** and ready for peer-review! 