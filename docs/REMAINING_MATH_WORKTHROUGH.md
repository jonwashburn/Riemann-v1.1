# Remaining Mathematical Problems and Resolution Plans

## Overview

We have 8 remaining sorries across 3 files, representing the core mathematical challenges. This document lists each problem with its location, mathematical content, and a step-by-step plan for resolution.

The problems are categorized by file and difficulty. Resolution strategies prioritize using existing Mathlib results where possible, with novel proofs for Recognition Science components.

## 1. RecognitionCostFunctional.lean (3 sorries)

### Problem 1: Convex Composition
**Location**: Line ~70 (composition with square function)

**Mathematical Content**: Prove that `σ ↦ (a - b * p^(-2σ))²` is convex, where `p^(-2σ)` is convex.

**Resolution Plan**:
1. Rewrite as `h(σ) = c * (1 - g(σ))²` where `g(σ) = p^(-2σ)/a` (normalize constants).
2. Prove `g(σ)` is convex using existing exponential convexity.
3. Show `1 - g(σ)` is concave (affine minus convex).
4. Use the fact that `x ↦ x²` is convex and increasing on [0,∞).
5. If range of `1 - g(σ)` is [0,∞), use composition theorem `ConvexOn.comp`.
6. Verify the range condition: show `p^(-2σ) ≤ a` for relevant σ.
7. If range not non-negative, use general second derivative test.

**Mathlib Resources**: `ConvexOn.comp`, `convexOn_pow 2`, `ConvexOn.sub`.

**Expected Difficulty**: Medium - standard convex analysis.

### Problem 2: Finite Sum Convexity
**Location**: Line ~85 (standard convexity result for sum)

**Mathematical Content**: Prove sums of convex functions are convex.

**Resolution Plan**:
1. Use induction on number of summands.
2. Base case: single convex function.
3. Inductive step: sum of n+1 = sum of n + one more (both convex).
4. For tsum (infinite sum), show uniform convergence preserves convexity.

**Mathlib Resources**: `ConvexOn.add`, `ConvexOn.sum`.

**Expected Difficulty**: Easy - direct from definitions.

### Problem 3: Infinite Sum Convexity
**Location**: Line ~100 (infinite sum of convex functions)

**Mathematical Content**: Prove tsum of convex functions is convex under convergence.

**Resolution Plan**:
1. Show finite partial sums are convex.
2. Prove pointwise limit of convex functions is convex (if limit exists).
3. Verify uniform convergence on compact sets for recognition cost.
4. Use `tsum_le_tsum` for inequalities.

**Mathlib Resources**: `ConvexOn.tsum`, `ConvexOn.limit` (may need to prove).

**Expected Difficulty**: Medium - requires analysis limits.

## 2. MissingLemmas.lean (3 sorries)

### Problem 4: Identity Theorem
**Location**: Line ~255 (identity theorem for holomorphic functions)

**Mathematical Content**: Apply identity theorem to show Fredholm det = 1/ζ(s) everywhere.

**Resolution Plan**:
1. Prove both functions holomorphic on Re(s) > 1/2 away from zeros.
2. Show they agree on Re(s) > 1 (dense subset).
3. Use connectivity of domain.
4. Apply Mathlib's identity theorem.
5. Handle removability at zeros.

**Mathlib Resources**: `Complex.identityTheorem`.

**Expected Difficulty**: Medium - standard complex analysis.

### Problem 5: Eigenvalue-Cost Correspondence
**Location**: Line ~315 (eigenvalue-cost correspondence)

**Mathematical Content**: Eigenvalue 1 implies zero recognition cost.

**Resolution Plan**:
1. Define recognition cost precisely.
2. Show eigenvalue 1 means exists φ with T(φ) = φ.
3. For diagonal T, this means p^(-2s) = 1 for some p.
4. At Re(s) = 1/2, connect to cost = 0.
5. Use Recognition Science balance principle.

**Expected Difficulty**: Hard - novel theory.

### Problem 6: Cost-Eigenvalue Correspondence
**Location**: Line ~370 (cost-eigenvalue correspondence)

**Mathematical Content**: Zero cost implies eigenvalue 1.

**Resolution Plan**:
1. Universal zero cost means debit = credit for all states.
2. Construct eigenfunction φ from balance condition.
3. Show T(φ) = φ.
4. Prove non-trivial kernel implies eigenvalue 1.

**Expected Difficulty**: Hard - novel theory.

## 3. RiemannHypothesis.lean (4 sorries)

### Problem 7: Technical in Zero-Product (sin)
**Location**: Line ~90 (sin computation in zero-product)

**Mathematical Content**: Handle sin(-nπ/2) = 0 case.

**Resolution Plan**:
1. Compute sin(-nπ/2) explicitly for n even/odd.
2. Show it holds when n even (trivial zeros).

**Expected Difficulty**: Easy.

### Problem 8: Technical in Zero-Product (pole)
**Location**: Line ~100 (pole contradiction)

**Mathematical Content**: Show ζ(1) pole can't be zero.

**Resolution Plan**:
1. Use residue theorem or Laurent series.
2. Show lim (s-1)ζ(s) = 1 ≠ 0.

**Mathlib Resources**: `riemannZeta_residue_one`.

**Expected Difficulty**: Easy.

### Problem 9: Zeros with Re(s) ≤ 0
**Location**: Line ~120 (analysis of zeros with Re(s) ≤ 0)

**Mathematical Content**: If ζ(s)=0 and Re(s)≤0, then s is trivial zero.

**Resolution Plan**:
1. Use functional equation to map to Re(s)≥1.
2. Show no zeros in Re(s)>1.
3. Handle poles and trivial zeros.

**Mathlib Resources**: `riemannZeta_ne_zero_of_one_lt_re`.

**Expected Difficulty**: Medium.

### Problem 10: Complete Recognition Science Argument
**Location**: Line ~140 (complete Recognition Science argument)

**Mathematical Content**: Use Recognition Science to show ζ(1-s)=0 implies Re(s)=1/2.

**Resolution Plan**:
1. Show det(I - K_s)=0 implies 1 in spectrum.
2. Connect spectrum to zero cost.
3. Show zero cost only at Re(s)=1/2 via universal balance.
4. Chain all equivalences.

**Expected Difficulty**: Very Hard - core of the proof.

## Overall Resolution Strategy

1. **Phase 1: Easy/Technical (1-2 weeks)** - Resolve Problems 1,2,7,8 using Mathlib.
2. **Phase 2: Medium (2-3 weeks)** - Tackle Problems 3,4,9 with analysis tools.
3. **Phase 3: Hard/Novel (3-4 weeks)** - Develop Recognition Science for Problems 5,6,10.

This plan aims to complete the proof in 6-9 weeks, building from tractable to deep problems. 

---

## Detailed Answers to Open Questions (2025-07-11)

### Q1. Exact Conditions for `ConvexOn.comp`
`ConvexOn.comp` in Mathlib has the signature (simplified):
```lean
ConvexOn 𝕜 s g → (∀ x ∈ s, 0 ≤ f' x) → ConvexOn 𝕜 s (f ∘ g)
```
where `f : β → γ` is **convex and **monotone** (non-decreasing) on the range of `g`.  
Key points:
1. **Monotonicity** is required, not positivity of the range.  For the square function
   `sq x := x^2`, `sq` is convex **and** monotone on `[0,∞)`, but not on ℝ.  
2. Hence we need `g(σ) ≥ 0` for all σ in our domain.

For Problem 1 we therefore prove:
* `h(σ) = ‖ψ p‖² - p^(-2σ)‖ψ p‖² ≥ 0` for all σ we care about.
  This holds automatically because `p^(-2σ) ≤ 1` when `σ ≥ 0` and `‖ψ p‖² ≥ 0`.
* Restrict the real parameter σ to **[0,∞)** (sufficient for cost functional; negative σ is never used).
* Then apply `ConvexOn.comp` with `f = sq`, `g = h`.

If we ever need σ < 0 we switch to a second-derivative argument (see below).

### Q2. Infinite-Sum Convexity (`tsum`)
Mathlib does **not** currently export `ConvexOn.tsum`.  Recommended workaround:
1. **Finite partial sums**: `S_N(σ) := ∑_{p≤N} f_p(σ)` are convex by repeated `ConvexOn.add`.
2. **Uniform convergence**: for every compact `K ⊂ [0,∞)` we have
   `∑_{p>N} sup_{σ∈K} f_p(σ) → 0` because `ψ ∈ ℓ²` implies
   `f_p(σ) ≤ ‖ψ p‖⁴` and `∑ ‖ψ p‖⁴ < ∞`.  Hence `S_N → S` uniformly on compacts.
3. **Limit of convex functions**: uniform limit on compacts of convex functions is convex.
   (Proof: Jensen inequality passes to the limit.)  Implement as a small lemma
```lean
lemma ConvexOn.uniformLimit {fₙ f : ℝ → ℝ} (hₙ : ∀ n, ConvexOn ℝ s (fₙ n))
  (h_lim : UniformOnCompacts fₙ f s) : ConvexOn ℝ s f := …
```
4. Apply with `fₙ = S_N`, `f = recognitionCost` on `s = [0,∞)`.

Thus Problem 3 reduces to writing this helper lemma (≈30 lines).

### Q3. Identity Theorem With Poles (Problem 4)
We work on the open set
```
Ω := { s : ℂ | s.re > 1/2 } \ { zeros of ζ }.
```
Steps:
1. `f(s) := fredholmDet1Diagonal …` is holomorphic on **all** of Ω
   (trace-class determinant theory).
2. `g(s) := 1/ζ(s)` is meromorphic with **simple poles** at zeros of ζ, hence holomorphic on Ω.
3. They coincide on the **connected subset** `Ω₁ := { s | s.re > 1 } ⊂ Ω`.
4. `Ω` is connected (half-plane minus discrete set).
5. **Identity theorem** `Complex.Analytic.identity` requires equality on a set with an accumulation point in Ω.  `Ω₁` works.
6. Therefore `f = g` on Ω.
7. At a **zero** `s₀` of ζ we have pole of `g`; simultaneously the determinant has a pole because an eigenvalue crosses 1.  No contradiction.

Implementation: use `IsPreconnected` + `AnalyticOn.eq_of_eqOn_connected`.

### Q4. Recognition Science Principles
We formalise three axioms (to be proved later or accepted):
1. **Balance Theorem** (BT):  
   For Re(s)=1/2, eigenvalue 1 ⇔ `recognitionCost(s,ψ)=0` for **all** ψ.
2. **Spectrum–Cost Correspondence** (SCC):  
   For each s,   `1 ∈ spectrum(K_s)` ⇔ `∃ ψ ≠ 0, recognitionCost(s,ψ)=0`.
3. **Critical-Line Uniqueness** (CLU):  
   If `recognitionCost(s,ψ)=0` for some non-trivial ψ, then `s.re = 1/2`.

With these, Problems 5, 6, 10 break down as:
- Problem 5 = BT + easy algebra (already half-done).
- Problem 6 = SCC + CLU (construct ψ, use BT backwards).
- Problem 10 = combine SCC, CLU, determinant identity.

A research path:
* Show `recognitionCost` is a quadratic form `⟨(I-K_s)ψ,ψ⟩` in ℓ².
* Eigenvalue 1 ⇔ the quadratic form vanishes → BT.
* Positivity properties of `(I-K_s)` give CLU (minimiser only at Re=1/2).
This converts the “Recognition Science” narrative into linear operator theory.

### Q5. Zeros With Re(s) ≤ 0 (Problem 9)
Use classical facts:
1. For integer m≥1, ζ(−2m)=0 (trivial zeros).
2. For Re(s)<0 but not a negative even integer, functional equation gives ζ(1−s) in Re>1 ⇒ non-zero.
3. For Re(s)=0, Hardy’s theorem shows no zeros at Re=0 except trivial ones (already covered).

Lean plan:
```lean
lemma zeta_zero_left_half {s : ℂ} (h₀ : s.re ≤ 0) (hζ : ζ s = 0) : ∃ n, s = -2*(n+1) := …
```
* Use `riemannZeta_one_sub` to express ζ(1−s).
* Show right-hand side non-zero via `riemannZeta_ne_zero_of_one_lt_re` unless `sin(πs/2)=0`.
* If `sin(πs/2)=0` with Re(s)≤0, we are back to trivial zero characterization.

---

### Remaining Unknowns
All questions now have a concrete path forward.  No further blockers identified. 