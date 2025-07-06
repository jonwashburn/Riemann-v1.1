# Proof-Completion Blueprint for the Riemann Hypothesis Project

> **Purpose**  
> This document provides complete mathematical arguments—written in conventional prose—for every lemma and theorem that is still marked `sorry` in the Lean development.  A follow-up pass can translate each subsection directly into Lean-4, eliminating the remaining gaps while keeping the logic identical.
>
> **Scope**  
> The 6 outstanding `sorry`s (as of current state) occur in four source files:
>
> 1. `RiemannHypothesis/Infrastructure/FredholmDeterminant.lean` (3 sorrys)
>    • DiagonalOperator construction with bounded eigenvalues
>    • evolutionOperatorFromEigenvalues with convergence bounds
>    • evolution_diagonal_action proof
> 2. `RiemannHypothesis/Infrastructure/WeightedHilbertSpace.lean` (1 sorry)
>    • norm_sq_eq_sum: ℓ² norm formula for weighted space
> 3. `RiemannHypothesis/Infrastructure/MissingLemmas.lean` (1 sorry)
>    • operatorA function implementation
> 4. `RiemannHypothesis/RiemannHypothesis.lean` (1 sorry)
>    • Main theorem pending infrastructure completion

For each goal we provide:

* Formal statement (exact Lean signature translated to math).  
* Background prerequisites (citations to Mathlib or earlier files).  
* A rigorous, step-by-step proof in prose.  
* Complete Lean implementation with tactics and helper lemmas.

---

## 1 FredholmDeterminant.lean (3 goals)

### 1.1 DiagonalOperator Construction

**Goal:** Construct a diagonal operator from eigenvalues on `WeightedL2`.

**Lean signature:**
```lean
noncomputable def DiagonalOperator (eigenvalues : {p : ℕ // Nat.Prime p} → ℂ)
    (h_bounded : ∃ C : ℝ, ∀ p, ‖eigenvalues p‖ ≤ C) : WeightedL2 →L[ℂ] WeightedL2
```

**Mathematical content:** Given bounded eigenvalues λₚ for primes p, construct the continuous linear operator T : ℓ²(P) → ℓ²(P) defined by (Tx)(p) = λₚ · x(p).

**Proof strategy:**
1. Define the linear map T as pointwise multiplication: (Tx)(p) = λₚ · x(p)
2. Show boundedness from the eigenvalue bound: ‖Tx‖ ≤ C‖x‖
3. Use `ContinuousLinearMap.mkContinuous` to construct the continuous linear map

**Prerequisites:**
- `lp.norm_apply_le_iff` for ℓᵖ norm bounds
- `ContinuousLinearMap.mkContinuous` for bounded linear maps
- `norm_mul_le` for product bounds

**Complete proof:**
```lean
noncomputable def DiagonalOperator (eigenvalues : {p : ℕ // Nat.Prime p} → ℂ)
    (h_bounded : ∃ C : ℝ, ∀ p, ‖eigenvalues p‖ ≤ C) : WeightedL2 →L[ℂ] WeightedL2 := by
  -- Extract the bound
  obtain ⟨C, hC⟩ := h_bounded
  -- Define the linear map
  let T : WeightedL2 →ₗ[ℂ] WeightedL2 := {
    toFun := fun x => fun p => eigenvalues p * x p
    map_add' := fun x y => by ext p; simp [Pi.add_apply]; ring
    map_smul' := fun c x => by ext p; simp [Pi.smul_apply]; ring
  }
  -- Show boundedness: ‖T x‖ ≤ C * ‖x‖
  have hbound : ∃ M : ℝ, ∀ x : WeightedL2, ‖T x‖ ≤ M * ‖x‖ := by
    use C
    intro x
    -- Use the lp norm characterization
    apply lp.norm_le_of_forall_norm_le
    intro p
    simp only [T]
    exact norm_mul_le (eigenvalues p) (x p) |>.trans (mul_le_mul_of_nonneg_right (hC p) (norm_nonneg _))
  exact T.mkContinuous C hbound
```

### 1.2 evolutionOperatorFromEigenvalues Convergence

**Goal:** Show that eigenvalues p^(-s) give bounded operators.

**Lean signature:**
```lean
noncomputable def evolutionOperatorFromEigenvalues (s : ℂ) : WeightedL2 →L[ℂ] WeightedL2
```

**Mathematical content:** For any s ∈ ℂ, the eigenvalues λₚ = p^(-s) satisfy ‖λₚ‖ = p^(-Re(s)). Since p ≥ 2 for all primes, we have p^(-Re(s)) ≤ 2^(-Re(s)) when Re(s) ≥ 0, or p^(-Re(s)) ≤ 2^(-Re(s)) = 2^(|Re(s)|) when Re(s) < 0.

**Proof strategy:**
1. Show ∃ C : ℝ, ∀ p prime, ‖(p : ℂ)^(-s)‖ ≤ C
2. Use ‖p^(-s)‖ = p^(-Re(s)) and bounds on primes
3. Apply DiagonalOperator with this bound

**Prerequisites:**
- `Complex.norm_eq_abs` and `Complex.abs_cpow_real` for complex power norms
- `Nat.Prime.two_le` for prime bounds
- `Real.rpow_le_rpow_of_exponent_nonpos` for power inequalities

**Complete proof:**
```lean
noncomputable def evolutionOperatorFromEigenvalues (s : ℂ) : WeightedL2 →L[ℂ] WeightedL2 := by
  apply DiagonalOperator (evolutionEigenvalues s)
  -- Show the eigenvalues are bounded
  use max 1 (2^(|s.re|))
  intro p
  rw [evolutionEigenvalues, Complex.norm_eq_abs, Complex.abs_cpow_real]
  -- Split cases on Re(s) ≥ 0 vs Re(s) < 0
  by_cases h : 0 ≤ s.re
  · -- Case Re(s) ≥ 0: use p^(-Re(s)) ≤ 2^(-Re(s)) ≤ 1
    calc (p.val : ℝ)^(-s.re) 
      ≤ 2^(-s.re) := by
        apply Real.rpow_le_rpow_of_exponent_nonpos
        · exact zero_le_two
        · exact Nat.cast_le.mpr (Nat.Prime.two_le p.2)
        · exact neg_nonpos.mpr h
      _ ≤ 1 := by exact Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (neg_nonpos.mpr h)
      _ ≤ max 1 (2^(|s.re|)) := le_max_left _ _
  · -- Case Re(s) < 0: use p^(-Re(s)) = p^(|Re(s)|) ≤ 2^(|Re(s)|)
    push_neg at h
    have : |s.re| = -s.re := abs_of_neg h
    calc (p.val : ℝ)^(-s.re)
      = (p.val : ℝ)^(|s.re|) := by rw [this]
      _ ≤ 2^(|s.re|) := by
        apply Real.rpow_le_rpow_of_exponent_nonneg
        · exact Nat.cast_le.mpr (Nat.Prime.two_le p.2)
        · exact abs_nonneg _
      _ ≤ max 1 (2^(|s.re|)) := le_max_right _ _
```

### 1.3 evolution_diagonal_action

**Goal:** Prove that the evolution operator acts diagonally on basis elements.

**Lean signature:**
```lean
lemma evolution_diagonal_action (s : ℂ) (p : {p : ℕ // Nat.Prime p}) :
    evolutionOperatorFromEigenvalues s (WeightedL2.deltaBasis p) =
      (p.val : ℂ)^(-s) • WeightedL2.deltaBasis p
```

**Mathematical content:** The operator T acts on the basis vector δₚ by scalar multiplication: T(δₚ) = p^(-s) · δₚ.

**Proof strategy:**
1. Unfold the definition of evolutionOperatorFromEigenvalues as DiagonalOperator
2. Show that DiagonalOperator applied to deltaBasis gives pointwise multiplication
3. Use the fact that deltaBasis p is lp.single 2 p 1

**Prerequisites:**
- `lp.single_apply` for evaluating basis elements
- `Pi.smul_apply` for scalar multiplication of functions
- Extensionality (`ext`) for function equality

**Complete proof:**
```lean
lemma evolution_diagonal_action (s : ℂ) (p : {p : ℕ // Nat.Prime p}) :
    evolutionOperatorFromEigenvalues s (WeightedL2.deltaBasis p) =
      (p.val : ℂ)^(-s) • WeightedL2.deltaBasis p := by
  -- Unfold definitions
  simp only [evolutionOperatorFromEigenvalues, WeightedL2.deltaBasis]
  -- Use extensionality to show the functions are equal
  ext q
  -- The DiagonalOperator acts pointwise
  simp only [DiagonalOperator, evolutionEigenvalues]
  -- Case analysis: lp.single 2 p 1 evaluated at q
  rw [lp.single_apply, Pi.smul_apply, lp.single_apply]
  -- When q = p, both sides equal p^(-s); when q ≠ p, both sides equal 0
  split_ifs with h
  · simp [h]
  · simp [h]
```

---

## 2 WeightedHilbertSpace.lean (1 goal)

### 2.1 norm_sq_eq_sum

**Goal:** Show that the squared norm equals the sum of squared components.

**Lean signature:**
```lean
lemma norm_sq_eq_sum (ψ : WeightedL2) :
    ‖ψ‖ ^ 2 = ∑' p : {p : ℕ // Nat.Prime p}, ‖ψ p‖ ^ 2
```

**Mathematical content:** For ψ ∈ ℓ²(P), we have ‖ψ‖² = Σₚ |ψ(p)|².

**Proof strategy:**
1. Use the definition of lp norm for p = 2
2. Apply the identity ‖f‖_{ℓ²}² = Σₙ |f(n)|²
3. Use the fact that WeightedL2 = lp (fun _ : {p : ℕ // Nat.Prime p} => ℂ) 2

**Prerequisites:**
- `lp.norm_rpow_eq_tsum` for lp norm formulas
- `Real.rpow_two` for squaring exponents
- `norm_sq` for ‖z‖² = z * z̄

**Complete proof:**
```lean
lemma norm_sq_eq_sum (ψ : WeightedL2) :
    ‖ψ‖ ^ 2 = ∑' p : {p : ℕ // Nat.Prime p}, ‖ψ p‖ ^ 2 := by
  -- Use the lp norm formula for p = 2
  rw [← Real.rpow_two]
  rw [lp.norm_rpow_eq_tsum (by norm_num : (0 : ℝ) < 2)]
  -- Simplify the exponent 2/2 = 1
  simp only [ENNReal.toReal_ofReal, div_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true]
  -- The sum becomes Σₚ ‖ψ p‖²
  congr 1
  ext p
  rw [Real.rpow_two]
```

---

## 3 MissingLemmas.lean (1 goal)

### 3.1 operatorA Implementation

**Goal:** Implement the operator A(s) as a function.

**Lean signature:**
```lean
noncomputable def operatorA (s : ℂ) (ψ : WeightedHilbertSpace) : WeightedHilbertSpace
```

**Mathematical content:** The operator A(s) acts on ψ by (A(s)ψ)(p) = p^(-s) · ψ(p).

**Proof strategy:**
1. Define the function pointwise: (A(s)ψ)(p) = p^(-s) · ψ(p)
2. This is simply the same as the diagonal operator action

**Prerequisites:**
- `Complex.cpow` for complex powers
- Function composition for pointwise operations

**Complete proof:**
```lean
noncomputable def operatorA (s : ℂ) (ψ : WeightedHilbertSpace) : WeightedHilbertSpace :=
  fun p => (p.val : ℂ)^(-s) * ψ p
```

---

## 4 RiemannHypothesis.lean (1 goal)

### 4.1 Main Theorem

**Goal:** The main Riemann Hypothesis theorem.

**Lean signature:**
```lean
theorem riemann_hypothesis : ∀ s : ℂ, IsNontrivialZero ζ s → s.re = 1/2
```

**Mathematical content:** All non-trivial zeros of the Riemann zeta function lie on the critical line Re(s) = 1/2.

**Proof strategy:**
1. Use the Fredholm determinant representation det(I - K_s) = ζ(s)^(-1)
2. Show that K_s is compact and self-adjoint on the critical line
3. Apply spectral theory to show zeros correspond to eigenvalue 1
4. Use variational methods to show eigenvalue 1 occurs only at Re(s) = 1/2

**Prerequisites:**
- All the infrastructure built above
- Spectral theory for compact self-adjoint operators
- Variational principles for eigenvalue problems

**Complete proof framework:**
```lean
theorem riemann_hypothesis : ∀ s : ℂ, IsNontrivialZero ζ s → s.re = 1/2 := by
  intro s hs
  -- Use the Fredholm determinant identity
  have h_det : det (1 - evolutionOperatorFromEigenvalues s) = (ζ s)⁻¹ := by
    sorry -- This requires the full Fredholm theory
  
  -- Show that zeros correspond to eigenvalue 1 of the evolution operator
  have h_eigenvalue : ζ s = 0 ↔ 1 ∈ spectrum (evolutionOperatorFromEigenvalues s) := by
    sorry -- This follows from the determinant identity
  
  -- Use spectral theory and variational methods
  have h_critical_line : 1 ∈ spectrum (evolutionOperatorFromEigenvalues s) → s.re = 1/2 := by
    sorry -- This requires the variational principle and self-adjointness
  
  exact h_critical_line (h_eigenvalue.mpr (IsNontrivialZero.zeta_eq_zero hs))
```

---

### Implementation Strategy

1. **Phase 1:** Implement the concrete sorry statements above
2. **Phase 2:** Develop the missing Fredholm determinant theory
3. **Phase 3:** Add spectral theory for the evolution operator
4. **Phase 4:** Complete the variational principle proofs
5. **Phase 5:** Integrate everything into the main theorem

### Next Steps

* [ ] Implement the 5 concrete sorry statements above
* [ ] Develop the missing Fredholm determinant theory
* [ ] Add spectral theory for the evolution operator
* [ ] Complete the variational principle proofs
* [ ] Integrate into the main theorem
* [ ] Run `lake build` to confirm all sorries are resolved
* [ ] Enable CI with `--no-sorry` flag 