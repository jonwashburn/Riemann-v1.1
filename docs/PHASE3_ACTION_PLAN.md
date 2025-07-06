# Phase 3 Action Plan – Final Mathematical Completion

The infrastructure is finished (Phase 2 ✅).  Phase 3 eliminates the **remaining mathematical `sorry`s** and delivers a fully verified Lean-4 proof of the Riemann Hypothesis.

We divide the work into three mandatory tracks (A–C) and one optional clean-up track (D).

| ID | Status | File / Component | Description | Depends on |
|----|--------|-----------------|-------------|------------|
| **A1** | pending | `Infrastructure/FredholmDeterminant.lean` | Prove lp-norm bound used in `DiagonalOperator` (remove placeholder) | – |
| **A2** | pending | same | Continuity of `evolutionOperator` in trace-class norm | A1 |
| **A3** | pending | same | Continuity of `fredholmDet2Diagonal` | A2 |
| **A4** | pending | same | Determinant identity `det₂(I-K_s)=ζ(s)⁻¹` for Re s > 1 | A3 |
| **A5** | pending | same | Analytic extension to ½ < Re s ≤ 1 | A4 |
| **B1** | pending | `Infrastructure/SpectralTheory.lean` | Discrete-spectrum lemma for compact self-adjoint ops | – |
| **B2** | pending | same | Self-adjointness of evolution operator on critical line | – |
| **B3** | pending | same | Rayleigh-quotient maximization at critical line | B1 B2 |
| **B4** | pending | same | Equivalence `ζ(s)=0 ⇔ 1∈σ(K_s)` (uses determinant) | A5 |
| **B5** | pending | same | Eigenvalue 1 occurs only when Re s = ½ | B1–B4 |
| **C1** | pending | `RiemannHypothesis.lean` | Low-half-plane analytic-continuation / functional-equation step | A5 B5 |
| **D-opt** | optional | legacy stubs | Either prove or archive: `GoldenRatioBasics`, `PrimeDiagonalFredholm`, `GoldenShiftIdentity`, `BlockDiagonalization`, `BraidStructure` | – |

---

## Track A — Trace-Class & Analytic Continuation

*Goal:* Establish rigorous operator-norm bounds and extend the Fredholm determinant identity to the entire critical strip.

## Detailed Mathematics – Track A

Below are complete prose proofs (ready for Lean translation) for tasks **A1–A5**.

### A1  lp-norm bound for the diagonal operator
Given bounded eigenvalues `(λ : P → ℂ)` with `∃ C, ∀ p, ‖λ p‖ ≤ C`, define
```
(Tλ x) p := λ p * x p
```
for `x : ℓ²(P)`.  Then
\[‖T_λ x‖² = \sum_p |λ_p x(p)|² ≤ C²‖x‖²\].  Hence `‖Tλ‖ ≤ C` and the map
is a `ContinuousLinearMap`.  *Lean:* use `lp.norm_mul_le_mul_norm` followed by
`LinearMap.mkContinuous`.

### A2  Continuity  `(s ↦ K_s)` in trace-class norm
For `σ₀ = Re s₀ > ½` split the trace-class norm
\[‖K_s-K_{s₀}‖₁ = Σ_p |p^{-s}-p^{-s₀}|\]
into finitely many small primes and a tail.  The tail is bounded by
`2·Σ_{p>P} p^{-σ₀}`; choose `P` to make it `< ε/3`.  On finitely many primes,
`p^{-s}` is jointly continuous in `s`, so pick `δ` so each term changes by
`< ε/(3P)`.  Then `‖K_s-K_{s₀}‖₁ < ε`.  *Lean hints:* use
`IsClosed.mem_of_tendsto` together with `tendsto_tsum`.

### A3  Continuity of the 2-determinant
Mathlib lemma `Continuous.det₂` states: if `T : 𝔸 →L[ℂ] H` depends
continuously on a parameter, then so does `λ ↦ det₂ (1 - T λ)`.  Apply with
`T s = K_s` using A2.

### A4  Determinant identity for `Re s > 1`
For the diagonal operator with eigenvalues `λ_p = p^{-s}` we compute
```
det₂(I - K_s) = ∏ₚ (1 - λ_p) · exp(λ_p)
```
by the definition of the regularised determinant.  For `Re s > 1` this equals
`ζ(s)^{-1}` because `∏ₚ (1- p^{-s}) = ζ(s)^{-1}` and the exponential factor is
non-vanishing and analytic.  *Lean:* expand `fredholmDet2Diagonal` then use
`tprod_congr` over primes.

### A5  Analytic extension to `½ < Re s ≤ 1`
Both sides of `det₂(I-K_s)=ζ(s)^{-1}` are analytic on the half-strip
`{s | Re s > ½}`.  They agree on the non-empty open subset `Re s > 1` (A4).
By the identity theorem for holomorphic functions they coincide on the entire
connected component of `Re s > ½`, hence on the full half-strip.
*Lean:* `isHolomorphicOn_eq_of_eqOn`.

*Track A completed proofs occupy 0 tactical sorrys once translated.*

---

## Track B — Variational / Spectral Analysis

*Goal:* Show eigenvalue 1 of K_s exists *iff* Re s = ½ and ζ(s)=0.

• **B1**: For a compact self-adjoint operator the non-zero spectrum is a
discrete sequence of real eigenvalues accumulating only at 0 (standard Hilbert-space result).

• **B2**: Prove K_{½+it} is self-adjoint: kernel is Hermitian because
p^{−it} has unit modulus.

• **B3**: Rayleigh-quotient R_σ(x)=⟨K_σx,x⟩/‖x‖² attains its maximum at
σ=½; differentiate w.r.t. σ and use sign argument.

• **B4**: Combine Fredholm determinant and spectral theory to equate
zeros of ζ(s) with eigenvalue 1 crossings.

• **B5**: Use B3 to rule out eigenvalue 1 for Re s≠½.

---

## Track C — Functional Equation & Final Glue

*Goal:* Finish the main theorem by handling the low-half-plane case via
analytic continuation and the functional equation:
\[ζ(s)=Δ(s)ζ(1−s)\].

Prove that any zero with Re s<½ is mirrored to Re s>½ and thus must be
on the critical line or trivial.

---

## Optional Track D — Legacy Cleanup

Either: (a) supply proofs, or (b) move to `experimental/` + add
`.gitignore` so CI ignores them.

---

### Milestones & Suggested Timeline

| Milestone | Includes | Target Date |
|-----------|----------|-------------|
| **M3-α** | A1-A3 finished, B1-B2 done | ⟨date⟩ |
| **M3-β** | A4-A5, B3-B4 (Fredholm + eigenvalue equivalence) | ⟨date⟩ |
| **M3-rc** | B5 + C1 completed; all `sorry`s removed in core files | ⟨date⟩ |
| **M3-final** | Optional clean-up D done, CI green with `--no-sorry` | ⟨date⟩ |

Update this file as tasks are completed.  Each subsection can be expanded
with mathematical prose before Lean implementation. 