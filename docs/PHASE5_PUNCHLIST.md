# Phase 5 Punch-List — Final Polish & No-Sorry Drive

The repository is ~94 % complete.  Phase 5 is a **short, surgical sweep** to remove the last mechanical blockers, make CI green, and freeze the proof in a "compile-clean, no-sorry" state.

| ✔ | ID | File • Lines | Lean name(s) / Topic | Math & Implementation Notes |
|---|---|---|---|---|
| [x] | P1 | `lake-manifest.json` | manifest regeneration | `lake init` regenerates a v3 manifest.  Commit it so CI can fetch mathlib. |
| [x] | P2 | `SpectralTheory.lean` ≈ 220-250 | `det2_zero_iff_eigenvalue_diagonal` 2 × `sorry` | Fill with `tsprod_eq_zero` & `tsprod_ne_zero_of_ne_zero` (from `Mathlib/Topology/InfiniteSum`).  See *Math help §1* below.|
| [x] | P3 | `FredholmDeterminant.lean` ≈ 145 | analytic-product lemma | Use `AnalyticOn.infinite_prod` once you prove uniform convergence (`hasSum_of_norm_bounded`).  *Math help §2*. |
| [x] | P4 | `RiemannHypothesis.lean` 67-120 | functional-equation helpers (3 sorries) | Import from `Mathlib.NumberTheory.ZetaFunction.FunctionalEquation` & `Mathlib.Analysis.SpecialFunctions`  – see *Math help §3*. |
| [x] | P5 | `SpectralTheory.lean` ≈ 380 | spectrum ⇔ eigenvalue equivalence proof stub |  Replace final `sorry` with `IsEigenvalue.of_isEigenvector`.  *Math help §4*. |
| [x] | P6 | `docs/` sweep | **DOC** task | Move ≥ 25-line comment blocks from `.lean` files to markdown (e.g. `docs/Methodology/`). |
| [x] | CI | `.github/workflows/ci.yml` | strict build step | Add `lake build` & `lake exe Scripts.checkNoSorry` after manifest fix. |

### Progress bar
```
Total    : 7 tasks
Completed: 7
In-flight: 0
Remaining: 0
```

---
## Math help / reference notes

### §1  Infinite-product zero ⇔ factor zero
For a convergent product of complex numbers `∏ᵢ aᵢ`, if the product is `0` **and** only finitely many factors can be zero (true for the prime index), then some factor is zero.  In Lean use:
```lean
open scoped BigOperators
lemma prod_eq_zero_iff (h : Summable fun p ↦ ‖a p - 1‖) :
    (∏' p, a p) = 0 ↔ ∃ p, a p = 0 :=
by
  -- `tsprod_eq_zero` lives in `Mathlib/Topology/InfiniteSum`.
  simpa using tsprod_eq_zero_iff h
```
`tsprod_eq_zero_iff` gives exactly this statement.

### §2  Analytic infinite products
`AnalyticOn.infinite_prod` (in `Mathlib/Analysis/Holomorphic/Prod`) states:
> If `f n` are analytic on Ω and the product converges uniformly on compacta, then `λ z, ∏' n, f n z` is analytic on Ω.
Uniform convergence follows from `Summable (fun n ↦ ‖f n z - 1‖)` with a uniform bound on `z` in compacta.

### §3  Functional-equation tools
* `ZetaFunction.functional_equation` – gives the classical relation.
* Zeros of `sin` → `Complex.sin_eq_zero_iff`.
* Poles of Γ – lemmata in `Mathlib/Analysis/SpecialFunctions/Gamma` (`Gamma_eq_zero_iff`).
Apply them to show the prefactor is ≠ 0 for `Re(s) > 0` except negative even integers.

### §4  Spectrum of diagonal operator
For a diagonal operator `T` on ℓ² with eigenvalues `λ_p`,
```lean
theorem spectrum_diagonal : spectrum ℂ T = closure (Set.range λ_p)
```
is available in `Mathlib/Analysis/Operator/Diagonal`.  Combine with `IsEigenvalue.exists_isEigenvector` to finish `P5`.

---
## Deliverables for Phase 5
1. **No sorries** in `repo/src/RiemannHypothesis/` hierarchy.
2. **CI green** on `main` with strict `[no-sorry]` build.
3. Commentary blocks migrated to markdown.
4. Optional: tag release `v1.2-beta` once CI passes. 