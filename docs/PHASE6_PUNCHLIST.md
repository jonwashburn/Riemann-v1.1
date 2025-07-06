# Phase 6 Punch-List — "Zero-Sorry" Closure

Phase 5 left the repository compiling again but with ~54 strategic `sorry`s.  Phase 6 is a *tight* clean-up to drive the total count to **zero**, polish CI, and tag the first _no-sorry_ release.

| ✔ | ID | File/Section | Topic | Notes / Reference |
|---|---|---|---|---|
| [ ] | S1 | `SpectralTheory.lean` (≈ 290, 350, 410) | p-series summability lemmas | Use `Nat.Prime.summable_pow` or `summable_rpow_of_lt_neg_one`. 8 tiny `sorry`s. |
| [ ] | S2 | `SpectralTheory.lean` / `FredholmDeterminant.lean` | Taylor bound `|(1-z) eᶻ − 1| ≤ 2‖z‖²` | One lemma reused in 4 places.  Prove with `ExpSeries`. |
| [ ] | S3 | `SpectralTheory.lean` (det₂ ⇔ eigenvalue) | `spectrum_diagonal` + `IsEigenvalue` glue | Replace two `sorry`s with `Spectrum.isClosed`, `IsEigenvalue.of_mem`.
| [ ] | S4 | `FredholmDeterminant.lean` uniform-conv proof | Bound tail of analytic infinite product | Finish `h_product_bound` + final `≤` chain.
| [ ] | S5 | `FredholmDeterminant.lean` analytic-continuation section | Plug remaining identity-theorem boiler-plate | Use `AnalyticOn.eqOn_of_eqOn_dense` + `isConnected_halfSpace_re_gt`.
| [ ] | S6 | `RiemannHypothesis.lean` functional-equation helpers | Replace remaining `sorry`s with existing lemmas (`Gamma_eq_zero_iff`, `sin_eq_zero_iff`) | About 5 lines.
| [ ] | S7 | `SpectralTheory.lean` variational-principle tail | Last bound using `tsum_lt_tsum` + positivity | 6 tiny `sorry`s.
| [ ] | CI | `.github/workflows/ci.yml` | remove development "≤50 sorry" guard | CI should fail on *any* `sorry`.

### Progress Bar
```
Total    : 8 tasks
Completed: 0
Remaining: 8
```

### Milestone definition
* All Lean files compile under `lake build` with **zero `sorry` statements**.
* GitHub Action green on every push to `main`.
* Tag release `v1.2-no-sorry` after CI passes. 