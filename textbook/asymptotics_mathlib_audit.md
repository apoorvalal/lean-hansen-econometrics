# Mathlib audit: probability / asymptotics machinery for Hansen Ch 5–7

Audit performed against the Mathlib snapshot vendored in `.lake/packages/mathlib/`.
Goal: decide what to use directly, wrap, or build from scratch as we move from
Chapter 5 (finite-sample classical inference) into Chapter 7 (OLS asymptotics).

## What's already there (use directly)

| Item | File | Declaration |
|---|---|---|
| Convergence in distribution | `Mathlib/MeasureTheory/Function/ConvergenceInDistribution.lean` | `MeasureTheory.TendstoInDistribution` |
| Convergence in probability / measure | `Mathlib/MeasureTheory/Function/ConvergenceInMeasure.lean` | `MeasureTheory.TendstoInMeasure` |
| Slutsky | `Mathlib/MeasureTheory/Function/ConvergenceInDistribution.lean` | `TendstoInDistribution.prodMk_of_tendstoInMeasure_const`, `continuous_comp_prodMk_of_tendstoInMeasure_const` |
| Continuous Mapping Theorem (in distribution) | `Mathlib/MeasureTheory/Function/ConvergenceInDistribution.lean` | `TendstoInDistribution.continuous_comp` |
| Strong Law of Large Numbers (real & Banach-valued, iid) | `Mathlib/Probability/StrongLaw.lean` | `strong_law_ae`, `strong_law_Lp` |
| Univariate Lindeberg-Lévy CLT | `Mathlib/Probability/CentralLimitTheorem.lean` | `tendstoInDistribution_inv_sqrt_mul_sum_sub` |
| Real Gaussian | `Mathlib/Probability/Distributions/Gaussian/Real.lean` | `gaussianReal m v` |
| Multivariate Gaussian | `Mathlib/Probability/Distributions/Gaussian/Multivariate.lean` | `multivariateGaussian μ S`, `stdGaussian E` |
| `HasGaussianLaw` predicate | `Mathlib/Probability/Distributions/Gaussian/HasGaussianLaw/Def.lean` | `HasGaussianLaw X P`, `IsGaussian` |
| Gaussian uncorrelated ⇒ independent | `Mathlib/Probability/Distributions/Gaussian/HasGaussianLaw/Independence.lean` | `ProbabilityTheory.HasGaussianLaw.indepFun_of_covariance_eq_zero`, `iIndepFun_of_covariance_eq_zero` |
| Gamma distribution | `Mathlib/Probability/Distributions/Gamma.lean` | `gammaMeasure a r` |

Caveats worth noting:

- `TendstoInDistribution` requires the image space to be `OpensMeasurableSpace`.
- Slutsky requires `IsCountablyGenerated` on the filter and same underlying probability space.
- `multivariateGaussian` is parameterized over `EuclideanSpace ℝ ι` for finite `ι`; covariance must be PSD.
- The Gaussian independence lemma uses `covarianceBilinDual` (an abstract bilinear-form formulation); applying it to concrete linear maps `A`, `B` will require translating to a matrix-form statement.

## What's missing (must build or wrap)

1. **Weak Law of Large Numbers** — only the strong law is in Mathlib. Trivial wrap (a.s. convergence ⇒ convergence in measure).
2. **Named χ²(k) distribution** — only `gammaMeasure` is present. χ²(k) = Γ(k/2, 1/2). Define a wrapper plus the basic API (mean, variance, support).
3. **Multivariate Lindeberg-Lévy CLT** — only the univariate version is in Mathlib. Cleanest port: Cramér-Wold reduction (every linear projection converges in distribution ⇒ joint converges).
4. **Delta Method** — not present as a named theorem. Straightforward via CMT + Fréchet derivative; not blocking until late Ch 7.
5. **Quadratic form of standard normal under symmetric idempotent → χ²(rank)** — not present. **Load-bearing missing piece for Chapter 5.** Construction: spectral decomposition of `M` (eigenvalues 0 / 1, `M = U diag(1,…,1,0,…,0) Uᵀ`), giving `eᵀ M e = ∑_{i ≤ r} (Uᵀe)_iˆ²`, a sum of `r` iid standard normal squares = χ²(r). Needs χ²(k) defined first, plus the additivity / sum-of-squares lemmas (Gamma additivity is likely already in Mathlib — worth a quick confirm).

## Proposed order of attack

1. Define `chiSquared k` as a `gammaMeasure` wrapper + minimal API.
2. Prove (or import) sum-of-squares-of-standard-normals = χ²(k).
3. Prove the symmetric-idempotent quadratic-form theorem (uses our existing `rank_eq_natCast_trace_of_isHermitian_idempotent`).
4. Finish Chapter 5: chi-square law for `s²` (1–3 above), independence of `β̂` and `s²` (almost free given Mathlib's Gaussian-independence lemma — main work is setting up the joint-Gaussian structure for `(Pe, Me)`), exact t, CIs / tests.
5. Asymptotics wrappers in this order: WLLN (trivial), multivariate CLT (Cramér-Wold), delta method (later, only when Ch 7 functional-of-parameters needs it).
6. Begin Chapter 7 with the iid-sample bridge that lifts our matrix-formulation OLS to a sample-size-indexed sequence.
