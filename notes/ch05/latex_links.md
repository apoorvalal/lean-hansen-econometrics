# Chapter 5 crosswalk

## Conventions
- Relative links only.
- Leave textbook theorem rows blank when the chapter-facing theorem is not formalized yet.
- Record reusable non-textbook bridge results in a separate section.

## Links
- Inventory: [inventory.md](./inventory.md)
- Excerpt: [ch5_excerpt.txt](./ch5_excerpt.txt)
- Lean file: [../../HansenEconometrics/Chapter5NormalRegression.lean](../../HansenEconometrics/Chapter5NormalRegression.lean)

## Textbook crosswalk

| Textbook statement | LaTeX / excerpt | Lean theorem | Notes |
| --- | --- | --- | --- |
| Theorem 5.7: `((n-k)s^2)/σ^2 ∼ χ^2_{n-k}` and independent of `β̂` | `Theorem 5.7 In the normal regression model, (n − k) s2 / σ2 ∼ χ2_{n−k} and is independent of β̂.` | `scaledOlsResidualVarianceStatistic_hasLaw_chiSquared`, `olsBeta_indep_scaledOlsResidualVarianceStatistic` | Formalized as separate distribution and independence theorems. |
| Theorem 5.8: `T ∼ t_{n-k}` | `Theorem 5.8 In the normal regression model, T ∼ t_{n−k}.` | `olsTStatistic_hasLaw_classicalStudentT` | Formalized through reusable numerator and studentization-factor bridge theorems. The standalone ratio-law `studentT` is bridged to the density-backed `classicalStudentT` in `HansenEconometrics/StudentT.lean`. |
| Theorem 5.9: exact CI for `β` | `Theorem 5.9 In the normal regression model, (5.8) with c = F −1(1 − α/2) ...` | `olsConfidenceInterval_coverage_eq_classicalStudentT_interval`, `olsConfidenceInterval_coverage_eq_classicalStudentT_cdf`, `olsConfidenceInterval_coverage_eq_one_sub_classical` | Formalized at the confidence-interval level, with `ae_mem_olsConfidenceInterval_iff_abs_t_le` bridging the textbook interval event to the `|T| ≤ c` event. The public wrappers now target the classical density-backed Student-`t` law. The literal inverse-cdf packaging is still thinner than Hansen's prose because we have not introduced a dedicated quantile API. |
| Theorem 5.10: large-`n` normal CI for `β` | `Theorem 5.10 In the normal regression model, if n − k ≥ 61 ...` | `olsConfidenceInterval_two_se_coverage_ge_nineteen_twentieths` | Formalized as the textbook two-standard-error interval coverage bound `19/20 ≤ P(β_j ∈ Ĉ_j)`. The numerical input is the standalone Student-`t` bound `classicalStudentT_Icc_neg_two_two_ge_nineteen_twentieths`, proved in `HansenEconometrics/StudentT.lean`. |
| Theorem 5.11: CI for `σ^2` | `Theorem 5.11 In the normal regression model (5.12) has coverage probability ...` | `olsVarianceConfidenceInterval_coverage_eq_chiSquared_interval`, `olsVarianceConfidenceInterval_coverage_eq_chiSquared_cdf`, `olsVarianceConfidenceInterval_coverage_eq_one_sub` | Formalized as the exact chi-square interval identity, a cdf version, and a critical-value wrapper. |
| Theorem 5.12: t test | `Theorem 5.12 In the normal regression model if the null hypothesis (5.13) ...` | `olsNullTStatistic_hasLaw_classicalStudentT`, `olsTTest_rejection_probability_eq_alpha` | Formalized in explicit null-hypothesis language: the literal null-centered t-statistic has the classical Student-`t` law under `H₀`, and the two-sided rejection rule has exact size `α` when calibrated by the classical Student-`t` tail probabilities. |
| Theorem 5.13: likelihood-ratio / F test result | `Theorem 5.13 In the normal regression model if the null hypothesis (5.16) ...` | `olsFStatistic_hasLaw_classicalFDist`, `olsFStatistic_rejection_probability_eq_alpha_classical` | Formalized as the exact `F_{q,n-k}` law for the classical block F statistic plus the upper-tail critical-value rejection theorem. |

## Lean-only bridge results

| Lean result | Role |
| --- | --- |
| `scaledOlsResidualVarianceStatistic` | Packages Hansen’s `(n-k)s^2/σ^2` statistic as a reusable random variable. |
| `residual_quadratic_form_of_linear_model` | Rewrites the residual sum of squares as the annihilator quadratic form `e'Me`. |
| `olsResidualVarianceEstimator_linear_model_quadratic_form` | Rewrites `s^2` directly in terms of `e'Me`. |
| `residual_quadratic_form_eq_sum_sq_eigenvector_coords` | Diagonalizes `e'Me` into a sum of squares on the `1`-eigenspace of the annihilator matrix. |
| `scaledOlsResidualVarianceStatistic_eq_sum_sq_eigenvector_coords` | Rewrites Hansen’s `(n-k)s^2/σ^2` statistic as a sum of squared standardized eigencoordinates. |
| `scaledOlsResidualVarianceStatistic_eq_residual_norm_sq_div` | Rewrites Hansen’s statistic as the residual norm squared divided by `σ^2`, which is the measurable bridge used in the independence proof. |
| `standardizedOlsBetaCoordinate_hasLaw_standardNormal` | Packages the exact Gaussian numerator in Hansen’s `t`-statistic. |
| `olsStudentizationFactor_hasLaw` | Packages the inverse square-root transform of the chi-square statistic that appears in the Studentization step. |
| `studentT_eq_classicalStudentT` | Bridges the ratio-law definition of Student’s `t` to the classical density-backed distribution in `HansenEconometrics/StudentT.lean`. |
| `classicalStudentT_Icc_neg_two_two_ge_nineteen_twentieths` | Supplies the standalone `[-2,2]` Student-`t` central-mass lower bound used in Theorem 5.10. |
| `sigma2_mem_olsVarianceConfidenceInterval_iff_scaledStatistic_mem_Icc` | Rewrites variance-interval coverage events into the chi-square event used in Theorem 5.11. |
| `fTestProjectionMatrix` | Packages the difference between restricted and unrestricted hat matrices as the projection driving the F-statistic numerator. |
| `scaledOlsFNumeratorStatistic_hasLaw_chiSquared` | Identifies the restricted-unrestricted RSS gap divided by `σ^2` as a `χ^2_q` random variable. |
| `scaledOlsFNumeratorStatistic_indep_scaledOlsResidualVarianceStatistic` | Supplies the independence between the F-statistic numerator and denominator chi-square pieces. |
