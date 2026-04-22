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
| Theorem 5.7: `((n-k)s^2)/σ^2 ∼ χ^2_{n-k}` and independent of `β̂` | `Theorem 5.7 In the normal regression model, (n − k) s2 / σ2 ∼ χ2_{n−k} and is independent of β̂.` |  | Deterministic diagonalization scaffolding is formalized, but the chapter-facing distribution theorem is not landed yet. |
| Theorem 5.8: `T ∼ t_{n-k}` | `Theorem 5.8 In the normal regression model, T ∼ t_{n−k}.` |  | Pending the exact chi-square and independence ingredients from Theorem 5.7. |
| Theorem 5.9: exact CI for `β` | `Theorem 5.9 In the normal regression model, (5.8) with c = F −1(1 − α/2) ...` |  | Pending Theorem 5.8. |
| Theorem 5.10: large-`n` normal CI for `β` | `Theorem 5.10 In the normal regression model, if n − k ≥ 61 ...` |  | Pending. |
| Theorem 5.11: CI for `σ^2` | `Theorem 5.11 In the normal regression model (5.12) has coverage probability ...` |  | Pending Theorem 5.7. |
| Theorem 5.12: t test | `Theorem 5.12 In the normal regression model if the null hypothesis (5.13) ...` |  | Pending Theorem 5.8. |
| Theorem 5.13: likelihood-ratio / F test result | `Theorem 5.13 In the normal regression model if the null hypothesis (5.16) ...` |  | Pending. |

## Lean-only bridge results

| Lean result | Role |
| --- | --- |
| `scaledOlsResidualVarianceStatistic` | Packages Hansen’s `(n-k)s^2/σ^2` statistic as a reusable random variable. |
| `residual_quadratic_form_of_linear_model` | Rewrites the residual sum of squares as the annihilator quadratic form `e'Me`. |
| `olsResidualVarianceEstimator_linear_model_quadratic_form` | Rewrites `s^2` directly in terms of `e'Me`. |
| `residual_quadratic_form_eq_sum_sq_eigenvector_coords` | Diagonalizes `e'Me` into a sum of squares on the `1`-eigenspace of the annihilator matrix. |
