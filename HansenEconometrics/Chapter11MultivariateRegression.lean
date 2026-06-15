import HansenEconometrics.Chapter11MultivariateRegression.SUR
import HansenEconometrics.Chapter11MultivariateRegression.ReducedRank
import HansenEconometrics.Chapter11MultivariateRegression.FactorModels
import HansenEconometrics.Chapter11MultivariateRegression.MatrixNormal

/-!
# Chapter 11 — Multivariate Regression

This compatibility module re-exports the Chapter 11 multivariate-regression
formalization.

The development is split by textbook topic:

* `Systems`: stacked system least squares, residuals, common-regressor block
  moments, and system/delta covariance formulas.
* `Asymptotics`: theorem-facing wrappers for Theorems 11.1--11.3 over the
  reusable Chapter 7/8 Gaussian-limit and covariance-consistency interfaces.
* `SUR`: seemingly unrelated regression variance, efficiency, and feasible
  covariance wrappers for Theorems 11.4--11.6.
* `ReducedRank`: reduced-rank MLE characterization for Theorem 11.7.
* `PCA` and `FactorModels`: principal components, factor-model PC estimators,
  and Assumption 11.1-facing consequences for Theorems 11.8--11.9.
* `MatrixNormal`: matrix-normal, Wishart, inverse-Wishart, and Hotelling
  distribution wrappers for Theorems 11.10--11.12.

The theorem-by-theorem crosswalk and completeness notes live in
`inventory/ch11-inventory.md`.
-/
