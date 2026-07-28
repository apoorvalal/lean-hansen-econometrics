import HansenEconometrics.Chapter11MultivariateRegression.Systems
import HansenEconometrics.Chapter11MultivariateRegression.Asymptotics
import HansenEconometrics.Chapter11MultivariateRegression.SUR
import HansenEconometrics.Chapter11MultivariateRegression.ReducedRank
import HansenEconometrics.Chapter11MultivariateRegression.ReducedRankJointSpectrum
import HansenEconometrics.Chapter11MultivariateRegression.ReducedRankLikelihood
import HansenEconometrics.Chapter11MultivariateRegression.PCA
import HansenEconometrics.Chapter11MultivariateRegression.FactorModels
import HansenEconometrics.Chapter11MultivariateRegression.MatrixNormal

/-!
# Chapter 11 — Multivariate Regression

This compatibility module re-exports the current Chapter 11
multivariate-regression support layer.

The development is split by textbook topic:

* `Systems`: stacked system least squares, residuals, common-regressor block
  moments, and system/delta covariance formulas.
* `Asymptotics`: Chapter 7/8 stacked-system Gaussian-limit wrappers, exact
  system moment WLLNs, feasible-middle perturbation routes, sandwich CMT
  assembly, and covariance-consistency interfaces for the Theorems 11.1--11.3
  route.
* `SUR`: seemingly unrelated regression variance definitions and support
  bridges for Theorems 11.4--11.6.
* `ReducedRank`: generalized-eigenvector predicates, reduced-rank formula and
  spectral certificates, and `A⊥` residual-pencil support for Theorem 11.7.
* `ReducedRankJointSpectrum`: tie-safe simultaneous construction of the primal
  and complementary residual-pencil blocks for Theorem 11.7.
* `ReducedRankLikelihood`: raw Gaussian likelihood, exact-rank admissibility,
  and an actual global MLE predicate kept distinct from the formula certificate.
* `PCA` and `FactorModels`: principal components, factor-model PC estimators,
  concrete sample-covariance/eigenspace support, and Assumption 11.1-facing
  support lemmas for Theorems 11.8--11.9.
* `MatrixNormal`: matrix-normal, Wishart, inverse-Wishart, and Hotelling
  distribution notation and law-map bridges for Theorems 11.10--11.12.

The theorem-by-theorem crosswalk and completeness notes live in
`inventory/ch11-inventory.md`.
-/
