import HansenEconometrics.Chapter7Asymptotics.Basic
import HansenEconometrics.Chapter7Asymptotics.Consistency
import HansenEconometrics.Chapter7Asymptotics.RobustCovariance
import HansenEconometrics.Chapter7Asymptotics.Normality
import HansenEconometrics.Chapter7Asymptotics.Inference

/-!
# Chapter 7 — Asymptotic Theory

This umbrella import is the stable public entry point for Hansen's Chapter 7
formalization. Detailed theorem-by-theorem status, crosswalk notes, and known
follow-up items live in `inventory/ch7-inventory.md`.

The implementation is split into five chapter-local modules:

* `Basic` — finite-sample OLS definitions, totalized estimators, stacking
  notation, and deterministic algebra.
* `Consistency` — LLN/sample-moment consistency, OLS consistency, residual
  variance consistency, and homoskedastic plug-in covariance consistency.
* `RobustCovariance` — score covariance, homoskedasticity, HC0/HC1/HC2/HC3
  middle matrices, leverage adjustments, and robust covariance consistency.
* `Normality` — scalar/vector CLT packaging, Gaussian linear-map bridges,
  Wald statistic bridges, and chi-square law identification.
* `Inference` — scalar t-statistics, confidence intervals, one-degree Wald
  statistics, and projection-family inference wrappers.

## Public Surface

The chapter-facing endpoints now advertise descriptive sufficient-condition
structures:

* `LeastSquaresConsistencyConditions`
* `ErrorVarianceConsistencyConditions`
* `ScoreCLTConditions`
* `RobustCovarianceConsistencyConditions`
* `HomoskedasticErrorVariance`

Chapter 7 uses `olsBetaStar` as the total proof engine. `olsBetaOrZero` is the
ordinary-OLS wrapper used by the textbook crosswalk when a statement is about
ordinary OLS on nonsingular samples. Detailed theorem mappings and remaining
gaps are maintained in `inventory/ch7-inventory.md`.
-/
