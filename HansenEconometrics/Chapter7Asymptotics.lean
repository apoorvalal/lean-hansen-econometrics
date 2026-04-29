import HansenEconometrics.Chapter7Asymptotics.Basic
import HansenEconometrics.Chapter7Asymptotics.Consistency
import HansenEconometrics.Chapter7Asymptotics.SampleMiddle
import HansenEconometrics.Chapter7Asymptotics.MiddleConsistency
import HansenEconometrics.Chapter7Asymptotics.SandwichAssembly
import HansenEconometrics.Chapter7Asymptotics.Normality
import HansenEconometrics.Chapter7Asymptotics.Inference

/-!
# Chapter 7 — Asymptotic Theory

This umbrella import is the stable public entry point for Hansen's Chapter 7
formalization. Detailed theorem-by-theorem status, crosswalk notes, and known
follow-up items live in `inventory/ch7-inventory.md`.

The implementation is split into seven chapter-local modules:

* `Basic` — finite-sample OLS definitions, totalized estimators, stacking
  notation, and deterministic algebra.
* `Consistency` — LLN/sample-moment consistency, OLS consistency, residual
  variance consistency, and homoskedastic plug-in covariance consistency.
* `SampleMiddle` — score covariance / homoskedastic identity, HC0–HC3
  sample middle-matrix definitions, and the `leverageStar` family.
* `MiddleConsistency` — measurability, leverage bounds, residual-score
  expansion algebra, `RobustCovarianceConsistencyConditions`, and WLLN
  consistency of HC0–HC3 middle matrices.
* `SandwichAssembly` — `heteroAsymCov`, sandwich CMT, distribution bridges,
  and the OLS HC0/HC1/HC2/HC3 sandwich estimators with their convergence theorems.
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
