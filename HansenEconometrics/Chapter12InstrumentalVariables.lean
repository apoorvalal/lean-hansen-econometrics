import HansenEconometrics.Chapter12InstrumentalVariables.Basic
import HansenEconometrics.Chapter12InstrumentalVariables.Asymptotics
import HansenEconometrics.Chapter12InstrumentalVariables.Bootstrap
import HansenEconometrics.Chapter12InstrumentalVariables.ControlFunction
import HansenEconometrics.Chapter12InstrumentalVariables.Functions
import HansenEconometrics.Chapter12InstrumentalVariables.GeneratedRegressors
import HansenEconometrics.Chapter12InstrumentalVariables.Kinal
import HansenEconometrics.Chapter12InstrumentalVariables.LATE
import HansenEconometrics.Chapter12InstrumentalVariables.LIML
import HansenEconometrics.Chapter12InstrumentalVariables.ManyInstruments
import HansenEconometrics.Chapter12InstrumentalVariables.Overidentification
import HansenEconometrics.Chapter12InstrumentalVariables.Tests
import HansenEconometrics.Chapter12InstrumentalVariables.WeakMany
import HansenEconometrics.Chapter12InstrumentalVariables.WeakInstruments

/-!
# Chapter 12 — Instrumental Variables

This compatibility module re-exports the current Chapter 12 instrumental-
variables support layer.

The development starts with deterministic IV/2SLS estimator algebra:

* `Basic`: instrument projections, reduced-form fitted regressors, IV and 2SLS
  definitions, Hansen equations (12.29)--(12.31), the fitted-regressor
  representation, and the structural-error decomposition (12.39).
* `Asymptotics`: proof-facing 2SLS consistency and asymptotic-normality
  interfaces for Theorems 12.1--12.2, keeping the rectangular IV score and
  Hansen covariance formulas explicit.
* `Functions`: nonlinear functions of 2SLS parameters and Wald-test notation
  for Theorems 12.4--12.6.
* `Kinal`: deterministic fitted-regressor/FWL bridges and condition surfaces
  for the Kinal finite-sample moment-threshold theorem, Theorem 12.7.
* `Bootstrap`: finite-resample bootstrap 2SLS notation, recentered score
  algebra, and the proof-facing interface for Theorem 12.8.
* `GeneratedRegressors`: generated-regressor notation, proof-facing
  null/Wald, least-squares first-stage, and expectation-error interfaces for
  Theorems 12.9--12.15, plus exact fixed-design normal wrappers for
  Theorems 12.10 and 12.15.
* `Overidentification`: Sargan, Newey subset, and Sargan-difference statistic
  surfaces for Theorems 12.16--12.17.
* `LIML`, `WeakInstruments`, and `ManyInstruments`: LIML notation plus the
  weak- and many-instrument theorem surfaces for Theorems 12.18--12.19.
* `ControlFunction`, `LATE`, `Tests`, and `WeakMany`: thin
  compatibility and chapter-support surfaces retained from the initial
  Chapter 12 API; the modules above remain canonical for numbered theorems.

The theorem-by-theorem crosswalk and completeness notes live in
`inventory/ch12-inventory.md`.
-/
