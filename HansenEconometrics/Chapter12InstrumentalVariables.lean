import HansenEconometrics.Chapter12InstrumentalVariables.Asymptotics
import HansenEconometrics.Chapter12InstrumentalVariables.Tests
import HansenEconometrics.Chapter12InstrumentalVariables.FiniteSample
import HansenEconometrics.Chapter12InstrumentalVariables.Bootstrap
import HansenEconometrics.Chapter12InstrumentalVariables.GeneratedRegressors
import HansenEconometrics.Chapter12InstrumentalVariables.ControlFunction
import HansenEconometrics.Chapter12InstrumentalVariables.LATE
import HansenEconometrics.Chapter12InstrumentalVariables.WeakMany

/-!
# Chapter 12 - Instrumental Variables

This compatibility module re-exports the current Chapter 12
instrumental-variables support layer:

* `Basic` contains deterministic IV, 2SLS, k-class/LIML, split-sample IV, JIVE,
  Wald IV, first-stage, and variance notation.
* `Asymptotics` contains convergence interfaces and projection lemmas for the
  Theorems 12.1--12.5 route.
* `Tests` contains Wald, endogeneity, overidentification, and subset-test
  notation plus the exact algebraic Theorem 12.17 bridge.
* `FiniteSample`, `Bootstrap`, `GeneratedRegressors`, and `ControlFunction`
  record support interfaces for Theorems 12.7--12.13.
* `LATE` records the Assumption 12.3 and Wald-ratio surface.
* `WeakMany` contains weak- and many-instrument support interfaces for
  Theorems 12.18--12.19.

The theorem-by-theorem crosswalk and completeness notes live in
`inventory/ch12-inventory.md`.
-/
