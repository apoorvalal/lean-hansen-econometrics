import HansenEconometrics.Chapter10Bootstrap.FiniteReplication
import HansenEconometrics.Chapter10Bootstrap.HigherOrder

/-!
# Chapter 10 — Resampling Methods

This compatibility module re-exports the Chapter 10 resampling formalization.
The development is split by proof layer and textbook topic:

* `Empirical`: finite empirical distributions, jackknife identities, bootstrap
  inclusion probabilities, and exact finite-resampling moments.
* `WLLN`: bootstrap convergence in probability, Marcinkiewicz WLLN support, and
  fixed/indexed bootstrap WLLN wrappers.
* `Distribution` and `WeakDistribution`: bootstrap CDF convergence,
  bounded-continuous weak convergence, event/CDF bridges, and CLT-facing routes.
* `DeltaMethod`: bootstrap continuous mapping and delta-method wrappers.
* `Variance` and `Covariance`: bootstrap variance, covariance, trimming, tail,
  and smooth-function consistency routes.
* `Studentization` and `Regression`: studentized statistics and finite OLS
  bootstrap regression wrappers.
* `FiniteReplication`: finite simulation variance/covariance estimators and
  their consistency transfers.
* `Quantiles`, `Percentile`, and `PercentileT`: lower-quantile convergence,
  percentile intervals, bias-corrected interval definitions, and percentile-`t`
  coverage.
* `Tests` and `HigherOrder`: bootstrap tests and Edgeworth-style second-order
  refinement bridges.

The theorem-by-theorem crosswalk and completeness notes live in
`inventory/ch10-inventory.md`.
-/
