# lean-hansen-econometrics

A gradual Lean formalization project for Bruce E. Hansen's *Econometrics*.

This repo is not meant to be a one-shot dump of isolated theorem files. The goal is to work through the book chapter by chapter, formalizing the core mathematical results, building reusable dependencies, and keeping a visible progress map.

## Scope

Primary source text:
- `HansenEconometrics.pdf` in the surrounding Hansen doodle project

Current emphasis:
- Chapter 2 (`Conditional Expectation and Projection`)
- Chapter 3 (`The Algebra of Least Squares`) OLS / projection algebra and FWL scaffolding

Longer-run goal:
- formalize as much of the book as is realistic, starting from probability / conditional expectation / projection foundations and moving outward toward asymptotics, least squares, testing, IV, GMM, time series, panel data, and beyond.

## Strategy

The intended workflow is:

1. extract and split the source PDF by chapter,
2. inventory theorem/lemma/corollary candidates,
3. identify the dependency graph,
4. formalize the lowest-level reusable results first,
5. commit frequently as each theorem cluster turns green.

In practice this means we will often restate Hansen’s results in more Lean-native language:
- sigma-algebras instead of only pointwise `E[Y | X = x]` notation,
- almost-everywhere equality where that is mathematically correct,
- projection and orthogonality statements in forms that line up with Mathlib.

## Repository structure

- `HansenEconometrics/` — Lean source files
- `notes/` — theorem inventories / progress notes
- `HansenEconometrics.lean` — root imports
- `lakefile.toml`, `lake-manifest.json`, `lean-toolchain` — Lean project config

## Chapter progress

Legend:
- `not started`
- `in progress`
- `partial`
- `done`

| ch | title | status | notes |
|---:|---|---|---|
| 01 | Introduction | not started | text extracted and inventoried; mostly exposition |
| 02 | Conditional Expectation and Projection | partial | conditional expectation, variance, and linear projection algebra completed |
| 03 | The Algebra of Least Squares | partial | OLS algebra + projection/annihilator/FWL coefficient and residual core landed |
| 04 | Least Squares Regression | partial | OLS/GLS algebra, unbiasedness, covariance identities, and Gauss-Markov lower bounds landed; HC2/HC3 and clustered SEs deferred |
| 05 | Normal Regression | inventoried | next target: finite-sample normal-model distributions and classical inference |
| 06 | A Review of Large Sample Asymptotics | inventoried | likely prerequisite for later asymptotics chapters |
| 07 | Asymptotic Theory for Least Squares | inventoried | consistency / asymptotic normality targets |
| 08 | Restricted Estimation | inventoried | constrained estimation / minimum distance |
| 09 | Hypothesis Testing | inventoried | Wald / LM / LR style results |
| 10 | Resampling Methods | inventoried | bootstrap / jackknife |
| 11 | Multivariate Regression | inventoried | |
| 12 | Instrumental Variables | inventoried | |
| 13 | Generalized Method of Moments | inventoried | |
| 14 | Time Series | inventoried | |
| 15 | Multivariate Time Series | inventoried | |
| 16 | Non-Stationary Time Series | inventoried | |
| 17 | Panel Data | inventoried | |
| 18 | Difference in Differences | inventoried | |
| 19 | Nonparametric Regression | inventoried | |
| 20 | Series Regression | inventoried | |
| 21 | Regression Discontinuity | inventoried | |
| 22 | M-Estimators | inventoried | |
| 23 | Nonlinear Least Squares | inventoried | |
| 24 | Quantile Regression | inventoried | |
| 25 | Binary Choice | inventoried | |
| 26 | Multiple Choice | inventoried | |
| 27 | Censoring and Selection | inventoried | |
| 28 | Model Selection, Stein Shrinkage, and Model Averaging | inventoried | |
| 29 | Machine Learning | inventoried | |

## Current Chapter 2 progress

Completed in `HansenEconometrics/Chapter2CondExp.lean`,
`HansenEconometrics/Chapter2Variance.lean`, and `HansenEconometrics/Chapter2LinearProjection.lean`:
- simple law of iterated expectations
- tower property for nested sigma-algebras
- tower property in the `X₁, X₂` then `X₁` form
- conditioning / pull-out theorem
- CEF error has conditional mean zero
- CEF error has unconditional mean zero
- orthogonality of CEF error to measurable functions
- integral conditional variance = integral squared CEF error
- law of total variance
- rearranged variance decomposition
- variance of the conditional expectation bounded by total variance
- Definition 2.5 / Theorem 2.9 linear projection coefficient algebra
- population normal equations and orthogonality for the best linear projection
- uniqueness from the population normal equations
- quadratic projection criterion simplification at the projection coefficient

Planned next within Chapter 2:
- full Theorem 2.6 residual-variance monotonicity for nested conditioning sets
- conditional expectation as best predictor
- full best-linear-predictor minimization statement
- later chapter 2 identification / existence statements where worthwhile

## Current Chapter 3 progress

Completed in `HansenEconometrics/Chapter3LeastSquaresAlgebra.lean`,
`HansenEconometrics/Chapter3Projections.lean`, and `HansenEconometrics/Chapter3FWL.lean`:
- SSE objective notation and its residual-sum-of-squares specialization at `β̂`
- Theorem 3.2 matrix expressions: closed-form OLS, residuals, and normal equations
- normal-equation uniqueness for closed-form OLS
- residuals sum to zero when a constant is in the regressor column span
- projection / hat matrix definition and `P X = X`
- Theorem 3.3.1-3: `P` symmetric/idempotent and `tr(P) = k`
- annihilator matrix definition, `M X = 0`, `M Y = ê`, `M` symmetric/idempotent, and `tr(M) = n-k`
- range projection facts and `M P = P M = 0`
- fitted/residual orthogonality and the dot-product Pythagorean decomposition
- FWL: partitioned normal equations, residualized regressors `M₁ X₂`, the sequential residual-maker
  identity, the coefficient identity, and residual equivalence

Planned next within Chapter 3:
- Theorem 3.4 partitioned coefficient formulae
- rank/eigenvalue parts of Theorem 3.3
- centered analysis-of-variance / `R²` identities

See also:
- `notes/ch02/theorem_inventory.md`
- `notes/ch02/ch2_excerpt.txt`
- `notes/ch03/inventory.md`
- `notes/ch03/ch3_excerpt.txt`
- `notes/ch04/inventory.md`
- `notes/ch04/ch4_excerpt.txt`

## Current Chapter 4 progress

Completed in `HansenEconometrics/Chapter4LeastSquaresRegression.lean`:
- Hansen equation (4.6): `β̂ = β + (Xᵀ X)⁻¹ Xᵀ e`
- the orthogonal-error specialization `Xᵀ e = 0 -> β̂ = β`
- fitted values as signal plus projected error
- residuals as the annihilator applied to the model error
- conditional and unconditional unbiasedness bridges
- conditional covariance identity and its homoskedastic specialization
- classical Gauss-Markov lower bound
- GLS algebra and the generalized Gauss-Markov weighted lower bound
- HC0 / White and HC1 covariance estimators

Explicitly deferred for now within Chapter 4:
- residual variance estimators
- HC2 / HC3
- clustered covariance estimators

Next target after Chapter 4:
- Chapter 5 normal-model finite-sample distribution theory and classical inference results

## Philosophy

The point is not to force Hansen’s prose into Lean line by line. The point is to build a usable formal skeleton of the mathematics behind the book.

That means:
- proving reusable infrastructure first,
- preferring mathematically canonical formulations,
- and being honest about what is already in Mathlib versus what we are adding on top.
