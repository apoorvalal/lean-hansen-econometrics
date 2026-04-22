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
- reusable random-variable conditioning helpers in `HansenEconometrics/ProbabilityUtils.lean`,
- variable-based wrappers for chapter-facing probability statements in the chapter files,
- sigma-algebras in the backend support layer when that matches Mathlib,
- almost-everywhere equality where that is mathematically correct,
- projection and orthogonality statements in forms that line up with Mathlib.

## Repository structure

- `HansenEconometrics/` — Lean source files
- `textbook/` — chapter excerpts and chapter-local redirect notes
- `inventory/` — canonical chapter inventories and crosswalks
- `AGENTS.md` — repo style guide for contributors and coding agents
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
| 03 | The Algebra of Least Squares | partial | OLS algebra + projection/annihilator (incl. rank) / FWL coefficient and residual core landed |
| 04 | Least Squares Regression | partial | OLS/GLS algebra, unbiasedness, covariance identities, and Gauss-Markov lower bounds landed; HC2/HC3 and clustered SEs deferred |
| 05 | Normal Regression | partial | normal-model scaffolding, chi-square distribution wrapper, Gaussian laws for `β̂` and residuals, and residual-quadratic-form setup for `s²` landed |
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
`HansenEconometrics/Chapter2Variance.lean`,
`HansenEconometrics/ProbabilityUtils.lean`,
and `HansenEconometrics/Chapter2LinearProjection.lean`:
- reusable helper definitions `conditioningSpace`, `XMeasurable`, `condExpOn`, `cefErrorOn`,
  `condVarOn`, and `residualVarOn`
- coordinatewise conditional-expectation / integral bridge lemmas for finite-dimensional random
  vectors and arrays
- simple law of iterated expectations
- tower property for nested sigma-algebras
- tower property in variable-facing form in `Chapter2CondExp.lean`
- conditioning / pull-out theorem in variable-facing form in `Chapter2CondExp.lean`
- CEF error has conditional mean zero in `Chapter2CondExp.lean`
- CEF error has unconditional mean zero in `Chapter2CondExp.lean`
- orthogonality of CEF error to measurable functions of `X` in `Chapter2CondExp.lean`
- integral conditional variance = integral squared CEF error
- Theorem 2.5: CEF error has finite second moment when `Y ∈ L²`
- law of total variance in sigma-algebra and variable-facing form
- rearranged variance decomposition
- variance of the conditional expectation bounded by total variance
- Theorem 2.6: residual-variance monotonicity for richer conditioning information
- Definition 2.5 / Theorem 2.9 linear projection coefficient algebra
- population normal equations and orthogonality for the best linear projection
- uniqueness from the population normal equations
- quadratic projection criterion simplification at the projection coefficient

Planned next within Chapter 2:
- additional best-linear-predictor corollaries beyond the current conditional-mean result
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
- general lemma: rank of a real symmetric idempotent matrix equals its trace
- Theorem 3.3 rank parts: `rank(P) = k` and `rank(M) = n - k`
- range projection facts and `M P = P M = 0`
- fitted/residual orthogonality and the dot-product Pythagorean decomposition
- FWL: partitioned normal equations, residualized regressors `M₁ X₂`, the sequential residual-maker
  identity, the coefficient identity, and residual equivalence

Planned next within Chapter 3:
- Theorem 3.4 partitioned coefficient formulae
- centered analysis-of-variance / `R²` identities

See also:
- `inventory/ch2-inventory.md`
- `textbook/ch02/latex_links.md`
- `textbook/ch02/ch2_excerpt.txt`
- `inventory/ch3-inventory.md`
- `textbook/ch03/ch3_excerpt.txt`
- `inventory/ch4-inventory.md`
- `textbook/ch04/ch4_excerpt.txt`

## Current Chapter 5 progress

Completed in `HansenEconometrics/Chapter5NormalRegression.lean`:
- finite-sample residual variance estimator definition
- deterministic linear-model rewrite of `s²` in terms of the model error
- Gaussian law for the OLS coefficient vector as an affine image of the error vector
- Gaussian law for the OLS residual vector as a linear image of the error vector
- residual sum of squares rewritten as the annihilator quadratic form `e'Me`
- `s²` rewritten as `e'Me / (n-k)`, which is the deterministic setup for the chi-square step

Completed in `HansenEconometrics/ChiSquared.lean`:
- chi-square distribution defined as a Gamma distribution with shape `k/2` and rate `1/2`
- basic probability-measure instance for positive degrees of freedom
- negative-support vanishing lemma inherited from the Gamma density

Planned next within Chapter 5:
- connect the residual quadratic form to the new chi-square distribution definition
- prove the key independence statements between `β̂` and residual quadratic forms / `s²`
- derive the exact t-statistic law
- package confidence intervals and classical tests as corollaries

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
- keeping public APIs close to the variable-based notation that applied econometricians expect,
- preferring mathematically canonical formulations,
- and being honest about what is already in Mathlib versus what we are adding on top.
