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

## CI and local linting

Every pull request is gated by `.github/workflows/ci.yml`, which runs:

```sh
lake build
lake build @mathlib/lint-style
lake env .lake/packages/mathlib/.lake/build/bin/lint-style --github HansenEconometrics
```

The first command builds the project. The final two commands build and run
Mathlib's text-style linter against the root `HansenEconometrics` module, so
style lints gate the PR alongside the build. The repository already enables
`weak.linter.mathlibStandardSet = true` in `lakefile.toml`, so Lean's
elaboration linters run during builds; existing warnings currently keep the CI
from using `lake build --wfail` as a hard gate.

For a local pre-push check, run the same commands without `--github` for more
readable output:

```sh
lake build
lake build @mathlib/lint-style
lake env .lake/packages/mathlib/.lake/build/bin/lint-style HansenEconometrics
```

A separate `.github/workflows/full-build-tags.yml` workflow runs a full
`lake build` only for selected tag patterns (`full-build-*` and `release-*`) or
manual dispatch. This is feasible for expensive validation runs because it
avoids charging every PR/push twice while still allowing release-style tags to
request a full clean CI build with Lean/Mathlib cache support. Once the current
Lean warnings are cleaned up, that workflow can be tightened to
`lake build --wfail`.

## Chapter progress

Legend:
- `not started`
- `in progress`
- `partial`
- `done`

| ch | title | status | notes |
|---:|---|---|---|
| 01 | Introduction | not started | text extracted and inventoried; mostly exposition |
| 02 | Conditional Expectation and Projection | partial | conditional expectation, variance, linear projection algebra, and variable-facing potential-outcomes/CIA CATE plus observed-regression wrappers completed |
| 03 | The Algebra of Least Squares | partial | OLS algebra + projection/annihilator (incl. rank), leverage identities/bounds, reduced-Gram and literal row-deleted leave-one-out formulas, influence diagnostics, and FWL coefficient/residual core landed |
| 04 | Least Squares Regression | partial | OLS/GLS algebra, unbiasedness, covariance identities, Gauss-Markov lower bounds, `s²` unbiasedness, HC2/HC3, and clustered covariance definitions/finite-sample adjustment landed |
| 05 | Normal Regression | partial | multivariate-normal wrappers, normal-model scaffolding, finite-sample Gaussian/chi-square/Student-t/F laws, confidence intervals, and classical test results landed; Kinal moment threshold deferred |
| 06 | A Review of Large Sample Asymptotics | partial | WLLN, iid scalar/vector CLT via Cramér-Wold, projection-level multivariate Lindeberg/heterogeneous-array CLT endpoints for 6.4/6.5, CMT in probability, O_p/o_p, Slutsky, Delta-method wrappers, smooth-function asymptotic wrappers, UI maximum bounds for 6.16, iid finite-power-moment and uniform higher-moment UI discharge for 6.14, convergence-in-measure faces of 6.13/6.15, weak-convergence bounded first-moment transfer for 6.13, and bounded/clipped/tail-assembly weak-moment bridges for 6.15 backed by Mathlib + AsymptoticUtils/Chapter6Asymptotics; remaining textbook-shaped gaps documented in the Ch 6 inventory |
| 07 | Asymptotic Theory for Least Squares | partial | Theorems 7.1-7.5 have totalized/ordinary OLS consistency, score CLT, vector CLT, and variance/covariance consistency wrappers; 7.6-7.14 have robust covariance, nonlinear Delta, t/CI/Wald wrappers at the current assumption layer, with packaged feasible HC0/HC1/HC2/HC3 remainder/leverage conditions; 7.16 and 7.17 have max-residual/max-leverage rate packaging with iid finite-squared-row-moment UI discharge and direct iid package endpoints; feasible HC bounded-weight hypotheses now have scalar WLLN primitive constructors, scalar/joint/compact moment condition bundles, a combined robust feasible-HC moment package, an iid joint-observation package deriving residual-variance, homoskedastic covariance/Wald, and direct HC0/HC1/HC2/HC3 covariance, standard-error, scalar t/CI/Wald, and totalized/ordinary multivariate Wald endpoints; Edgeworth has generic first-order and uniform second-order CDF-expansion interfaces, with the concrete expansion proof still pending |
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
`HansenEconometrics/Chapter2LinearProjection.lean`,
and `HansenEconometrics/Chapter2PotentialOutcomes.lean`:
- reusable helper definitions `conditioningSpace`, `XMeasurable`, `condExpOn`, `cefErrorOn`,
  `condVarOn`, and `residualVarOn`
- coordinatewise conditional-expectation / integral bridge lemmas for finite-dimensional random
  vectors and arrays
- reusable finite-dimensional mean and covariance helpers `meanVec`, `covVec`, and `covMat`
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
- potential-outcomes definitions for observed outcome, treatment effect, ATE, and CATE
- CIA package via Mathlib conditional independence and conditional distributions
- branchwise observed-regression bridge for `E[Y | D, X]` under mean independence / CIA

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
- centered analysis-of-variance and `R²` identities
- leverage identities/bounds, reduced-Gram and literal row-deleted leave-one-out formulas, and
  Section 3.21 influence diagnostics
- FWL: partitioned normal equations, residualized regressors `M₁ X₂`, the sequential residual-maker
  identity, the coefficient identity, and residual equivalence

Planned next within Chapter 3:
- no immediate Chapter 3 blocker; remaining issue #42 work is concentrated in Chapters 4, 6, and 7

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
- Gaussian law for the OLS coefficient vector as an affine image of the error vector
- Gaussian law for the OLS residual vector as a linear image of the error vector
- chi-square law for the scaled residual variance statistic and independence from `β̂`
- exact Student-t, confidence-interval, variance-interval, and classical test layers

Reused from `HansenEconometrics/Chapter4LeastSquaresRegression.lean`:
- finite-sample residual variance estimator definition
- deterministic linear-model and quadratic-form rewrites of `s²` in terms of the model error

Completed in `HansenEconometrics/MultivariateNormal.lean`:
- standard-normal finite-moment, mean, and variance wrappers
- affine-image law for multivariate normals, including the random-variable `HasLaw` form
- multivariate-normal mean/covariance identities, marginal laws, and scalar jointly-Gaussian
  independence iff zero covariance

Completed in `HansenEconometrics/ChiSquared.lean`:
- chi-square distribution defined as a Gamma distribution with shape `k/2` and rate `1/2`
- basic probability-measure instance for positive degrees of freedom
- negative-support vanishing lemma inherited from the Gamma density

Planned next within Chapter 5:
- keep Theorem 5.5 (Kinal 1980) deferred until a later chapter needs the moment-existence threshold
- extend likelihood / MLE derivations if later chapters need them
- add closed-form standard-normal moment formulas only if they become useful downstream

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
- HC0 / White, HC1, HC2, and HC3 covariance estimators
- clustered covariance estimator, finite-sample adjustment, singleton HC0/HC1 identities, and
  linear-model rewrite
- method-of-moments `σ̂²`, including the diagonal heteroskedastic `E[σ̂² | X] = n⁻¹ tr(MD)` trace formula
- residual variance estimator `s²`, deterministic rewrites, and homoskedastic conditional/unconditional unbiasedness

Explicitly deferred for now within Chapter 4:
- clustered covariance asymptotics and richer partition infrastructure
- HC4 and other leverage-adjustment families

Next target after Chapter 4:
- Chapter 5 normal-model finite-sample distribution theory and classical inference results

## Philosophy

The point is not to force Hansen’s prose into Lean line by line. The point is to build a usable formal skeleton of the mathematics behind the book.

That means:
- proving reusable infrastructure first,
- keeping public APIs close to the variable-based notation that applied econometricians expect,
- preferring mathematically canonical formulations,
- and being honest about what is already in Mathlib versus what we are adding on top.
