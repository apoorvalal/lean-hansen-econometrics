# lean-hansen-econometrics

A gradual Lean formalization project for Bruce E. Hansen's *Econometrics*.

This repo is not meant to be a one-shot dump of isolated theorem files. The goal is to work through the book chapter by chapter, formalizing the core mathematical results, building reusable dependencies, and keeping a visible progress map.

## Scope

Primary source text:
- `HansenEconometrics.pdf` in the surrounding Hansen doodle project

Current emphasis:
- Chapter 2 (`Conditional Expectation and Projection`)
- Chapter 3 (`The Algebra of Least Squares`) scaffolded and ready for the next theorem pass

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
| 01 | Introduction | not started | mostly exposition; probably little to formalize directly |
| 02 | Conditional Expectation and Projection | partial | conditional expectation core + variance layer completed |
| 03 | The Algebra of Least Squares | partial | OLS algebra + projection/annihilator matrix core landed |
| 04 | Least Squares Regression | not started | finite-sample regression theory |
| 05 | Normal Regression | not started | distributional finite-sample results |
| 06 | A Review of Large Sample Asymptotics | not started | likely prerequisite for later asymptotics chapters |
| 07 | Asymptotic Theory for Least Squares | not started | consistency / asymptotic normality targets |
| 08 | Restricted Estimation | not started | constrained estimation / minimum distance |
| 09 | Hypothesis Testing | not started | Wald / LM / LR style results |
| 10 | Resampling Methods | not started | bootstrap / jackknife |
| 11 | Multivariate Regression | not started | |
| 12 | Instrumental Variables | not started | |
| 13 | Generalized Method of Moments | not started | |
| 14 | Time Series | not started | |
| 15 | Multivariate Time Series | not started | |
| 16 | Non-Stationary Time Series | not started | |
| 17 | Panel Data | not started | |
| 18 | Difference in Differences | not started | |
| 19 | Nonparametric Regression | not started | |
| 20 | Series Regression | not started | |
| 21 | Regression Discontinuity | not started | |
| 22 | M-Estimators | not started | |
| 23 | Nonlinear Least Squares | not started | |
| 24 | Quantile Regression | not started | |
| 25 | Binary Choice | not started | |
| 26 | Multiple Choice | not started | |
| 27 | Censoring and Selection | not started | |
| 28 | Model Selection, Stein Shrinkage, and Model Averaging | not started | |
| 29 | Machine Learning | not started | |

## Current Chapter 2 progress

Completed in `HansenEconometrics/Chapter2CondExp.lean` and `HansenEconometrics/Chapter2Variance.lean`:
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

Planned next within Chapter 2:
- conditional expectation as best predictor
- linear projection / best linear predictor
- later chapter 2 identification / existence statements where worthwhile

See also:
- `notes/theorem_inventory.md`

## Philosophy

The point is not to force Hansen’s prose into Lean line by line. The point is to build a usable formal skeleton of the mathematics behind the book.

That means:
- proving reusable infrastructure first,
- preferring mathematically canonical formulations,
- and being honest about what is already in Mathlib versus what we are adding on top.
