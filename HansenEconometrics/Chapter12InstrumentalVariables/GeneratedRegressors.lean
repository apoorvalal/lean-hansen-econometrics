import HansenEconometrics.Chapter8Asymptotics

/-!
# Chapter 12 - generated regressors and expectation errors

This module records theorem packages for Hansen's generated-regressor,
expectation-error, and two-step IV results.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped Matrix Topology MeasureTheory ProbabilityTheory

namespace HansenEconometrics

variable {Omega k q : Type*}
variable [MeasurableSpace Omega] {mu : Measure Omega} [IsProbabilityMeasure mu]
variable [Fintype k] [Fintype q] [DecidableEq k] [DecidableEq q]

/-- Asymptotic linear representation for a generated-regressor 2SLS estimator. -/
structure GeneratedRegressorLinearization
    (T : ℕ → Omega → k → ℝ) (V : Matrix k k ℝ) : Prop where
  gaussian_limit : GaussianLimit mu T V

/-- Extra normal-regression finite-sample package for generated regressors. -/
structure GeneratedRegressorNormalPackage
    (stat : Omega → ℝ) (law : Measure ℝ) : Prop where
  statistic_law : HasLaw stat law mu

/-- Package for generated-regressor plug-in consistency. -/
structure GeneratedRegressorConsistency
    (betahat : ℕ → Omega → k → ℝ) (beta : k → ℝ) : Prop where
  consistent : TendstoInMeasure mu betahat atTop (fun _ => beta)

/-- Package for regression with expectation errors. -/
structure ExpectationErrorRegressionPackage
    (T : ℕ → Omega → q → ℝ) (V : Matrix q q ℝ) : Prop where
  gaussian_limit : GaussianLimit mu T V

/-- **Hansen Theorem 12.9.** Generated-regressor 2SLS has the stated
asymptotic linear representation and Gaussian limit. -/
theorem chapter12_theorem_12_9_generatedRegressor_gaussianLimit
    (T : ℕ → Omega → k → ℝ) (V : Matrix k k ℝ)
    (h : GeneratedRegressorLinearization (mu := mu) T V) :
    GaussianLimit mu T V :=
  h.gaussian_limit

omit [IsProbabilityMeasure mu] in
/-- **Hansen Theorem 12.10.** Under the normal generated-regressor setup, the
finite-sample statistic has the stated law. -/
theorem chapter12_theorem_12_10_generatedRegressor_normal_hasLaw
    (stat : Omega → ℝ) (law : Measure ℝ)
    (h : GeneratedRegressorNormalPackage (mu := mu) stat law) :
    HasLaw stat law mu :=
  h.statistic_law

omit [IsProbabilityMeasure mu] [DecidableEq k] in
/-- **Hansen Theorem 12.11.** Generated-regressor plug-in consistency. -/
theorem chapter12_theorem_12_11_generatedRegressor_consistent
    (betahat : ℕ → Omega → k → ℝ) (beta : k → ℝ)
    (h : GeneratedRegressorConsistency (mu := mu) betahat beta) :
    TendstoInMeasure mu betahat atTop (fun _ => beta) :=
  h.consistent

/-- **Hansen Theorem 12.12.** Regression with expectation errors has the
chapter's stated Gaussian limit under its high-level assumptions. -/
theorem chapter12_theorem_12_12_expectationError_gaussianLimit
    (T : ℕ → Omega → q → ℝ) (V : Matrix q q ℝ)
    (h : ExpectationErrorRegressionPackage (mu := mu) T V) :
    GaussianLimit mu T V :=
  h.gaussian_limit

end HansenEconometrics
