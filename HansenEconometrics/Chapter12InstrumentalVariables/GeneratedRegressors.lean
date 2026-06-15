import HansenEconometrics.Chapter8Asymptotics

/-!
# Chapter 12 - generated regressors and expectation errors

This module records support interfaces for Hansen's generated-regressor,
expectation-error, and two-step IV routes. The projection lemmas do not yet
derive Theorems 12.9--12.12 from the displayed model assumptions.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped Matrix Topology MeasureTheory ProbabilityTheory

namespace HansenEconometrics

variable {Omega k q : Type*}
variable [MeasurableSpace Omega] {mu : Measure Omega} [IsProbabilityMeasure mu]
variable [Fintype k] [Fintype q] [DecidableEq k] [DecidableEq q]

/-- High-level Gaussian-limit interface for a generated-regressor 2SLS estimator. -/
structure GeneratedRegressorGaussianLimitInterface
    (T : ℕ → Omega → k → ℝ) (V : Matrix k k ℝ) : Prop where
  gaussian_limit : GaussianLimit mu T V

/-- Extra normal-regression finite-sample law interface for generated regressors. -/
structure GeneratedRegressorNormalLawInterface
    (stat : Omega → ℝ) (law : Measure ℝ) : Prop where
  statistic_law : HasLaw stat law mu

/-- Interface for generated-regressor plug-in consistency. -/
structure GeneratedRegressorConsistencyInterface
    (betahat : ℕ → Omega → k → ℝ) (beta : k → ℝ) : Prop where
  consistent : TendstoInMeasure mu betahat atTop (fun _ => beta)

/-- Gaussian-limit interface for regression with expectation errors. -/
structure ExpectationErrorGaussianLimitInterface
    (T : ℕ → Omega → q → ℝ) (V : Matrix q q ℝ) : Prop where
  gaussian_limit : GaussianLimit mu T V

/-- Interface projection for the generated-regressor Gaussian limit. -/
theorem generatedRegressor_gaussianLimit_from_interface
    (T : ℕ → Omega → k → ℝ) (V : Matrix k k ℝ)
    (h : GeneratedRegressorGaussianLimitInterface (mu := mu) T V) :
    GaussianLimit mu T V :=
  h.gaussian_limit

omit [IsProbabilityMeasure mu] in
/-- Interface projection for the generated-regressor finite-sample law. -/
theorem generatedRegressor_normal_hasLaw_from_interface
    (stat : Omega → ℝ) (law : Measure ℝ)
    (h : GeneratedRegressorNormalLawInterface (mu := mu) stat law) :
    HasLaw stat law mu :=
  h.statistic_law

omit [IsProbabilityMeasure mu] [DecidableEq k] in
/-- Interface projection for generated-regressor plug-in consistency. -/
theorem generatedRegressor_consistent_from_interface
    (betahat : ℕ → Omega → k → ℝ) (beta : k → ℝ)
    (h : GeneratedRegressorConsistencyInterface (mu := mu) betahat beta) :
    TendstoInMeasure mu betahat atTop (fun _ => beta) :=
  h.consistent

/-- Interface projection for regression with expectation errors. -/
theorem expectationError_gaussianLimit_from_interface
    (T : ℕ → Omega → q → ℝ) (V : Matrix q q ℝ)
    (h : ExpectationErrorGaussianLimitInterface (mu := mu) T V) :
    GaussianLimit mu T V :=
  h.gaussian_limit

end HansenEconometrics
