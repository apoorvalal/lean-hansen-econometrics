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

/-- Reusable Gaussian-limit linear-map bridge for Chapter 12 generated-regressor
and expectation-error arguments.

This is the step used to pass from a joint Gaussian limit to the Gaussian limit
of a selected block or linear combination. -/
theorem gaussianLimit_linearMap
    (T : ℕ → Omega → k → ℝ) (V : Matrix k k ℝ) (R : Matrix q k ℝ)
    (h : GaussianLimit mu T V) :
    GaussianLimit mu (fun n ω => R *ᵥ T n ω) (R * V * Rᵀ) := by
  refine ⟨?_, ?_⟩
  · simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.PosSemidef.mul_mul_conjTranspose_same h.covariance_posSemidef R
  · have hlin :
        TendstoInDistribution
          (fun n ω => matrixContinuousLinearMap R (WithLp.toLp 2 (T n ω)))
          atTop (fun z : EuclideanSpace ℝ k => matrixContinuousLinearMap R z)
          (fun _ => mu) (multivariateGaussian 0 V) := by
      have hg :
          Continuous (fun x : k → ℝ => matrixContinuousLinearMap R (WithLp.toLp 2 x)) := by
        fun_prop
      simpa [Function.comp_def] using h.limit.continuous_comp hg
    have hLaw :
        HasLaw (fun z : EuclideanSpace ℝ k => matrixContinuousLinearMap R z)
          (multivariateGaussian 0 (R * V * Rᵀ)) (multivariateGaussian 0 V) := by
      simpa [matrixContinuousLinearMap, Matrix.conjTranspose_eq_transpose_of_trivial] using
        hasLaw_multivariateGaussian_zero_linearMap
          (n := k) (q := q) h.covariance_posSemidef R
    have hEuclid :
        TendstoInDistribution
          (fun n ω => matrixContinuousLinearMap R (WithLp.toLp 2 (T n ω)))
          atTop (fun z : EuclideanSpace ℝ q => z)
          (fun _ => mu) (multivariateGaussian 0 (R * V * Rᵀ)) :=
      tendstoInDistribution_id_of_hasLaw_limit (E := EuclideanSpace ℝ q) hlin hLaw
    have hofLp : Continuous (fun z : EuclideanSpace ℝ q => z.ofLp) := by
      fun_prop
    simpa [Function.comp_def, matrixContinuousLinearMap_apply] using
      hEuclid.continuous_comp hofLp

/-- Interface projection for the generated-regressor Gaussian limit. -/
theorem generatedRegressor_gaussianLimit_from_interface
    (T : ℕ → Omega → k → ℝ) (V : Matrix k k ℝ)
    (h : GeneratedRegressorGaussianLimitInterface (mu := mu) T V) :
    GaussianLimit mu T V :=
  h.gaussian_limit

/-- Linear image of a generated-regressor Gaussian limit.

This theorem supports Hansen Theorems 12.9 and 12.11: once the coefficient
vector has its joint Gaussian limit, any tested block or linear restriction has
the corresponding Gaussian limit with covariance `R V R'`. -/
theorem generatedRegressor_gaussianLimit_linearMap_from_interface
    (T : ℕ → Omega → k → ℝ) (V : Matrix k k ℝ) (R : Matrix q k ℝ)
    (h : GeneratedRegressorGaussianLimitInterface (mu := mu) T V) :
    GaussianLimit mu (fun n ω => R *ᵥ T n ω) (R * V * Rᵀ) :=
  gaussianLimit_linearMap T V R h.gaussian_limit

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

/-- Linear image of an expectation-error Gaussian limit.

This is the reusable layer needed for Hansen Theorem 12.13: the alpha estimator
limit is a linear image of the joint expectation-error/generated-regressor
limit, with covariance `R V R'`. -/
theorem expectationError_gaussianLimit_linearMap_from_interface
    (T : ℕ → Omega → k → ℝ) (V : Matrix k k ℝ) (R : Matrix q k ℝ)
    (h : ExpectationErrorGaussianLimitInterface (mu := mu) T V) :
    GaussianLimit mu (fun n ω => R *ᵥ T n ω) (R * V * Rᵀ) :=
  gaussianLimit_linearMap T V R h.gaussian_limit

end HansenEconometrics
