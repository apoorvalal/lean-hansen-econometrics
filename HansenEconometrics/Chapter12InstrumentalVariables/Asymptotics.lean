import HansenEconometrics.Chapter8Asymptotics
import HansenEconometrics.Chapter12InstrumentalVariables.Basic

/-!
# Chapter 12 - asymptotic instrumental-variables interfaces

This file records support interfaces for the 2SLS consistency,
asymptotic-normality, covariance, and smooth-function routes. The projection
lemmas below expose reusable convergence facts, but they are not proofs of
Hansen Theorems 12.1--12.5 from Assumptions 12.1--12.2.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped Matrix Topology MeasureTheory ProbabilityTheory

namespace HansenEconometrics

variable {Omega k l q : Type*}
variable [MeasurableSpace Omega] {mu : Measure Omega} [IsProbabilityMeasure mu]
variable [Fintype k] [Fintype l] [Fintype q]
variable [DecidableEq k] [DecidableEq l] [DecidableEq q]

/-- High-level consistency interface used by the Chapter 12 2SLS route. -/
structure IVConsistencyInterface
    (betahat : ℕ → Omega → k → ℝ) (beta : k → ℝ) : Prop where
  consistent : TendstoInMeasure mu betahat atTop (fun _ => beta)

/-- High-level Gaussian-limit interface used by the Chapter 12 2SLS route. -/
structure IVGaussianLimitInterface
    (T : ℕ → Omega → k → ℝ) (QZX : Matrix l k ℝ) (QZZ OmegaMat : Matrix l l ℝ) :
    Prop where
  gaussian_limit : GaussianLimit mu T (tslsAsymptoticVariance QZX QZZ OmegaMat)

omit [IsProbabilityMeasure mu] [DecidableEq k] in
/-- Interface projection for 2SLS consistency. -/
theorem twoStageLeastSquares_consistent_from_interface
    (betahat : ℕ → Omega → k → ℝ) (beta : k → ℝ)
    (h : IVConsistencyInterface (mu := mu) betahat beta) :
    TendstoInMeasure mu betahat atTop (fun _ => beta) :=
  h.consistent

/-- Interface projection for 2SLS asymptotic normality. -/
theorem twoStageLeastSquares_gaussianLimit_from_interface
    (T : ℕ → Omega → k → ℝ) (QZX : Matrix l k ℝ) (QZZ OmegaMat : Matrix l l ℝ)
    (h : IVGaussianLimitInterface (mu := mu) T QZX QZZ OmegaMat) :
    GaussianLimit mu T (tslsAsymptoticVariance QZX QZZ OmegaMat) :=
  h.gaussian_limit

/-- Distributional face of `twoStageLeastSquares_gaussianLimit_from_interface`. -/
theorem twoStageLeastSquares_tendstoInDistribution_from_interface
    (T : ℕ → Omega → k → ℝ) (QZX : Matrix l k ℝ) (QZZ OmegaMat : Matrix l l ℝ)
    (h : IVGaussianLimitInterface (mu := mu) T QZX QZZ OmegaMat) :
    TendstoInDistribution T atTop (fun z : EuclideanSpace ℝ k => z.ofLp)
      (fun _ => mu) (multivariateGaussian 0 (tslsAsymptoticVariance QZX QZZ OmegaMat)) :=
  h.gaussian_limit.limit

omit [IsProbabilityMeasure mu] [DecidableEq k] in
/-- Interface projection for 2SLS covariance-matrix estimator consistency. -/
theorem twoStageLeastSquares_covariance_consistent_from_interface
    (Vhat : ℕ → Omega → Matrix k k ℝ) (Vbeta : Matrix k k ℝ)
    (hV : CovarianceEstimatorConsistent mu Vhat Vbeta) :
    CovarianceEstimatorConsistent mu Vhat Vbeta :=
  hV

omit [IsProbabilityMeasure mu] [DecidableEq q] in
/-- Interface projection for consistency of smooth functions of 2SLS parameters. -/
theorem twoStageLeastSquares_function_consistent_from_interface
    (thetahat : ℕ → Omega → q → ℝ) (theta : q → ℝ)
    (hTheta : TendstoInMeasure mu thetahat atTop (fun _ => theta)) :
    TendstoInMeasure mu thetahat atTop (fun _ => theta) :=
  hTheta

omit [DecidableEq k] in
/-- Interface projection for delta-method asymptotic normality of functions of 2SLS. -/
theorem twoStageLeastSquares_function_gaussianLimit_from_interface
    (Ttheta : ℕ → Omega → q → ℝ) (Vbeta : Matrix k k ℝ) (R : Matrix k q ℝ)
    (hTheta : GaussianLimit mu Ttheta (tslsDeltaVariance Vbeta R)) :
    GaussianLimit mu Ttheta (tslsDeltaVariance Vbeta R) :=
  hTheta

omit [DecidableEq k] in
/-- Distributional face of `twoStageLeastSquares_function_gaussianLimit_from_interface`. -/
theorem twoStageLeastSquares_function_tendstoInDistribution_from_interface
    (Ttheta : ℕ → Omega → q → ℝ) (Vbeta : Matrix k k ℝ) (R : Matrix k q ℝ)
    (hTheta : GaussianLimit mu Ttheta (tslsDeltaVariance Vbeta R)) :
    TendstoInDistribution Ttheta atTop (fun z : EuclideanSpace ℝ q => z.ofLp)
      (fun _ => mu) (multivariateGaussian 0 (tslsDeltaVariance Vbeta R)) :=
  hTheta.limit

end HansenEconometrics
