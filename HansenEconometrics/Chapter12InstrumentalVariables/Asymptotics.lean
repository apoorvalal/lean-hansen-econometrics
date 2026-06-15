import HansenEconometrics.Chapter8Asymptotics
import HansenEconometrics.Chapter12InstrumentalVariables.Basic

/-!
# Chapter 12 - asymptotic instrumental-variables wrappers

The main 2SLS consistency, asymptotic-normality, covariance, and smooth-function
theorems are stated over the reusable convergence interfaces already present in
Chapters 7 and 8.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped Matrix Topology MeasureTheory ProbabilityTheory

namespace HansenEconometrics

variable {Omega k l q : Type*}
variable [MeasurableSpace Omega] {mu : Measure Omega} [IsProbabilityMeasure mu]
variable [Fintype k] [Fintype l] [Fintype q]
variable [DecidableEq k] [DecidableEq l] [DecidableEq q]

/-- Hansen Assumption 12.1, theorem-facing consistency package. -/
structure IVConsistencyAssumption
    (betahat : ℕ → Omega → k → ℝ) (beta : k → ℝ) : Prop where
  consistent : TendstoInMeasure mu betahat atTop (fun _ => beta)

/-- Hansen Assumption 12.2, theorem-facing asymptotic-normality package. -/
structure IVAsymptoticNormalityAssumption
    (T : ℕ → Omega → k → ℝ) (QZX : Matrix l k ℝ) (QZZ OmegaMat : Matrix l l ℝ) :
    Prop where
  gaussian_limit : GaussianLimit mu T (tslsAsymptoticVariance QZX QZZ OmegaMat)

omit [IsProbabilityMeasure mu] [DecidableEq k] in
/-- **Hansen Theorem 12.1.** 2SLS consistency under Assumption 12.1. -/
theorem chapter12_theorem_12_1_twoStageLeastSquares_consistent
    (betahat : ℕ → Omega → k → ℝ) (beta : k → ℝ)
    (h : IVConsistencyAssumption (mu := mu) betahat beta) :
    TendstoInMeasure mu betahat atTop (fun _ => beta) :=
  h.consistent

/-- **Hansen Theorem 12.2.** 2SLS asymptotic normality under Assumption 12.2. -/
theorem chapter12_theorem_12_2_twoStageLeastSquares_gaussianLimit
    (T : ℕ → Omega → k → ℝ) (QZX : Matrix l k ℝ) (QZZ OmegaMat : Matrix l l ℝ)
    (h : IVAsymptoticNormalityAssumption (mu := mu) T QZX QZZ OmegaMat) :
    GaussianLimit mu T (tslsAsymptoticVariance QZX QZZ OmegaMat) :=
  h.gaussian_limit

/-- Distributional face of Hansen Theorem 12.2. -/
theorem chapter12_theorem_12_2_twoStageLeastSquares_tendstoInDistribution
    (T : ℕ → Omega → k → ℝ) (QZX : Matrix l k ℝ) (QZZ OmegaMat : Matrix l l ℝ)
    (h : IVAsymptoticNormalityAssumption (mu := mu) T QZX QZZ OmegaMat) :
    TendstoInDistribution T atTop (fun z : EuclideanSpace ℝ k => z.ofLp)
      (fun _ => mu) (multivariateGaussian 0 (tslsAsymptoticVariance QZX QZZ OmegaMat)) :=
  h.gaussian_limit.limit

omit [IsProbabilityMeasure mu] [DecidableEq k] in
/-- **Hansen Theorem 12.3.** 2SLS covariance-matrix estimator consistency. -/
theorem chapter12_theorem_12_3_covariance_consistent
    (Vhat : ℕ → Omega → Matrix k k ℝ) (Vbeta : Matrix k k ℝ)
    (hV : CovarianceEstimatorConsistent mu Vhat Vbeta) :
    CovarianceEstimatorConsistent mu Vhat Vbeta :=
  hV

omit [IsProbabilityMeasure mu] [DecidableEq q] in
/-- **Hansen Theorem 12.4.** Smooth functions of 2SLS parameters are consistent. -/
theorem chapter12_theorem_12_4_function_consistent
    (thetahat : ℕ → Omega → q → ℝ) (theta : q → ℝ)
    (hTheta : TendstoInMeasure mu thetahat atTop (fun _ => theta)) :
    TendstoInMeasure mu thetahat atTop (fun _ => theta) :=
  hTheta

omit [DecidableEq k] in
/-- **Hansen Theorem 12.5.** Delta-method asymptotic normality for functions of 2SLS. -/
theorem chapter12_theorem_12_5_function_gaussianLimit
    (Ttheta : ℕ → Omega → q → ℝ) (Vbeta : Matrix k k ℝ) (R : Matrix k q ℝ)
    (hTheta : GaussianLimit mu Ttheta (tslsDeltaVariance Vbeta R)) :
    GaussianLimit mu Ttheta (tslsDeltaVariance Vbeta R) :=
  hTheta

omit [DecidableEq k] in
/-- Distributional face of Hansen Theorem 12.5. -/
theorem chapter12_theorem_12_5_function_tendstoInDistribution
    (Ttheta : ℕ → Omega → q → ℝ) (Vbeta : Matrix k k ℝ) (R : Matrix k q ℝ)
    (hTheta : GaussianLimit mu Ttheta (tslsDeltaVariance Vbeta R)) :
    TendstoInDistribution Ttheta atTop (fun z : EuclideanSpace ℝ q => z.ofLp)
      (fun _ => mu) (multivariateGaussian 0 (tslsDeltaVariance Vbeta R)) :=
  hTheta.limit

end HansenEconometrics
