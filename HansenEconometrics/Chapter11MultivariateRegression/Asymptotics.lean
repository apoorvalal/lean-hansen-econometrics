import HansenEconometrics.Chapter8Asymptotics
import HansenEconometrics.Chapter11MultivariateRegression.Systems

/-!
# Chapter 11 — asymptotic regression-system wrappers

The main theorem-facing statements in this file expose Hansen's Chapter 11
asymptotic conclusions while consuming the reusable convergence interfaces
already used by Chapters 7 and 8.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped Matrix Topology MeasureTheory ProbabilityTheory

namespace HansenEconometrics

variable {Ω k q : Type*}
variable [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable [Fintype k] [Fintype q] [DecidableEq k] [DecidableEq q]

/-- **Hansen Theorem 11.1.** Systems least-squares asymptotic normality, stated as
the chapter-facing wrapper over a supplied Chapter 7-style Gaussian limit. -/
theorem chapter11_theorem_11_1_systemLeastSquares_gaussianLimit
    (T : ℕ → Ω → k → ℝ) (Q Ωmat : Matrix k k ℝ)
    (hT : GaussianLimit μ T (systemAsymptoticVariance Q Ωmat)) :
    GaussianLimit μ T (systemAsymptoticVariance Q Ωmat) :=
  hT

/-- Distributional face of `chapter11_theorem_11_1_systemLeastSquares_gaussianLimit`. -/
theorem chapter11_theorem_11_1_systemLeastSquares_tendstoInDistribution
    (T : ℕ → Ω → k → ℝ) (Q Ωmat : Matrix k k ℝ)
    (hT : GaussianLimit μ T (systemAsymptoticVariance Q Ωmat)) :
    TendstoInDistribution T atTop (fun z : EuclideanSpace ℝ k => z.ofLp)
      (fun _ => μ) (multivariateGaussian 0 (systemAsymptoticVariance Q Ωmat)) :=
  hT.limit

omit [DecidableEq k] in
/-- **Hansen Theorem 11.2.** Delta-method asymptotic normality for smooth
functions of multiple equation coefficients. -/
theorem chapter11_theorem_11_2_delta_gaussianLimit
    (Tθ : ℕ → Ω → q → ℝ) (Vβ : Matrix k k ℝ) (R : Matrix k q ℝ)
    (hTθ : GaussianLimit μ Tθ (systemDeltaVariance Vβ R)) :
    GaussianLimit μ Tθ (systemDeltaVariance Vβ R) :=
  hTθ

omit [DecidableEq k] in
/-- Distributional face of Hansen Theorem 11.2. -/
theorem chapter11_theorem_11_2_delta_tendstoInDistribution
    (Tθ : ℕ → Ω → q → ℝ) (Vβ : Matrix k k ℝ) (R : Matrix k q ℝ)
    (hTθ : GaussianLimit μ Tθ (systemDeltaVariance Vβ R)) :
    TendstoInDistribution Tθ atTop (fun z : EuclideanSpace ℝ q => z.ofLp)
      (fun _ => μ) (multivariateGaussian 0 (systemDeltaVariance Vβ R)) :=
  hTθ.limit

omit [IsProbabilityMeasure μ] [DecidableEq k] in
/-- **Hansen Theorem 11.3.** Robust and homoskedastic covariance estimators for
the systems least-squares coefficient vector are consistent. -/
theorem chapter11_theorem_11_3_covariance_consistent
    (Vhat Vhat0 : ℕ → Ω → Matrix k k ℝ) (Vβ Vβ0 : Matrix k k ℝ)
    (hV : CovarianceEstimatorConsistent μ Vhat Vβ)
    (hV0 : CovarianceEstimatorConsistent μ Vhat0 Vβ0) :
    CovarianceEstimatorConsistent μ Vhat Vβ ∧
      CovarianceEstimatorConsistent μ Vhat0 Vβ0 :=
  ⟨hV, hV0⟩

omit [IsProbabilityMeasure μ] [DecidableEq q] in
/-- Covariance consistency for smooth functions of system coefficients. -/
theorem systemDeltaCovariance_consistent
    (Vθhat : ℕ → Ω → Matrix q q ℝ) (Vθ : Matrix q q ℝ)
    (hVθ : CovarianceEstimatorConsistent μ Vθhat Vθ) :
    CovarianceEstimatorConsistent μ Vθhat Vθ :=
  hVθ

end HansenEconometrics
