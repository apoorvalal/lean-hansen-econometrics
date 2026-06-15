import HansenEconometrics.Chapter8Asymptotics
import HansenEconometrics.Chapter11MultivariateRegression.Systems

/-!
# Chapter 11 — asymptotic regression-system interfaces

This file records the reusable Chapter 8 convergence interfaces needed by the
Chapter 11 regression-system theorems. These lemmas are interface projections
and distributional faces; they are not, by themselves, proofs of Hansen
Theorems 11.1--11.3 from Assumption 7.2.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped Matrix Topology MeasureTheory ProbabilityTheory

namespace HansenEconometrics

variable {Ω k q : Type*}
variable [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable [Fintype k] [Fintype q] [DecidableEq k] [DecidableEq q]

/-- Interface projection for system least-squares asymptotic normality. -/
theorem systemLeastSquares_gaussianLimit_from_interface
    (T : ℕ → Ω → k → ℝ) (Q Ωmat : Matrix k k ℝ)
    (hT : GaussianLimit μ T (systemAsymptoticVariance Q Ωmat)) :
    GaussianLimit μ T (systemAsymptoticVariance Q Ωmat) :=
  hT

/-- Distributional face of `systemLeastSquares_gaussianLimit_from_interface`. -/
theorem systemLeastSquares_tendstoInDistribution_from_interface
    (T : ℕ → Ω → k → ℝ) (Q Ωmat : Matrix k k ℝ)
    (hT : GaussianLimit μ T (systemAsymptoticVariance Q Ωmat)) :
    TendstoInDistribution T atTop (fun z : EuclideanSpace ℝ k => z.ofLp)
      (fun _ => μ) (multivariateGaussian 0 (systemAsymptoticVariance Q Ωmat)) :=
  hT.limit

omit [DecidableEq k] in
/-- Interface projection for delta-method asymptotic normality of smooth
functions of multiple-equation coefficients. -/
theorem systemDelta_gaussianLimit_from_interface
    (Tθ : ℕ → Ω → q → ℝ) (Vβ : Matrix k k ℝ) (R : Matrix k q ℝ)
    (hTθ : GaussianLimit μ Tθ (systemDeltaVariance Vβ R)) :
    GaussianLimit μ Tθ (systemDeltaVariance Vβ R) :=
  hTθ

omit [DecidableEq k] in
/-- Distributional face of `systemDelta_gaussianLimit_from_interface`. -/
theorem systemDelta_tendstoInDistribution_from_interface
    (Tθ : ℕ → Ω → q → ℝ) (Vβ : Matrix k k ℝ) (R : Matrix k q ℝ)
    (hTθ : GaussianLimit μ Tθ (systemDeltaVariance Vβ R)) :
    TendstoInDistribution Tθ atTop (fun z : EuclideanSpace ℝ q => z.ofLp)
      (fun _ => μ) (multivariateGaussian 0 (systemDeltaVariance Vβ R)) :=
  hTθ.limit

omit [IsProbabilityMeasure μ] [DecidableEq k] in
/-- Interface projection for a pair of system least-squares covariance
consistency statements. -/
theorem systemCovariance_consistent_from_interfaces
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
