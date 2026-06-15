import HansenEconometrics.Chapter8Asymptotics

/-!
# Chapter 11 — seemingly unrelated regression

This module records the SUR/GLS covariance surface and interface-level
projections used by the Hansen Theorems 11.4--11.6 formalization route.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped Matrix Topology MeasureTheory ProbabilityTheory

namespace HansenEconometrics

open Matrix

variable {Ω k : Type*}
variable [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable [Fintype k] [DecidableEq k]

/-- SUR asymptotic variance `(E[X'Σ⁻¹X])⁻¹`. -/
noncomputable def surAsymptoticVariance (M : Matrix k k ℝ) : Matrix k k ℝ :=
  M⁻¹

/-- Feasible SUR variance estimator surface. -/
noncomputable def surVarianceEstimator (Mhat : Matrix k k ℝ) : Matrix k k ℝ :=
  Mhat⁻¹

/-- Interface projection for SUR asymptotic normality. -/
theorem sur_gaussianLimit_from_interface
    (T : ℕ → Ω → k → ℝ) (M : Matrix k k ℝ)
    (hT : GaussianLimit μ T (surAsymptoticVariance M)) :
    GaussianLimit μ T (surAsymptoticVariance M) :=
  hT

/-- Distributional face of `sur_gaussianLimit_from_interface`. -/
theorem sur_tendstoInDistribution_from_interface
    (T : ℕ → Ω → k → ℝ) (M : Matrix k k ℝ)
    (hT : GaussianLimit μ T (surAsymptoticVariance M)) :
    TendstoInDistribution T atTop (fun z : EuclideanSpace ℝ k => z.ofLp)
      (fun _ => μ) (multivariateGaussian 0 (surAsymptoticVariance M)) :=
  hT.limit

omit [Fintype k] [DecidableEq k] in
/-- Loewner-order bridge for SUR efficiency once the variance gap has been
established by a concrete SUR proof. -/
theorem sur_efficiency_from_loewner_gap
    (Vsur Vols : Matrix k k ℝ) (h : (Vols - Vsur).PosSemidef) :
    (Vols - Vsur).PosSemidef :=
  h

omit [IsProbabilityMeasure μ] [DecidableEq k] in
/-- Interface projection for feasible SUR covariance consistency. -/
theorem surCovariance_consistent_from_interface
    (Vhat : ℕ → Ω → Matrix k k ℝ) (Vsur : Matrix k k ℝ)
    (hV : CovarianceEstimatorConsistent μ Vhat Vsur) :
    CovarianceEstimatorConsistent μ Vhat Vsur :=
  hV

end HansenEconometrics
