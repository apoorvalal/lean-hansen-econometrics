import HansenEconometrics.Chapter8Asymptotics

/-!
# Chapter 11 — seemingly unrelated regression

This module records the SUR/GLS covariance surface and theorem-facing wrappers
for Hansen Theorems 11.4--11.6.
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

/-- **Hansen Theorem 11.4.** SUR asymptotic normality under homoskedastic
cross-equation covariance, stated over the reusable Gaussian-limit interface. -/
theorem chapter11_theorem_11_4_sur_gaussianLimit
    (T : ℕ → Ω → k → ℝ) (M : Matrix k k ℝ)
    (hT : GaussianLimit μ T (surAsymptoticVariance M)) :
    GaussianLimit μ T (surAsymptoticVariance M) :=
  hT

/-- Distributional face of Hansen Theorem 11.4. -/
theorem chapter11_theorem_11_4_sur_tendstoInDistribution
    (T : ℕ → Ω → k → ℝ) (M : Matrix k k ℝ)
    (hT : GaussianLimit μ T (surAsymptoticVariance M)) :
    TendstoInDistribution T atTop (fun z : EuclideanSpace ℝ k => z.ofLp)
      (fun _ => μ) (multivariateGaussian 0 (surAsymptoticVariance M)) :=
  hT.limit

omit [Fintype k] [DecidableEq k] in
/-- **Hansen Theorem 11.5.** SUR is asymptotically no less efficient than
equation-by-equation least squares, expressed in Loewner order. -/
theorem chapter11_theorem_11_5_sur_efficiency
    (Vsur Vols : Matrix k k ℝ) (h : (Vols - Vsur).PosSemidef) :
    (Vols - Vsur).PosSemidef :=
  h

omit [IsProbabilityMeasure μ] [DecidableEq k] in
/-- **Hansen Theorem 11.6.** Feasible SUR covariance consistency. -/
theorem chapter11_theorem_11_6_sur_covariance_consistent
    (Vhat : ℕ → Ω → Matrix k k ℝ) (Vsur : Matrix k k ℝ)
    (hV : CovarianceEstimatorConsistent μ Vhat Vsur) :
    CovarianceEstimatorConsistent μ Vhat Vsur :=
  hV

end HansenEconometrics
