import HansenEconometrics.Assumptions.Conditioning
import HansenEconometrics.Chapter2LinearProjection

/-!
# Regression Setup Assumptions

This module packages textbook-facing population regression hypotheses and exposes
their moment and projection consequences as methods. Structures contain
assumptions; orthogonality, covariance, and projection formulas are theorems.
-/

open scoped ENNReal Topology MeasureTheory ProbabilityTheory Matrix
open MeasureTheory ProbabilityTheory Matrix

namespace HansenEconometrics

variable {Ω k : Type*}
variable [MeasurableSpace Ω] [Fintype k]
variable {μ : Measure Ω}

/-- Textbook affine linear model with L2 regressors and error. -/
structure AffineLinearModelL2
    (μ : Measure Ω) (X : Ω → k → ℝ) (Y e : Ω → ℝ) (α : ℝ) (β : k → ℝ) where
  isProbability : IsProbabilityMeasure μ
  regressor_memLp : ∀ j, MemLp (fun ω => X ω j) 2 μ
  error_memLp : MemLp e 2 μ
  model : Y = fun ω => α + dotProduct (X ω) β + e ω

/-- Zero-intercept linear model with L2 regressors and error. -/
structure LinearModelL2
    (μ : Measure Ω) (X : Ω → k → ℝ) (Y e : Ω → ℝ) (β : k → ℝ) where
  isProbability : IsProbabilityMeasure μ
  regressor_memLp : ∀ j, MemLp (fun ω => X ω j) 2 μ
  error_memLp : MemLp e 2 μ
  model : Y = fun ω => dotProduct (X ω) β + e ω

/-- Linear model with conditional mean-zero error given regressors. -/
structure LinearModelCondExog
    (μ : Measure Ω) (X : Ω → k → ℝ) (Y e : Ω → ℝ) (β : k → ℝ)
    extends LinearModelL2 μ X Y e β where
  measurable_regressor : Measurable X
  sigmaFinite_trim : SigmaFinite (μ.trim (conditioningSpace_le measurable_regressor))
  cond_error_zero : condExpOn μ e X =ᵐ[μ] 0

/-- Linear model with unconditional moment exogeneity. -/
structure LinearModelMomentExog
    (μ : Measure Ω) (X : Ω → k → ℝ) (Y e : Ω → ℝ) (β : k → ℝ)
    extends LinearModelL2 μ X Y e β where
  error_mean_zero : ∫ ω, e ω ∂μ = 0
  moment_exogeneity : μ[fun ω => e ω • X ω] = 0

/-- Affine model with covariance orthogonality between regressors and error. -/
structure LinearModelCovExog
    (μ : Measure Ω) (X : Ω → k → ℝ) (Y e : Ω → ℝ) (α : ℝ) (β : k → ℝ)
    extends AffineLinearModelL2 μ X Y e α β where
  error_mean_zero : ∫ ω, e ω ∂μ = 0
  covariance_exogeneity : covVec μ X e = 0

namespace LinearModelL2

/-- View a zero-intercept model as an affine model with intercept `0`. -/
def toAffine
    {X : Ω → k → ℝ} {Y e : Ω → ℝ} {β : k → ℝ}
    (h : LinearModelL2 μ X Y e β) :
    AffineLinearModelL2 μ X Y e 0 β where
  isProbability := h.isProbability
  regressor_memLp := h.regressor_memLp
  error_memLp := h.error_memLp
  model := by
    rw [h.model]
    funext ω
    ring

end LinearModelL2

namespace LinearModelCondExog

/-- Conditional exogeneity gives an L1 conditioning setup for the error. -/
def errorConditionalL1
    {X : Ω → k → ℝ} {Y e : Ω → ℝ} {β : k → ℝ}
    (h : LinearModelCondExog μ X Y e β) :
    ConditionalL1Setup μ e X where
  isProbability := h.isProbability
  measurable_conditioning := h.measurable_regressor
  sigmaFinite_trim := h.sigmaFinite_trim
  integrable_response := by
    haveI : IsProbabilityMeasure μ := h.isProbability
    exact h.error_memLp.integrable one_le_two

/-- Conditional exogeneity implies the structural error has mean zero. -/
theorem error_integral_zero
    {X : Ω → k → ℝ} {Y e : Ω → ℝ} {β : k → ℝ}
    (h : LinearModelCondExog μ X Y e β) :
    ∫ ω, e ω ∂μ = 0 := by
  have hlie := h.errorConditionalL1.simple_law_iterated_expectation
  calc
    ∫ ω, e ω ∂μ = ∫ ω, condExpOn μ e X ω ∂μ := hlie.symm
    _ = ∫ _ω, (0 : ℝ) ∂μ := by
          exact integral_congr_ae h.cond_error_zero
    _ = 0 := by simp

/-- Conditional exogeneity implies population moment exogeneity. -/
theorem moment_exogeneity
    {X : Ω → k → ℝ} {Y e : Ω → ℝ} {β : k → ℝ}
    (h : LinearModelCondExog μ X Y e β) :
    μ[fun ω => e ω • X ω] = 0 := by
  haveI : IsProbabilityMeasure μ := h.isProbability
  have hvec_int : Integrable (fun ω => e ω • X ω) μ := by
    refine Integrable.of_eval ?_
    intro j
    have hprod : Integrable (fun ω => e ω * X ω j) μ :=
      h.error_memLp.integrable_mul (h.regressor_memLp j)
    simpa [Pi.smul_apply, smul_eq_mul] using hprod
  funext j
  have hpred : XPredictorL1 μ X (fun ω => X ω j) := {
    x_measurable := by
      have hf : Measurable (fun x : k → ℝ => x j) :=
        (continuous_apply j).measurable
      exact (hf.comp (Measurable.of_comap_le le_rfl)).aestronglyMeasurable
    integrable_predictor := (h.regressor_memLp j).integrable one_le_two }
  have hprod : Integrable (fun ω => (fun ω => X ω j) ω * e ω) μ := by
    have hmul : Integrable (fun ω => e ω * X ω j) μ :=
      h.error_memLp.integrable_mul (h.regressor_memLp j)
    convert hmul using 1
    ext ω
    ring
  have hcond := h.errorConditionalL1.conditioning_integral hpred hprod
  calc
    (μ[fun ω => e ω • X ω]) j = ∫ ω, e ω * X ω j ∂μ := by
      simpa [Pi.smul_apply, smul_eq_mul] using
        integral_apply (μ := μ) (f := fun ω => e ω • X ω) hvec_int j
    _ = ∫ ω, X ω j * e ω ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with ω
      ring
    _ = ∫ ω, X ω j * condExpOn μ e X ω ∂μ := hcond
    _ = ∫ _ω, (0 : ℝ) ∂μ := by
      apply integral_congr_ae
      filter_upwards [h.cond_error_zero] with ω hω
      simp [hω]
    _ = (0 : k → ℝ) j := by simp

/-- Package conditional exogeneity as moment exogeneity. -/
def toMomentExog
    {X : Ω → k → ℝ} {Y e : Ω → ℝ} {β : k → ℝ}
    (h : LinearModelCondExog μ X Y e β) :
    LinearModelMomentExog μ X Y e β where
  isProbability := h.isProbability
  regressor_memLp := h.regressor_memLp
  error_memLp := h.error_memLp
  model := h.model
  error_mean_zero := h.error_integral_zero
  moment_exogeneity := h.moment_exogeneity

end LinearModelCondExog

namespace LinearModelMomentExog

/-- Moment exogeneity with mean-zero errors implies covariance orthogonality. -/
theorem covariance_exogeneity
    {X : Ω → k → ℝ} {Y e : Ω → ℝ} {β : k → ℝ}
    (h : LinearModelMomentExog μ X Y e β) :
    covVec μ X e = 0 := by
  haveI : IsProbabilityMeasure μ := h.isProbability
  ext j
  have hmoment_j : ∫ ω, e ω * X ω j ∂μ = 0 := by
    have hcoord := congrFun h.moment_exogeneity j
    have hvec_int : Integrable (fun ω => e ω • X ω) μ := by
      refine Integrable.of_eval ?_
      intro l
      have hprod : Integrable (fun ω => e ω * X ω l) μ :=
        h.error_memLp.integrable_mul (h.regressor_memLp l)
      simpa [Pi.smul_apply, smul_eq_mul] using hprod
    calc
      ∫ ω, e ω * X ω j ∂μ
          = (∫ ω, e ω • X ω ∂μ) j := by
            rw [integral_apply (μ := μ) (f := fun ω => e ω • X ω) hvec_int j]
            simp [Pi.smul_apply, smul_eq_mul]
      _ = 0 := hcoord
  rw [covVec, ProbabilityTheory.covariance_eq_sub (h.regressor_memLp j) h.error_memLp]
  rw [h.error_mean_zero]
  calc
    μ[(fun ω => X ω j) * e] - μ[fun ω => X ω j] * 0
        = μ[(fun ω => X ω j) * e] := by ring
    _ = ∫ ω, e ω * X ω j ∂μ := by
          apply integral_congr_ae
          filter_upwards [] with ω
          simp [Pi.mul_apply, mul_comm]
    _ = 0 := hmoment_j

/-- Package moment exogeneity as covariance exogeneity for the zero-intercept affine model. -/
def toCovExog
    {X : Ω → k → ℝ} {Y e : Ω → ℝ} {β : k → ℝ}
    (h : LinearModelMomentExog μ X Y e β) :
    LinearModelCovExog μ X Y e 0 β where
  isProbability := h.isProbability
  regressor_memLp := h.regressor_memLp
  error_memLp := h.error_memLp
  model := h.toLinearModelL2.toAffine.model
  error_mean_zero := h.error_mean_zero
  covariance_exogeneity := h.covariance_exogeneity

end LinearModelMomentExog

namespace LinearModelCondExog

/-- Conditional exogeneity implies covariance orthogonality. -/
theorem covariance_exogeneity
    {X : Ω → k → ℝ} {Y e : Ω → ℝ} {β : k → ℝ}
    (h : LinearModelCondExog μ X Y e β) :
    covVec μ X e = 0 :=
  h.toMomentExog.covariance_exogeneity

end LinearModelCondExog

namespace LinearModelCovExog

/-- Hansen Theorem 2.10 intercept formula from the packaged affine model. -/
theorem intercept_eq_mean_sub_dotProduct
    {X : Ω → k → ℝ} {Y e : Ω → ℝ} {α : ℝ} {β : k → ℝ}
    (h : LinearModelCovExog μ X Y e α β) :
    α = ∫ ω, Y ω ∂μ - meanVec μ X ⬝ᵥ β := by
  haveI : IsProbabilityMeasure μ := h.isProbability
  exact linearProjectionIntercept_eq_mean_sub_dotProduct
    (μ := μ) X Y e α β h.regressor_memLp h.error_memLp h.model h.error_mean_zero

/-- Hansen Theorem 2.10 slope formula from the packaged affine model. -/
theorem beta_eq_linearProjectionBeta
    {X : Ω → k → ℝ} {Y e : Ω → ℝ} {α : ℝ} {β : k → ℝ}
    [DecidableEq k]
    [Invertible (covMat μ X)]
    (h : LinearModelCovExog μ X Y e α β) :
    β = linearProjectionBeta (covMat μ X) (covVec μ X Y) := by
  haveI : IsProbabilityMeasure μ := h.isProbability
  exact linearProjectionBeta_eq_covMat_inv_covVec
    (μ := μ) X Y e α β h.regressor_memLp h.error_memLp h.model h.covariance_exogeneity

end LinearModelCovExog

end HansenEconometrics
