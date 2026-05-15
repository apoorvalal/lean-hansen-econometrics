import HansenEconometrics.Chapter2PotentialOutcomes

/-!
# Potential-Outcome Setup Assumptions

This module packages the recurring measurability and integrability hypotheses
used by the variable-facing potential-outcomes results in Chapter 2. The
structures are textbook-facing assumption surfaces; their methods delegate to
the theorem names in `Chapter2PotentialOutcomes`.
-/

open scoped ENNReal Topology MeasureTheory ProbabilityTheory
open MeasureTheory ProbabilityTheory

namespace HansenEconometrics

variable {Ω β : Type*}
variable [MeasurableSpace Ω] [MeasurableSpace β]
variable {μ : Measure Ω}

/-- Basic potential-outcome setup for binary treatment and observed covariates. -/
structure PotentialOutcomeSetup
    (μ : Measure Ω) (Y0 Y1 : Ω → ℝ) (D : Ω → Bool) (X : Ω → β) where
  /-- Covariates are measurable. -/
  covariates_measurable : Measurable X
  /-- Treatment is measurable. -/
  treatment_measurable : Measurable D
  /-- The conditioning measure on `σ(X)` is sigma-finite. -/
  sigmaFinite_covariates :
    SigmaFinite (μ.trim (conditioningSpace_le covariates_measurable))
  /-- Untreated potential outcome is integrable. -/
  untreated_integrable : Integrable Y0 μ
  /-- Treated potential outcome is integrable. -/
  treated_integrable : Integrable Y1 μ

/-- Potential-outcome setup plus the mean-independence consequence of CIA. -/
structure PotentialOutcomeMeanIndependentSetup
    (μ : Measure Ω) (Y0 Y1 : Ω → ℝ) (D : Ω → Bool) (X : Ω → β)
    extends PotentialOutcomeSetup μ Y0 Y1 D X where
  /-- Conditioning additionally on treatment does not change potential-outcome means. -/
  mean_independent : TreatmentMeanIndependentOn μ Y0 Y1 D X

namespace PotentialOutcomeSetup

/-- Average treatment effect as the difference of potential-outcome means. -/
theorem ate_eq_integral_sub
    {Y0 Y1 : Ω → ℝ} {D : Ω → Bool} {X : Ω → β}
    (h : PotentialOutcomeSetup μ Y0 Y1 D X) :
    averageTreatmentEffect μ Y0 Y1 = ∫ ω, Y1 ω ∂μ - ∫ ω, Y0 ω ∂μ :=
  averageTreatmentEffect_eq_integral_sub
    (μ := μ) h.treated_integrable h.untreated_integrable

/-- CATE equals the difference in conditional potential-outcome means. -/
theorem cate_eq_sub
    {Y0 Y1 : Ω → ℝ} {D : Ω → Bool} {X : Ω → β}
    (h : PotentialOutcomeSetup μ Y0 Y1 D X) :
    conditionalAverageTreatmentEffectOn μ Y0 Y1 X =ᵐ[μ]
      fun ω => potentialOutcomeMeanOn μ Y1 X ω - potentialOutcomeMeanOn μ Y0 X ω :=
  conditionalAverageTreatmentEffectOn_eq_sub
    (μ := μ) (X := X) h.treated_integrable h.untreated_integrable

/-- CATE equals the reusable contrast between conditional potential-outcome means. -/
theorem cate_eq_conditional_contrast
    {Y0 Y1 : Ω → ℝ} {D : Ω → Bool} {X : Ω → β}
    (h : PotentialOutcomeSetup μ Y0 Y1 D X) :
    conditionalAverageTreatmentEffectOn μ Y0 Y1 X =ᵐ[μ]
      conditionalPotentialOutcomeContrastOn μ Y0 Y1 X :=
  conditionalAverageTreatmentEffectOn_eq_conditionalPotentialOutcomeContrastOn
    (μ := μ) (X := X) h.treated_integrable h.untreated_integrable

/-- Pullback bridge from pointwise potential-outcome means to the CATE. -/
theorem cate_eq_surface
    {Y0 Y1 : Ω → ℝ} {D : Ω → Bool} {X : Ω → β} {m0 m1 : β → ℝ}
    (h : PotentialOutcomeSetup μ Y0 Y1 D X)
    (hm1 : potentialOutcomeMeanOn μ Y1 X =ᵐ[μ] fun ω => m1 (X ω))
    (hm0 : potentialOutcomeMeanOn μ Y0 X =ᵐ[μ] fun ω => m0 (X ω)) :
    conditionalAverageTreatmentEffectOn μ Y0 Y1 X =ᵐ[μ]
      fun ω => conditionalAverageTreatmentEffectSurface m0 m1 (X ω) :=
  conditionalAverageTreatmentEffectOn_eq_surface
    (μ := μ) h.treated_integrable h.untreated_integrable hm1 hm0

/-- CATE bridge written as the treatment contrast of an observed-regression surface. -/
theorem cate_eq_observed_contrast_surface
    {Y0 Y1 : Ω → ℝ} {D : Ω → Bool} {X : Ω → β} {m0 m1 : β → ℝ}
    (h : PotentialOutcomeSetup μ Y0 Y1 D X)
    (hm1 : potentialOutcomeMeanOn μ Y1 X =ᵐ[μ] fun ω => m1 (X ω))
    (hm0 : potentialOutcomeMeanOn μ Y0 X =ᵐ[μ] fun ω => m0 (X ω)) :
    conditionalAverageTreatmentEffectOn μ Y0 Y1 X =ᵐ[μ]
      fun ω =>
        observedRegressionTreatmentContrastSurface (observedRegressionSurface m0 m1) (X ω) :=
  conditionalAverageTreatmentEffectOn_eq_observedRegressionTreatmentContrastSurface
    (μ := μ) h.treated_integrable h.untreated_integrable hm1 hm0

/-- Observed-outcome conditional mean given treatment and covariates splits by treatment branch. -/
theorem observed_condExp_branch
    {Y0 Y1 : Ω → ℝ} {D : Ω → Bool} {X : Ω → β}
    (h : PotentialOutcomeSetup μ Y0 Y1 D X) :
    condExpOn μ (observedOutcome D Y0 Y1) (fun ω => (D ω, X ω)) =ᵐ[μ]
      fun ω =>
        if D ω then
          condExpOn μ Y1 (fun ω => (D ω, X ω)) ω
        else
          condExpOn μ Y0 (fun ω => (D ω, X ω)) ω :=
  condExpOn_observedOutcome_treatment_covariates_eq_branch
    (μ := μ) h.treatment_measurable h.treated_integrable h.untreated_integrable

/-- The ATE is the mean of the CATE. -/
theorem ate_eq_integral_cate
    {Y0 Y1 : Ω → ℝ} {D : Ω → Bool} {X : Ω → β}
    (h : PotentialOutcomeSetup μ Y0 Y1 D X) :
    averageTreatmentEffect μ Y0 Y1 =
      ∫ ω, conditionalAverageTreatmentEffectOn μ Y0 Y1 X ω ∂μ := by
  haveI : SigmaFinite (μ.trim (conditioningSpace_le h.covariates_measurable)) :=
    h.sigmaFinite_covariates
  exact averageTreatmentEffect_eq_integral_conditionalAverageTreatmentEffectOn
    (μ := μ) h.covariates_measurable

/-- The ATE is also the mean of the conditional potential-outcome contrast. -/
theorem ate_eq_integral_contrast
    {Y0 Y1 : Ω → ℝ} {D : Ω → Bool} {X : Ω → β}
    (h : PotentialOutcomeSetup μ Y0 Y1 D X) :
    averageTreatmentEffect μ Y0 Y1 =
      ∫ ω, conditionalPotentialOutcomeContrastOn μ Y0 Y1 X ω ∂μ := by
  haveI : SigmaFinite (μ.trim (conditioningSpace_le h.covariates_measurable)) :=
    h.sigmaFinite_covariates
  exact averageTreatmentEffect_eq_integral_conditionalPotentialOutcomeContrastOn
    (μ := μ) h.covariates_measurable h.treated_integrable h.untreated_integrable

end PotentialOutcomeSetup

namespace PotentialOutcomeMeanIndependentSetup

/-- Forget mean independence to the basic potential-outcome setup. -/
abbrev toSetup
    {Y0 Y1 : Ω → ℝ} {D : Ω → Bool} {X : Ω → β}
    (h : PotentialOutcomeMeanIndependentSetup μ Y0 Y1 D X) :
    PotentialOutcomeSetup μ Y0 Y1 D X :=
  h.toPotentialOutcomeSetup

/-- Observed-regression branch identity under mean independence. -/
theorem observed_condExp_branch
    {Y0 Y1 : Ω → ℝ} {D : Ω → Bool} {X : Ω → β}
    (h : PotentialOutcomeMeanIndependentSetup μ Y0 Y1 D X) :
    condExpOn μ (observedOutcome D Y0 Y1) (fun ω => (D ω, X ω)) =ᵐ[μ]
      fun ω =>
        if D ω then
          potentialOutcomeMeanOn μ Y1 X ω
        else
          potentialOutcomeMeanOn μ Y0 X ω :=
  condExpOn_observedOutcome_treatment_covariates_eq_branch_of_meanIndependent
    (μ := μ) h.mean_independent h.treatment_measurable
    h.treated_integrable h.untreated_integrable

/-- Surface version of the observed-regression bridge under mean independence. -/
theorem observed_condExp_surface
    {Y0 Y1 : Ω → ℝ} {D : Ω → Bool} {X : Ω → β} {m0 m1 : β → ℝ}
    (h : PotentialOutcomeMeanIndependentSetup μ Y0 Y1 D X)
    (hm1 : potentialOutcomeMeanOn μ Y1 X =ᵐ[μ] fun ω => m1 (X ω))
    (hm0 : potentialOutcomeMeanOn μ Y0 X =ᵐ[μ] fun ω => m0 (X ω)) :
    condExpOn μ (observedOutcome D Y0 Y1) (fun ω => (D ω, X ω)) =ᵐ[μ]
      fun ω => observedRegressionSurface m0 m1 (D ω, X ω) :=
  condExpOn_observedOutcome_treatment_covariates_eq_surface_of_meanIndependent
    (μ := μ) h.mean_independent h.treatment_measurable
    h.treated_integrable h.untreated_integrable hm1 hm0

/-- Adding treatment to the conditioning variables does not change the potential-outcome
contrast. -/
theorem treatment_covariates_contrast_eq
    {Y0 Y1 : Ω → ℝ} {D : Ω → Bool} {X : Ω → β}
    (h : PotentialOutcomeMeanIndependentSetup μ Y0 Y1 D X) :
    conditionalPotentialOutcomeContrastOn μ Y0 Y1 (fun ω => (D ω, X ω)) =ᵐ[μ]
      conditionalPotentialOutcomeContrastOn μ Y0 Y1 X :=
  conditionalPotentialOutcomeContrastOn_treatment_covariates_eq_of_meanIndependent
    (μ := μ) h.mean_independent

/-- Treatment-and-covariate potential-outcome contrast equals the CATE. -/
theorem treatment_covariates_contrast_eq_cate
    {Y0 Y1 : Ω → ℝ} {D : Ω → Bool} {X : Ω → β}
    (h : PotentialOutcomeMeanIndependentSetup μ Y0 Y1 D X) :
    conditionalPotentialOutcomeContrastOn μ Y0 Y1 (fun ω => (D ω, X ω)) =ᵐ[μ]
      conditionalAverageTreatmentEffectOn μ Y0 Y1 X :=
  conditionalPotentialOutcomeContrastOn_treatment_covariates_eq_cate_of_meanIndependent
    (μ := μ) h.mean_independent h.treated_integrable h.untreated_integrable

/-- Conditioning the treatment effect on `(D, X)` gives the same CATE as conditioning on `X`. -/
theorem treatment_covariates_cate_eq
    {Y0 Y1 : Ω → ℝ} {D : Ω → Bool} {X : Ω → β}
    (h : PotentialOutcomeMeanIndependentSetup μ Y0 Y1 D X) :
    conditionalAverageTreatmentEffectOn μ Y0 Y1 (fun ω => (D ω, X ω)) =ᵐ[μ]
      conditionalAverageTreatmentEffectOn μ Y0 Y1 X :=
  conditionalAverageTreatmentEffectOn_treatment_covariates_eq_of_meanIndependent
    (μ := μ) h.mean_independent h.treated_integrable h.untreated_integrable

end PotentialOutcomeMeanIndependentSetup

namespace PotentialOutcomeCIAOn

/-- Conditional independence supplies the basic setup fields. -/
def toPotentialOutcomeSetup
    [StandardBorelSpace Ω] [IsFiniteMeasure μ]
    {Y0 Y1 : Ω → ℝ} {D : Ω → Bool} {X : Ω → β}
    (h : PotentialOutcomeCIAOn μ Y0 Y1 D X) :
    PotentialOutcomeSetup μ Y0 Y1 D X where
  covariates_measurable := h.x_measurable
  treatment_measurable := h.d_measurable
  sigmaFinite_covariates := inferInstance
  untreated_integrable := h.y0_integrable
  treated_integrable := h.y1_integrable

/-- Conditional independence supplies the mean-independent setup surface. -/
def toPotentialOutcomeMeanIndependentSetup
    [StandardBorelSpace Ω] [IsFiniteMeasure μ]
    {Y0 Y1 : Ω → ℝ} {D : Ω → Bool} {X : Ω → β}
    (h : PotentialOutcomeCIAOn μ Y0 Y1 D X) :
    PotentialOutcomeMeanIndependentSetup μ Y0 Y1 D X where
  toPotentialOutcomeSetup := h.toPotentialOutcomeSetup
  mean_independent := h.toTreatmentMeanIndependentOn

/-- CIA-facing observed-regression branch identity as a setup method. -/
theorem condExpOn_observedOutcome_treatment_covariates_eq_branch_setup
    [StandardBorelSpace Ω] [IsFiniteMeasure μ]
    {Y0 Y1 : Ω → ℝ} {D : Ω → Bool} {X : Ω → β}
    (h : PotentialOutcomeCIAOn μ Y0 Y1 D X) :
    condExpOn μ (observedOutcome D Y0 Y1) (fun ω => (D ω, X ω)) =ᵐ[μ]
      fun ω =>
        if D ω then
          potentialOutcomeMeanOn μ Y1 X ω
        else
          potentialOutcomeMeanOn μ Y0 X ω :=
  h.toPotentialOutcomeMeanIndependentSetup.observed_condExp_branch

/-- CIA-facing observed-regression surface identity as a setup method. -/
theorem condExpOn_observedOutcome_treatment_covariates_eq_surface_setup
    [StandardBorelSpace Ω] [IsFiniteMeasure μ]
    {Y0 Y1 : Ω → ℝ} {D : Ω → Bool} {X : Ω → β} {m0 m1 : β → ℝ}
    (h : PotentialOutcomeCIAOn μ Y0 Y1 D X)
    (hm1 : potentialOutcomeMeanOn μ Y1 X =ᵐ[μ] fun ω => m1 (X ω))
    (hm0 : potentialOutcomeMeanOn μ Y0 X =ᵐ[μ] fun ω => m0 (X ω)) :
    condExpOn μ (observedOutcome D Y0 Y1) (fun ω => (D ω, X ω)) =ᵐ[μ]
      fun ω => observedRegressionSurface m0 m1 (D ω, X ω) :=
  h.toPotentialOutcomeMeanIndependentSetup.observed_condExp_surface
    hm1 hm0

end PotentialOutcomeCIAOn

end HansenEconometrics
