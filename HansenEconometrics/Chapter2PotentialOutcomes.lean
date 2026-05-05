import HansenEconometrics.Chapter2CondExp

/-!
# Chapter 2 Potential Outcomes

This file starts the variable-facing potential-outcomes API for Hansen Section 2.30.
The first public surface is stated as random-variable and almost-everywhere identities, matching the
Chapter 2 probability layer. Pointwise regular-conditional-distribution versions of Theorem 2.12 can
be built on top of this layer later.
-/

open scoped ENNReal Topology MeasureTheory ProbabilityTheory
open MeasureTheory ProbabilityTheory

namespace HansenEconometrics

variable {Ω β : Type*}

/-- Hansen Section 2.30 observed outcome for a binary treatment:
`Y = Y(1)` on treated units and `Y = Y(0)` on untreated units. -/
def observedOutcome (D : Ω → Bool) (Y0 Y1 : Ω → ℝ) : Ω → ℝ :=
  fun ω => if D ω then Y1 ω else Y0 ω

/-- Hansen Definition 2.6: individual treatment effect `Y(1) - Y(0)`. -/
def treatmentEffect (Y0 Y1 : Ω → ℝ) : Ω → ℝ :=
  fun ω => Y1 ω - Y0 ω

@[simp] theorem observedOutcome_true (Y0 Y1 : Ω → ℝ) :
    observedOutcome (fun _ => true) Y0 Y1 = Y1 := by
  funext ω
  simp [observedOutcome]

@[simp] theorem observedOutcome_false (Y0 Y1 : Ω → ℝ) :
    observedOutcome (fun _ => false) Y0 Y1 = Y0 := by
  funext ω
  simp [observedOutcome]

@[simp] theorem observedOutcome_of_treated
    {D : Ω → Bool} {Y0 Y1 : Ω → ℝ} {ω : Ω} (hD : D ω = true) :
    observedOutcome D Y0 Y1 ω = Y1 ω := by
  simp [observedOutcome, hD]

@[simp] theorem observedOutcome_of_untreated
    {D : Ω → Bool} {Y0 Y1 : Ω → ℝ} {ω : Ω} (hD : D ω = false) :
    observedOutcome D Y0 Y1 ω = Y0 ω := by
  simp [observedOutcome, hD]

@[simp] theorem treatmentEffect_eq_sub (Y0 Y1 : Ω → ℝ) :
    treatmentEffect Y0 Y1 = fun ω => Y1 ω - Y0 ω := rfl

section Probability

variable [MeasurableSpace Ω] [MeasurableSpace β]
variable {μ : Measure Ω}

/-- Average treatment effect: the population mean of the individual treatment effect.
Hansen Definition 2.7 calls this the average causal effect, `ACE`. -/
noncomputable def averageTreatmentEffect (μ : Measure Ω) (Y0 Y1 : Ω → ℝ) : ℝ :=
  ∫ ω, treatmentEffect Y0 Y1 ω ∂μ

/-- Conditional mean of a potential outcome after conditioning on observed covariates. -/
noncomputable def potentialOutcomeMeanOn
    (μ : Measure Ω) (Yd : Ω → ℝ) (X : Ω → β) : Ω → ℝ :=
  condExpOn μ Yd X

/-- Conditional average treatment effect after conditioning on observed covariates.
Hansen Definition 2.8 writes this as the conditional average causal effect, `ACE(x)`. -/
noncomputable def conditionalAverageTreatmentEffectOn
    (μ : Measure Ω) (Y0 Y1 : Ω → ℝ) (X : Ω → β) : Ω → ℝ :=
  condExpOn μ (treatmentEffect Y0 Y1) X

/-- Difference between the conditional means of the treated and untreated potential outcomes. -/
noncomputable def conditionalPotentialOutcomeContrastOn
    (μ : Measure Ω) (Y0 Y1 : Ω → ℝ) (X : Ω → β) : Ω → ℝ :=
  fun ω => potentialOutcomeMeanOn μ Y1 X ω - potentialOutcomeMeanOn μ Y0 X ω

/-- A mean-independence bridge toward Hansen's conditional-independence assumption:
conditioning on treatment and covariates gives the same potential-outcome conditional means as
conditioning on covariates alone. CIA implies this condition under standard integrability and
regular-conditional-probability hypotheses. -/
def TreatmentMeanIndependentOn
    (μ : Measure Ω) (Y0 Y1 : Ω → ℝ) (D : Ω → Bool) (X : Ω → β) : Prop :=
  condExpOn μ Y0 (fun ω => (D ω, X ω)) =ᵐ[μ] condExpOn μ Y0 X ∧
    condExpOn μ Y1 (fun ω => (D ω, X ω)) =ᵐ[μ] condExpOn μ Y1 X

/-- The average treatment effect is the difference in the means of the two potential outcomes.
Hansen writes this quantity as `ACE`. -/
theorem averageTreatmentEffect_eq_integral_sub
    {Y0 Y1 : Ω → ℝ}
    (hY1 : Integrable Y1 μ) (hY0 : Integrable Y0 μ) :
    averageTreatmentEffect μ Y0 Y1 = ∫ ω, Y1 ω ∂μ - ∫ ω, Y0 ω ∂μ := by
  simp [averageTreatmentEffect, treatmentEffect, integral_sub hY1 hY0]

/-- Conditional average treatment effects are the difference in conditional means of the two
potential outcomes. Hansen writes this quantity as `ACE(x)`. -/
theorem conditionalAverageTreatmentEffectOn_eq_sub
    {Y0 Y1 : Ω → ℝ} {X : Ω → β}
    (hY1 : Integrable Y1 μ) (hY0 : Integrable Y0 μ) :
    conditionalAverageTreatmentEffectOn μ Y0 Y1 X =ᵐ[μ]
      fun ω => potentialOutcomeMeanOn μ Y1 X ω - potentialOutcomeMeanOn μ Y0 X ω := by
  simpa [conditionalAverageTreatmentEffectOn, potentialOutcomeMeanOn,
      treatmentEffect, condExpOn] using
    (MeasureTheory.condExp_sub
      (μ := μ) (f := Y1) (g := Y0) hY1 hY0 (conditioningSpace X))

/-- CATE equals the reusable contrast between conditional potential-outcome means. -/
theorem conditionalAverageTreatmentEffectOn_eq_conditionalPotentialOutcomeContrastOn
    {Y0 Y1 : Ω → ℝ} {X : Ω → β}
    (hY1 : Integrable Y1 μ) (hY0 : Integrable Y0 μ) :
    conditionalAverageTreatmentEffectOn μ Y0 Y1 X =ᵐ[μ]
      conditionalPotentialOutcomeContrastOn μ Y0 Y1 X := by
  simpa [conditionalPotentialOutcomeContrastOn] using
    conditionalAverageTreatmentEffectOn_eq_sub (μ := μ) (X := X) hY1 hY0

/-- The average treatment effect is the mean of the CATE. Hansen writes this as the identity
`ACE = ∫ ACE(x) f(x) dx`; this is the potential-outcomes version of the tower property. -/
theorem averageTreatmentEffect_eq_integral_conditionalAverageTreatmentEffectOn
    {Y0 Y1 : Ω → ℝ} {X : Ω → β}
    (hX : Measurable X)
    [SigmaFinite (μ.trim (conditioningSpace_le hX))] :
    averageTreatmentEffect μ Y0 Y1 =
      ∫ ω, conditionalAverageTreatmentEffectOn μ Y0 Y1 X ω ∂μ := by
  exact
    (simple_law_iterated_expectation_rv
      (μ := μ) (Y := treatmentEffect Y0 Y1) (X := X) hX).symm

/-- The average treatment effect is also the mean of the conditional potential-outcome contrast.
This is the a.e. Lean version of Hansen's identity `ACE = ∫ ACE(x) f(x) dx` after rewriting
the CATE as a difference of conditional potential-outcome means. -/
theorem averageTreatmentEffect_eq_integral_conditionalPotentialOutcomeContrastOn
    {Y0 Y1 : Ω → ℝ} {X : Ω → β}
    (hX : Measurable X)
    [SigmaFinite (μ.trim (conditioningSpace_le hX))]
    (hY1 : Integrable Y1 μ) (hY0 : Integrable Y0 μ) :
    averageTreatmentEffect μ Y0 Y1 =
      ∫ ω, conditionalPotentialOutcomeContrastOn μ Y0 Y1 X ω ∂μ := by
  rw [averageTreatmentEffect_eq_integral_conditionalAverageTreatmentEffectOn (μ := μ) hX]
  exact integral_congr_ae
    (conditionalAverageTreatmentEffectOn_eq_conditionalPotentialOutcomeContrastOn
      (μ := μ) (X := X) hY1 hY0)

/-- If treatment is mean-independent of potential outcomes after conditioning on `X`, then adding
the treatment indicator to the conditioning variables does not change the conditional
potential-outcome contrast. -/
theorem conditionalPotentialOutcomeContrastOn_treatment_covariates_eq_of_meanIndependent
    {Y0 Y1 : Ω → ℝ} {D : Ω → Bool} {X : Ω → β}
    (hmean : TreatmentMeanIndependentOn μ Y0 Y1 D X) :
    conditionalPotentialOutcomeContrastOn μ Y0 Y1 (fun ω => (D ω, X ω)) =ᵐ[μ]
      conditionalPotentialOutcomeContrastOn μ Y0 Y1 X := by
  filter_upwards [hmean.2, hmean.1] with ω hY1 hY0
  simp [conditionalPotentialOutcomeContrastOn, potentialOutcomeMeanOn, hY1, hY0]

/-- Mean-independence bridge for the variable-facing version of Hansen Theorem 2.12. Under the
mean-independence consequence of CIA, the potential-outcome contrast after conditioning on
`(D, X)` equals the conditional average treatment effect after conditioning on `X`. -/
theorem conditionalPotentialOutcomeContrastOn_treatment_covariates_eq_cate_of_meanIndependent
    {Y0 Y1 : Ω → ℝ} {D : Ω → Bool} {X : Ω → β}
    (hmean : TreatmentMeanIndependentOn μ Y0 Y1 D X)
    (hY1 : Integrable Y1 μ) (hY0 : Integrable Y0 μ) :
    conditionalPotentialOutcomeContrastOn μ Y0 Y1 (fun ω => (D ω, X ω)) =ᵐ[μ]
      conditionalAverageTreatmentEffectOn μ Y0 Y1 X :=
  (conditionalPotentialOutcomeContrastOn_treatment_covariates_eq_of_meanIndependent
    (μ := μ) hmean).trans <|
      (conditionalAverageTreatmentEffectOn_eq_conditionalPotentialOutcomeContrastOn
        (μ := μ) (X := X) hY1 hY0).symm

end Probability

end HansenEconometrics
