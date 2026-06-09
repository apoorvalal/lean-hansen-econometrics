import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator
import Mathlib.Probability.Independence.Conditional
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

/-- Pointwise covariate-surface notation for Hansen's conditional average causal effect.

When `m0 x` and `m1 x` are versions of the conditional means
`E[Y(0) | X = x]` and `E[Y(1) | X = x]`, this is the surface
`ACE(x) = m1(x) - m0(x)`. -/
def conditionalAverageTreatmentEffectSurface (m0 m1 : β → ℝ) : β → ℝ :=
  fun x => m1 x - m0 x

@[simp] theorem conditionalAverageTreatmentEffectSurface_apply
    (m0 m1 : β → ℝ) (x : β) :
    conditionalAverageTreatmentEffectSurface m0 m1 x = m1 x - m0 x :=
  rfl

/-- Pointwise observed-outcome regression surface for binary treatment.

`observedRegressionSurface m0 m1 (d, x)` is Hansen's `m(d,x)` when the untreated and treated
branches are represented by the supplied covariate surfaces `m0` and `m1`. -/
def observedRegressionSurface (m0 m1 : β → ℝ) : Bool × β → ℝ :=
  fun z => if z.1 then m1 z.2 else m0 z.2

@[simp] theorem observedRegressionSurface_true (m0 m1 : β → ℝ) (x : β) :
    observedRegressionSurface m0 m1 (true, x) = m1 x :=
  rfl

@[simp] theorem observedRegressionSurface_false (m0 m1 : β → ℝ) (x : β) :
    observedRegressionSurface m0 m1 (false, x) = m0 x :=
  rfl

/-- Pointwise treatment contrast of an observed-regression surface: `m(1,x)-m(0,x)`. -/
def observedRegressionTreatmentContrastSurface (m : Bool × β → ℝ) : β → ℝ :=
  fun x => m (true, x) - m (false, x)

@[simp] theorem observedRegressionTreatmentContrastSurface_apply
    (m : Bool × β → ℝ) (x : β) :
    observedRegressionTreatmentContrastSurface m x = m (true, x) - m (false, x) :=
  rfl

/-- For a two-branch observed-regression surface, the pointwise treatment contrast is `ACE(x)`. -/
@[simp] theorem observedRegressionTreatmentContrastSurface_observedRegressionSurface
    (m0 m1 : β → ℝ) :
    observedRegressionTreatmentContrastSurface (observedRegressionSurface m0 m1) =
      conditionalAverageTreatmentEffectSurface m0 m1 := by
  funext x
  simp [observedRegressionTreatmentContrastSurface, conditionalAverageTreatmentEffectSurface]

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

omit [MeasurableSpace Ω] in
private theorem treatmentSet_measurable_conditioningSpace_pair
    {D : Ω → Bool} {X : Ω → β} :
    MeasurableSet[conditioningSpace (fun ω => (D ω, X ω))] {ω | D ω = true} := by
  have hD_le : conditioningSpace D ≤ conditioningSpace (fun ω => (D ω, X ω)) := by
    exact conditioningSpace_le_of_factor
      (X₁ := D) (X₂ := fun ω => (D ω, X ω)) (f := Prod.fst) measurable_fst rfl
  exact hD_le _ ((Measurable.of_comap_le le_rfl) (measurableSet_singleton true))

omit [MeasurableSpace Ω] in
private theorem observedOutcome_eq_indicator_add_compl
    {D : Ω → Bool} {Y0 Y1 : Ω → ℝ} :
    observedOutcome D Y0 Y1 =
      fun ω => ({ω | D ω = true}.indicator Y1) ω +
        ({ω | D ω = true}ᶜ.indicator Y0) ω := by
  funext ω
  by_cases hD : D ω = true
  · simp [observedOutcome, hD]
  · simp [observedOutcome, hD]

/-- Hansen Definition 2.9, variable-facing conditional independence assumption.

This package records the conditional independence of treatment and each potential outcome after
conditioning on covariates, together with the measurability and integrability hypotheses needed to
turn that conditional-independence statement into the mean-independence bridge used by the CATE
theorems below. -/
structure PotentialOutcomeCIAOn
    [StandardBorelSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (Y0 Y1 : Ω → ℝ) (D : Ω → Bool) (X : Ω → β) : Prop where
  /-- Covariates are measurable. -/
  x_measurable : Measurable X
  /-- Treatment is measurable. -/
  d_measurable : Measurable D
  /-- Untreated potential outcome is measurable. -/
  y0_measurable : Measurable Y0
  /-- Treated potential outcome is measurable. -/
  y1_measurable : Measurable Y1
  /-- Untreated potential outcome is integrable. -/
  y0_integrable : Integrable Y0 μ
  /-- Treated potential outcome is integrable. -/
  y1_integrable : Integrable Y1 μ
  /-- Treatment and the untreated potential outcome are conditionally independent given `X`. -/
  condIndep_y0 : D ⟂ᵢ[X, x_measurable; μ] Y0
  /-- Treatment and the treated potential outcome are conditionally independent given `X`. -/
  condIndep_y1 : D ⟂ᵢ[X, x_measurable; μ] Y1

omit [MeasurableSpace Ω] in
private theorem conditioningSpace_pair_comm
    {D : Ω → Bool} {X : Ω → β} :
    conditioningSpace (fun ω => (D ω, X ω)) =
      conditioningSpace (fun ω => (X ω, D ω)) := by
  unfold conditioningSpace
  change MeasurableSpace.comap (fun ω => (D ω, X ω))
      ((inferInstance : MeasurableSpace Bool).prod (inferInstance : MeasurableSpace β)) =
    MeasurableSpace.comap (fun ω => (X ω, D ω))
      ((inferInstance : MeasurableSpace β).prod (inferInstance : MeasurableSpace Bool))
  rw [MeasurableSpace.comap_prodMk, MeasurableSpace.comap_prodMk, sup_comm]

private theorem condExpOn_covariate_treatment_eq_of_condIndep
    [StandardBorelSpace Ω] [IsFiniteMeasure μ]
    {Y : Ω → ℝ} {D : Ω → Bool} {X : Ω → β}
    (hX : Measurable X) (hD : Measurable D) (hYmeas : Measurable Y)
    (hYint : Integrable Y μ)
    (hcond : D ⟂ᵢ[X, hX; μ] Y) :
    condExpOn μ Y (fun ω => (X ω, D ω)) =ᵐ[μ] condExpOn μ Y X := by
  have hpair : Measurable (fun ω => (X ω, D ω)) := hX.prod hD
  have hkernel_map :
      condDistrib Y (fun ω => (X ω, D ω)) μ =ᵐ[μ.map (fun ω => (X ω, D ω))]
        (condDistrib Y X μ).prodMkRight Bool := by
    exact (condIndepFun_iff_condDistrib_prod_ae_eq_prodMkRight
      (f := Y) (g := D) (k := X) hYmeas hD hX).mp hcond
  have hkernel :
      ∀ᵐ ω ∂μ, condDistrib Y (fun ω => (X ω, D ω)) μ (X ω, D ω) =
        (condDistrib Y X μ).prodMkRight Bool (X ω, D ω) :=
    ae_of_ae_map hpair.aemeasurable hkernel_map
  have hpair_ce :
      condExpOn μ Y (fun ω => (X ω, D ω)) =ᵐ[μ]
        fun ω => ∫ y, y ∂condDistrib Y (fun ω => (X ω, D ω)) μ (X ω, D ω) := by
    simpa [condExpOn, conditioningSpace] using
      (condExp_ae_eq_integral_condDistrib'
        (X := fun ω => (X ω, D ω)) (Y := Y) (μ := μ) hpair hYint)
  have hX_ce :
      condExpOn μ Y X =ᵐ[μ]
        fun ω => ∫ y, y ∂condDistrib Y X μ (X ω) := by
    simpa [condExpOn, conditioningSpace] using
      (condExp_ae_eq_integral_condDistrib'
        (X := X) (Y := Y) (μ := μ) hX hYint)
  have hintegral :
      (fun ω => ∫ y, y ∂condDistrib Y (fun ω => (X ω, D ω)) μ (X ω, D ω)) =ᵐ[μ]
        fun ω => ∫ y, y ∂condDistrib Y X μ (X ω) := by
    filter_upwards [hkernel] with ω hω
    rw [hω]
    rfl
  exact hpair_ce.trans (hintegral.trans hX_ce.symm)

/-- Conditional independence of treatment and each potential outcome given `X` implies the
mean-independence bridge used by the variable-facing CATE theorems. -/
theorem PotentialOutcomeCIAOn.toTreatmentMeanIndependentOn
    [StandardBorelSpace Ω] [IsFiniteMeasure μ]
    {Y0 Y1 : Ω → ℝ} {D : Ω → Bool} {X : Ω → β}
    (hcia : PotentialOutcomeCIAOn μ Y0 Y1 D X) :
    TreatmentMeanIndependentOn μ Y0 Y1 D X := by
  constructor
  · have hXD := condExpOn_covariate_treatment_eq_of_condIndep
      (μ := μ) (Y := Y0) (D := D) (X := X)
      hcia.x_measurable hcia.d_measurable hcia.y0_measurable hcia.y0_integrable
      hcia.condIndep_y0
    simpa [condExpOn, conditioningSpace_pair_comm] using hXD
  · have hXD := condExpOn_covariate_treatment_eq_of_condIndep
      (μ := μ) (Y := Y1) (D := D) (X := X)
      hcia.x_measurable hcia.d_measurable hcia.y1_measurable hcia.y1_integrable
      hcia.condIndep_y1
    simpa [condExpOn, conditioningSpace_pair_comm] using hXD

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

/-- Pullback bridge from a pointwise `ACE(x)` surface to the variable-facing CATE.

This is the a.e. Lean version of replacing Hansen's pointwise notation by a chosen pair of
conditional-mean versions `m0` and `m1`, pulled back along the observed covariates. -/
theorem conditionalAverageTreatmentEffectOn_eq_surface
    {Y0 Y1 : Ω → ℝ} {X : Ω → β} {m0 m1 : β → ℝ}
    (hY1 : Integrable Y1 μ) (hY0 : Integrable Y0 μ)
    (hm1 : potentialOutcomeMeanOn μ Y1 X =ᵐ[μ] fun ω => m1 (X ω))
    (hm0 : potentialOutcomeMeanOn μ Y0 X =ᵐ[μ] fun ω => m0 (X ω)) :
    conditionalAverageTreatmentEffectOn μ Y0 Y1 X =ᵐ[μ]
      fun ω => conditionalAverageTreatmentEffectSurface m0 m1 (X ω) := by
  filter_upwards
    [conditionalAverageTreatmentEffectOn_eq_conditionalPotentialOutcomeContrastOn
      (μ := μ) (X := X) hY1 hY0, hm1, hm0]
    with ω hcate h1 h0
  rw [hcate]
  simp [conditionalPotentialOutcomeContrastOn, conditionalAverageTreatmentEffectSurface, h1, h0]

/-- The same pointwise `ACE(x)` bridge written as `m(1,x)-m(0,x)` for the observed-regression
surface generated by the two potential-outcome conditional-mean versions. -/
theorem conditionalAverageTreatmentEffectOn_eq_observedRegressionTreatmentContrastSurface
    {Y0 Y1 : Ω → ℝ} {X : Ω → β} {m0 m1 : β → ℝ}
    (hY1 : Integrable Y1 μ) (hY0 : Integrable Y0 μ)
    (hm1 : potentialOutcomeMeanOn μ Y1 X =ᵐ[μ] fun ω => m1 (X ω))
    (hm0 : potentialOutcomeMeanOn μ Y0 X =ᵐ[μ] fun ω => m0 (X ω)) :
    conditionalAverageTreatmentEffectOn μ Y0 Y1 X =ᵐ[μ]
      fun ω =>
        observedRegressionTreatmentContrastSurface (observedRegressionSurface m0 m1) (X ω) := by
  simpa using
    conditionalAverageTreatmentEffectOn_eq_surface
      (μ := μ) (X := X) hY1 hY0 hm1 hm0

/-- The observed-outcome conditional mean given treatment and covariates splits into the
corresponding potential-outcome conditional mean on each treatment branch. This is the
variable/a.e. regression-surface form behind Hansen's notation `m(d, x) = E[Y | D = d, X = x]`. -/
theorem condExpOn_observedOutcome_treatment_covariates_eq_branch
    {Y0 Y1 : Ω → ℝ} {D : Ω → Bool} {X : Ω → β}
    (hD : Measurable D) (hY1 : Integrable Y1 μ) (hY0 : Integrable Y0 μ) :
    condExpOn μ (observedOutcome D Y0 Y1) (fun ω => (D ω, X ω)) =ᵐ[μ]
      fun ω =>
        if D ω then
          condExpOn μ Y1 (fun ω => (D ω, X ω)) ω
        else
          condExpOn μ Y0 (fun ω => (D ω, X ω)) ω := by
  let Z : Ω → Bool × β := fun ω => (D ω, X ω)
  let s : Set Ω := {ω | D ω = true}
  have hs : MeasurableSet s := hD (measurableSet_singleton true)
  let mZ := conditioningSpace Z
  have hs_m : MeasurableSet[mZ] s := by
    simpa [mZ, Z, s] using
      (treatmentSet_measurable_conditioningSpace_pair (D := D) (X := X))
  have hY1_ind : Integrable (s.indicator Y1) μ := hY1.indicator hs
  have hY0_ind : Integrable (sᶜ.indicator Y0) μ := hY0.indicator hs.compl
  have hadd :
      μ[(fun ω => s.indicator Y1 ω + sᶜ.indicator Y0 ω) | mZ] =ᵐ[μ]
        μ[s.indicator Y1 | mZ] + μ[sᶜ.indicator Y0 | mZ] := by
    simpa using
      (MeasureTheory.condExp_add
        (μ := μ) (f := s.indicator Y1) (g := sᶜ.indicator Y0) hY1_ind hY0_ind mZ)
  have htreated :
      μ[s.indicator Y1 | mZ] =ᵐ[μ] s.indicator (μ[Y1 | mZ]) :=
    MeasureTheory.condExp_indicator (μ := μ) (m := mZ) (f := Y1) (s := s) hY1 hs_m
  have huntreated :
      μ[sᶜ.indicator Y0 | mZ] =ᵐ[μ] sᶜ.indicator (μ[Y0 | mZ]) :=
    MeasureTheory.condExp_indicator
      (μ := μ) (m := mZ) (f := Y0) (s := sᶜ) hY0 hs_m.compl
  have hbranch :
      μ[(fun ω => s.indicator Y1 ω + sᶜ.indicator Y0 ω) | mZ] =ᵐ[μ]
        fun ω => if D ω then μ[Y1 | mZ] ω else μ[Y0 | mZ] ω := by
    filter_upwards [hadd, htreated, huntreated] with ω haddω htreatedω huntreatedω
    rw [haddω]
    change μ[s.indicator Y1 | mZ] ω + μ[sᶜ.indicator Y0 | mZ] ω =
      if D ω then μ[Y1 | mZ] ω else μ[Y0 | mZ] ω
    rw [htreatedω, huntreatedω]
    by_cases hDω : D ω = true
    · simp [s, hDω]
    · simp [s, hDω]
  simpa [condExpOn, Z, mZ, s, observedOutcome_eq_indicator_add_compl] using hbranch

/-- Under the mean-independence consequence of CIA, the observed-outcome regression on treatment
and covariates uses the `X`-conditioned treated potential-outcome mean on treated units and the
`X`-conditioned untreated potential-outcome mean on untreated units. -/
theorem condExpOn_observedOutcome_treatment_covariates_eq_branch_of_meanIndependent
    {Y0 Y1 : Ω → ℝ} {D : Ω → Bool} {X : Ω → β}
    (hmean : TreatmentMeanIndependentOn μ Y0 Y1 D X)
    (hD : Measurable D) (hY1 : Integrable Y1 μ) (hY0 : Integrable Y0 μ) :
    condExpOn μ (observedOutcome D Y0 Y1) (fun ω => (D ω, X ω)) =ᵐ[μ]
      fun ω =>
        if D ω then
          potentialOutcomeMeanOn μ Y1 X ω
        else
          potentialOutcomeMeanOn μ Y0 X ω := by
  have hbranch :=
    condExpOn_observedOutcome_treatment_covariates_eq_branch
      (μ := μ) (Y0 := Y0) (Y1 := Y1) (D := D) (X := X) hD hY1 hY0
  filter_upwards [hbranch, hmean.2, hmean.1] with ω hobs hY1_eq hY0_eq
  rw [hobs]
  by_cases hDω : D ω = true
  · simp [potentialOutcomeMeanOn, hDω, hY1_eq]
  · simp [potentialOutcomeMeanOn, hDω, hY0_eq]

/-- Surface version of the observed-regression bridge.

If `m0` and `m1` are pointwise versions of the two potential-outcome conditional means, then
the observed-outcome regression on `(D,X)` is the pullback of the pointwise surface `m(d,x)`
generated by those branches. -/
theorem condExpOn_observedOutcome_treatment_covariates_eq_surface_of_meanIndependent
    {Y0 Y1 : Ω → ℝ} {D : Ω → Bool} {X : Ω → β} {m0 m1 : β → ℝ}
    (hmean : TreatmentMeanIndependentOn μ Y0 Y1 D X)
    (hD : Measurable D) (hY1 : Integrable Y1 μ) (hY0 : Integrable Y0 μ)
    (hm1 : potentialOutcomeMeanOn μ Y1 X =ᵐ[μ] fun ω => m1 (X ω))
    (hm0 : potentialOutcomeMeanOn μ Y0 X =ᵐ[μ] fun ω => m0 (X ω)) :
    condExpOn μ (observedOutcome D Y0 Y1) (fun ω => (D ω, X ω)) =ᵐ[μ]
      fun ω => observedRegressionSurface m0 m1 (D ω, X ω) := by
  filter_upwards
    [condExpOn_observedOutcome_treatment_covariates_eq_branch_of_meanIndependent
      (μ := μ) hmean hD hY1 hY0, hm1, hm0]
    with ω hobs h1 h0
  rw [hobs]
  by_cases hDω : D ω = true
  · simp [observedRegressionSurface, hDω, h1]
  · simp [observedRegressionSurface, hDω, h0]

/-- CIA-facing observed-regression bridge for Hansen Theorem 2.12. Conditional independence of
treatment and potential outcomes given covariates identifies the observed-outcome regression on
`(D, X)` with the corresponding branch of the `X`-conditioned potential-outcome means. -/
theorem condExpOn_observedOutcome_treatment_covariates_eq_branch_of_CIA
    [StandardBorelSpace Ω] [IsFiniteMeasure μ]
    {Y0 Y1 : Ω → ℝ} {D : Ω → Bool} {X : Ω → β}
    (hcia : PotentialOutcomeCIAOn μ Y0 Y1 D X) :
    condExpOn μ (observedOutcome D Y0 Y1) (fun ω => (D ω, X ω)) =ᵐ[μ]
      fun ω =>
        if D ω then
          potentialOutcomeMeanOn μ Y1 X ω
        else
          potentialOutcomeMeanOn μ Y0 X ω :=
  condExpOn_observedOutcome_treatment_covariates_eq_branch_of_meanIndependent
    (μ := μ) hcia.toTreatmentMeanIndependentOn hcia.d_measurable
    hcia.y1_integrable hcia.y0_integrable

/-- CIA-facing surface version of the observed-regression bridge for Hansen Theorem 2.12. -/
theorem condExpOn_observedOutcome_treatment_covariates_eq_surface_of_CIA
    [StandardBorelSpace Ω] [IsFiniteMeasure μ]
    {Y0 Y1 : Ω → ℝ} {D : Ω → Bool} {X : Ω → β} {m0 m1 : β → ℝ}
    (hcia : PotentialOutcomeCIAOn μ Y0 Y1 D X)
    (hm1 : potentialOutcomeMeanOn μ Y1 X =ᵐ[μ] fun ω => m1 (X ω))
    (hm0 : potentialOutcomeMeanOn μ Y0 X =ᵐ[μ] fun ω => m0 (X ω)) :
    condExpOn μ (observedOutcome D Y0 Y1) (fun ω => (D ω, X ω)) =ᵐ[μ]
      fun ω => observedRegressionSurface m0 m1 (D ω, X ω) :=
  condExpOn_observedOutcome_treatment_covariates_eq_surface_of_meanIndependent
    (μ := μ) hcia.toTreatmentMeanIndependentOn hcia.d_measurable
    hcia.y1_integrable hcia.y0_integrable hm1 hm0

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

/-- Direct CATE bridge for the variable-facing version of Hansen Theorem 2.12. Under the
mean-independence consequence of CIA, conditioning the treatment effect on `(D, X)` gives the same
conditional average treatment effect as conditioning on `X` alone. -/
theorem conditionalAverageTreatmentEffectOn_treatment_covariates_eq_of_meanIndependent
    {Y0 Y1 : Ω → ℝ} {D : Ω → Bool} {X : Ω → β}
    (hmean : TreatmentMeanIndependentOn μ Y0 Y1 D X)
    (hY1 : Integrable Y1 μ) (hY0 : Integrable Y0 μ) :
    conditionalAverageTreatmentEffectOn μ Y0 Y1 (fun ω => (D ω, X ω)) =ᵐ[μ]
      conditionalAverageTreatmentEffectOn μ Y0 Y1 X :=
  (conditionalAverageTreatmentEffectOn_eq_conditionalPotentialOutcomeContrastOn
    (μ := μ) (X := fun ω => (D ω, X ω)) hY1 hY0).trans <|
      (conditionalPotentialOutcomeContrastOn_treatment_covariates_eq_of_meanIndependent
        (μ := μ) hmean).trans <|
        (conditionalAverageTreatmentEffectOn_eq_conditionalPotentialOutcomeContrastOn
          (μ := μ) (X := X) hY1 hY0).symm

/-- CIA-facing version of the variable-conditioned potential-outcome contrast theorem.
Conditional independence of treatment and potential outcomes given covariates implies that adding
treatment to the conditioning variables does not change the potential-outcome contrast. -/
theorem conditionalPotentialOutcomeContrastOn_treatment_covariates_eq_of_CIA
    [StandardBorelSpace Ω] [IsFiniteMeasure μ]
    {Y0 Y1 : Ω → ℝ} {D : Ω → Bool} {X : Ω → β}
    (hcia : PotentialOutcomeCIAOn μ Y0 Y1 D X) :
    conditionalPotentialOutcomeContrastOn μ Y0 Y1 (fun ω => (D ω, X ω)) =ᵐ[μ]
      conditionalPotentialOutcomeContrastOn μ Y0 Y1 X :=
  conditionalPotentialOutcomeContrastOn_treatment_covariates_eq_of_meanIndependent
    (μ := μ) hcia.toTreatmentMeanIndependentOn

/-- CIA-facing version of Hansen Theorem 2.12 at the variable/a.e. layer. Under conditional
independence of treatment and potential outcomes given covariates, the treatment-and-covariate
potential-outcome contrast equals the conditional average treatment effect. -/
theorem conditionalPotentialOutcomeContrastOn_treatment_covariates_eq_cate_of_CIA
    [StandardBorelSpace Ω] [IsFiniteMeasure μ]
    {Y0 Y1 : Ω → ℝ} {D : Ω → Bool} {X : Ω → β}
    (hcia : PotentialOutcomeCIAOn μ Y0 Y1 D X) :
    conditionalPotentialOutcomeContrastOn μ Y0 Y1 (fun ω => (D ω, X ω)) =ᵐ[μ]
      conditionalAverageTreatmentEffectOn μ Y0 Y1 X :=
  conditionalPotentialOutcomeContrastOn_treatment_covariates_eq_cate_of_meanIndependent
    (μ := μ) hcia.toTreatmentMeanIndependentOn hcia.y1_integrable hcia.y0_integrable

/-- Direct CIA-facing CATE bridge for Hansen Theorem 2.12: under conditional independence,
conditioning the treatment effect on `(D, X)` gives the same CATE as conditioning on `X` alone. -/
theorem conditionalAverageTreatmentEffectOn_treatment_covariates_eq_of_CIA
    [StandardBorelSpace Ω] [IsFiniteMeasure μ]
    {Y0 Y1 : Ω → ℝ} {D : Ω → Bool} {X : Ω → β}
    (hcia : PotentialOutcomeCIAOn μ Y0 Y1 D X) :
    conditionalAverageTreatmentEffectOn μ Y0 Y1 (fun ω => (D ω, X ω)) =ᵐ[μ]
      conditionalAverageTreatmentEffectOn μ Y0 Y1 X :=
  conditionalAverageTreatmentEffectOn_treatment_covariates_eq_of_meanIndependent
    (μ := μ) hcia.toTreatmentMeanIndependentOn hcia.y1_integrable hcia.y0_integrable

end Probability

end HansenEconometrics
