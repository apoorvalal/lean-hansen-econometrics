import Mathlib.Probability.Independence.Integration
import HansenEconometrics.Chapter2PotentialOutcomes

/-!
# Chapter 12 - local average treatment effects

This module gives a noncircular binary-instrument identification theorem for
Hansen's LATE discussion.  `BinaryLATEConditions` contains only primitive
potential-outcome assumptions.  The public endpoint
`lateWaldRatio_eq_complierConditionalAverageTreatmentEffect` derives both the
strictly positive first stage and the Wald-ratio identity.
-/

open scoped ENNReal MeasureTheory ProbabilityTheory
open MeasureTheory ProbabilityTheory Set

namespace HansenEconometrics

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Real-valued encoding of a binary treatment. -/
def binaryTreatmentValue (D : Ω → Bool) : Ω → ℝ :=
  fun ω => if D ω then 1 else 0

/-- Potential treatment selected by the binary instrument value `z`. -/
def potentialTreatmentAtInstrument
    (X0 X1 : Ω → Bool) (z : Bool) : Ω → Bool :=
  if z then X1 else X0

/-- Joint latent row with respect to which instrument independence is stated. -/
def lateLatentRow
    (X0 X1 : Ω → Bool) (Y0 Y1 : Ω → ℝ) :
    Ω → (Bool × Bool) × (ℝ × ℝ) :=
  fun ω => ((X0 ω, X1 ω), (Y0 ω, Y1 ω))

/-- Units whose treatment is induced by changing the instrument from zero to one. -/
def complierSet (X0 X1 : Ω → Bool) : Set Ω :=
  {ω | X0 ω = false ∧ X1 ω = true}

/-- Population mean conditional on a positive-probability event, written as a
normalized indicator integral. -/
noncomputable def meanOnEvent
    (μ : Measure Ω) (s : Set Ω) (V : Ω → ℝ) : ℝ :=
  (∫ ω, s.indicator V ω ∂μ) / μ.real s

/-- Mean of `V` in the binary-instrument cell `Z = z`. -/
noncomputable def instrumentCellMean
    (μ : Measure Ω) (Z : Ω → Bool) (z : Bool) (V : Ω → ℝ) : ℝ :=
  meanOnEvent μ {ω | Z ω = z} V

/-- Wald ratio used to identify LATE for a binary instrument. -/
noncomputable def lateWaldRatio (EY1 EY0 EX1 EX0 : ℝ) : ℝ :=
  (EY1 - EY0) / (EX1 - EX0)

/-- Observed-data binary-IV Wald estimand. -/
noncomputable def binaryInstrumentWaldRatio
    (μ : Measure Ω) (Z D : Ω → Bool) (Y : Ω → ℝ) : ℝ :=
  lateWaldRatio
    (instrumentCellMean μ Z true Y)
    (instrumentCellMean μ Z false Y)
    (instrumentCellMean μ Z true (binaryTreatmentValue D))
    (instrumentCellMean μ Z false (binaryTreatmentValue D))

/-- Average treatment effect among compliers.  Positive complier mass in
`BinaryLATEConditions` makes this normalized event mean nondegenerate. -/
noncomputable def complierConditionalAverageTreatmentEffect
    (μ : Measure Ω) (X0 X1 : Ω → Bool) (Y0 Y1 : Ω → ℝ) : ℝ :=
  meanOnEvent μ (complierSet X0 X1) (treatmentEffect Y0 Y1)

/-- Primitive binary-IV assumptions for LATE identification.

The observed treatment obeys consistency with `X(0), X(1)`.  The observed
outcome obeys consistency and exclusion through the treatment-indexed potential
outcomes `Y(0), Y(1)`.  Instrument independence is joint independence from the
full latent row, and monotonicity rules out defiers almost surely. -/
structure BinaryLATEConditions
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z D X0 X1 : Ω → Bool) (Y Y0 Y1 : Ω → ℝ) : Prop where
  z_measurable : Measurable Z
  x0_measurable : Measurable X0
  x1_measurable : Measurable X1
  y0_integrable : Integrable Y0 μ
  y1_integrable : Integrable Y1 μ
  treatment_consistency :
    D =ᵐ[μ] fun ω => potentialTreatmentAtInstrument X0 X1 (Z ω) ω
  outcome_consistency_exclusion :
    Y =ᵐ[μ] observedOutcome D Y0 Y1
  instrument_independent : Z ⟂ᵢ[μ] lateLatentRow X0 X1 Y0 Y1
  monotonicity : ∀ᵐ ω ∂μ, X0 ω ≤ X1 ω
  instrument_zero_pos : 0 < μ.real {ω | Z ω = false}
  instrument_one_pos : 0 < μ.real {ω | Z ω = true}
  complier_pos : 0 < μ.real (complierSet X0 X1)

private theorem binaryTreatmentValue_measurable
    {D : Ω → Bool} (hD : Measurable D) :
    Measurable (binaryTreatmentValue D) := by
  exact (measurable_of_finite (fun d : Bool => if d then (1 : ℝ) else 0)).comp hD

private theorem binaryTreatmentValue_integrable
    {μ : Measure Ω} [IsFiniteMeasure μ] {D : Ω → Bool} (hD : Measurable D) :
    Integrable (binaryTreatmentValue D) μ := by
  refine Integrable.of_bound (binaryTreatmentValue_measurable hD).aestronglyMeasurable 1 ?_
  filter_upwards [] with ω
  cases h : D ω <;> simp [binaryTreatmentValue, h]

private theorem potentialTreatmentAtInstrument_measurable
    {X0 X1 : Ω → Bool} (hX0 : Measurable X0) (hX1 : Measurable X1) (z : Bool) :
    Measurable (potentialTreatmentAtInstrument X0 X1 z) := by
  cases z <;> simp [potentialTreatmentAtInstrument, hX0, hX1]

private theorem observedOutcome_integrable
    {μ : Measure Ω} {D : Ω → Bool} {Y0 Y1 : Ω → ℝ}
    (hD : Measurable D) (hY0 : Integrable Y0 μ) (hY1 : Integrable Y1 μ) :
    Integrable (observedOutcome D Y0 Y1) μ := by
  let s : Set Ω := {ω | D ω = true}
  have hs : MeasurableSet s := hD (measurableSet_singleton true)
  have heq : observedOutcome D Y0 Y1 =
      fun ω => s.indicator Y1 ω + sᶜ.indicator Y0 ω := by
    funext ω
    by_cases h : D ω = true <;> simp [observedOutcome, s, h]
  rw [heq]
  exact (hY1.indicator hs).add (hY0.indicator hs.compl)

private theorem complierSet_measurable
    {X0 X1 : Ω → Bool} (hX0 : Measurable X0) (hX1 : Measurable X1) :
    MeasurableSet (complierSet X0 X1) := by
  exact (hX0 (measurableSet_singleton false)).inter
    (hX1 (measurableSet_singleton true))

private theorem instrumentCellMean_eq_integral_of_indep
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Z : Ω → Bool} {V : Ω → ℝ} (z : Bool)
    (hZ : Measurable Z) (hV : AEStronglyMeasurable V μ)
    (hIndep : Z ⟂ᵢ[μ] V) (hpos : 0 < μ.real {ω | Z ω = z}) :
    instrumentCellMean μ Z z V = ∫ ω, V ω ∂μ := by
  let s : Set Ω := {ω | Z ω = z}
  let cellIndicator : Bool → ℝ := fun b => if b = z then 1 else 0
  have hs : MeasurableSet s := hZ (measurableSet_singleton z)
  have hcell : Measurable cellIndicator := measurable_of_finite cellIndicator
  have hcellZ : AEStronglyMeasurable (cellIndicator ∘ Z) μ :=
    (hcell.comp hZ).aestronglyMeasurable
  have hfactor :=
    (hIndep.comp hcell measurable_id).integral_mul_eq_mul_integral hcellZ hV
  have hcellIntegral : (∫ ω, cellIndicator (Z ω) ∂μ) = μ.real s := by
    have heq : (fun ω => cellIndicator (Z ω)) =
        s.indicator (fun _ => (1 : ℝ)) := by
      funext ω
      by_cases h : Z ω = z <;> simp [s, cellIndicator, h]
    rw [heq]
    exact integral_indicator_one (μ := μ) hs
  have hindicator : s.indicator V = fun ω => cellIndicator (Z ω) * V ω := by
    funext ω
    by_cases h : Z ω = z <;> simp [s, cellIndicator, h]
  have hproduct :
      (∫ ω, cellIndicator (Z ω) * V ω ∂μ) =
        (∫ ω, cellIndicator (Z ω) ∂μ) * ∫ ω, V ω ∂μ := by
    simpa [Function.comp_def] using hfactor
  rw [instrumentCellMean, meanOnEvent, show {ω | Z ω = z} = s from rfl,
    hindicator, hproduct, hcellIntegral]
  simpa [s] using mul_div_cancel_left₀ (∫ ω, V ω ∂μ) (ne_of_gt hpos)

namespace BinaryLATEConditions

variable {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {Z D X0 X1 : Ω → Bool} {Y Y0 Y1 : Ω → ℝ}

private theorem potentialTreatmentValue_independent
    (h : BinaryLATEConditions μ Z D X0 X1 Y Y0 Y1) (z : Bool) :
    Z ⟂ᵢ[μ] binaryTreatmentValue (potentialTreatmentAtInstrument X0 X1 z) := by
  let selectTreatment : (Bool × Bool) × (ℝ × ℝ) → ℝ := fun row =>
    if (if z then row.1.2 else row.1.1) then 1 else 0
  have hselect : Measurable selectTreatment := by
    apply (measurable_of_finite (fun d : Bool => if d then (1 : ℝ) else 0)).comp
    cases z
    · exact measurable_fst.comp measurable_fst
    · exact measurable_snd.comp measurable_fst
  have hcomp := h.instrument_independent.comp measurable_id hselect
  cases z <;>
    simpa [selectTreatment, lateLatentRow, potentialTreatmentAtInstrument,
      binaryTreatmentValue, Function.comp_def] using hcomp

private theorem potentialOutcome_independent
    (h : BinaryLATEConditions μ Z D X0 X1 Y Y0 Y1) (z : Bool) :
    Z ⟂ᵢ[μ] observedOutcome (potentialTreatmentAtInstrument X0 X1 z) Y0 Y1 := by
  let selectOutcome : (Bool × Bool) × (ℝ × ℝ) → ℝ := fun row =>
    if (if z then row.1.2 else row.1.1) then row.2.2 else row.2.1
  have hx0 : Measurable (fun row : (Bool × Bool) × (ℝ × ℝ) => row.1.1) :=
    measurable_fst.comp measurable_fst
  have hx1 : Measurable (fun row : (Bool × Bool) × (ℝ × ℝ) => row.1.2) :=
    measurable_snd.comp measurable_fst
  have hy0 : Measurable (fun row : (Bool × Bool) × (ℝ × ℝ) => row.2.1) :=
    measurable_fst.comp measurable_snd
  have hy1 : Measurable (fun row : (Bool × Bool) × (ℝ × ℝ) => row.2.2) :=
    measurable_snd.comp measurable_snd
  have hselect : Measurable selectOutcome := by
    cases z
    · exact Measurable.ite (hx0 (measurableSet_singleton true)) hy1 hy0
    · exact Measurable.ite (hx1 (measurableSet_singleton true)) hy1 hy0
  have hcomp := h.instrument_independent.comp measurable_id hselect
  cases z <;>
    simpa [selectOutcome, lateLatentRow, potentialTreatmentAtInstrument,
      observedOutcome, Function.comp_def] using hcomp

private theorem treatment_cellMean_eq_potential
    (h : BinaryLATEConditions μ Z D X0 X1 Y Y0 Y1) (z : Bool) :
    instrumentCellMean μ Z z (binaryTreatmentValue D) =
      instrumentCellMean μ Z z
        (binaryTreatmentValue (potentialTreatmentAtInstrument X0 X1 z)) := by
  unfold instrumentCellMean meanOnEvent
  congr 1
  apply integral_congr_ae
  filter_upwards [h.treatment_consistency] with ω hD
  by_cases hZ : Z ω = z
  · cases z <;> simp_all [potentialTreatmentAtInstrument, binaryTreatmentValue]
  · simp [hZ]

private theorem outcome_cellMean_eq_potential
    (h : BinaryLATEConditions μ Z D X0 X1 Y Y0 Y1) (z : Bool) :
    instrumentCellMean μ Z z Y =
      instrumentCellMean μ Z z
        (observedOutcome (potentialTreatmentAtInstrument X0 X1 z) Y0 Y1) := by
  unfold instrumentCellMean meanOnEvent
  congr 1
  apply integral_congr_ae
  filter_upwards [h.treatment_consistency, h.outcome_consistency_exclusion]
    with ω hD hY
  by_cases hZ : Z ω = z
  · cases z <;> simp_all [potentialTreatmentAtInstrument, observedOutcome]
  · simp [hZ]

private theorem treatment_cellMean_eq_integral
    (h : BinaryLATEConditions μ Z D X0 X1 Y Y0 Y1) (z : Bool) :
    instrumentCellMean μ Z z (binaryTreatmentValue D) =
      ∫ ω, binaryTreatmentValue (potentialTreatmentAtInstrument X0 X1 z) ω ∂μ := by
  rw [h.treatment_cellMean_eq_potential z]
  apply instrumentCellMean_eq_integral_of_indep z h.z_measurable
  · have hmeas := binaryTreatmentValue_measurable
      (potentialTreatmentAtInstrument_measurable h.x0_measurable h.x1_measurable z)
    exact hmeas.aestronglyMeasurable
  · exact h.potentialTreatmentValue_independent z
  · cases z
    · exact h.instrument_zero_pos
    · exact h.instrument_one_pos

private theorem outcome_cellMean_eq_integral
    (h : BinaryLATEConditions μ Z D X0 X1 Y Y0 Y1) (z : Bool) :
    instrumentCellMean μ Z z Y =
      ∫ ω, observedOutcome (potentialTreatmentAtInstrument X0 X1 z) Y0 Y1 ω ∂μ := by
  rw [h.outcome_cellMean_eq_potential z]
  apply instrumentCellMean_eq_integral_of_indep z h.z_measurable
  · exact (observedOutcome_integrable
      (potentialTreatmentAtInstrument_measurable h.x0_measurable h.x1_measurable z)
      h.y0_integrable h.y1_integrable).1
  · exact h.potentialOutcome_independent z
  · cases z
    · exact h.instrument_zero_pos
    · exact h.instrument_one_pos

private theorem treatment_integral_difference_eq_complierMass
    (h : BinaryLATEConditions μ Z D X0 X1 Y Y0 Y1) :
    (∫ ω, binaryTreatmentValue X1 ω ∂μ) -
        (∫ ω, binaryTreatmentValue X0 ω ∂μ) =
      μ.real (complierSet X0 X1) := by
  have hX0int := binaryTreatmentValue_integrable (μ := μ) h.x0_measurable
  have hX1int := binaryTreatmentValue_integrable (μ := μ) h.x1_measurable
  rw [← integral_sub hX1int hX0int]
  calc
    (∫ ω, binaryTreatmentValue X1 ω - binaryTreatmentValue X0 ω ∂μ) =
        ∫ ω, (complierSet X0 X1).indicator (fun _ => (1 : ℝ)) ω ∂μ := by
      apply integral_congr_ae
      filter_upwards [h.monotonicity] with ω hmono
      cases h0 : X0 ω <;> cases h1 : X1 ω <;>
        simp_all [binaryTreatmentValue, complierSet, Bool.le_iff_imp]
    _ = μ.real (complierSet X0 X1) :=
      integral_indicator_one (μ := μ)
        (complierSet_measurable h.x0_measurable h.x1_measurable)

private theorem outcome_integral_difference_eq_complierEffect
    (h : BinaryLATEConditions μ Z D X0 X1 Y Y0 Y1) :
    (∫ ω, observedOutcome X1 Y0 Y1 ω ∂μ) -
        (∫ ω, observedOutcome X0 Y0 Y1 ω ∂μ) =
      ∫ ω, (complierSet X0 X1).indicator (treatmentEffect Y0 Y1) ω ∂μ := by
  have hX0out := observedOutcome_integrable h.x0_measurable h.y0_integrable h.y1_integrable
  have hX1out := observedOutcome_integrable h.x1_measurable h.y0_integrable h.y1_integrable
  rw [← integral_sub hX1out hX0out]
  apply integral_congr_ae
  filter_upwards [h.monotonicity] with ω hmono
  cases h0 : X0 ω <;> cases h1 : X1 ω <;>
    simp_all [observedOutcome, complierSet, Bool.le_iff_imp]

/-- The first-stage difference equals complier probability and is strictly positive. -/
theorem firstStage_eq_complierMass_and_pos
    (h : BinaryLATEConditions μ Z D X0 X1 Y Y0 Y1) :
    instrumentCellMean μ Z true (binaryTreatmentValue D) -
        instrumentCellMean μ Z false (binaryTreatmentValue D) =
          μ.real (complierSet X0 X1) ∧
      0 < instrumentCellMean μ Z true (binaryTreatmentValue D) -
        instrumentCellMean μ Z false (binaryTreatmentValue D) := by
  have hfirst : instrumentCellMean μ Z true (binaryTreatmentValue D) -
      instrumentCellMean μ Z false (binaryTreatmentValue D) =
        μ.real (complierSet X0 X1) := by
    rw [h.treatment_cellMean_eq_integral true, h.treatment_cellMean_eq_integral false]
    simpa [potentialTreatmentAtInstrument] using h.treatment_integral_difference_eq_complierMass
  exact ⟨hfirst, hfirst.symm ▸ h.complier_pos⟩

/-- Noncircular binary-IV LATE identification.

Under consistency/exclusion, joint instrument independence, monotonicity,
integrability, positive instrument-cell probabilities, and positive complier
mass, the observed Wald ratio equals the conditional average treatment effect
among compliers.  The positive first stage is derived, not assumed. -/
theorem lateWaldRatio_eq_complierConditionalAverageTreatmentEffect
    (h : BinaryLATEConditions μ Z D X0 X1 Y Y0 Y1) :
    binaryInstrumentWaldRatio μ Z D Y =
      complierConditionalAverageTreatmentEffect μ X0 X1 Y0 Y1 := by
  have hfirst := h.firstStage_eq_complierMass_and_pos
  have houtcome : instrumentCellMean μ Z true Y - instrumentCellMean μ Z false Y =
      ∫ ω, (complierSet X0 X1).indicator (treatmentEffect Y0 Y1) ω ∂μ := by
    rw [h.outcome_cellMean_eq_integral true, h.outcome_cellMean_eq_integral false]
    simpa [potentialTreatmentAtInstrument] using h.outcome_integral_difference_eq_complierEffect
  rw [binaryInstrumentWaldRatio, lateWaldRatio, houtcome, hfirst.1,
    complierConditionalAverageTreatmentEffect, meanOnEvent]

end BinaryLATEConditions

end HansenEconometrics
