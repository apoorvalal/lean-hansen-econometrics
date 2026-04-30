import HansenEconometrics.Chapter7Asymptotics.SampleMiddle

/-!
# Chapter 7 Asymptotics: Middle-Matrix Consistency (RobustCovariance, part 2/3)

This file contains measurability, leverage bounds, the residual-score expansion algebra
behind Theorem 7.6, the `RobustCovarianceConsistencyConditions` package, and the WLLN
consistency theorems for HC0/HC1/HC2/HC3 sample middle matrices.

It was extracted from the former `RobustCovariance.lean` together with `SampleMiddle.lean`
and `SandwichAssembly.lean`.
-/

open scoped Matrix Real

namespace HansenEconometrics

open Matrix

section Assumption72

open MeasureTheory ProbabilityTheory Filter
open scoped Matrix.Norms.Elementwise Function Topology ProbabilityTheory

variable {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
variable {n : Type*} [Fintype n]
variable {k : Type*} [Fintype k] [DecidableEq k]

omit [DecidableEq k] in
@[reducible]
private noncomputable def matrixBorelMeasurableSpaceInst :
    MeasurableSpace (Matrix k k ℝ) :=
  matrixBorelMeasurableSpace k k

attribute [local instance] matrixBorelMeasurableSpaceInst

omit [DecidableEq k] in
private lemma matrixBorelSpaceInst : BorelSpace (Matrix k k ℝ) :=
  matrixBorelSpace k k

attribute [local instance] matrixBorelSpaceInst

/-- Measurability of a generic leverage-adjusted middle matrix from component
measurability and measurability of the scalar weight function. -/
theorem sampleScoreCovLevAdjStar_stack_aestronglyMeasurable_components
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (weight : ℝ → ℝ) (hweight_meas : Measurable weight)
    (β : k → ℝ) (h : SampleMomentAssumption71 μ X e)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (he_meas : ∀ i, AEStronglyMeasurable (e i) μ) :
    ∀ n, AEStronglyMeasurable
      (fun ω => sampleScoreCovLevAdjStar weight
        (stackRegressors X n ω) (stackOutcomes y n ω)) μ := by
  intro n
  have hBeta_meas := olsBetaStar_stack_aestronglyMeasurable
    (μ := μ) (X := X) (e := e) (y := y) β h hmodel n
  have hRawGram_meas : AEStronglyMeasurable
      (fun ω => (stackRegressors X n ω)ᵀ * stackRegressors X n ω) μ := by
    have hform : (fun ω => (stackRegressors X n ω)ᵀ * stackRegressors X n ω) =
        (fun ω => ∑ i ∈ Finset.range n, Matrix.vecMulVec (X i ω) (X i ω)) := by
      funext ω
      rw [stackRegressors_transpose_mul_self_eq_sum, sum_fin_eq_sum_range_vecMulVec]
    rw [hform]
    refine Finset.aestronglyMeasurable_fun_sum _ (fun i _ => ?_)
    exact ((h.ident_outer i).integrable_iff.mpr h.int_outer).aestronglyMeasurable
  have hRawInv_meas : AEStronglyMeasurable
      (fun ω => ((stackRegressors X n ω)ᵀ * stackRegressors X n ω)⁻¹) μ :=
    aestronglyMeasurable_matrix_inv hRawGram_meas
  have hdot_fixed_cont : Continuous (fun x : k → ℝ => x ⬝ᵥ β) := by
    simpa [dotProduct] using
      (continuous_finset_sum Finset.univ
        (fun i _ => (continuous_apply i).mul continuous_const))
  have hdot_pair_cont : Continuous (fun p : (k → ℝ) × (k → ℝ) => p.1 ⬝ᵥ p.2) := by
    simpa [dotProduct] using
      (continuous_finset_sum Finset.univ
        (fun i _ =>
          ((continuous_apply i).comp continuous_fst).mul
            ((continuous_apply i).comp continuous_snd)))
  have houter_cont : Continuous (fun v : k → ℝ => Matrix.vecMulVec v v) := by
    refine continuous_pi (fun a => ?_)
    refine continuous_pi (fun b => ?_)
    simpa [Matrix.vecMulVec_apply] using
      (continuous_apply a).mul (continuous_apply b)
  have hterm : ∀ i : Fin n, AEStronglyMeasurable
      (fun ω =>
        (weight (leverageStar (stackRegressors X n ω) i) *
            (olsResidualStar (stackRegressors X n ω) (stackOutcomes y n ω) i) ^ 2) •
          Matrix.vecMulVec (stackRegressors X n ω i) (stackRegressors X n ω i)) μ := by
    intro i
    have hXrow : AEStronglyMeasurable (fun ω => stackRegressors X n ω i) μ := by
      simpa [stackRegressors] using hX_meas i.val
    have hYrow : AEStronglyMeasurable (fun ω => stackOutcomes y n ω i) μ := by
      have hYexpr : AEStronglyMeasurable
          (fun ω => X i.val ω ⬝ᵥ β + e i.val ω) μ :=
        (hdot_fixed_cont.comp_aestronglyMeasurable (hX_meas i.val)).add (he_meas i.val)
      refine hYexpr.congr (ae_of_all μ (fun ω => ?_))
      simpa [stackOutcomes] using (hmodel i.val ω).symm
    have hfit : AEStronglyMeasurable
        (fun ω =>
          stackRegressors X n ω i ⬝ᵥ
            olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω)) μ :=
      hdot_pair_cont.comp_aestronglyMeasurable (hXrow.prodMk hBeta_meas)
    have hres_exp : AEStronglyMeasurable
        (fun ω =>
          stackOutcomes y n ω i -
            stackRegressors X n ω i ⬝ᵥ
              olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω)) μ :=
      hYrow.sub hfit
    have hres : AEStronglyMeasurable
        (fun ω => olsResidualStar (stackRegressors X n ω) (stackOutcomes y n ω) i) μ := by
      refine hres_exp.congr (ae_of_all μ (fun ω => ?_))
      simp [olsResidualStar, Matrix.mulVec, dotProduct]
    have hmulVec : AEStronglyMeasurable
        (fun ω =>
          ((stackRegressors X n ω)ᵀ * stackRegressors X n ω)⁻¹ *ᵥ
            stackRegressors X n ω i) μ := by
      exact (Continuous.matrix_mulVec continuous_fst continuous_snd).comp_aestronglyMeasurable
        (hRawInv_meas.prodMk hXrow)
    have hlev : AEStronglyMeasurable
        (fun ω => leverageStar (stackRegressors X n ω) i) μ := by
      refine hdot_pair_cont.comp_aestronglyMeasurable (hXrow.prodMk ?_)
      simpa [leverageStar] using hmulVec
    have hweight : AEStronglyMeasurable
        (fun ω => weight (leverageStar (stackRegressors X n ω) i)) μ := by
      exact (hweight_meas.comp_aemeasurable hlev.aemeasurable).aestronglyMeasurable
    have hcoeff : AEStronglyMeasurable
        (fun ω =>
          weight (leverageStar (stackRegressors X n ω) i) *
            (olsResidualStar (stackRegressors X n ω) (stackOutcomes y n ω) i) ^ 2) μ :=
      hweight.mul (hres.pow 2)
    have houter : AEStronglyMeasurable
        (fun ω => Matrix.vecMulVec (stackRegressors X n ω i) (stackRegressors X n ω i)) μ :=
      houter_cont.comp_aestronglyMeasurable hXrow
    exact hcoeff.smul houter
  have hsum : AEStronglyMeasurable
      (fun ω =>
        ∑ i : Fin n,
          (weight (leverageStar (stackRegressors X n ω) i) *
              (olsResidualStar (stackRegressors X n ω) (stackOutcomes y n ω) i) ^ 2) •
            Matrix.vecMulVec (stackRegressors X n ω i) (stackRegressors X n ω i)) μ := by
    refine Finset.aestronglyMeasurable_fun_sum _ (fun i _ => hterm i)
  simpa [sampleScoreCovLevAdjStar] using
    AEStronglyMeasurable.const_smul hsum ((Fintype.card (Fin n) : ℝ)⁻¹)

/-- Measurability of the generic leverage-adjustment middle-matrix gap from
component measurability. -/
theorem sampleScoreCovLevAdjmtStar_stack_aestronglyMeasurable_components
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (weight : ℝ → ℝ) (hweight_meas : Measurable weight)
    (β : k → ℝ) (h : SampleMomentAssumption71 μ X e)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (he_meas : ∀ i, AEStronglyMeasurable (e i) μ) :
    ∀ n, AEStronglyMeasurable
      (fun ω => sampleScoreCovLevAdjmtStar weight
        (stackRegressors X n ω) (stackOutcomes y n ω)) μ := by
  intro n
  exact
    (sampleScoreCovLevAdjStar_stack_aestronglyMeasurable_components
      (μ := μ) (X := X) (e := e) (y := y) weight hweight_meas
      β h hmodel hX_meas he_meas n).sub
    (sampleScoreCovStar_stack_aestronglyMeasurable_components
      (μ := μ) (X := X) (e := e) (y := y) β h hmodel hX_meas he_meas n)

theorem measurable_hc2Weight : Measurable (fun h : ℝ => (1 - h)⁻¹) :=
  measurable_inv.comp (measurable_const.sub measurable_id)

theorem measurable_hc3Weight : Measurable (fun h : ℝ => ((1 - h)⁻¹) ^ 2) :=
  measurable_hc2Weight.pow_const 2

/-- Measurability of the HC2 middle-matrix adjustment from component
measurability. -/
theorem sampleScoreCovHC2AdjStar_stack_aestronglyMeasurable_components
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (β : k → ℝ) (h : SampleMomentAssumption71 μ X e)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (he_meas : ∀ i, AEStronglyMeasurable (e i) μ) :
    ∀ n, AEStronglyMeasurable
      (fun ω => sampleScoreCovHC2AdjStar
        (stackRegressors X n ω) (stackOutcomes y n ω)) μ := by
  simpa [sampleScoreCovHC2AdjStar] using
    sampleScoreCovLevAdjmtStar_stack_aestronglyMeasurable_components
      (μ := μ) (X := X) (e := e) (y := y)
      (weight := fun h => (1 - h)⁻¹) measurable_hc2Weight
      β h hmodel hX_meas he_meas

/-- Measurability of the HC3 middle-matrix adjustment from component
measurability. -/
theorem sampleScoreCovHC3AdjStar_stack_aestronglyMeasurable_components
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (β : k → ℝ) (h : SampleMomentAssumption71 μ X e)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (he_meas : ∀ i, AEStronglyMeasurable (e i) μ) :
    ∀ n, AEStronglyMeasurable
      (fun ω => sampleScoreCovHC3AdjStar
        (stackRegressors X n ω) (stackOutcomes y n ω)) μ := by
  simpa [sampleScoreCovHC3AdjStar] using
    sampleScoreCovLevAdjmtStar_stack_aestronglyMeasurable_components
      (μ := μ) (X := X) (e := e) (y := y)
      (weight := fun h => ((1 - h)⁻¹) ^ 2) measurable_hc3Weight
      β h hmodel hX_meas he_meas

set_option linter.flexible false in
/-- **Generic leverage-adjustment expansion, entrywise form.**

The leverage-adjusted-minus-HC0 middle matrix is the sample average with scalar
weight `w(hᵢᵢ)-1` multiplying the usual residual-score outer product. -/
theorem sampleScoreCovLevAdjmtStar_apply
    (weight : ℝ → ℝ) (X : Matrix n k ℝ) (y : n → ℝ) (a b : k) :
    sampleScoreCovLevAdjmtStar weight X y a b =
      sampleScoreCovLevAdjmtEntryStar weight X y a b := by
  simp [sampleScoreCovLevAdjmtStar,
    sampleScoreCovLevAdjStar,
    sampleScoreCovLevAdjmtEntryStar,
    sampleScoreCovStar, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.sum_apply, Matrix.vecMulVec_apply, smul_eq_mul]
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl ?_
  intro i _
  ring

/-- **HC2 leverage-adjustment expansion, entrywise form.**

The HC2-minus-HC0 middle matrix is the sample average with scalar weight
`(1-hᵢᵢ)⁻¹ - 1` multiplying the usual residual-score outer product. -/
theorem sampleScoreCovHC2AdjStar_apply
    (X : Matrix n k ℝ) (y : n → ℝ) (a b : k) :
    sampleScoreCovHC2AdjStar X y a b =
      (Fintype.card n : ℝ)⁻¹ *
        ∑ i : n, (((1 - leverageStar X i)⁻¹ - 1) *
          (olsResidualStar X y i) ^ 2 * X i a * X i b) := by
  change sampleScoreCovLevAdjmtStar
      (fun h => (1 - h)⁻¹) X y a b = _
  rw [sampleScoreCovLevAdjmtStar_apply]
  rfl

/-- **HC3 leverage-adjustment expansion, entrywise form.**

The HC3-minus-HC0 middle matrix is the sample average with scalar weight
`(1-hᵢᵢ)⁻² - 1` multiplying the usual residual-score outer product. -/
theorem sampleScoreCovHC3AdjStar_apply
    (X : Matrix n k ℝ) (y : n → ℝ) (a b : k) :
    sampleScoreCovHC3AdjStar X y a b =
      (Fintype.card n : ℝ)⁻¹ *
        ∑ i : n, ((((1 - leverageStar X i)⁻¹) ^ 2 - 1) *
          (olsResidualStar X y i) ^ 2 * X i a * X i b) := by
  change sampleScoreCovLevAdjmtStar
      (fun h => ((1 - h)⁻¹) ^ 2) X y a b = _
  rw [sampleScoreCovLevAdjmtStar_apply]
  rfl

/-- Each scalar leverage-adjustment weight is bounded by its sup norm. -/
theorem leverageAdjustmentWeight_abs_le_norm
    (weight : ℝ → ℝ) (X : Matrix n k ℝ) (i : n) :
    |weight (leverageStar X i) - 1| ≤
      levAdjWtNormStar weight X := by
  simpa [levAdjWtNormStar, Real.norm_eq_abs] using
    norm_le_pi_norm (fun i : n => weight (leverageStar X i) - 1) i

/-- On leverage values `0 ≤ h ≤ 1/2`, the HC2 weight deviation is at most
`2h`. -/
theorem hc2Weight_abs_sub_one_le_two_mul
    {h : ℝ} (hh_nonneg : 0 ≤ h) (hh_half : h ≤ 1 / 2) :
    |(1 - h)⁻¹ - 1| ≤ 2 * h := by
  have hden_pos : 0 < 1 - h := by
    linarith
  have hrepr : (1 - h)⁻¹ - 1 = h / (1 - h) := by
    field_simp [hden_pos.ne']
    ring
  have hfrac_nonneg : 0 ≤ h / (1 - h) := by
    exact div_nonneg hh_nonneg hden_pos.le
  rw [hrepr, abs_of_nonneg hfrac_nonneg]
  rw [div_le_iff₀ hden_pos]
  nlinarith

/-- On leverage values `0 ≤ h ≤ 1/2`, the HC3 weight deviation is at most
`8h`. The constant is crude but sufficient for the `oₚ(1)` argument. -/
theorem hc3Weight_abs_sub_one_le_eight_mul
    {h : ℝ} (hh_nonneg : 0 ≤ h) (hh_half : h ≤ 1 / 2) :
    |((1 - h)⁻¹) ^ 2 - 1| ≤ 8 * h := by
  have hden_pos : 0 < 1 - h := by
    linarith
  have hrepr : ((1 - h)⁻¹) ^ 2 - 1 = (h * (2 - h)) / (1 - h) ^ 2 := by
    field_simp [hden_pos.ne']
    ring
  have hfrac_nonneg : 0 ≤ (h * (2 - h)) / (1 - h) ^ 2 := by
    have hnum_nonneg : 0 ≤ h * (2 - h) := by
      nlinarith
    exact div_nonneg hnum_nonneg (sq_nonneg _)
  rw [hrepr, abs_of_nonneg hfrac_nonneg]
  have hsq_pos : 0 < (1 - h) ^ 2 := by
    positivity
  rw [div_le_iff₀ hsq_pos]
  calc
    h * (2 - h) ≤ 2 * h := by
      nlinarith
    _ ≤ 8 * h * (1 - h) ^ 2 := by
      have hsq_lower : (1 / 4 : ℝ) ≤ (1 - h) ^ 2 := by
        nlinarith
      nlinarith

/-- If the maximal leverage is smaller than `δ ≤ 1/2`, then the HC2
adjustment-weight norm is smaller than `2δ`. -/
theorem levAdjWtNormStar_hc2_lt_maxLevStar_lt
    (X : Matrix n k ℝ) {δ : ℝ} (hδ : 0 < δ) (hδ_half : δ ≤ 1 / 2)
    (hmax : maxLeverageStar X < δ) :
    levAdjWtNormStar (fun h => (1 - h)⁻¹) X < 2 * δ := by
  let z : n → ℝ := fun i => (1 - leverageStar X i)⁻¹ - 1
  have hcoords : ∀ i : n, leverageStar X i < δ := by
    intro i
    exact lt_of_le_of_lt (leverageStar_le_maxLeverageStar X i) hmax
  have hz : ‖z‖ < 2 * δ := by
    refine
      (@pi_norm_lt_iff n (fun _ : n => ℝ) _
        (fun _ => (by infer_instance : SeminormedAddGroup ℝ)) z (2 * δ)
        (show 0 < 2 * δ by positivity)).2 ?_
    intro i
    have hi_nonneg : 0 ≤ leverageStar X i := leverageStar_nonneg X i
    have hi_lt : leverageStar X i < δ := hcoords i
    have hi_half : leverageStar X i ≤ 1 / 2 := by
      linarith
    have hbound :
        |(1 - leverageStar X i)⁻¹ - 1| ≤ 2 * leverageStar X i :=
      hc2Weight_abs_sub_one_le_two_mul hi_nonneg hi_half
    have hlt : 2 * leverageStar X i < 2 * δ := by
      exact mul_lt_mul_of_pos_left hi_lt (by positivity)
    simpa [z, Real.norm_eq_abs] using lt_of_le_of_lt hbound hlt
  simpa [levAdjWtNormStar, z] using hz

/-- If the maximal leverage is smaller than `δ ≤ 1/2`, then the HC3
adjustment-weight norm is smaller than `8δ`. -/
theorem levAdjWtNormStar_hc3_lt_maxLevStar_lt
    (X : Matrix n k ℝ) {δ : ℝ} (hδ : 0 < δ) (hδ_half : δ ≤ 1 / 2)
    (hmax : maxLeverageStar X < δ) :
    levAdjWtNormStar (fun h => ((1 - h)⁻¹) ^ 2) X < 8 * δ := by
  let z : n → ℝ := fun i => ((1 - leverageStar X i) ^ 2)⁻¹ - 1
  have hcoords : ∀ i : n, leverageStar X i < δ := by
    intro i
    exact lt_of_le_of_lt (leverageStar_le_maxLeverageStar X i) hmax
  have hz : ‖z‖ < 8 * δ := by
    refine
      (@pi_norm_lt_iff n (fun _ : n => ℝ) _
        (fun _ => (by infer_instance : SeminormedAddGroup ℝ)) z (8 * δ)
        (show 0 < 8 * δ by positivity)).2 ?_
    intro i
    have hi_nonneg : 0 ≤ leverageStar X i := leverageStar_nonneg X i
    have hi_lt : leverageStar X i < δ := hcoords i
    have hi_half : leverageStar X i ≤ 1 / 2 := by
      linarith
    have hbound :
        |((1 - leverageStar X i) ^ 2)⁻¹ - 1| ≤ 8 * leverageStar X i := by
      simpa [pow_two] using
        (hc3Weight_abs_sub_one_le_eight_mul (h := leverageStar X i) hi_nonneg hi_half)
    have hlt : 8 * leverageStar X i < 8 * δ := by
      exact mul_lt_mul_of_pos_left hi_lt (by positivity)
    simpa [z, Real.norm_eq_abs] using lt_of_le_of_lt hbound hlt
  simpa [levAdjWtNormStar, z, pow_two] using hz

/-- HC2 adjustment-weight norms are `oₚ(1)` once maximal leverage is `oₚ(1)`. -/
theorem levAdjWtNormStar_hc2_tendstoInMeasure_zero_maxLevStar
    {μ : Measure Ω} {X : ℕ → Ω → (k → ℝ)}
    (hMax : TendstoInMeasure μ
      (fun n ω => maxLeverageStar (stackRegressors X n ω))
      atTop (fun _ => 0)) :
    TendstoInMeasure μ
      (fun n ω =>
        levAdjWtNormStar (fun h => (1 - h)⁻¹)
          (stackRegressors X n ω))
      atTop (fun _ => 0) := by
  rw [tendstoInMeasure_iff_dist] at hMax ⊢
  intro ε hε
  rw [ENNReal.tendsto_atTop_zero]
  intro η hη
  let δ : ℝ := min (1 / 4 : ℝ) (ε / 4)
  have hδ : 0 < δ := by
    dsimp [δ]
    refine lt_min ?_ ?_
    · norm_num
    · positivity
  have hδ_half : δ ≤ 1 / 2 := by
    dsimp [δ]
    have hle : min (1 / 4 : ℝ) (ε / 4) ≤ 1 / 4 := min_le_left _ _
    linarith
  have htwoδ_lt_ε : 2 * δ < ε := by
    dsimp [δ]
    have hle : min (1 / 4 : ℝ) (ε / 4) ≤ ε / 4 := min_le_right _ _
    nlinarith
  have hMaxevent := (hMax δ hδ).eventually_lt_const hη
  obtain ⟨N, hN⟩ := eventually_atTop.1 hMaxevent
  refine ⟨N, fun n hn => ?_⟩
  have hMaxn : μ {ω | δ ≤ dist (maxLeverageStar (stackRegressors X n ω)) 0} < η :=
    hN n hn
  have hcover :
      {ω | ε ≤ dist
          (levAdjWtNormStar (fun h => (1 - h)⁻¹)
            (stackRegressors X n ω)) 0} ⊆
        {ω | δ ≤ dist (maxLeverageStar (stackRegressors X n ω)) 0} := by
    intro ω hω
    by_contra hsmall
    have hmax_lt : maxLeverageStar (stackRegressors X n ω) < δ := by
      have hdist_lt : dist (maxLeverageStar (stackRegressors X n ω)) 0 < δ :=
        not_le.mp hsmall
      simpa [Real.dist_eq, maxLeverageStar, abs_of_nonneg (norm_nonneg _)] using hdist_lt
    have hweight_lt :
        levAdjWtNormStar (fun h => (1 - h)⁻¹)
          (stackRegressors X n ω) < 2 * δ :=
      levAdjWtNormStar_hc2_lt_maxLevStar_lt
        (X := stackRegressors X n ω) hδ hδ_half hmax_lt
    have hdist_lt :
        dist
            (levAdjWtNormStar (fun h => (1 - h)⁻¹)
              (stackRegressors X n ω))
            0 < ε := by
      simpa [Real.dist_eq, levAdjWtNormStar,
        abs_of_nonneg (norm_nonneg _)] using
        lt_trans hweight_lt htwoδ_lt_ε
    exact (not_le_of_gt hdist_lt) hω
  exact le_of_lt (lt_of_le_of_lt (measure_mono hcover) hMaxn)

/-- HC3 adjustment-weight norms are `oₚ(1)` once maximal leverage is `oₚ(1)`. -/
theorem levAdjWtNormStar_hc3_tendstoInMeasure_zero_maxLevStar
    {μ : Measure Ω} {X : ℕ → Ω → (k → ℝ)}
    (hMax : TendstoInMeasure μ
      (fun n ω => maxLeverageStar (stackRegressors X n ω))
      atTop (fun _ => 0)) :
    TendstoInMeasure μ
      (fun n ω =>
        levAdjWtNormStar (fun h => ((1 - h)⁻¹) ^ 2)
          (stackRegressors X n ω))
      atTop (fun _ => 0) := by
  rw [tendstoInMeasure_iff_dist] at hMax ⊢
  intro ε hε
  rw [ENNReal.tendsto_atTop_zero]
  intro η hη
  let δ : ℝ := min (1 / 4 : ℝ) (ε / 16)
  have hδ : 0 < δ := by
    dsimp [δ]
    refine lt_min ?_ ?_
    · norm_num
    · positivity
  have hδ_half : δ ≤ 1 / 2 := by
    dsimp [δ]
    have hle : min (1 / 4 : ℝ) (ε / 16) ≤ 1 / 4 := min_le_left _ _
    linarith
  have heightδ_lt_ε : 8 * δ < ε := by
    dsimp [δ]
    have hle : min (1 / 4 : ℝ) (ε / 16) ≤ ε / 16 := min_le_right _ _
    nlinarith
  have hMaxevent := (hMax δ hδ).eventually_lt_const hη
  obtain ⟨N, hN⟩ := eventually_atTop.1 hMaxevent
  refine ⟨N, fun n hn => ?_⟩
  have hMaxn : μ {ω | δ ≤ dist (maxLeverageStar (stackRegressors X n ω)) 0} < η :=
    hN n hn
  have hcover :
      {ω | ε ≤ dist
          (levAdjWtNormStar (fun h => ((1 - h)⁻¹) ^ 2)
            (stackRegressors X n ω)) 0} ⊆
        {ω | δ ≤ dist (maxLeverageStar (stackRegressors X n ω)) 0} := by
    intro ω hω
    by_contra hsmall
    have hmax_lt : maxLeverageStar (stackRegressors X n ω) < δ := by
      have hdist_lt : dist (maxLeverageStar (stackRegressors X n ω)) 0 < δ :=
        not_le.mp hsmall
      simpa [Real.dist_eq, maxLeverageStar, abs_of_nonneg (norm_nonneg _)] using hdist_lt
    have hweight_lt :
        levAdjWtNormStar (fun h => ((1 - h)⁻¹) ^ 2)
          (stackRegressors X n ω) < 8 * δ :=
      levAdjWtNormStar_hc3_lt_maxLevStar_lt
        (X := stackRegressors X n ω) hδ hδ_half hmax_lt
    have hdist_lt :
        dist
            (levAdjWtNormStar (fun h => ((1 - h)⁻¹) ^ 2)
              (stackRegressors X n ω))
            0 < ε := by
      simpa [Real.dist_eq, levAdjWtNormStar,
        abs_of_nonneg (norm_nonneg _)] using
        lt_trans hweight_lt heightδ_lt_ε
    exact (not_le_of_gt hdist_lt) hω
  exact le_of_lt (lt_of_le_of_lt (measure_mono hcover) hMaxn)

/-- The residual absolute-weight average is nonnegative. -/
theorem sampleScoreCovResAbsWtStar_nonneg
    (X : Matrix n k ℝ) (y : n → ℝ) (a b : k) :
    0 ≤ sampleScoreCovResAbsWtStar X y a b := by
  unfold sampleScoreCovResAbsWtStar
  exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
    (Finset.sum_nonneg (fun i _ => abs_nonneg _))

/-- Diagonal entries of the feasible HC0 middle matrix are nonnegative. -/
theorem sampleScoreCovStar_apply_self_nonneg
    (X : Matrix n k ℝ) (y : n → ℝ) (a : k) :
    0 ≤ sampleScoreCovStar X y a a := by
  simp [sampleScoreCovStar, Matrix.smul_apply, Matrix.sum_apply,
    Matrix.vecMulVec_apply, smul_eq_mul]
  refine mul_nonneg (inv_nonneg.mpr (show 0 ≤ (Fintype.card n : ℝ) by positivity)) ?_
  refine Finset.sum_nonneg ?_
  intro i _
  have hsq : 0 ≤ ((olsResidualStar X y i) * X i a) ^ 2 := sq_nonneg _
  simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hsq

/-- The absolute residual-score average for entry `(a,b)` is bounded by the sum
of the two corresponding HC0 diagonal sample averages. -/
theorem sampleScoreCovResAbsWtStar_le_diag_add
    (X : Matrix n k ℝ) (y : n → ℝ) (a b : k) :
    sampleScoreCovResAbsWtStar X y a b ≤
      sampleScoreCovStar X y a a + sampleScoreCovStar X y b b := by
  calc
    sampleScoreCovResAbsWtStar X y a b
        ≤ (Fintype.card n : ℝ)⁻¹ *
            ∑ i : n, ((olsResidualStar X y i) ^ 2 * X i a * X i a +
              (olsResidualStar X y i) ^ 2 * X i b * X i b) := by
          unfold sampleScoreCovResAbsWtStar
          refine mul_le_mul_of_nonneg_left ?_
            (inv_nonneg.mpr (show 0 ≤ (Fintype.card n : ℝ) by positivity))
          refine Finset.sum_le_sum ?_
          intro i _
          have hr2_nonneg : 0 ≤ (olsResidualStar X y i) ^ 2 := sq_nonneg _
          have habs : |X i a * X i b| ≤ X i a * X i a + X i b * X i b := by
            have habs2 : 2 * |X i a * X i b| ≤ X i a * X i a + X i b * X i b := by
              rw [abs_mul, two_mul]
              have htwo : 2 * |X i a| * |X i b| ≤ X i a * X i a + X i b * X i b :=
                by simpa [sq_abs, pow_two] using
                  (two_mul_le_add_sq |X i a| |X i b|)
              nlinarith
            nlinarith [abs_nonneg (X i a * X i b), habs2]
          calc
            |(olsResidualStar X y i) ^ 2 * X i a * X i b|
                = (olsResidualStar X y i) ^ 2 * |X i a * X i b| := by
                    rw [show
                      (olsResidualStar X y i) ^ 2 * X i a * X i b =
                        (olsResidualStar X y i) ^ 2 * (X i a * X i b) by ring]
                    rw [abs_mul, abs_of_nonneg hr2_nonneg]
            _ ≤ (olsResidualStar X y i) ^ 2 * (X i a * X i a + X i b * X i b) :=
                  mul_le_mul_of_nonneg_left habs hr2_nonneg
            _ = (olsResidualStar X y i) ^ 2 * X i a * X i a +
                  (olsResidualStar X y i) ^ 2 * X i b * X i b := by
                  ring
    _ = sampleScoreCovStar X y a a + sampleScoreCovStar X y b b := by
      simp [sampleScoreCovStar, Matrix.smul_apply, Matrix.sum_apply,
        Matrix.vecMulVec_apply, smul_eq_mul, pow_two]
      rw [Finset.sum_add_distrib, mul_add]
      let c : ℝ := (Fintype.card n : ℝ)⁻¹
      have hA :
          ∑ x : n, olsResidualStar X y x * olsResidualStar X y x * X x a * X x a =
            ∑ x : n, olsResidualStar X y x * (olsResidualStar X y x * (X x a * X x a)) := by
        refine Finset.sum_congr rfl ?_
        intro x hx
        ring
      have hB :
          ∑ x : n, olsResidualStar X y x * olsResidualStar X y x * X x b * X x b =
            ∑ x : n, olsResidualStar X y x * (olsResidualStar X y x * (X x b * X x b)) := by
        refine Finset.sum_congr rfl ?_
        intro x hx
        ring
      calc
        c * ∑ x : n, olsResidualStar X y x * olsResidualStar X y x * X x a * X x a +
            c * ∑ x : n, olsResidualStar X y x * olsResidualStar X y x * X x b * X x b
            = c * ∑ x : n, olsResidualStar X y x * (olsResidualStar X y x * (X x a * X x a)) +
                c * ∑ x : n, olsResidualStar X y x * olsResidualStar X y x * X x b * X x b := by
              rw [hA]
        _ = c * ∑ x : n, olsResidualStar X y x * (olsResidualStar X y x * (X x a * X x a)) +
              c * ∑ x : n, olsResidualStar X y x * (olsResidualStar X y x * (X x b * X x b)) := by
              rw [hB]

/-- Deterministic entrywise bound for generic leverage adjustments.

The scalar HC2/HC3 remainder is bounded by the largest leverage-adjustment
weight times the absolute residual-score average. -/
theorem sampleScoreCovLevAdjmtEntryStar_abs_le
    (weight : ℝ → ℝ) (X : Matrix n k ℝ) (y : n → ℝ) (a b : k) :
    |sampleScoreCovLevAdjmtEntryStar weight X y a b| ≤
      levAdjWtNormStar weight X *
        sampleScoreCovResAbsWtStar X y a b := by
  classical
  let c : ℝ := (Fintype.card n : ℝ)⁻¹
  let base : n → ℝ := fun i => (olsResidualStar X y i) ^ 2 * X i a * X i b
  have hc_nonneg : 0 ≤ c := inv_nonneg.mpr (Nat.cast_nonneg _)
  have hentry :
      sampleScoreCovLevAdjmtEntryStar weight X y a b =
        c * ∑ i : n, (weight (leverageStar X i) - 1) * base i := by
    simp [sampleScoreCovLevAdjmtEntryStar, c, base, mul_assoc]
  have hsum_abs :
      |∑ i : n, (weight (leverageStar X i) - 1) * base i| ≤
        ∑ i : n, |(weight (leverageStar X i) - 1) * base i| :=
    Finset.abs_sum_le_sum_abs _ _
  have hsum_bound :
      ∑ i : n, |(weight (leverageStar X i) - 1) * base i| ≤
        ∑ i : n, levAdjWtNormStar weight X * |base i| := by
    refine Finset.sum_le_sum ?_
    intro i _
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right
      (leverageAdjustmentWeight_abs_le_norm weight X i) (abs_nonneg _)
  calc
    |sampleScoreCovLevAdjmtEntryStar weight X y a b|
        = c * |∑ i : n, (weight (leverageStar X i) - 1) * base i| := by
          rw [hentry, abs_mul, abs_of_nonneg hc_nonneg]
    _ ≤ c * ∑ i : n, |(weight (leverageStar X i) - 1) * base i| :=
          mul_le_mul_of_nonneg_left hsum_abs hc_nonneg
    _ ≤ c * ∑ i : n, levAdjWtNormStar weight X * |base i| :=
          mul_le_mul_of_nonneg_left hsum_bound hc_nonneg
    _ = levAdjWtNormStar weight X *
          sampleScoreCovResAbsWtStar X y a b := by
          rw [← Finset.mul_sum]
          simp [sampleScoreCovResAbsWtStar, c, base]
          ring

/-- Scalar leverage-adjustment entries are `oₚ(1)` when the largest adjustment
weight is `oₚ(1)` and the corresponding absolute residual-score average is
`Oₚ(1)`. -/
theorem sampleScoreCovLevAdjmtEntryStar_tendstoInMeasure_zero_of_weight_norm
    {μ : Measure Ω} {X : ℕ → Ω → (k → ℝ)} {y : ℕ → Ω → ℝ}
    (weight : ℝ → ℝ) (a b : k)
    (hWeight : TendstoInMeasure μ
      (fun n ω =>
        levAdjWtNormStar weight (stackRegressors X n ω))
      atTop (fun _ => 0))
    (hAbsWeight : BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovResAbsWtStar
          (stackRegressors X n ω) (stackOutcomes y n ω) a b)) :
    TendstoInMeasure μ
      (fun n ω =>
        sampleScoreCovLevAdjmtEntryStar weight
          (stackRegressors X n ω) (stackOutcomes y n ω) a b)
      atTop (fun _ => 0) := by
  have hprod :=
    TendstoInMeasure.mul_boundedInProbability
      (μ := μ) hWeight hAbsWeight
  refine TendstoInMeasure.of_abs_le_zero_real hprod ?_
  intro n ω
  have hnonneg : 0 ≤
      levAdjWtNormStar weight (stackRegressors X n ω) *
        sampleScoreCovResAbsWtStar
          (stackRegressors X n ω) (stackOutcomes y n ω) a b := by
    exact mul_nonneg (norm_nonneg _)
      (sampleScoreCovResAbsWtStar_nonneg
        (stackRegressors X n ω) (stackOutcomes y n ω) a b)
  rw [abs_of_nonneg hnonneg]
  exact sampleScoreCovLevAdjmtEntryStar_abs_le
    (weight := weight) (X := stackRegressors X n ω)
    (y := stackOutcomes y n ω) a b

/-- Generic leverage-adjustment convergence from scalar entries.

This turns the remaining HC2/HC3 adjustment goal into one scalar sample-average
goal per matrix entry, leaving the max-leverage argument independent of matrix
convergence bookkeeping. -/
theorem sampleScoreCovLevAdjmtStar_stack_tendstoInMeasure_zero_entries
    {μ : Measure Ω} {X : ℕ → Ω → (k → ℝ)} {y : ℕ → Ω → ℝ}
    (weight : ℝ → ℝ)
    (hEntry : ∀ a b : k, TendstoInMeasure μ
      (fun n ω =>
        sampleScoreCovLevAdjmtEntryStar weight
          (stackRegressors X n ω) (stackOutcomes y n ω) a b)
      atTop (fun _ => 0)) :
    TendstoInMeasure μ
      (fun n ω =>
        sampleScoreCovLevAdjmtStar weight
          (stackRegressors X n ω) (stackOutcomes y n ω))
      atTop (fun _ => 0) := by
  refine tendstoInMeasure_pi (μ := μ) (fun a => ?_)
  refine tendstoInMeasure_pi (μ := μ) (fun b => ?_)
  have h := hEntry a b
  refine h.congr_left (fun n => ae_of_all μ (fun ω => ?_))
  exact (sampleScoreCovLevAdjmtStar_apply
    (weight := weight) (X := stackRegressors X n ω)
    (y := stackOutcomes y n ω) a b).symm

/-- HC2 adjustment convergence from scalar entrywise adjustment sums. -/
theorem sampleScoreCovHC2AdjStar_stack_tendstoInMeasure_zero_entries
    {μ : Measure Ω} {X : ℕ → Ω → (k → ℝ)} {y : ℕ → Ω → ℝ}
    (hEntry : ∀ a b : k, TendstoInMeasure μ
      (fun n ω =>
        sampleScoreCovLevAdjmtEntryStar (fun h => (1 - h)⁻¹)
          (stackRegressors X n ω) (stackOutcomes y n ω) a b)
      atTop (fun _ => 0)) :
    TendstoInMeasure μ
      (fun n ω =>
        sampleScoreCovHC2AdjStar
          (stackRegressors X n ω) (stackOutcomes y n ω))
      atTop (fun _ => 0) := by
  simpa [sampleScoreCovHC2AdjStar] using
    sampleScoreCovLevAdjmtStar_stack_tendstoInMeasure_zero_entries
      (μ := μ) (X := X) (y := y) (weight := fun h => (1 - h)⁻¹) hEntry

/-- HC3 adjustment convergence from scalar entrywise adjustment sums. -/
theorem sampleScoreCovHC3AdjStar_stack_tendstoInMeasure_zero_entries
    {μ : Measure Ω} {X : ℕ → Ω → (k → ℝ)} {y : ℕ → Ω → ℝ}
    (hEntry : ∀ a b : k, TendstoInMeasure μ
      (fun n ω =>
        sampleScoreCovLevAdjmtEntryStar
          (fun h => ((1 - h)⁻¹) ^ 2)
          (stackRegressors X n ω) (stackOutcomes y n ω) a b)
      atTop (fun _ => 0)) :
    TendstoInMeasure μ
      (fun n ω =>
        sampleScoreCovHC3AdjStar
          (stackRegressors X n ω) (stackOutcomes y n ω))
      atTop (fun _ => 0) := by
  simpa [sampleScoreCovHC3AdjStar] using
    sampleScoreCovLevAdjmtStar_stack_tendstoInMeasure_zero_entries
      (μ := μ) (X := X) (y := y)
      (weight := fun h => ((1 - h)⁻¹) ^ 2) hEntry

/-- HC2 adjustment entries are `oₚ(1)` once maximal leverage is `oₚ(1)` and
the corresponding residual absolute-weight averages are `Oₚ(1)`. -/
theorem sampleScoreCovHC2AdjEntryStar_tendstoInMeasure_zero_maxLevStar
    {μ : Measure Ω} {X : ℕ → Ω → (k → ℝ)} {y : ℕ → Ω → ℝ}
    (a b : k)
    (hMax : TendstoInMeasure μ
      (fun n ω => maxLeverageStar (stackRegressors X n ω))
      atTop (fun _ => 0))
    (hAbsWeight : BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovResAbsWtStar
          (stackRegressors X n ω) (stackOutcomes y n ω) a b)) :
    TendstoInMeasure μ
      (fun n ω =>
        sampleScoreCovLevAdjmtEntryStar (fun h => (1 - h)⁻¹)
          (stackRegressors X n ω) (stackOutcomes y n ω) a b)
      atTop (fun _ => 0) := by
  exact sampleScoreCovLevAdjmtEntryStar_tendstoInMeasure_zero_of_weight_norm
    (μ := μ) (X := X) (y := y) (weight := fun h => (1 - h)⁻¹) a b
    (levAdjWtNormStar_hc2_tendstoInMeasure_zero_maxLevStar
      (μ := μ) (X := X) hMax)
    hAbsWeight

/-- HC3 adjustment entries are `oₚ(1)` once maximal leverage is `oₚ(1)` and
the corresponding residual absolute-weight averages are `Oₚ(1)`. -/
theorem sampleScoreCovHC3AdjEntryStar_tendstoInMeasure_zero_maxLevStar
    {μ : Measure Ω} {X : ℕ → Ω → (k → ℝ)} {y : ℕ → Ω → ℝ}
    (a b : k)
    (hMax : TendstoInMeasure μ
      (fun n ω => maxLeverageStar (stackRegressors X n ω))
      atTop (fun _ => 0))
    (hAbsWeight : BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovResAbsWtStar
          (stackRegressors X n ω) (stackOutcomes y n ω) a b)) :
    TendstoInMeasure μ
      (fun n ω =>
        sampleScoreCovLevAdjmtEntryStar
          (fun h => ((1 - h)⁻¹) ^ 2)
          (stackRegressors X n ω) (stackOutcomes y n ω) a b)
      atTop (fun _ => 0) := by
  exact sampleScoreCovLevAdjmtEntryStar_tendstoInMeasure_zero_of_weight_norm
    (μ := μ) (X := X) (y := y) (weight := fun h => ((1 - h)⁻¹) ^ 2) a b
    (levAdjWtNormStar_hc3_tendstoInMeasure_zero_maxLevStar
      (μ := μ) (X := X) hMax)
    hAbsWeight

/-- HC2 adjustment convergence from maximal leverage and residual
absolute-weight boundedness. -/
theorem sampleScoreCovHC2AdjStar_stack_tendstoInMeasure_zero_maxLevStar
    {μ : Measure Ω} {X : ℕ → Ω → (k → ℝ)} {y : ℕ → Ω → ℝ}
    (hMax : TendstoInMeasure μ
      (fun n ω => maxLeverageStar (stackRegressors X n ω))
      atTop (fun _ => 0))
    (hAbsWeight : ∀ a b : k, BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovResAbsWtStar
          (stackRegressors X n ω) (stackOutcomes y n ω) a b)) :
    TendstoInMeasure μ
      (fun n ω =>
        sampleScoreCovHC2AdjStar
          (stackRegressors X n ω) (stackOutcomes y n ω))
      atTop (fun _ => 0) := by
  exact sampleScoreCovHC2AdjStar_stack_tendstoInMeasure_zero_entries
    (μ := μ) (X := X) (y := y) (fun a b =>
      sampleScoreCovHC2AdjEntryStar_tendstoInMeasure_zero_maxLevStar
        (μ := μ) (X := X) (y := y) a b hMax (hAbsWeight a b))

/-- HC3 adjustment convergence from maximal leverage and residual
absolute-weight boundedness. -/
theorem sampleScoreCovHC3AdjStar_stack_tendstoInMeasure_zero_maxLevStar
    {μ : Measure Ω} {X : ℕ → Ω → (k → ℝ)} {y : ℕ → Ω → ℝ}
    (hMax : TendstoInMeasure μ
      (fun n ω => maxLeverageStar (stackRegressors X n ω))
      atTop (fun _ => 0))
    (hAbsWeight : ∀ a b : k, BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovResAbsWtStar
          (stackRegressors X n ω) (stackOutcomes y n ω) a b)) :
    TendstoInMeasure μ
      (fun n ω =>
        sampleScoreCovHC3AdjStar
          (stackRegressors X n ω) (stackOutcomes y n ω))
      atTop (fun _ => 0) := by
  exact sampleScoreCovHC3AdjStar_stack_tendstoInMeasure_zero_entries
    (μ := μ) (X := X) (y := y) (fun a b =>
      sampleScoreCovHC3AdjEntryStar_tendstoInMeasure_zero_maxLevStar
        (μ := μ) (X := X) (y := y) a b hMax (hAbsWeight a b))

/-- **Theorem 7.6 residual-score expansion, entrywise form.**

Under the linear model, each residual score outer product decomposes into the
true-error score outer product, a cross term, and a quadratic estimation-error
term. This is the per-observation algebra behind feasible HC0 consistency. -/
theorem residualScoreOuter_linear_model_apply
    (X : Matrix n k ℝ) (β : k → ℝ) (e : n → ℝ) (i : n) (a b : k) :
    Matrix.vecMulVec
        (olsResidualStar X (X *ᵥ β + e) i • X i)
        (olsResidualStar X (X *ᵥ β + e) i • X i) a b =
      Matrix.vecMulVec (e i • X i) (e i • X i) a b -
        (2 * e i * (X i ⬝ᵥ (olsBetaStar X (X *ᵥ β + e) - β))) *
          Matrix.vecMulVec (X i) (X i) a b +
        (X i ⬝ᵥ (olsBetaStar X (X *ᵥ β + e) - β)) ^ 2 *
          Matrix.vecMulVec (X i) (X i) a b := by
  rw [olsResidualStar_linear_model_apply]
  simp [Matrix.vecMulVec_apply]
  ring

/-- Cross remainder in the HC0 residual-score expansion. -/
noncomputable def sampleScoreCovCrossRemainder
    (X : Matrix n k ℝ) (e : n → ℝ) (d : k → ℝ) : Matrix k k ℝ :=
  (Fintype.card n : ℝ)⁻¹ •
    ∑ i : n, (2 * e i * (X i ⬝ᵥ d)) • Matrix.vecMulVec (X i) (X i)

/-- Empirical third-moment weight multiplying one coordinate of `β̂ - β` in the
HC0 cross remainder. -/
noncomputable def sampleScoreCovCrossWeight
    (X : Matrix n k ℝ) (e : n → ℝ) (a b l : k) : ℝ :=
  (Fintype.card n : ℝ)⁻¹ * ∑ i : n, 2 * e i * X i l * X i a * X i b

set_option linter.flexible false in
omit [DecidableEq k] in
/-- Coordinate representation of the HC0 cross remainder as coefficient error
times empirical third-moment weights. -/
theorem sampleScoreCovCrossRemainder_apply_eq_sum_weight
    (X : Matrix n k ℝ) (e : n → ℝ) (d : k → ℝ) (a b : k) :
    sampleScoreCovCrossRemainder X e d a b =
      ∑ l : k, d l * sampleScoreCovCrossWeight X e a b l := by
  classical
  unfold sampleScoreCovCrossRemainder sampleScoreCovCrossWeight
  simp [Matrix.sum_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, dotProduct,
    Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]
  rw [Finset.sum_comm]

/-- Quadratic estimation-error remainder in the HC0 residual-score expansion. -/
noncomputable def sampleScoreCovQuadRem
    (X : Matrix n k ℝ) (d : k → ℝ) : Matrix k k ℝ :=
  (Fintype.card n : ℝ)⁻¹ •
    ∑ i : n, (X i ⬝ᵥ d) ^ 2 • Matrix.vecMulVec (X i) (X i)

/-- Empirical fourth-moment weight multiplying a pair of coefficient-error
coordinates in the HC0 quadratic remainder. -/
noncomputable def sampleScoreCovQuadraticWeight
    (X : Matrix n k ℝ) (a b l m : k) : ℝ :=
  (Fintype.card n : ℝ)⁻¹ * ∑ i : n, X i l * X i m * X i a * X i b

set_option linter.flexible false in
omit [DecidableEq k] in
/-- Coordinate representation of the HC0 quadratic remainder as products of
coefficient errors times empirical fourth-moment weights. -/
theorem sampleScoreCovQuadRem_apply_eq_sum_weight
    (X : Matrix n k ℝ) (d : k → ℝ) (a b : k) :
    sampleScoreCovQuadRem X d a b =
      ∑ l : k, ∑ m : k,
        d l * d m * sampleScoreCovQuadraticWeight X a b l m := by
  classical
  unfold sampleScoreCovQuadRem sampleScoreCovQuadraticWeight
  simp [Matrix.sum_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, dotProduct,
    Finset.mul_sum, pow_two, mul_assoc, mul_left_comm, mul_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  rw [Finset.sum_comm]

/-- **Theorem 7.6 residual-score expansion, sample-average form.**

Under the linear model, the residual HC0 middle matrix equals the true-error
middle matrix minus a cross remainder plus a quadratic estimation-error
remainder. -/
theorem sampleScoreCovStar_linear_model
    (X : Matrix n k ℝ) (β : k → ℝ) (e : n → ℝ) :
    sampleScoreCovStar X (X *ᵥ β + e) =
      sampleScoreCovIdeal X e -
        sampleScoreCovCrossRemainder X e
          (olsBetaStar X (X *ᵥ β + e) - β) +
        sampleScoreCovQuadRem X
          (olsBetaStar X (X *ᵥ β + e) - β) := by
  ext a b
  simp [sampleScoreCovStar, sampleScoreCovIdeal,
    sampleScoreCovCrossRemainder, sampleScoreCovQuadRem,
    Matrix.sum_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply,
    Matrix.vecMulVec_apply, Finset.mul_sum]
  ring_nf
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  ring_nf

/-- Descriptive public condition package for the current Lean proof behind the
robust covariance / t-statistic / Wald layer in Hansen Chapter 7.

This is stronger than bare textbook Assumption 7.2: it packages the score CLT
bundle together with the true-error score-outer-product WLLN assumptions used to
prove HC0 consistency, and the later HC1/HC2/HC3 public wrappers still build on
that stronger sufficient layer. -/
structure RobustCovarianceConsistencyConditions (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → (k → ℝ)) (e : ℕ → Ω → ℝ)
    extends ScoreCLTConditions μ X e where
  /-- Pairwise independence of the true-error score outer products. -/
  indep_score_outer : Pairwise ((· ⟂ᵢ[μ] ·) on
    (fun i ω => Matrix.vecMulVec (e i ω • X i ω) (e i ω • X i ω)))
  /-- Identical distribution of the true-error score outer products. -/
  ident_score_outer : ∀ i,
    IdentDistrib
      (fun ω => Matrix.vecMulVec (e i ω • X i ω) (e i ω • X i ω))
      (fun ω => Matrix.vecMulVec (e 0 ω • X 0 ω) (e 0 ω • X 0 ω)) μ μ
  /-- Integrability of the true-error score outer product. -/
  int_score_outer :
    Integrable (fun ω => Matrix.vecMulVec (e 0 ω • X 0 ω) (e 0 ω • X 0 ω)) μ

/-- Compatibility name for the HC0 proof bundle behind
`RobustCovarianceConsistencyConditions`. -/
abbrev SampleHC0Assumption76
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → (k → ℝ)) (e : ℕ → Ω → ℝ) :=
  RobustCovarianceConsistencyConditions μ X e

namespace RobustCovarianceConsistencyConditions

/-- Compatibility projection for code that still names the internal HC0 bundle. -/
abbrev toSampleHC0Assumption76
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ}
    (h : RobustCovarianceConsistencyConditions μ X e) :
    SampleHC0Assumption76 μ X e := h

/-- Compatibility projection onto the CLT condition package. -/
abbrev toSampleCLTAssumption72
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ}
    (h : RobustCovarianceConsistencyConditions μ X e) :
    SampleCLTAssumption72 μ X e := h.toScoreCLTConditions

/-- Compatibility constructor from the old internal HC0-bundle name. -/
abbrev ofSample
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ}
    (h : SampleHC0Assumption76 μ X e) :
    RobustCovarianceConsistencyConditions μ X e := h

end RobustCovarianceConsistencyConditions

end Assumption72

end HansenEconometrics
