import HansenEconometrics.Chapter13GMM.Asymptotics
import HansenEconometrics.Chapter12InstrumentalVariables.Overidentification

/-!
# Chapter 13 — efficient and feasible GMM

This module contains the probability-facing proofs for Hansen Theorems 13.6
and 13.7. It reuses Chapter 12's homoskedastic score-covariance identity and
robust residual-middle consistency.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped Matrix Matrix.Norms.Elementwise Function Topology MeasureTheory
  ProbabilityTheory ENNReal

namespace HansenEconometrics

@[reducible]
private noncomputable def matrixBorelMeasurableSpaceInst
    {i j : Type*} [Fintype i] [Fintype j] :
    MeasurableSpace (Matrix i j ℝ) :=
  matrixBorelMeasurableSpace i j

private lemma matrixBorelSpaceInst
    {i j : Type*} [Fintype i] [Fintype j] :
    @BorelSpace (Matrix i j ℝ) _
      (matrixBorelMeasurableSpaceInst (i := i) (j := j)) :=
  matrixBorelSpace i j

attribute [local instance] matrixBorelMeasurableSpaceInst matrixBorelSpaceInst

variable {OmegaSpace : Type*} [MeasurableSpace OmegaSpace]
variable {mu : Measure OmegaSpace} [IsProbabilityMeasure mu]
variable {k l : Type*}
variable [Fintype k] [Fintype l] [DecidableEq k] [DecidableEq l]

/-! ## Hansen Theorem 13.6 -/

/-- **Hansen Theorem 13.6.** Under Assumption 12.2 and conditional
homoskedasticity, the population 2SLS weight attains the efficient GMM
covariance. -/
theorem twoSLSWeight_is_efficientGMM_of_assumption12_2_homoskedastic
    [Nonempty l]
    {Z : ℕ → OmegaSpace → l → ℝ}
    {X : ℕ → OmegaSpace → k → ℝ}
    {e : ℕ → OmegaSpace → ℝ}
    (h : TwoSLSResidualJointIidMixedMomentPositiveCovarianceConditions
      mu Z X e)
    (hZ0 : Measurable (Z 0))
    [SigmaFinite (mu.trim (conditioningSpace_le hZ0))]
    (hhomo : HomoskedasticErrorVariance mu Z e) :
    gmmAsymptoticVarianceStar
        (twoSLSCombinedQZX (popGram mu (twoSLSCombinedRegressors Z X)))
        (twoSLSCombinedQZZ
          (popGram mu (twoSLSCombinedRegressors Z X)))⁻¹
        (scoreCovMat mu Z e) =
      (gmmPopulationGram
        (twoSLSCombinedQZX (popGram mu (twoSLSCombinedRegressors Z X)))
        (scoreCovMat mu Z e)⁻¹)⁻¹ := by
  have hcov :=
    scoreCovMat_eq_errorVariance_smul_twoSLSCombinedQZZ_of_assumption12_2_homoskedastic
      (μ := mu) (Z := Z) (X := X) (e := e) h hZ0 hhomo
  have hsigma2 : 0 < errorVariance mu e := by
    classical
    obtain ⟨i⟩ := (inferInstance : Nonempty l)
    have hdiag : 0 < (scoreCovMat mu Z e) i i :=
      Matrix.PosDef.diag_pos h.omega_posDef
    have hqdiag : 0 <
        twoSLSCombinedQZZ
          (popGram mu (twoSLSCombinedRegressors Z X)) i i :=
      Matrix.PosDef.diag_pos h.qzz_posDef
    rw [hcov] at hdiag
    have hmul : 0 < errorVariance mu e *
        twoSLSCombinedQZZ
          (popGram mu (twoSLSCombinedRegressors Z X)) i i := by
      simpa [Pi.smul_apply, smul_eq_mul] using hdiag
    exact pos_of_mul_pos_left hmul hqdiag.le
  exact gmmAsymptoticVarianceStar_twoSLSWeight_efficient
    (twoSLSCombinedQZX (popGram mu (twoSLSCombinedRegressors Z X)))
    (twoSLSCombinedQZZ (popGram mu (twoSLSCombinedRegressors Z X)))
    (scoreCovMat mu Z e) (errorVariance mu e)
    h.omega_posDef h.qzx_rank hcov (ne_of_gt hsigma2)

/-- **Hansen Theorem 13.6, observed-row form.** Literal observed-row
Assumption 12.2 and conditional homoskedasticity imply that the population
2SLS weight attains the efficient GMM covariance. -/
theorem twoSLSWeight_is_efficientGMM_of_assumption12_2_observedRows_homoskedastic
    [Nonempty l]
    {Z : ℕ → OmegaSpace → l → ℝ}
    {X : ℕ → OmegaSpace → k → ℝ}
    {e Y : ℕ → OmegaSpace → ℝ}
    {b : k → ℝ}
    (h : TwoSLSObservedIidFourthMomentPositiveCovarianceConditions
      mu Z X e Y b)
    (hZ0 : Measurable (Z 0))
    [SigmaFinite (mu.trim (conditioningSpace_le hZ0))]
    (hhomo : HomoskedasticErrorVariance mu Z e) :
    gmmAsymptoticVarianceStar
        (twoSLSCombinedQZX (popGram mu (twoSLSCombinedRegressors Z X)))
        (twoSLSCombinedQZZ
          (popGram mu (twoSLSCombinedRegressors Z X)))⁻¹
        (scoreCovMat mu Z e) =
      (gmmPopulationGram
        (twoSLSCombinedQZX (popGram mu (twoSLSCombinedRegressors Z X)))
        (scoreCovMat mu Z e)⁻¹)⁻¹ :=
  twoSLSWeight_is_efficientGMM_of_assumption12_2_homoskedastic
    h.toJointIidMixedMomentConditions hZ0 hhomo

/-! ## Hansen Theorem 13.7 -/

/-- Hansen equation (13.8) weight: the nonsingular inverse of the uncentered
2SLS residual-score second moment. -/
noncomputable def gmmUncenteredTwoStepWeightStar
    {n : Type*} [Fintype n]
    (Z : Matrix n l ℝ) (X : Matrix n k ℝ) (y : n → ℝ) :
    Matrix l l ℝ :=
  (twoSLSOmegaHatStar Z X y)⁻¹

/-- Mean 2SLS residual score `n⁻¹ Z'e_tilde`. -/
noncomputable def gmmResidualScoreMeanStar
    {n : Type*} [Fintype n]
    (Z : Matrix n l ℝ) (X : Matrix n k ℝ) (y : n → ℝ) : l → ℝ :=
  sampleCrossMoment Z (twoSLSResidualStar Z X y)

/-- Hansen equation (13.9), written as the uncentered residual-score second
moment minus the outer product of its sample mean. -/
noncomputable def gmmCenteredOmegaHatStar
    {n : Type*} [Fintype n]
    (Z : Matrix n l ℝ) (X : Matrix n k ℝ) (y : n → ℝ) :
    Matrix l l ℝ :=
  twoSLSOmegaHatStar Z X y -
    Matrix.vecMulVec
      (gmmResidualScoreMeanStar Z X y) (gmmResidualScoreMeanStar Z X y)

/-- Hansen equation (13.9) weight: the nonsingular inverse of the centered
2SLS residual-score covariance. -/
noncomputable def gmmCenteredTwoStepWeightStar
    {n : Type*} [Fintype n]
    (Z : Matrix n l ℝ) (X : Matrix n k ℝ) (y : n → ℝ) :
    Matrix l l ℝ :=
  (gmmCenteredOmegaHatStar Z X y)⁻¹

/-- The centered residual score is the true score minus the sample cross
moment times the 2SLS coefficient error. -/
theorem gmmResidualScoreMeanStar_linear_model
    {n : Type*} [Fintype n]
    (Z : Matrix n l ℝ) (X : Matrix n k ℝ) (b : k → ℝ) (e : n → ℝ) :
    gmmResidualScoreMeanStar Z X (X *ᵥ b + e) =
      sampleCrossMoment Z e - sampleQZX Z X *ᵥ
        (twoSLSBetaStar Z X (X *ᵥ b + e) - b) := by
  rw [gmmResidualScoreMeanStar, twoSLSResidualStar_linear_model,
    sampleCrossMoment_sub_mulVec]

omit [IsProbabilityMeasure mu] in
/-- Residual-score mean measurability from measurable observation rows. -/
theorem gmmResidualScoreMeanStar_aestronglyMeasurable_of_rows
    {n : ℕ}
    {Z : ℕ → OmegaSpace → l → ℝ}
    {X : ℕ → OmegaSpace → k → ℝ}
    {Y : ℕ → OmegaSpace → ℝ}
    (hZ : ∀ i, AEStronglyMeasurable (Z i) mu)
    (hX : ∀ i, AEStronglyMeasurable (X i) mu)
    (hY : ∀ i, AEStronglyMeasurable (Y i) mu) :
    AEStronglyMeasurable
      (fun omega =>
        gmmResidualScoreMeanStar
          (stackRegressors Z n omega) (stackRegressors X n omega)
          (stackOutcomes Y n omega)) mu := by
  let Zmat : OmegaSpace → Matrix (Fin n) l ℝ :=
    fun omega => stackRegressors Z n omega
  let residual : OmegaSpace → Fin n → ℝ := fun omega =>
    twoSLSResidualStar
      (stackRegressors Z n omega) (stackRegressors X n omega)
      (stackOutcomes Y n omega)
  have hZmat : AEStronglyMeasurable Zmat mu := by
    simpa [Zmat, stackRegressors] using
      stackMatrix_aestronglyMeasurable (μ := mu) hZ
  have hres : AEStronglyMeasurable residual mu := by
    simpa [residual] using
      twoSLSResidualStar_aestronglyMeasurable_of_rows
        (μ := mu) (Z := Z) (X := X) (Y := Y) hZ hX hY
  have hZt : AEStronglyMeasurable (fun omega => (Zmat omega)ᵀ) mu :=
    continuous_id.matrix_transpose.comp_aestronglyMeasurable hZmat
  have hcross : AEStronglyMeasurable
      (fun omega => (Zmat omega)ᵀ *ᵥ residual omega) mu :=
    (Continuous.matrix_mulVec continuous_fst continuous_snd)
      |>.comp_aestronglyMeasurable (hZt.prodMk hres)
  simpa [gmmResidualScoreMeanStar, sampleCrossMoment, Zmat, residual] using
    hcross.const_smul ((Fintype.card (Fin n) : ℝ)⁻¹)

omit [IsProbabilityMeasure mu] in
/-- Centered residual-score covariance measurability from measurable rows. -/
theorem gmmCenteredOmegaHatStar_aestronglyMeasurable_of_rows
    {n : ℕ}
    {Z : ℕ → OmegaSpace → l → ℝ}
    {X : ℕ → OmegaSpace → k → ℝ}
    {Y : ℕ → OmegaSpace → ℝ}
    (hOmega : AEStronglyMeasurable
      (fun omega =>
        twoSLSOmegaHatStar
          (stackRegressors Z n omega) (stackRegressors X n omega)
          (stackOutcomes Y n omega)) mu)
    (hZ : ∀ i, AEStronglyMeasurable (Z i) mu)
    (hX : ∀ i, AEStronglyMeasurable (X i) mu)
    (hY : ∀ i, AEStronglyMeasurable (Y i) mu) :
    AEStronglyMeasurable
      (fun omega =>
        gmmCenteredOmegaHatStar
          (stackRegressors Z n omega) (stackRegressors X n omega)
          (stackOutcomes Y n omega)) mu := by
  have hMean := gmmResidualScoreMeanStar_aestronglyMeasurable_of_rows
    (mu := mu) (n := n) (Z := Z) (X := X) (Y := Y) hZ hX hY
  have houter_cont : Continuous
      (fun v : l → ℝ => Matrix.vecMulVec v v) := by
    fun_prop
  exact hOmega.sub (houter_cont.comp_aestronglyMeasurable hMean)

omit [IsProbabilityMeasure mu] in
/-- Centered two-step weight measurability from measurable observation rows. -/
theorem gmmCenteredTwoStepWeightStar_aestronglyMeasurable_of_rows
    {n : ℕ}
    {Z : ℕ → OmegaSpace → l → ℝ}
    {X : ℕ → OmegaSpace → k → ℝ}
    {Y : ℕ → OmegaSpace → ℝ}
    (hOmega : AEStronglyMeasurable
      (fun omega =>
        twoSLSOmegaHatStar
          (stackRegressors Z n omega) (stackRegressors X n omega)
          (stackOutcomes Y n omega)) mu)
    (hZ : ∀ i, AEStronglyMeasurable (Z i) mu)
    (hX : ∀ i, AEStronglyMeasurable (X i) mu)
    (hY : ∀ i, AEStronglyMeasurable (Y i) mu) :
    AEStronglyMeasurable
      (fun omega =>
        gmmCenteredTwoStepWeightStar
          (stackRegressors Z n omega) (stackRegressors X n omega)
          (stackOutcomes Y n omega)) mu :=
  aestronglyMeasurable_matrix_inv
    (gmmCenteredOmegaHatStar_aestronglyMeasurable_of_rows
      (mu := mu) (Z := Z) (X := X) (Y := Y) hOmega hZ hX hY)

/-- The uncentered two-step weight converges to the efficient weight under the
Chapter 12 robust-middle consistency package. -/
theorem gmmUncenteredTwoStepWeightStar_tendstoInMeasure
    {Z : ℕ → OmegaSpace → l → ℝ}
    {X : ℕ → OmegaSpace → k → ℝ}
    {e Y : ℕ → OmegaSpace → ℝ}
    (h : TwoSLSResidualJointIidMixedMomentPositiveCovarianceConditions
      mu Z X e)
    (b : k → ℝ)
    (hmodel : ∀ i omega, Y i omega = (X i omega) ⬝ᵥ b + e i omega) :
    TendstoInMeasure mu
      (fun n omega =>
        gmmUncenteredTwoStepWeightStar
          (stackRegressors Z n omega) (stackRegressors X n omega)
          (stackOutcomes Y n omega))
      atTop (fun _ => (scoreCovMat mu Z e)⁻¹) := by
  let hCov := h.toCovarianceMomentConsistencyConditions b hmodel
  exact tendstoInMeasure_matrix_inv hCov.omega_meas hCov.omega_tendsto
    (fun _ =>
      (Matrix.isUnit_iff_isUnit_det _).mp h.omega_posDef.isUnit)

set_option maxHeartbeats 1200000 in
-- The proof assembles several finite-dimensional vector and matrix CMT steps.
/-- The sample mean of the 2SLS residual score converges to zero. This is the
vanishing correction that makes Hansen's centered and uncentered weights
asymptotically equivalent. -/
theorem gmmResidualScoreMeanStar_tendstoInMeasure_zero
    {Z : ℕ → OmegaSpace → l → ℝ}
    {X : ℕ → OmegaSpace → k → ℝ}
    {e Y : ℕ → OmegaSpace → ℝ}
    (h : TwoSLSResidualJointIidMixedMomentPositiveCovarianceConditions
      mu Z X e)
    (b : k → ℝ)
    (hmodel : ∀ i omega, Y i omega = (X i omega) ⬝ᵥ b + e i omega) :
    TendstoInMeasure mu
      (fun n omega =>
        gmmResidualScoreMeanStar
          (stackRegressors Z n omega) (stackRegressors X n omega)
          (stackOutcomes Y n omega))
      atTop (fun _ => 0) := by
  let hCov := h.toCovarianceMomentConsistencyConditions b hmodel
  let hMom := hCov.sample_moments
  have hY : ∀ i, AEStronglyMeasurable (Y i) mu :=
    outcome_aestronglyMeasurable_of_linear_model b
      h.x_aestronglyMeasurable h.e_aestronglyMeasurable hmodel
  have hBetaMeas : ∀ n, AEStronglyMeasurable
      (fun omega =>
        twoSLSBetaStar
          (stackRegressors Z n omega) (stackRegressors X n omega)
          (stackOutcomes Y n omega)) mu := fun n =>
    twoSLSBetaStar_aestronglyMeasurable_of_rows
      (μ := mu) (n := n) (Z := Z) (X := X) (Y := Y)
      h.z_aestronglyMeasurable h.x_aestronglyMeasurable hY
  have hBeta : TendstoInMeasure mu
      (fun n omega =>
        twoSLSBetaStar
          (stackRegressors Z n omega) (stackRegressors X n omega)
          (stackOutcomes Y n omega))
      atTop (fun _ => b) :=
    twoSLSBetaStar_tendstoInMeasure_beta_of_sample_moments_model
      hMom b hmodel
  have hDeltaMeas : ∀ n, AEStronglyMeasurable
      (fun omega =>
        twoSLSBetaStar
            (stackRegressors Z n omega) (stackRegressors X n omega)
            (stackOutcomes Y n omega) - b) mu := fun n =>
    (hBetaMeas n).sub aestronglyMeasurable_const
  have hDelta : TendstoInMeasure mu
      (fun n omega =>
        twoSLSBetaStar
            (stackRegressors Z n omega) (stackRegressors X n omega)
            (stackOutcomes Y n omega) - b)
      atTop (fun _ => 0) := by
    refine tendstoInMeasure_pi fun j => ?_
    simpa [Pi.sub_apply] using
      TendstoInMeasure.sub_limit_zero_real
        (TendstoInMeasure.pi_apply hBeta j)
  have hProduct : TendstoInMeasure mu
      (fun n omega =>
        sampleQZX (stackRegressors Z n omega)
            (stackRegressors X n omega) *ᵥ
          (twoSLSBetaStar
              (stackRegressors Z n omega) (stackRegressors X n omega)
              (stackOutcomes Y n omega) - b))
      atTop (fun _ => 0) := by
    simpa using tendstoInMeasure_mulVec_rect
      hMom.qzx_meas hDeltaMeas hMom.qzx_tendsto hDelta
  have hProductMeas : ∀ n, AEStronglyMeasurable
      (fun omega =>
        sampleQZX (stackRegressors Z n omega)
            (stackRegressors X n omega) *ᵥ
          (twoSLSBetaStar
              (stackRegressors Z n omega) (stackRegressors X n omega)
              (stackOutcomes Y n omega) - b)) mu := fun n =>
    (Continuous.matrix_mulVec continuous_fst continuous_snd)
      |>.comp_aestronglyMeasurable ((hMom.qzx_meas n).prodMk (hDeltaMeas n))
  have hDifference : TendstoInMeasure mu
      (fun n omega =>
        sampleCrossMoment (stackRegressors Z n omega) (stackErrors e n omega) -
          sampleQZX (stackRegressors Z n omega)
              (stackRegressors X n omega) *ᵥ
            (twoSLSBetaStar
                (stackRegressors Z n omega) (stackRegressors X n omega)
                (stackOutcomes Y n omega) - b))
      atTop (fun _ => 0) := by
    have hraw := tendstoInMeasure_continuous_comp
      (fun n => (hMom.score_meas n).prodMk (hProductMeas n))
      (tendstoInMeasure_prodMk hMom.score_tendsto_zero hProduct)
      (continuous_fst.sub continuous_snd)
    simpa only [sub_zero] using hraw
  refine TendstoInMeasure.congr (fun n => ?_) EventuallyEq.rfl hDifference
  exact ae_of_all mu fun omega => by
    have hYstack := stack_linear_model X e Y b hmodel n omega
    change
      sampleCrossMoment (stackRegressors Z n omega) (stackErrors e n omega) -
          sampleQZX (stackRegressors Z n omega)
              (stackRegressors X n omega) *ᵥ
            (twoSLSBetaStar
                (stackRegressors Z n omega) (stackRegressors X n omega)
                (stackOutcomes Y n omega) - b) =
        gmmResidualScoreMeanStar
          (stackRegressors Z n omega) (stackRegressors X n omega)
          (stackOutcomes Y n omega)
    rw [hYstack, gmmResidualScoreMeanStar_linear_model]

set_option maxHeartbeats 1200000 in
-- The centered covariance uses a product-space CMT for matrix subtraction.
/-- Hansen's centered residual-score covariance has the same probability
limit as the uncentered residual-score second moment. -/
theorem gmmCenteredOmegaHatStar_tendstoInMeasure
    {Z : ℕ → OmegaSpace → l → ℝ}
    {X : ℕ → OmegaSpace → k → ℝ}
    {e Y : ℕ → OmegaSpace → ℝ}
    (h : TwoSLSResidualJointIidMixedMomentPositiveCovarianceConditions
      mu Z X e)
    (b : k → ℝ)
    (hmodel : ∀ i omega, Y i omega = (X i omega) ⬝ᵥ b + e i omega) :
    TendstoInMeasure mu
      (fun n omega =>
        gmmCenteredOmegaHatStar
          (stackRegressors Z n omega) (stackRegressors X n omega)
          (stackOutcomes Y n omega))
      atTop (fun _ => scoreCovMat mu Z e) := by
  let hCov := h.toCovarianceMomentConsistencyConditions b hmodel
  have hY : ∀ i, AEStronglyMeasurable (Y i) mu :=
    outcome_aestronglyMeasurable_of_linear_model b
      h.x_aestronglyMeasurable h.e_aestronglyMeasurable hmodel
  have hMeanMeas : ∀ n, AEStronglyMeasurable
      (fun omega =>
        gmmResidualScoreMeanStar
          (stackRegressors Z n omega) (stackRegressors X n omega)
          (stackOutcomes Y n omega)) mu := fun n =>
    gmmResidualScoreMeanStar_aestronglyMeasurable_of_rows
      (mu := mu) (n := n) (Z := Z) (X := X) (Y := Y)
      h.z_aestronglyMeasurable h.x_aestronglyMeasurable hY
  have hMean := gmmResidualScoreMeanStar_tendstoInMeasure_zero h b hmodel
  have houter_cont : Continuous
      (fun v : l → ℝ => Matrix.vecMulVec v v) := by
    fun_prop
  have hOuterMeas : ∀ n, AEStronglyMeasurable
      (fun omega =>
        Matrix.vecMulVec
          (gmmResidualScoreMeanStar
            (stackRegressors Z n omega) (stackRegressors X n omega)
            (stackOutcomes Y n omega))
          (gmmResidualScoreMeanStar
            (stackRegressors Z n omega) (stackRegressors X n omega)
            (stackOutcomes Y n omega))) mu := fun n =>
    houter_cont.comp_aestronglyMeasurable (hMeanMeas n)
  have hOuter : TendstoInMeasure mu
      (fun n omega =>
        Matrix.vecMulVec
          (gmmResidualScoreMeanStar
            (stackRegressors Z n omega) (stackRegressors X n omega)
            (stackOutcomes Y n omega))
          (gmmResidualScoreMeanStar
            (stackRegressors Z n omega) (stackRegressors X n omega)
            (stackOutcomes Y n omega)))
      atTop (fun _ => 0) := by
    simpa [Matrix.vecMulVec_apply] using
      tendstoInMeasure_continuous_comp hMeanMeas hMean houter_cont
  have hraw := tendstoInMeasure_continuous_comp
    (fun n => (hCov.omega_meas n).prodMk (hOuterMeas n))
    (tendstoInMeasure_prodMk hCov.omega_tendsto hOuter)
    (continuous_fst.sub continuous_snd)
  simpa [gmmCenteredOmegaHatStar] using hraw

/-- Hansen's centered two-step weight converges to the efficient population
weight. -/
theorem gmmCenteredTwoStepWeightStar_tendstoInMeasure
    {Z : ℕ → OmegaSpace → l → ℝ}
    {X : ℕ → OmegaSpace → k → ℝ}
    {e Y : ℕ → OmegaSpace → ℝ}
    (h : TwoSLSResidualJointIidMixedMomentPositiveCovarianceConditions
      mu Z X e)
    (b : k → ℝ)
    (hmodel : ∀ i omega, Y i omega = (X i omega) ⬝ᵥ b + e i omega) :
    TendstoInMeasure mu
      (fun n omega =>
        gmmCenteredTwoStepWeightStar
          (stackRegressors Z n omega) (stackRegressors X n omega)
          (stackOutcomes Y n omega))
      atTop (fun _ => (scoreCovMat mu Z e)⁻¹) := by
  let hCov := h.toCovarianceMomentConsistencyConditions b hmodel
  have hY : ∀ i, AEStronglyMeasurable (Y i) mu :=
    outcome_aestronglyMeasurable_of_linear_model b
      h.x_aestronglyMeasurable h.e_aestronglyMeasurable hmodel
  have hCenteredMeas : ∀ n, AEStronglyMeasurable
      (fun omega =>
        gmmCenteredOmegaHatStar
          (stackRegressors Z n omega) (stackRegressors X n omega)
          (stackOutcomes Y n omega)) mu := fun n =>
    gmmCenteredOmegaHatStar_aestronglyMeasurable_of_rows
      (mu := mu) (n := n) (Z := Z) (X := X) (Y := Y)
      (hCov.omega_meas n) h.z_aestronglyMeasurable
      h.x_aestronglyMeasurable hY
  exact tendstoInMeasure_matrix_inv hCenteredMeas
    (gmmCenteredOmegaHatStar_tendstoInMeasure h b hmodel)
    (fun _ =>
      (Matrix.isUnit_iff_isUnit_det _).mp h.omega_posDef.isUnit)

/-- **Hansen Theorem 13.7, uncentered form.** The two-step GMM estimator based
on equation (13.8) has the efficient Gaussian limit. -/
theorem gmmBetaOrZero_uncenteredTwoStep_tendstoInDistribution
    {Z : ℕ → OmegaSpace → l → ℝ}
    {X : ℕ → OmegaSpace → k → ℝ}
    {e Y : ℕ → OmegaSpace → ℝ}
    (h : TwoSLSResidualJointIidMixedMomentPositiveCovarianceConditions
      mu Z X e)
    (b : k → ℝ)
    (hmodel : ∀ i omega, Y i omega = (X i omega) ⬝ᵥ b + e i omega) :
    TendstoInDistribution
      (fun (n : ℕ) omega =>
        Real.sqrt (n : ℝ) •
          (gmmBetaOrZero
            (stackRegressors X n omega) (stackRegressors Z n omega)
            (stackOutcomes Y n omega)
            (gmmUncenteredTwoStepWeightStar
              (stackRegressors Z n omega) (stackRegressors X n omega)
              (stackOutcomes Y n omega)) - b))
      atTop (fun z : EuclideanSpace ℝ k => z.ofLp) (fun _ => mu)
      (multivariateGaussian 0
        ((gmmPopulationGram
          (twoSLSCombinedQZX
            (popGram mu (twoSLSCombinedRegressors Z X)))
          (scoreCovMat mu Z e)⁻¹)⁻¹)) := by
  let hIid :=
    h.toTwoSLSResidualJointIidFourthMomentPositiveCovarianceConditions
      |>.toIidFourthConditions
  let hGram : TwoSLSGramScoreCLTPositiveCovarianceConditions mu Z X e :=
    hIid.toGramConditions
  let hCov := h.toCovarianceMomentConsistencyConditions b hmodel
  have hWeightMeas : ∀ n, AEStronglyMeasurable
      (fun omega =>
        gmmUncenteredTwoStepWeightStar
          (stackRegressors Z n omega) (stackRegressors X n omega)
          (stackOutcomes Y n omega)) mu :=
    fun n => aestronglyMeasurable_matrix_inv (hCov.omega_meas n)
  have hY : ∀ i, AEStronglyMeasurable (Y i) mu :=
    outcome_aestronglyMeasurable_of_linear_model b
      h.x_aestronglyMeasurable h.e_aestronglyMeasurable hmodel
  exact gmmBetaOrZero_tendstoInDistribution_efficient_of_assumption12_2
    hGram hWeightMeas
    (gmmUncenteredTwoStepWeightStar_tendstoInMeasure h b hmodel)
    b hmodel
    (fun n => gmmBetaOrZero_scaled_centered_aemeasurable_of_rows
      (mu := mu) (Z := Z) (X := X) (Y := Y)
      h.z_aestronglyMeasurable h.x_aestronglyMeasurable hY
      (hWeightMeas n) b)

/-- **Hansen Theorem 13.7, observed-row uncentered form.** The two-step GMM
estimator using equation (13.8) has the efficient Gaussian limit under the
literal observed-row Assumption 12.2 package. -/
theorem gmmBetaOrZero_uncenteredTwoStep_tendstoInDistribution_observedRows
    {Z : ℕ → OmegaSpace → l → ℝ}
    {X : ℕ → OmegaSpace → k → ℝ}
    {e Y : ℕ → OmegaSpace → ℝ}
    {b : k → ℝ}
    (h : TwoSLSObservedIidFourthMomentPositiveCovarianceConditions
      mu Z X e Y b) :
    TendstoInDistribution
      (fun (n : ℕ) omega =>
        Real.sqrt (n : ℝ) •
          (gmmBetaOrZero
            (stackRegressors X n omega) (stackRegressors Z n omega)
            (stackOutcomes Y n omega)
            (gmmUncenteredTwoStepWeightStar
              (stackRegressors Z n omega) (stackRegressors X n omega)
              (stackOutcomes Y n omega)) - b))
      atTop (fun z : EuclideanSpace ℝ k => z.ofLp) (fun _ => mu)
      (multivariateGaussian 0
        ((gmmPopulationGram
          (twoSLSCombinedQZX
            (popGram mu (twoSLSCombinedRegressors Z X)))
          (scoreCovMat mu Z e)⁻¹)⁻¹)) :=
  gmmBetaOrZero_uncenteredTwoStep_tendstoInDistribution
    h.toJointIidMixedMomentConditions b h.model

/-- **Hansen Theorem 13.7, centered form.** The two-step GMM estimator based
on equation (13.9) has the efficient Gaussian limit. -/
theorem gmmBetaOrZero_centeredTwoStep_tendstoInDistribution
    {Z : ℕ → OmegaSpace → l → ℝ}
    {X : ℕ → OmegaSpace → k → ℝ}
    {e Y : ℕ → OmegaSpace → ℝ}
    (h : TwoSLSResidualJointIidMixedMomentPositiveCovarianceConditions
      mu Z X e)
    (b : k → ℝ)
    (hmodel : ∀ i omega, Y i omega = (X i omega) ⬝ᵥ b + e i omega) :
    TendstoInDistribution
      (fun (n : ℕ) omega =>
        Real.sqrt (n : ℝ) •
          (gmmBetaOrZero
            (stackRegressors X n omega) (stackRegressors Z n omega)
            (stackOutcomes Y n omega)
            (gmmCenteredTwoStepWeightStar
              (stackRegressors Z n omega) (stackRegressors X n omega)
              (stackOutcomes Y n omega)) - b))
      atTop (fun z : EuclideanSpace ℝ k => z.ofLp) (fun _ => mu)
      (multivariateGaussian 0
        ((gmmPopulationGram
          (twoSLSCombinedQZX
            (popGram mu (twoSLSCombinedRegressors Z X)))
          (scoreCovMat mu Z e)⁻¹)⁻¹)) := by
  let hIid :=
    h.toTwoSLSResidualJointIidFourthMomentPositiveCovarianceConditions
      |>.toIidFourthConditions
  let hGram : TwoSLSGramScoreCLTPositiveCovarianceConditions mu Z X e :=
    hIid.toGramConditions
  let hCov := h.toCovarianceMomentConsistencyConditions b hmodel
  have hY : ∀ i, AEStronglyMeasurable (Y i) mu :=
    outcome_aestronglyMeasurable_of_linear_model b
      h.x_aestronglyMeasurable h.e_aestronglyMeasurable hmodel
  have hWeightMeas : ∀ n, AEStronglyMeasurable
      (fun omega =>
        gmmCenteredTwoStepWeightStar
          (stackRegressors Z n omega) (stackRegressors X n omega)
          (stackOutcomes Y n omega)) mu := fun n =>
    gmmCenteredTwoStepWeightStar_aestronglyMeasurable_of_rows
      (mu := mu) (n := n) (Z := Z) (X := X) (Y := Y)
      (hCov.omega_meas n) h.z_aestronglyMeasurable
      h.x_aestronglyMeasurable hY
  exact gmmBetaOrZero_tendstoInDistribution_efficient_of_assumption12_2
    hGram hWeightMeas
    (gmmCenteredTwoStepWeightStar_tendstoInMeasure h b hmodel)
    b hmodel
    (fun n => gmmBetaOrZero_scaled_centered_aemeasurable_of_rows
      (mu := mu) (Z := Z) (X := X) (Y := Y)
      h.z_aestronglyMeasurable h.x_aestronglyMeasurable hY
      (hWeightMeas n) b)

/-- **Hansen Theorem 13.7, observed-row centered form.** The two-step GMM
estimator using equation (13.9) has the efficient Gaussian limit under the
literal observed-row Assumption 12.2 package. -/
theorem gmmBetaOrZero_centeredTwoStep_tendstoInDistribution_observedRows
    {Z : ℕ → OmegaSpace → l → ℝ}
    {X : ℕ → OmegaSpace → k → ℝ}
    {e Y : ℕ → OmegaSpace → ℝ}
    {b : k → ℝ}
    (h : TwoSLSObservedIidFourthMomentPositiveCovarianceConditions
      mu Z X e Y b) :
    TendstoInDistribution
      (fun (n : ℕ) omega =>
        Real.sqrt (n : ℝ) •
          (gmmBetaOrZero
            (stackRegressors X n omega) (stackRegressors Z n omega)
            (stackOutcomes Y n omega)
            (gmmCenteredTwoStepWeightStar
              (stackRegressors Z n omega) (stackRegressors X n omega)
              (stackOutcomes Y n omega)) - b))
      atTop (fun z : EuclideanSpace ℝ k => z.ofLp) (fun _ => mu)
      (multivariateGaussian 0
        ((gmmPopulationGram
          (twoSLSCombinedQZX
            (popGram mu (twoSLSCombinedRegressors Z X)))
          (scoreCovMat mu Z e)⁻¹)⁻¹)) :=
  gmmBetaOrZero_centeredTwoStep_tendstoInDistribution
    h.toJointIidMixedMomentConditions b h.model

end HansenEconometrics
