import HansenEconometrics.Chapter13GMM
import HansenEconometrics.Chapter12InstrumentalVariables.Asymptotics

/-!
# Chapter 13 — GMM asymptotic interfaces

This module contains the convergence and distributional layer for linear GMM.
It keeps probability and measure-theoretic details out of the chapter-facing
finite-sample file.

The proof architecture has three parts:

* normalize raw sample moments without changing the GMM estimator;
* pass sample moment derivatives and weight matrices through the Star influence
  matrix by the continuous mapping theorem;
* combine that random linear map with Chapter 7's instrument-score CLT.
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

/-! ## Raw and normalized sample estimators -/

section Normalization

variable {n k l : Type*}
variable [Fintype n] [Fintype k] [Fintype l] [DecidableEq k]

/-- Star GMM written with the normalized sample derivative `n⁻¹Z'X` and
normalized outcome moment `n⁻¹Z'Y`. -/
noncomputable def gmmNormalizedBetaStar
    (X : Matrix n k ℝ) (Z : Matrix n l ℝ) (y : n → ℝ)
    (W : Matrix l l ℝ) : k → ℝ :=
  LinearGMM.betaStar (sampleQZX Z X) (sampleCrossMoment Z y) W

/-- On a nonempty sample, normalization does not change Star GMM. -/
theorem gmmBetaStar_eq_normalized
    (X : Matrix n k ℝ) (Z : Matrix n l ℝ) (y : n → ℝ)
    (W : Matrix l l ℝ) [Nonempty n] :
    gmmBetaStar X Z y W = gmmNormalizedBetaStar X Z y W := by
  have hn : (Fintype.card n : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hQ :
      (Fintype.card n : ℝ) • sampleQZX Z X = Zᵀ * X := by
    unfold sampleQZX
    rw [smul_smul, mul_inv_cancel₀ hn, one_smul]
  have hg :
      (Fintype.card n : ℝ) • sampleCrossMoment Z y = Zᵀ *ᵥ y :=
    smul_card_sampleCrossMoment Z y
  unfold gmmBetaStar gmmNormalizedBetaStar
  rw [← hQ, ← hg]
  exact LinearGMM.betaStar_smul
    (Fintype.card n : ℝ) (sampleQZX Z X) (sampleCrossMoment Z y) W hn

omit [Fintype l] [DecidableEq k] in
/-- The normalized outcome moment separates into its coefficient and error
parts under a finite-sample linear model. -/
private theorem sampleCrossMoment_add_linearPredictor
    (X : Matrix n k ℝ) (Z : Matrix n l ℝ) (b : k → ℝ) (e : n → ℝ) :
    sampleCrossMoment Z (X *ᵥ b + e) =
      sampleQZX Z X *ᵥ b + sampleCrossMoment Z e := by
  simp [sampleCrossMoment, sampleQZX, Matrix.mulVec_add,
    Matrix.mulVec_mulVec, Matrix.smul_mulVec]

end Normalization

/-! ## Random-weight influence convergence -/

variable {OmegaSpace : Type*} [MeasurableSpace OmegaSpace]
variable {mu : Measure OmegaSpace} [IsProbabilityMeasure mu]
variable {k l : Type*}
variable [Fintype k] [Fintype l] [DecidableEq k]

/-- Totalized sample GMM influence matrix. -/
noncomputable def gmmLinearizationMatrixStar
    (Q : Matrix l k ℝ) (W : Matrix l l ℝ) : Matrix k l ℝ :=
  LinearGMM.influenceMatrixStar Q W

/-- Population GMM influence matrix on an identified moment system. -/
noncomputable def gmmPopulationLinearizationMatrix
    (Q : Matrix l k ℝ) (W : Matrix l l ℝ)
    [Invertible (gmmPopulationGram Q W)] : Matrix k l ℝ :=
  LinearGMM.influenceMatrix Q W

/-- Exact normalized Star-GMM decomposition on a nonsingular sample Gram
matrix. -/
theorem gmmNormalizedBetaStar_sub_eq_linearizedScore_of_isUnit
    {n : Type*} [Fintype n]
    (X : Matrix n k ℝ) (Z : Matrix n l ℝ) (b : k → ℝ) (e : n → ℝ)
    (W : Matrix l l ℝ)
    (h : IsUnit (gmmPopulationGram (sampleQZX Z X) W).det) :
    gmmNormalizedBetaStar X Z (X *ᵥ b + e) W - b =
      gmmLinearizationMatrixStar (sampleQZX Z X) W *ᵥ
        sampleCrossMoment Z e := by
  rw [gmmNormalizedBetaStar, sampleCrossMoment_add_linearPredictor]
  rw [LinearGMM.betaStar_linear_decomposition_of_isUnit (h := h)]
  simp [gmmLinearizationMatrixStar]

omit [IsProbabilityMeasure mu] [Fintype k] [DecidableEq k] in
/-- Measurability of the weighted GMM Gram follows from measurability of its
derivative and weight inputs. -/
theorem gmmPopulationGram_aestronglyMeasurable
    (Qhat : OmegaSpace → Matrix l k ℝ)
    (What : OmegaSpace → Matrix l l ℝ)
    (hQ : AEStronglyMeasurable Qhat mu)
    (hW : AEStronglyMeasurable What mu) :
    AEStronglyMeasurable
      (fun omega => gmmPopulationGram (Qhat omega) (What omega)) mu := by
  have hQt : AEStronglyMeasurable (fun omega => (Qhat omega)ᵀ) mu :=
    continuous_id.matrix_transpose.comp_aestronglyMeasurable hQ
  have hQtW : AEStronglyMeasurable
      (fun omega => (Qhat omega)ᵀ * What omega) mu :=
    (Continuous.matrix_mul continuous_fst continuous_snd).comp_aestronglyMeasurable
      (hQt.prodMk hW)
  simpa [gmmPopulationGram, LinearGMM.gram] using
    (Continuous.matrix_mul continuous_fst continuous_snd).comp_aestronglyMeasurable
      (hQtW.prodMk hQ)

omit [IsProbabilityMeasure mu] in
/-- Measurability of the totalized GMM influence matrix follows from
measurability of its derivative and weight inputs. -/
theorem gmmLinearizationMatrixStar_aestronglyMeasurable
    (Qhat : OmegaSpace → Matrix l k ℝ)
    (What : OmegaSpace → Matrix l l ℝ)
    (hQ : AEStronglyMeasurable Qhat mu)
    (hW : AEStronglyMeasurable What mu) :
    AEStronglyMeasurable
      (fun omega => gmmLinearizationMatrixStar (Qhat omega) (What omega)) mu := by
  have hQt : AEStronglyMeasurable (fun omega => (Qhat omega)ᵀ) mu :=
    continuous_id.matrix_transpose.comp_aestronglyMeasurable hQ
  have hQtW : AEStronglyMeasurable
      (fun omega => (Qhat omega)ᵀ * What omega) mu :=
    (Continuous.matrix_mul continuous_fst continuous_snd).comp_aestronglyMeasurable
      (hQt.prodMk hW)
  have hGram : AEStronglyMeasurable
      (fun omega => LinearGMM.gram (Qhat omega) (What omega)) mu := by
    simpa [LinearGMM.gram] using
      (Continuous.matrix_mul continuous_fst continuous_snd).comp_aestronglyMeasurable
        (hQtW.prodMk hQ)
  have hGramInv : AEStronglyMeasurable
      (fun omega => (LinearGMM.gram (Qhat omega) (What omega))⁻¹) mu :=
    aestronglyMeasurable_matrix_inv hGram
  have hInvQt : AEStronglyMeasurable
      (fun omega =>
        (LinearGMM.gram (Qhat omega) (What omega))⁻¹ * (Qhat omega)ᵀ) mu :=
    (Continuous.matrix_mul continuous_fst continuous_snd).comp_aestronglyMeasurable
      (hGramInv.prodMk hQt)
  simpa [gmmLinearizationMatrixStar, LinearGMM.influenceMatrixStar] using
    (Continuous.matrix_mul continuous_fst continuous_snd).comp_aestronglyMeasurable
      (hInvQt.prodMk hW)

set_option maxHeartbeats 800000 in
-- The proof expands finite-sample matrix products over finite function spaces.
omit [IsProbabilityMeasure mu] in
/-- Finite-sample textbook-facing GMM measurability from measurable rows and
a measurable weight matrix. -/
theorem gmmBetaOrZero_aestronglyMeasurable_of_rows
    {n : ℕ}
    {Z : ℕ → OmegaSpace → l → ℝ}
    {X : ℕ → OmegaSpace → k → ℝ}
    {Y : ℕ → OmegaSpace → ℝ}
    {What : OmegaSpace → Matrix l l ℝ}
    (hZ : ∀ i, AEStronglyMeasurable (Z i) mu)
    (hX : ∀ i, AEStronglyMeasurable (X i) mu)
    (hY : ∀ i, AEStronglyMeasurable (Y i) mu)
    (hW : AEStronglyMeasurable What mu) :
    AEStronglyMeasurable
      (fun omega =>
        gmmBetaOrZero
          (stackRegressors X n omega) (stackRegressors Z n omega)
          (stackOutcomes Y n omega) (What omega)) mu := by
  let Zmat : OmegaSpace → Matrix (Fin n) l ℝ :=
    fun omega => stackRegressors Z n omega
  let Xmat : OmegaSpace → Matrix (Fin n) k ℝ :=
    fun omega => stackRegressors X n omega
  let yvec : OmegaSpace → Fin n → ℝ :=
    fun omega => stackOutcomes Y n omega
  let Dhat : OmegaSpace → Matrix l k ℝ :=
    fun omega => (Zmat omega)ᵀ * Xmat omega
  let ghat : OmegaSpace → l → ℝ :=
    fun omega => (Zmat omega)ᵀ *ᵥ yvec omega
  have hZmat : AEStronglyMeasurable Zmat mu := by
    simpa [Zmat, stackRegressors] using
      stackMatrix_aestronglyMeasurable (μ := mu) hZ
  have hXmat : AEStronglyMeasurable Xmat mu := by
    simpa [Xmat, stackRegressors] using
      stackMatrix_aestronglyMeasurable (μ := mu) hX
  have hyvec : AEStronglyMeasurable yvec mu := by
    simpa [yvec, stackOutcomes] using
      stackScalar_aestronglyMeasurable (μ := mu) hY
  have hZt : AEStronglyMeasurable (fun omega => (Zmat omega)ᵀ) mu :=
    continuous_id.matrix_transpose.comp_aestronglyMeasurable hZmat
  have hD : AEStronglyMeasurable Dhat mu := by
    exact (Continuous.matrix_mul continuous_fst continuous_snd)
      |>.comp_aestronglyMeasurable (hZt.prodMk hXmat)
  have hg : AEStronglyMeasurable ghat mu := by
    exact (Continuous.matrix_mulVec continuous_fst continuous_snd)
      |>.comp_aestronglyMeasurable (hZt.prodMk hyvec)
  have hA := gmmLinearizationMatrixStar_aestronglyMeasurable
    Dhat What hD hW
  have hbeta : AEStronglyMeasurable
      (fun omega =>
        gmmLinearizationMatrixStar (Dhat omega) (What omega) *ᵥ
          ghat omega) mu :=
    (Continuous.matrix_mulVec continuous_fst continuous_snd)
      |>.comp_aestronglyMeasurable (hA.prodMk hg)
  simpa [gmmBetaOrZero_eq_gmmBetaStar, gmmBetaStar,
    LinearGMM.betaStar_eq_influenceMatrixStar_mulVec,
    gmmLinearizationMatrixStar, Dhat, ghat, Zmat, Xmat, yvec] using hbeta

set_option maxHeartbeats 800000 in
-- The wrapper elaborates the finite-sample matrix measurability theorem.
omit [IsProbabilityMeasure mu] in
/-- Scaled and centered textbook-facing finite-sample GMM measurability from
measurable rows and a measurable weight matrix. -/
theorem gmmBetaOrZero_scaled_centered_aemeasurable_of_rows
    {n : ℕ}
    {Z : ℕ → OmegaSpace → l → ℝ}
    {X : ℕ → OmegaSpace → k → ℝ}
    {Y : ℕ → OmegaSpace → ℝ}
    {What : OmegaSpace → Matrix l l ℝ}
    (hZ : ∀ i, AEStronglyMeasurable (Z i) mu)
    (hX : ∀ i, AEStronglyMeasurable (X i) mu)
    (hY : ∀ i, AEStronglyMeasurable (Y i) mu)
    (hW : AEStronglyMeasurable What mu) (b : k → ℝ) :
    AEMeasurable
      (fun omega =>
        Real.sqrt (n : ℝ) •
          (gmmBetaOrZero
            (stackRegressors X n omega) (stackRegressors Z n omega)
            (stackOutcomes Y n omega) (What omega) - b)) mu :=
  (((gmmBetaOrZero_aestronglyMeasurable_of_rows
      (mu := mu) (Z := Z) (X := X) (Y := Y)
      hZ hX hY hW).sub aestronglyMeasurable_const)
    |>.const_smul (Real.sqrt (n : ℝ))).aemeasurable

/-- Convergence package for a sample moment derivative and a possibly random
GMM weight matrix. -/
structure GMMWeightConvergenceConditions
    (mu : Measure OmegaSpace) [IsProbabilityMeasure mu]
    (Qhat : ℕ → OmegaSpace → Matrix l k ℝ)
    (What : ℕ → OmegaSpace → Matrix l l ℝ)
    (Q : Matrix l k ℝ) (W : Matrix l l ℝ) : Prop where
  q_meas : ∀ n, AEStronglyMeasurable (Qhat n) mu
  weight_meas : ∀ n, AEStronglyMeasurable (What n) mu
  q_tendsto : TendstoInMeasure mu Qhat atTop (fun _ => Q)
  weight_tendsto : TendstoInMeasure mu What atTop (fun _ => W)
  gram_nonsing : IsUnit (gmmPopulationGram Q W).det

set_option maxHeartbeats 1200000 in
-- The rectangular matrix CMT chain has expensive finite-product synthesis.
/-- The sample weighted Gram converges to its population counterpart. -/
theorem gmmPopulationGram_tendstoInMeasure
    {Qhat : ℕ → OmegaSpace → Matrix l k ℝ}
    {What : ℕ → OmegaSpace → Matrix l l ℝ}
    {Q : Matrix l k ℝ} {W : Matrix l l ℝ}
    (h : GMMWeightConvergenceConditions mu Qhat What Q W) :
    TendstoInMeasure mu
      (fun n omega => gmmPopulationGram (Qhat n omega) (What n omega))
      atTop (fun _ => gmmPopulationGram Q W) := by
  let Qt : ℕ → OmegaSpace → Matrix k l ℝ :=
    fun n omega => (Qhat n omega)ᵀ
  have hQt_meas : ∀ n, AEStronglyMeasurable (Qt n) mu :=
    fun n => continuous_id.matrix_transpose.comp_aestronglyMeasurable (h.q_meas n)
  have hQt : TendstoInMeasure mu Qt atTop (fun _ => Qᵀ) := by
    simpa [Qt] using tendstoInMeasure_continuous_comp h.q_meas h.q_tendsto
      continuous_id.matrix_transpose
  have hQtW_meas : ∀ n,
      AEStronglyMeasurable (fun omega => Qt n omega * What n omega) mu := by
    intro n
    exact (Continuous.matrix_mul continuous_fst continuous_snd).comp_aestronglyMeasurable
      ((hQt_meas n).prodMk (h.weight_meas n))
  have hQtW : TendstoInMeasure mu
      (fun n omega => Qt n omega * What n omega)
      atTop (fun _ => Qᵀ * W) :=
    tendstoInMeasure_matrix_mul_rect hQt_meas h.weight_meas
      hQt h.weight_tendsto
  simpa [Qt, gmmPopulationGram, LinearGMM.gram] using
    tendstoInMeasure_matrix_mul_rect hQtW_meas h.q_meas hQtW h.q_tendsto

/-- The probability that the sample GMM Gram is singular tends to zero. -/
theorem measure_gmmPopulationGram_singular_tendsto_zero
    {Qhat : ℕ → OmegaSpace → Matrix l k ℝ}
    {What : ℕ → OmegaSpace → Matrix l l ℝ}
    {Q : Matrix l k ℝ} {W : Matrix l l ℝ}
    (h : GMMWeightConvergenceConditions mu Qhat What Q W) :
    Tendsto
      (fun n => mu {omega |
        ¬ IsUnit (gmmPopulationGram (Qhat n omega) (What n omega)).det})
      atTop (𝓝 0) :=
  matrix_singular_measure_tendsto_zero_of_tendstoInMeasure
    (fun n => gmmPopulationGram_aestronglyMeasurable
      (Qhat n) (What n) (h.q_meas n) (h.weight_meas n))
    (gmmPopulationGram_tendstoInMeasure h) h.gram_nonsing

set_option maxHeartbeats 1200000 in
-- The rectangular matrix CMT chain has expensive finite-product synthesis.
/-- The sample GMM influence matrix converges to its population counterpart
when the moment derivative and weight matrix converge and the population Gram
is nonsingular. -/
theorem gmmLinearizationMatrixStar_tendstoInMeasure
    {Qhat : ℕ → OmegaSpace → Matrix l k ℝ}
    {What : ℕ → OmegaSpace → Matrix l l ℝ}
    {Q : Matrix l k ℝ} {W : Matrix l l ℝ}
    (h : GMMWeightConvergenceConditions mu Qhat What Q W) :
    TendstoInMeasure mu
      (fun n omega =>
        gmmLinearizationMatrixStar (Qhat n omega) (What n omega))
      atTop (fun _ => LinearGMM.influenceMatrixStar Q W) := by
  let Qt : ℕ → OmegaSpace → Matrix k l ℝ :=
    fun n omega => (Qhat n omega)ᵀ
  let Gram : ℕ → OmegaSpace → Matrix k k ℝ :=
    fun n omega => LinearGMM.gram (Qhat n omega) (What n omega)
  have hQt_meas : ∀ n, AEStronglyMeasurable (Qt n) mu :=
    fun n => continuous_id.matrix_transpose.comp_aestronglyMeasurable (h.q_meas n)
  have hQt : TendstoInMeasure mu Qt atTop (fun _ => Qᵀ) := by
    simpa [Qt] using tendstoInMeasure_continuous_comp h.q_meas h.q_tendsto
      continuous_id.matrix_transpose
  have hGram_meas : ∀ n, AEStronglyMeasurable (Gram n) mu := by
    intro n
    exact gmmPopulationGram_aestronglyMeasurable
      (Qhat n) (What n) (h.q_meas n) (h.weight_meas n)
  have hGram : TendstoInMeasure mu Gram atTop
      (fun _ => gmmPopulationGram Q W) := by
    simpa [Gram] using gmmPopulationGram_tendstoInMeasure h
  have hGramInv_meas : ∀ n,
      AEStronglyMeasurable (fun omega => (Gram n omega)⁻¹) mu :=
    fun n => aestronglyMeasurable_matrix_inv (hGram_meas n)
  have hGramInv : TendstoInMeasure mu
      (fun n omega => (Gram n omega)⁻¹) atTop
      (fun _ => (gmmPopulationGram Q W)⁻¹) :=
    tendstoInMeasure_matrix_inv hGram_meas hGram
      (fun _ => h.gram_nonsing)
  have hInvQt_meas : ∀ n, AEStronglyMeasurable
      (fun omega => (Gram n omega)⁻¹ * Qt n omega) mu := by
    intro n
    exact (Continuous.matrix_mul continuous_fst continuous_snd).comp_aestronglyMeasurable
      ((hGramInv_meas n).prodMk (hQt_meas n))
  have hInvQt : TendstoInMeasure mu
      (fun n omega => (Gram n omega)⁻¹ * Qt n omega) atTop
      (fun _ => (gmmPopulationGram Q W)⁻¹ * Qᵀ) :=
    tendstoInMeasure_matrix_mul_rect hGramInv_meas hQt_meas hGramInv hQt
  have hFull := tendstoInMeasure_matrix_mul_rect
    hInvQt_meas h.weight_meas hInvQt h.weight_tendsto
  simpa [gmmLinearizationMatrixStar, LinearGMM.influenceMatrixStar,
    gmmPopulationGram, LinearGMM.gram, Gram, Qt] using hFull

/-! ## Linearized GMM central limit theorem -/

variable [DecidableEq l]

/-- Sample derivative, random weight, and instrument-score CLT package for
Hansen Theorem 13.3. -/
structure GMMMomentCLTConditions
    (mu : Measure OmegaSpace) [IsProbabilityMeasure mu]
    (Qhat : ℕ → OmegaSpace → Matrix l k ℝ)
    (What : ℕ → OmegaSpace → Matrix l l ℝ)
    (Z : ℕ → OmegaSpace → l → ℝ)
    (e : ℕ → OmegaSpace → ℝ)
    (Q : Matrix l k ℝ) (W : Matrix l l ℝ) : Prop
    extends GMMWeightConvergenceConditions mu Qhat What Q W where
  score_clt : ScoreCLTConditions mu Z e

namespace TwoSLSGramScoreCLTConditions

/-- Convert the Chapter 12 sample-moment and score-CLT package into the GMM
conditions for a convergent positive-definite weight sequence. -/
theorem toGMMMomentCLTConditions
    {Z : ℕ → OmegaSpace → l → ℝ}
    {X : ℕ → OmegaSpace → k → ℝ}
    {e : ℕ → OmegaSpace → ℝ}
    (h : TwoSLSGramScoreCLTConditions mu Z X e)
    (What : ℕ → OmegaSpace → Matrix l l ℝ) (W : Matrix l l ℝ)
    (hWhat_meas : ∀ n, AEStronglyMeasurable (What n) mu)
    (hWhat_tendsto : TendstoInMeasure mu What atTop (fun _ => W))
    (hW : W.PosDef) :
    GMMMomentCLTConditions mu
      (fun n omega =>
        sampleQZX (stackRegressors Z n omega) (stackRegressors X n omega))
      What Z e
      (twoSLSCombinedQZX (popGram mu (twoSLSCombinedRegressors Z X))) W := by
  have hMom := h.toTwoSLSGramInstrumentMomentRankConditions
    |>.toSampleMomentConvergenceConditions
  exact
    { q_meas := by
        simpa [stackRegressors] using hMom.qzx_meas
      weight_meas := hWhat_meas
      q_tendsto := by
        simpa [stackRegressors] using hMom.qzx_tendsto
      weight_tendsto := hWhat_tendsto
      gram_nonsing := LinearGMM.gram_det_isUnit_of_posDef_rank
        _ W hW h.qzx_rank
      score_clt := h.score_clt }

end TwoSLSGramScoreCLTConditions

namespace TwoSLSGramScoreCLTPositiveCovarianceConditions

/-- Hansen Assumption 12.2 supplies the Chapter 13 GMM moment conditions for
any convergent positive-definite weight sequence. -/
theorem toGMMMomentCLTConditions
    {Z : ℕ → OmegaSpace → l → ℝ}
    {X : ℕ → OmegaSpace → k → ℝ}
    {e : ℕ → OmegaSpace → ℝ}
    (h : TwoSLSGramScoreCLTPositiveCovarianceConditions mu Z X e)
    (What : ℕ → OmegaSpace → Matrix l l ℝ) (W : Matrix l l ℝ)
    (hWhat_meas : ∀ n, AEStronglyMeasurable (What n) mu)
    (hWhat_tendsto : TendstoInMeasure mu What atTop (fun _ => W))
    (hW : W.PosDef) :
    GMMMomentCLTConditions mu
      (fun n omega =>
        sampleQZX (stackRegressors Z n omega) (stackRegressors X n omega))
      What Z e
      (twoSLSCombinedQZX (popGram mu (twoSLSCombinedRegressors Z X))) W := by
  let hCore : TwoSLSGramScoreCLTConditions mu Z X e :=
    { toTwoSLSGramInstrumentMomentRankConditions :=
        h.toTwoSLSGramInstrumentMomentRankConditions
      score_clt := h.score_clt }
  exact hCore.toGMMMomentCLTConditions What W hWhat_meas hWhat_tendsto hW

end TwoSLSGramScoreCLTPositiveCovarianceConditions

set_option maxHeartbeats 1200000 in
-- The distributional matrix-map assembly has expensive product-space synthesis.
/-- The random GMM influence matrix applied to the scaled instrument score has
the sandwich Gaussian limit in Hansen equation (13.7). -/
theorem gmmLinearizedScore_tendstoInDistribution
    {Qhat : ℕ → OmegaSpace → Matrix l k ℝ}
    {What : ℕ → OmegaSpace → Matrix l l ℝ}
    {Z : ℕ → OmegaSpace → l → ℝ}
    {e : ℕ → OmegaSpace → ℝ}
    {Q : Matrix l k ℝ} {W : Matrix l l ℝ}
    (h : GMMMomentCLTConditions mu Qhat What Z e Q W) :
    TendstoInDistribution
      (fun n omega =>
        gmmLinearizationMatrixStar (Qhat n omega) (What n omega) *ᵥ
          (Real.sqrt (n : ℝ) •
            sampleCrossMoment (stackRegressors Z n omega)
              (stackErrors e n omega)))
      atTop (fun z : EuclideanSpace ℝ k => z.ofLp) (fun _ => mu)
      (multivariateGaussian 0
        (gmmAsymptoticVarianceStar Q W (scoreCovMat mu Z e))) := by
  let A : Matrix k l ℝ := LinearGMM.influenceMatrixStar Q W
  let T : ℕ → OmegaSpace → EuclideanSpace ℝ l := fun n omega =>
    WithLp.toLp 2
      (Real.sqrt (n : ℝ) •
        sampleCrossMoment (stackRegressors Z n omega) (stackErrors e n omega))
  have hT : TendstoInDistribution T atTop
      (fun z : EuclideanSpace ℝ l => z) (fun _ => mu)
      (multivariateGaussian 0 (scoreCovMat mu Z e)) := by
    simpa [T] using
      scoreEuclidean_sampleCrossMoment_tendstoInDistribution_multivariateGaussian
        (μ := mu) (X := Z) (e := e) h.score_clt
  have hA : TendstoInMeasure mu
      (fun n omega =>
        gmmLinearizationMatrixStar (Qhat n omega) (What n omega))
      atTop (fun _ => A) := by
    simpa [A] using gmmLinearizationMatrixStar_tendstoInMeasure
      h.toGMMWeightConvergenceConditions
  have hlin := matrixContinuousLinearMap_tendstoInDistribution_of_vector_and_matrix
    (μ := mu) (T := T) (Zlim := fun z : EuclideanSpace ℝ l => z)
    (Ahat := fun n omega =>
      gmmLinearizationMatrixStar (Qhat n omega) (What n omega))
    (A := A) hT
      (fun n => gmmLinearizationMatrixStar_aestronglyMeasurable
        (Qhat n) (What n) (h.q_meas n) (h.weight_meas n)) hA
  have hOmega : (scoreCovMat mu Z e).PosSemidef :=
    scoreCovMat_posSemidef (μ := mu) (X := Z) (e := e) h.score_clt
  have hLaw :
      HasLaw (fun z : EuclideanSpace ℝ l => matrixContinuousLinearMap A z)
        (multivariateGaussian 0 (A * scoreCovMat mu Z e * Aᵀ))
        (multivariateGaussian 0 (scoreCovMat mu Z e)) := by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
      hasLaw_multivariateGaussian_zero_linearMap (n := l) (q := k) hOmega A
  have htarget : TendstoInDistribution
      (fun n omega =>
        matrixContinuousLinearMap
          (gmmLinearizationMatrixStar (Qhat n omega) (What n omega))
          (T n omega))
      atTop (fun z : EuclideanSpace ℝ k => z) (fun _ => mu)
      (multivariateGaussian 0 (A * scoreCovMat mu Z e * Aᵀ)) := by
    simpa [Function.comp_def] using
      tendstoInDistribution_id_of_hasLaw_limit
        (E := EuclideanSpace ℝ k) hlin hLaw
  have htargetVec := htarget.continuous_comp
    (PiLp.continuous_ofLp 2 (fun _ : k => ℝ))
  have hdesired : TendstoInDistribution
      (fun n omega =>
        gmmLinearizationMatrixStar (Qhat n omega) (What n omega) *ᵥ
          (Real.sqrt (n : ℝ) •
            sampleCrossMoment (stackRegressors Z n omega)
              (stackErrors e n omega)))
      atTop (fun z : EuclideanSpace ℝ k => z.ofLp) (fun _ => mu)
      (multivariateGaussian 0 (A * scoreCovMat mu Z e * Aᵀ)) := by
    refine TendstoInDistribution.congr ?_ EventuallyEq.rfl htargetVec
    intro n
    exact ae_of_all mu (fun omega => by
      simp [T, matrixContinuousLinearMap_apply, Matrix.mulVec_smul,
        Matrix.mulVec_sum, Finset.smul_sum, smul_smul])
  simpa [A, gmmAsymptoticVarianceStar,
    LinearGMM.asymptoticVarianceStar] using hdesired

/-! ## Hansen Theorem 13.3 -/

omit [DecidableEq l] in
/-- The scaled Star-GMM estimator differs from its linearized score only on
the singular sample-Gram event, whose probability tends to zero. -/
theorem gmmBetaStar_sqrt_linearization_tendstoInMeasure_zero
    {What : ℕ → OmegaSpace → Matrix l l ℝ}
    {Z : ℕ → OmegaSpace → l → ℝ}
    {X : ℕ → OmegaSpace → k → ℝ}
    {e Y : ℕ → OmegaSpace → ℝ}
    {Q : Matrix l k ℝ} {W : Matrix l l ℝ}
    (h : GMMWeightConvergenceConditions mu
      (fun n omega =>
        sampleQZX (stackRegressors Z n omega) (stackRegressors X n omega))
      What Q W)
    (b : k → ℝ)
    (hmodel : ∀ i omega, Y i omega = (X i omega) ⬝ᵥ b + e i omega) :
    TendstoInMeasure mu
      ((fun (n : ℕ) omega =>
        Real.sqrt (n : ℝ) •
          (gmmBetaStar
            (stackRegressors X n omega) (stackRegressors Z n omega)
            (stackOutcomes Y n omega) (What n omega) - b)) -
        fun (n : ℕ) omega =>
          gmmLinearizationMatrixStar
            (sampleQZX (stackRegressors Z n omega)
              (stackRegressors X n omega))
            (What n omega) *ᵥ
              (Real.sqrt (n : ℝ) •
                sampleCrossMoment (stackRegressors Z n omega)
                  (stackErrors e n omega)))
      atTop (fun _ => 0) := by
  have hsingular :=
    measure_gmmPopulationGram_singular_tendsto_zero h
  intro epsilon hepsilon
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    hsingular (Eventually.of_forall (fun _ => zero_le _)) ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  refine measure_mono ?_
  intro omega homega
  simp only [Set.mem_setOf_eq] at homega ⊢
  intro hgram
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hY :
      stackOutcomes Y n omega =
        stackRegressors X n omega *ᵥ b + stackErrors e n omega :=
    stack_linear_model X e Y b hmodel n omega
  have hR :
      Real.sqrt (n : ℝ) •
          (gmmBetaStar
            (stackRegressors X n omega) (stackRegressors Z n omega)
            (stackOutcomes Y n omega) (What n omega) - b) -
        gmmLinearizationMatrixStar
            (sampleQZX (stackRegressors Z n omega)
              (stackRegressors X n omega))
            (What n omega) *ᵥ
          (Real.sqrt (n : ℝ) •
            sampleCrossMoment (stackRegressors Z n omega)
              (stackErrors e n omega)) = 0 := by
    rw [gmmBetaStar_eq_normalized, hY]
    rw [gmmNormalizedBetaStar_sub_eq_linearizedScore_of_isUnit
      (h := hgram)]
    simp [Matrix.mulVec_smul]
  change epsilon ≤ edist
      (Real.sqrt (n : ℝ) •
          (gmmBetaStar
            (stackRegressors X n omega) (stackRegressors Z n omega)
            (stackOutcomes Y n omega) (What n omega) - b) -
        gmmLinearizationMatrixStar
            (sampleQZX (stackRegressors Z n omega)
              (stackRegressors X n omega))
            (What n omega) *ᵥ
          (Real.sqrt (n : ℝ) •
            sampleCrossMoment (stackRegressors Z n omega)
              (stackErrors e n omega))) 0 at homega
  rw [hR, edist_self] at homega
  exact absurd homega (not_le.mpr hepsilon)

/-- **Hansen Theorem 13.3 (Star form).** Under convergence of the sample
derivative and weight matrix, the linear GMM estimator is asymptotically
normal with the sandwich covariance in equation (13.8). -/
theorem gmmBetaStar_tendstoInDistribution
    {What : ℕ → OmegaSpace → Matrix l l ℝ}
    {Z : ℕ → OmegaSpace → l → ℝ}
    {X : ℕ → OmegaSpace → k → ℝ}
    {e Y : ℕ → OmegaSpace → ℝ}
    {Q : Matrix l k ℝ} {W : Matrix l l ℝ}
    (h : GMMMomentCLTConditions mu
      (fun n omega =>
        sampleQZX (stackRegressors Z n omega) (stackRegressors X n omega))
      What Z e Q W)
    (b : k → ℝ)
    (hmodel : ∀ i omega, Y i omega = (X i omega) ⬝ᵥ b + e i omega)
    (hmeas : ∀ (n : ℕ), AEMeasurable
      (fun omega =>
        Real.sqrt (n : ℝ) •
          (gmmBetaStar
            (stackRegressors X n omega) (stackRegressors Z n omega)
            (stackOutcomes Y n omega) (What n omega) - b)) mu) :
    TendstoInDistribution
      (fun (n : ℕ) omega =>
        Real.sqrt (n : ℝ) •
          (gmmBetaStar
            (stackRegressors X n omega) (stackRegressors Z n omega)
            (stackOutcomes Y n omega) (What n omega) - b))
      atTop (fun z : EuclideanSpace ℝ k => z.ofLp) (fun _ => mu)
      (multivariateGaussian 0
        (gmmAsymptoticVarianceStar Q W (scoreCovMat mu Z e))) := by
  exact tendstoInDistribution_of_tendstoInMeasure_sub
    (X := fun (n : ℕ) omega =>
      gmmLinearizationMatrixStar
        (sampleQZX (stackRegressors Z n omega)
          (stackRegressors X n omega))
        (What n omega) *ᵥ
          (Real.sqrt (n : ℝ) •
            sampleCrossMoment (stackRegressors Z n omega)
              (stackErrors e n omega)))
    (Y := fun (n : ℕ) omega =>
      Real.sqrt (n : ℝ) •
        (gmmBetaStar
          (stackRegressors X n omega) (stackRegressors Z n omega)
          (stackOutcomes Y n omega) (What n omega) - b))
    (Z := fun z : EuclideanSpace ℝ k => z.ofLp)
    (gmmLinearizedScore_tendstoInDistribution h)
    (gmmBetaStar_sqrt_linearization_tendstoInMeasure_zero
      h.toGMMWeightConvergenceConditions b hmodel)
    hmeas

/-- **Hansen Theorem 13.3 (OrZero form).** This is the textbook-facing
totalized version of `gmmBetaStar_tendstoInDistribution`. -/
theorem gmmBetaOrZero_tendstoInDistribution
    {What : ℕ → OmegaSpace → Matrix l l ℝ}
    {Z : ℕ → OmegaSpace → l → ℝ}
    {X : ℕ → OmegaSpace → k → ℝ}
    {e Y : ℕ → OmegaSpace → ℝ}
    {Q : Matrix l k ℝ} {W : Matrix l l ℝ}
    (h : GMMMomentCLTConditions mu
      (fun n omega =>
        sampleQZX (stackRegressors Z n omega) (stackRegressors X n omega))
      What Z e Q W)
    (b : k → ℝ)
    (hmodel : ∀ i omega, Y i omega = (X i omega) ⬝ᵥ b + e i omega)
    (hmeas : ∀ (n : ℕ), AEMeasurable
      (fun omega =>
        Real.sqrt (n : ℝ) •
          (gmmBetaOrZero
            (stackRegressors X n omega) (stackRegressors Z n omega)
            (stackOutcomes Y n omega) (What n omega) - b)) mu) :
    TendstoInDistribution
      (fun (n : ℕ) omega =>
        Real.sqrt (n : ℝ) •
          (gmmBetaOrZero
            (stackRegressors X n omega) (stackRegressors Z n omega)
            (stackOutcomes Y n omega) (What n omega) - b))
      atTop (fun z : EuclideanSpace ℝ k => z.ofLp) (fun _ => mu)
      (multivariateGaussian 0
        (gmmAsymptoticVarianceStar Q W (scoreCovMat mu Z e))) := by
  have hstar_meas : ∀ (n : ℕ), AEMeasurable
      (fun omega =>
        Real.sqrt (n : ℝ) •
          (gmmBetaStar
            (stackRegressors X n omega) (stackRegressors Z n omega)
            (stackOutcomes Y n omega) (What n omega) - b)) mu := by
    intro n
    simpa using hmeas n
  have hstar := gmmBetaStar_tendstoInDistribution h b hmodel hstar_meas
  simpa using hstar

/-- **Hansen Theorem 13.3 under Assumption 12.2.** A convergent
positive-definite weight sequence gives the standard GMM sandwich limit. -/
theorem gmmBetaOrZero_tendstoInDistribution_of_assumption12_2
    {What : ℕ → OmegaSpace → Matrix l l ℝ}
    {Z : ℕ → OmegaSpace → l → ℝ}
    {X : ℕ → OmegaSpace → k → ℝ}
    {e Y : ℕ → OmegaSpace → ℝ}
    (h : TwoSLSGramScoreCLTPositiveCovarianceConditions mu Z X e)
    (W : Matrix l l ℝ)
    (hWhat_meas : ∀ n, AEStronglyMeasurable (What n) mu)
    (hWhat_tendsto : TendstoInMeasure mu What atTop (fun _ => W))
    (hW : W.PosDef)
    (b : k → ℝ)
    (hmodel : ∀ i omega, Y i omega = (X i omega) ⬝ᵥ b + e i omega)
    (hmeas : ∀ (n : ℕ), AEMeasurable
      (fun omega =>
        Real.sqrt (n : ℝ) •
          (gmmBetaOrZero
            (stackRegressors X n omega) (stackRegressors Z n omega)
            (stackOutcomes Y n omega) (What n omega) - b)) mu) :
    TendstoInDistribution
      (fun (n : ℕ) omega =>
        Real.sqrt (n : ℝ) •
          (gmmBetaOrZero
            (stackRegressors X n omega) (stackRegressors Z n omega)
            (stackOutcomes Y n omega) (What n omega) - b))
      atTop (fun z : EuclideanSpace ℝ k => z.ofLp) (fun _ => mu)
      (multivariateGaussian 0
        (gmmAsymptoticVarianceStar
          (twoSLSCombinedQZX
            (popGram mu (twoSLSCombinedRegressors Z X)))
          W (scoreCovMat mu Z e))) := by
  exact gmmBetaOrZero_tendstoInDistribution
    (h.toGMMMomentCLTConditions What W hWhat_meas hWhat_tendsto hW)
    b hmodel hmeas

/-! ## Hansen Theorem 13.4 -/

/-- **Hansen Theorem 13.4.** If the GMM weight converges to the inverse score
covariance, the coefficient limit has covariance `(Q'Omega⁻¹Q)⁻¹`. -/
theorem gmmBetaOrZero_tendstoInDistribution_efficient_of_assumption12_2
    {What : ℕ → OmegaSpace → Matrix l l ℝ}
    {Z : ℕ → OmegaSpace → l → ℝ}
    {X : ℕ → OmegaSpace → k → ℝ}
    {e Y : ℕ → OmegaSpace → ℝ}
    (h : TwoSLSGramScoreCLTPositiveCovarianceConditions mu Z X e)
    (hWhat_meas : ∀ n, AEStronglyMeasurable (What n) mu)
    (hWhat_tendsto : TendstoInMeasure mu What atTop
      (fun _ => (scoreCovMat mu Z e)⁻¹))
    (b : k → ℝ)
    (hmodel : ∀ i omega, Y i omega = (X i omega) ⬝ᵥ b + e i omega)
    (hmeas : ∀ (n : ℕ), AEMeasurable
      (fun omega =>
        Real.sqrt (n : ℝ) •
          (gmmBetaOrZero
            (stackRegressors X n omega) (stackRegressors Z n omega)
            (stackOutcomes Y n omega) (What n omega) - b)) mu) :
    TendstoInDistribution
      (fun (n : ℕ) omega =>
        Real.sqrt (n : ℝ) •
          (gmmBetaOrZero
            (stackRegressors X n omega) (stackRegressors Z n omega)
            (stackOutcomes Y n omega) (What n omega) - b))
      atTop (fun z : EuclideanSpace ℝ k => z.ofLp) (fun _ => mu)
      (multivariateGaussian 0
        ((gmmPopulationGram
          (twoSLSCombinedQZX
            (popGram mu (twoSLSCombinedRegressors Z X)))
          (scoreCovMat mu Z e)⁻¹)⁻¹)) := by
  have hgeneral :=
    gmmBetaOrZero_tendstoInDistribution_of_assumption12_2
      h (scoreCovMat mu Z e)⁻¹ hWhat_meas hWhat_tendsto
        h.omega_posDef.inv b hmodel hmeas
  rw [gmmAsymptoticVarianceStar_efficient
    (twoSLSCombinedQZX (popGram mu (twoSLSCombinedRegressors Z X)))
    (scoreCovMat mu Z e) h.omega_posDef h.qzx_rank] at hgeneral
  exact hgeneral

end HansenEconometrics
