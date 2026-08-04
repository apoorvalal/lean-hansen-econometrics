import HansenEconometrics.Chapter13GMM.Inference
import HansenEconometrics.Chapter13GMM.Efficiency
import HansenEconometrics.Chapter12InstrumentalVariables.Overidentification

/-!
# Chapter 13 — distance and specification tests

This module develops Hansen Theorems 13.12--13.17. Theorem 13.12 is exact for
linear restrictions and conditional on an explicit optimizer linearization
for nonlinear restrictions. The deterministic distance results use the
quadratic-completion lemma in `Chapter13GMM.Primitives`. The distributional
results reuse the Gaussian quadratic-form laws and Chapter 9's feasible-
statistic theorems.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped Matrix MatrixOrder Matrix.Norms.Elementwise Function Topology MeasureTheory
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

/-! ## GMM criterion and distance -/

/-- GMM criterion based on normalized sample moments `n⁻¹Z'(Y-Xb)`. -/
noncomputable def gmmNormalizedCriterion
    {n k l : Type*} [Fintype n] [Fintype k] [Fintype l]
    [DecidableEq k]
    (X : Matrix n k ℝ) (Z : Matrix n l ℝ) (y : n → ℝ)
    (W : Matrix l l ℝ) (b : k → ℝ) : ℝ :=
  LinearGMM.criterion (sampleQZX Z X) (sampleCrossMoment Z y) W b

/-- Hansen's sample criterion `n gbar(b)' W gbar(b)`. -/
noncomputable def gmmCriterionValue
    {n k l : Type*} [Fintype n] [Fintype k] [Fintype l]
    [DecidableEq k]
    (X : Matrix n k ℝ) (Z : Matrix n l ℝ) (y : n → ℝ)
    (W : Matrix l l ℝ) (b : k → ℝ) : ℝ :=
  (Fintype.card n : ℝ) * gmmNormalizedCriterion X Z y W b

/-- Hansen's GMM distance statistic: restricted criterion minus unrestricted
criterion. The two coefficients may use different construction procedures,
but this definition uses the displayed common weight `W`. -/
noncomputable def gmmDistanceStat
    {n k l : Type*} [Fintype n] [Fintype k] [Fintype l]
    [DecidableEq k]
    (X : Matrix n k ℝ) (Z : Matrix n l ℝ) (y : n → ℝ)
    (W : Matrix l l ℝ) (btilde bhat : k → ℝ) : ℝ :=
  gmmCriterionValue X Z y W btilde -
    gmmCriterionValue X Z y W bhat

set_option maxHeartbeats 800000 in
-- Expanding the finite-dimensional criterion map is elaboration intensive.
/-- Measurability of the normalized sample GMM criterion from measurable
matrix, outcome, weight, and coefficient inputs. -/
theorem gmmCriterionValue_aestronglyMeasurable
    {OmegaSpace : Type*} [MeasurableSpace OmegaSpace]
    {mu : Measure OmegaSpace}
    {n k l : Type*} [Fintype n] [Fintype k] [Fintype l]
    [DecidableEq k]
    {X : OmegaSpace → Matrix n k ℝ}
    {Z : OmegaSpace → Matrix n l ℝ}
    {y : OmegaSpace → n → ℝ}
    {W : OmegaSpace → Matrix l l ℝ}
    {b : OmegaSpace → k → ℝ}
    (hX : AEStronglyMeasurable X mu)
    (hZ : AEStronglyMeasurable Z mu)
    (hy : AEStronglyMeasurable y mu)
    (hW : AEStronglyMeasurable W mu)
    (hb : AEStronglyMeasurable b mu) :
    AEStronglyMeasurable
      (fun omega =>
        gmmCriterionValue (X omega) (Z omega) (y omega)
          (W omega) (b omega)) mu := by
  let Qhat : OmegaSpace → Matrix l k ℝ := fun omega =>
    sampleQZX (Z omega) (X omega)
  let ghat : OmegaSpace → l → ℝ := fun omega =>
    sampleCrossMoment (Z omega) (y omega)
  have hZt : AEStronglyMeasurable (fun omega => (Z omega)ᵀ) mu :=
    continuous_id.matrix_transpose.comp_aestronglyMeasurable hZ
  have hQhat : AEStronglyMeasurable Qhat mu := by
    have hmul : AEStronglyMeasurable
        (fun omega => (Z omega)ᵀ * X omega) mu :=
      (Continuous.matrix_mul continuous_fst continuous_snd)
        |>.comp_aestronglyMeasurable (hZt.prodMk hX)
    simpa [Qhat, sampleQZX] using
      hmul.const_smul (Fintype.card n : ℝ)⁻¹
  have hghat : AEStronglyMeasurable ghat mu := by
    have hmul : AEStronglyMeasurable
        (fun omega => (Z omega)ᵀ *ᵥ y omega) mu :=
      (Continuous.matrix_mulVec continuous_fst continuous_snd)
        |>.comp_aestronglyMeasurable (hZt.prodMk hy)
    simpa [ghat, sampleCrossMoment] using
      hmul.const_smul (Fintype.card n : ℝ)⁻¹
  have hQb : AEStronglyMeasurable
      (fun omega => Qhat omega *ᵥ b omega) mu :=
    (Continuous.matrix_mulVec continuous_fst continuous_snd)
      |>.comp_aestronglyMeasurable (hQhat.prodMk hb)
  have hres : AEStronglyMeasurable
      (fun omega => ghat omega - Qhat omega *ᵥ b omega) mu :=
    hghat.sub hQb
  have hWres : AEStronglyMeasurable
      (fun omega => W omega *ᵥ
        (ghat omega - Qhat omega *ᵥ b omega)) mu :=
    (Continuous.matrix_mulVec continuous_fst continuous_snd)
      |>.comp_aestronglyMeasurable (hW.prodMk hres)
  have hquad : AEStronglyMeasurable
      (fun omega =>
        (ghat omega - Qhat omega *ᵥ b omega) ⬝ᵥ
          (W omega *ᵥ (ghat omega - Qhat omega *ᵥ b omega))) mu :=
    (Continuous.dotProduct continuous_fst continuous_snd)
      |>.comp_aestronglyMeasurable (hres.prodMk hWres)
  simpa [gmmCriterionValue, gmmNormalizedCriterion, LinearGMM.criterion,
    Qhat, ghat] using hquad.const_smul (Fintype.card n : ℝ)

/-- On a nonsingular sample Gram, the common-weight GMM distance is exactly
the efficient minimum-distance criterion in coefficient space. -/
theorem gmmDistanceStat_eq_emdJStatOrZero_of_commonWeight_isUnit
    {n k l : Type*} [Fintype n] [Fintype k] [Fintype l]
    [Nonempty n] [DecidableEq k]
    (X : Matrix n k ℝ) (Z : Matrix n l ℝ) (y : n → ℝ)
    (W : Matrix l l ℝ) (btilde : k → ℝ)
    (hW : W.PosSemidef)
    (hunit : IsUnit (gmmNormalizedGram X Z W).det) :
    gmmDistanceStat X Z y W btilde
        (gmmBetaOrZero X Z y W) =
      emdJStatOrZero
        (gmmNormalizedGram X Z W)⁻¹
        (gmmBetaOrZero X Z y W) btilde
        (Real.sqrt (Fintype.card n : ℝ)) := by
  let G : Matrix k k ℝ := gmmNormalizedGram X Z W
  let bhat : k → ℝ := gmmBetaOrZero X Z y W
  let root : ℝ := Real.sqrt (Fintype.card n : ℝ)
  letI : Invertible G :=
    Matrix.invertibleOfIsUnitDet (A := G) (by simpa [G] using hunit)
  letI : Invertible
      (LinearGMM.gram (sampleQZX Z X) W) := by
    simpa [G, gmmNormalizedGram] using (inferInstance : Invertible G)
  have hbeta : bhat =
      LinearGMM.beta (sampleQZX Z X) (sampleCrossMoment Z y) W := by
    dsimp [bhat]
    rw [gmmBetaOrZero_eq_gmmBetaStar,
      gmmBetaStar_eq_normalized X Z y W]
    exact LinearGMM.betaStar_eq_beta
      (sampleQZX Z X) (sampleCrossMoment Z y) W
  have hcompletion := LinearGMM.criterion_eq_at_beta_add_quadratic_form
    (sampleQZX Z X) (sampleCrossMoment Z y) W btilde hW
  have hcriterion :
      gmmNormalizedCriterion X Z y W btilde -
          gmmNormalizedCriterion X Z y W bhat =
        (btilde - bhat) ⬝ᵥ (G *ᵥ (btilde - bhat)) := by
    have hc :
        gmmNormalizedCriterion X Z y W btilde =
          gmmNormalizedCriterion X Z y W bhat +
            (btilde - bhat) ⬝ᵥ (G *ᵥ (btilde - bhat)) := by
      simpa [gmmNormalizedCriterion, G, hbeta] using hcompletion
    linarith
  have hsqrt : root ^ 2 = (Fintype.card n : ℝ) := by
    simp [root, Real.sq_sqrt (Nat.cast_nonneg (Fintype.card n))]
  have hdiff : bhat - btilde = -(btilde - bhat) := by
    abel
  calc
    gmmDistanceStat X Z y W btilde bhat =
        (Fintype.card n : ℝ) *
          (gmmNormalizedCriterion X Z y W btilde -
            gmmNormalizedCriterion X Z y W bhat) := by
          simp [gmmDistanceStat, gmmCriterionValue, mul_sub]
    _ = (Fintype.card n : ℝ) *
        ((btilde - bhat) ⬝ᵥ (G *ᵥ (btilde - bhat))) := by
          rw [hcriterion]
    _ = emdJStatOrZero G⁻¹ bhat btilde root := by
      rw [← hsqrt]
      unfold emdJStatOrZero criterionJStatOrZero
      rw [Matrix.nonsing_inv_nonsing_inv G (by simpa [G] using hunit)]
      rw [hdiff]
      simp only [Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul,
        Matrix.mulVec_neg, neg_dotProduct_neg]
      simp [pow_two, mul_assoc]
    _ = emdJStatOrZero
        (gmmNormalizedGram X Z W)⁻¹
        (gmmBetaOrZero X Z y W) btilde
        (Real.sqrt (Fintype.card n : ℝ)) := by
          rfl

/-- The equation (13.8) efficient two-step GMM estimator. -/
noncomputable def gmmUncenteredTwoStepBetaOrZero
    {n k l : Type*} [Fintype n] [Fintype k] [Fintype l]
    [DecidableEq k] [DecidableEq l]
    (X : Matrix n k ℝ) (Z : Matrix n l ℝ) (y : n → ℝ) : k → ℝ :=
  gmmBetaOrZero X Z y (gmmUncenteredTwoStepWeightStar Z X y)

/-- Hansen's common-efficient-weight distance statistic, with the constrained
coefficient supplied by the constrained GMM optimization problem. -/
noncomputable def gmmUncenteredTwoStepDistanceStatOrZero
    {n k l : Type*} [Fintype n] [Fintype k] [Fintype l]
    [DecidableEq k] [DecidableEq l]
    (X : Matrix n k ℝ) (Z : Matrix n l ℝ) (y : n → ℝ)
    (btilde : k → ℝ) : ℝ :=
  let W := gmmUncenteredTwoStepWeightStar Z X y
  gmmDistanceStat X Z y W btilde (gmmBetaOrZero X Z y W)

private theorem twoSLSOmegaHatStar_posSemidef_local
    {n k l : Type*} [Fintype n] [Fintype k] [Fintype l]
    [DecidableEq k] [DecidableEq l]
    (Z : Matrix n l ℝ) (X : Matrix n k ℝ) (y : n → ℝ) :
    (twoSLSOmegaHatStar Z X y).PosSemidef := by
  classical
  have hsum :
      (∑ i : n, (twoSLSResidualStar Z X y i) ^ 2 •
        Matrix.vecMulVec (Z i) (Z i)).PosSemidef := by
    refine Matrix.posSemidef_sum (s := Finset.univ) ?_
    intro i _
    exact Matrix.PosSemidef.smul
      (by simpa using Matrix.posSemidef_vecMulVec_self_star (Z i))
      (sq_nonneg _)
  have hscale : 0 ≤ (Fintype.card n : ℝ)⁻¹ :=
    inv_nonneg.mpr (Nat.cast_nonneg _)
  simpa [twoSLSOmegaHatStar] using
    Matrix.PosSemidef.smul hsum hscale

/-- Efficient minimum-distance criterion for a linear restriction equals the
corresponding Wald quadratic form. -/
theorem emdJStatOrZero_eq_restrictionWaldStatOrZero
    {k : Type*} {r : ℕ} [Fintype k] [DecidableEq k]
    (R : Matrix k (Fin r) ℝ) (c : Fin r → ℝ) (V : Matrix k k ℝ)
    (bhat : k → ℝ) (root : ℝ)
    (hV : V.PosDef) (hR : Function.Injective R.mulVec) :
    emdJStatOrZero V bhat (emdBetaStar R c V bhat) root =
      restrictionWaldStatOrZero
        (root • (Rᵀ *ᵥ bhat - c)) (Rᵀ * V * R) := by
  let G : Matrix (Fin r) (Fin r) ℝ := Rᵀ * V * R
  let A : Matrix (Fin r) (Fin r) ℝ := G⁻¹
  let B : Matrix k (Fin r) ℝ := V * R * A
  let u : Fin r → ℝ := root • (Rᵀ *ᵥ bhat - c)
  have hVunit : IsUnit V.det :=
    (Matrix.isUnit_iff_isUnit_det _).mp hV.isUnit
  have hVsym : Vᵀ = V :=
    (Matrix.conjTranspose_eq_transpose_of_trivial V).symm.trans
      hV.isHermitian.eq
  have hGunit : IsUnit G.det := by
    simpa [G] using restrictionCov_det_isUnit_of_cov_posDef V R hV hR
  have hAsym : Aᵀ = A := by
    dsimp [A, G]
    rw [Matrix.transpose_nonsing_inv, Matrix.transpose_mul,
      Matrix.transpose_mul, hVsym,
      Matrix.transpose_transpose]
    simp [Matrix.mul_assoc]
  have hAGA : A * G * A = A := by
    calc
      A * G * A = A * (G * A) := by simp [Matrix.mul_assoc]
      _ = A := by rw [Matrix.mul_nonsing_inv G hGunit]; simp
  have hdiff :
      root • (bhat - emdBetaStar R c V bhat) = B *ᵥ u := by
    rw [emdBetaStar_eq_hansen R c V bhat hVunit]
    simp [B, A, G, u, Matrix.mulVec_smul]
  have hpull : Bᵀ * V⁻¹ * B = A := by
    dsimp [B]
    rw [Matrix.transpose_mul, Matrix.transpose_mul, hAsym,
      hVsym]
    calc
      A * (Rᵀ * V) * V⁻¹ * (V * R * A) =
          A * Rᵀ * (V * V⁻¹) * V * R * A := by
            simp [Matrix.mul_assoc]
      _ = A * Rᵀ * V * R * A := by
        rw [Matrix.mul_nonsing_inv V hVunit]
        simp [Matrix.mul_assoc]
      _ = A * G * A := by simp [G, Matrix.mul_assoc]
      _ = A := hAGA
  unfold emdJStatOrZero criterionJStatOrZero
    restrictionWaldStatOrZero
  rw [hdiff, quadraticForm_mulVec_eq_pullback_rect, hpull]

/-- **Hansen Theorem 13.13, first clause.** With a common weight matrix, the
constrained criterion cannot be below the unrestricted GMM minimum. -/
theorem gmmDistanceStat_nonneg_of_commonWeight
    {n k l : Type*} [Fintype n] [Fintype k] [Fintype l]
    [Nonempty n] [DecidableEq k]
    (X : Matrix n k ℝ) (Z : Matrix n l ℝ) (y : n → ℝ)
    (W : Matrix l l ℝ) (btilde : k → ℝ)
    [Invertible (gmmNormalizedGram X Z W)]
    (hW : W.PosSemidef) :
    0 ≤ gmmDistanceStat X Z y W btilde
      (gmmBetaOrZero X Z y W) := by
  letI : Invertible
      (LinearGMM.gram (sampleQZX Z X) W) := by
    simpa [gmmNormalizedGram] using
      (inferInstance : Invertible (gmmNormalizedGram X Z W))
  have hbeta : gmmBetaOrZero X Z y W =
      LinearGMM.beta (sampleQZX Z X) (sampleCrossMoment Z y) W := by
    rw [gmmBetaOrZero_eq_gmmBetaStar,
      gmmBetaStar_eq_normalized X Z y W]
    exact LinearGMM.betaStar_eq_beta
      (sampleQZX Z X) (sampleCrossMoment Z y) W
  have hmin := LinearGMM.beta_minimizes
    (sampleQZX Z X) (sampleCrossMoment Z y) W btilde hW
  unfold gmmDistanceStat gmmCriterionValue gmmNormalizedCriterion
  rw [hbeta]
  rw [← mul_sub]
  exact mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr hmin)

/-- **Hansen Theorem 13.13, second clause.** With a common efficient weight
and a linear restriction, the GMM distance statistic equals the Wald
statistic exactly. -/
theorem gmmDistanceStat_eq_wald_of_linear_commonWeight
    {n k l : Type*} {r : ℕ}
    [Fintype n] [Fintype k] [Fintype l] [Nonempty n]
    [DecidableEq k]
    (X : Matrix n k ℝ) (Z : Matrix n l ℝ) (y : n → ℝ)
    (W : Matrix l l ℝ) (R : Matrix k (Fin r) ℝ) (c : Fin r → ℝ)
    (hW : W.PosSemidef)
    (hG : (gmmNormalizedGram X Z W).PosDef)
    (hR : Function.Injective R.mulVec) :
    gmmDistanceStat X Z y W
        (gmmConstrainedBetaStar X Z y W R c)
        (gmmBetaOrZero X Z y W) =
      restrictionWaldStatOrZero
        (Real.sqrt (Fintype.card n : ℝ) •
          (Rᵀ *ᵥ gmmBetaOrZero X Z y W - c))
        (Rᵀ * (gmmNormalizedGram X Z W)⁻¹ * R) := by
  let G : Matrix k k ℝ := gmmNormalizedGram X Z W
  let bhat : k → ℝ := gmmBetaOrZero X Z y W
  let btilde : k → ℝ := gmmConstrainedBetaStar X Z y W R c
  let root : ℝ := Real.sqrt (Fintype.card n : ℝ)
  have hGunit : IsUnit G.det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (by simpa [G] using hG.isUnit)
  letI : Invertible G :=
    Matrix.invertibleOfIsUnitDet (A := G) hGunit
  letI : Invertible
      (LinearGMM.gram (sampleQZX Z X) W) := by
    simpa [G, gmmNormalizedGram] using (inferInstance : Invertible G)
  have hbeta : bhat =
      LinearGMM.beta (sampleQZX Z X) (sampleCrossMoment Z y) W := by
    dsimp [bhat]
    rw [gmmBetaOrZero_eq_gmmBetaStar,
      gmmBetaStar_eq_normalized X Z y W]
    exact LinearGMM.betaStar_eq_beta
      (sampleQZX Z X) (sampleCrossMoment Z y) W
  have hcompletion := LinearGMM.criterion_eq_at_beta_add_quadratic_form
    (sampleQZX Z X) (sampleCrossMoment Z y) W btilde hW
  have hcriterion :
      gmmNormalizedCriterion X Z y W btilde -
          gmmNormalizedCriterion X Z y W bhat =
        (btilde - bhat) ⬝ᵥ (G *ᵥ (btilde - bhat)) := by
    have hc :
        gmmNormalizedCriterion X Z y W btilde =
          gmmNormalizedCriterion X Z y W bhat +
            (btilde - bhat) ⬝ᵥ (G *ᵥ (btilde - bhat)) := by
      simpa [gmmNormalizedCriterion, G, hbeta] using hcompletion
    linarith
  have hbtilde : btilde = emdBetaStar R c G⁻¹ bhat := by
    simp [btilde, bhat, gmmConstrainedBetaStar, emdBetaStar, G,
      Matrix.nonsing_inv_nonsing_inv G hGunit]
  have hscale :
      (Fintype.card n : ℝ) *
          ((btilde - bhat) ⬝ᵥ (G *ᵥ (btilde - bhat))) =
        emdJStatOrZero G⁻¹ bhat btilde root := by
    have hsqrt : root ^ 2 = (Fintype.card n : ℝ) := by
      simp [root, Real.sq_sqrt (Nat.cast_nonneg (Fintype.card n))]
    have hdiff : bhat - btilde = -(btilde - bhat) := by
      abel
    rw [← hsqrt]
    unfold emdJStatOrZero criterionJStatOrZero
    rw [Matrix.nonsing_inv_nonsing_inv G hGunit]
    rw [hdiff]
    simp only [Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul,
      Matrix.mulVec_neg, neg_dotProduct_neg]
    simp [pow_two, mul_assoc]
  have hemd := emdJStatOrZero_eq_restrictionWaldStatOrZero
    R c G⁻¹ bhat root hG.inv hR
  calc
    gmmDistanceStat X Z y W btilde bhat =
        (Fintype.card n : ℝ) *
          (gmmNormalizedCriterion X Z y W btilde -
            gmmNormalizedCriterion X Z y W bhat) := by
          simp [gmmDistanceStat, gmmCriterionValue, mul_sub]
    _ = (Fintype.card n : ℝ) *
        ((btilde - bhat) ⬝ᵥ (G *ᵥ (btilde - bhat))) := by
          rw [hcriterion]
    _ = emdJStatOrZero G⁻¹ bhat btilde root := hscale
    _ = emdJStatOrZero G⁻¹ bhat (emdBetaStar R c G⁻¹ bhat) root := by
          rw [← hbtilde]
    _ = restrictionWaldStatOrZero
        (root • (Rᵀ *ᵥ bhat - c)) (Rᵀ * G⁻¹ * R) := hemd
    _ = restrictionWaldStatOrZero
        (Real.sqrt (Fintype.card n : ℝ) •
          (Rᵀ *ᵥ gmmBetaOrZero X Z y W - c))
        (Rᵀ * (gmmNormalizedGram X Z W)⁻¹ * R) := by
          rfl

/-! ## Hansen Theorem 13.12 -/

/-- Generic transfer engine for Hansen Theorem 13.12. If a distance statistic
differs from the Chapter 13.8 Wald statistic by `o_p(1)`, it has the same
chi-square limit. -/
theorem gmmDistanceStat_tendstoInDistribution_chiSquared
    {OmegaSpace : Type*} [MeasurableSpace OmegaSpace]
    {mu : Measure OmegaSpace} [IsProbabilityMeasure mu]
    {r : ℕ} [Fact (0 < r)]
    (D Wald : ℕ → OmegaSpace → ℝ)
    (hWald : TendstoInDistribution Wald atTop (fun x : ℝ => x)
      (fun _ => mu) (chiSquared r))
    (hrem : TendstoInMeasure mu (D - Wald) atTop (fun _ => 0))
    (hD_meas : ∀ n, AEMeasurable (D n) mu) :
    TendstoInDistribution D atTop (fun x : ℝ => x)
      (fun _ => mu) (chiSquared r) :=
  tendstoInDistribution_of_tendstoInMeasure_sub
    (X := Wald) (Y := D) (Z := fun x : ℝ => x)
    hWald hrem hD_meas

set_option maxHeartbeats 2000000 in
-- The core combines two-step GMM, nonlinear MD, and a singular-event bridge.
private theorem
    gmmUncenteredTwoStepDistanceStatOrZero_tendstoInDistribution_of_linearization
    {OmegaSpace : Type*} [MeasurableSpace OmegaSpace]
    {mu : Measure OmegaSpace} [IsProbabilityMeasure mu]
    {k l q : Type*} [Fintype k] [Fintype l] [Fintype q]
    [DecidableEq k] [DecidableEq l] [DecidableEq q]
    [Fact (0 < Fintype.card q)]
    {Z : ℕ → OmegaSpace → l → ℝ}
    {X : ℕ → OmegaSpace → k → ℝ}
    {e Y : ℕ → OmegaSpace → ℝ}
    {b : k → ℝ}
    (h : TwoSLSObservedIidFourthMomentPositiveCovarianceConditions
      mu Z X e Y b)
    (Rderiv : Matrix k q ℝ)
    (btilde : ℕ → OmegaSpace → k → ℝ)
    (hbtilde_meas : ∀ n, AEStronglyMeasurable (btilde n) mu)
    (hR : Function.Injective Rderiv.mulVec)
    (hlinear :
      let Q :=
        twoSLSCombinedQZX (popGram mu (twoSLSCombinedRegressors Z X))
      let G := gmmPopulationGram Q (scoreCovMat mu Z e)⁻¹
      ConstrainedEstimatorLinearization mu
        (fun n => Real.sqrt (n : ℝ)) btilde b G Rderiv
        (fun n omega =>
          Real.sqrt (n : ℝ) •
            (gmmUncenteredTwoStepBetaOrZero
              (stackRegressors X n omega) (stackRegressors Z n omega)
              (stackOutcomes Y n omega) - b))) :
    TendstoInDistribution
      (fun n omega =>
        gmmUncenteredTwoStepDistanceStatOrZero
          (stackRegressors X n omega) (stackRegressors Z n omega)
          (stackOutcomes Y n omega) (btilde n omega))
      atTop (fun x : ℝ => x) (fun _ => mu)
      (chiSquared (Fintype.card q)) := by
  classical
  let hCore := h.toJointIidMixedMomentConditions
  let hIid :=
    hCore.toTwoSLSResidualJointIidFourthMomentPositiveCovarianceConditions
      |>.toIidFourthConditions
  let hGram : TwoSLSGramScoreCLTPositiveCovarianceConditions mu Z X e :=
    hIid.toGramConditions
  let hCov := hCore.toCovarianceMomentConsistencyConditions b h.model
  let Q : Matrix l k ℝ :=
    twoSLSCombinedQZX (popGram mu (twoSLSCombinedRegressors Z X))
  let Omega : Matrix l l ℝ := scoreCovMat mu Z e
  let G : Matrix k k ℝ := gmmPopulationGram Q Omega⁻¹
  let V : Matrix k k ℝ := G⁻¹
  let OmegaHat : ℕ → OmegaSpace → Matrix l l ℝ := fun n omega =>
    twoSLSOmegaHatStar
      (stackRegressors Z n omega) (stackRegressors X n omega)
      (stackOutcomes Y n omega)
  let What : ℕ → OmegaSpace → Matrix l l ℝ := fun n omega =>
    (OmegaHat n omega)⁻¹
  let bhat : ℕ → OmegaSpace → k → ℝ := fun n omega =>
    gmmBetaOrZero
      (stackRegressors X n omega) (stackRegressors Z n omega)
      (stackOutcomes Y n omega) (What n omega)
  let Qhat : ℕ → OmegaSpace → Matrix l k ℝ := fun n omega =>
    sampleQZX (stackRegressors Z n omega)
      (stackRegressors X n omega)
  let Ghat : ℕ → OmegaSpace → Matrix k k ℝ := fun n omega =>
    gmmPopulationGram (Qhat n omega) (What n omega)
  let Vhat : ℕ → OmegaSpace → Matrix k k ℝ := fun n omega =>
    (Ghat n omega)⁻¹
  let D : ℕ → OmegaSpace → ℝ := fun n omega =>
    gmmDistanceStat
      (stackRegressors X n omega) (stackRegressors Z n omega)
      (stackOutcomes Y n omega) (What n omega)
      (btilde n omega) (bhat n omega)
  let E : ℕ → OmegaSpace → ℝ := fun n omega =>
    emdJStatOrZero (Vhat n omega) (bhat n omega) (btilde n omega)
      (Real.sqrt (n : ℝ))
  have hOmega_meas : ∀ n, AEStronglyMeasurable (OmegaHat n) mu := by
    intro n
    simpa [OmegaHat] using hCov.omega_meas n
  have hWhat_meas : ∀ n, AEStronglyMeasurable (What n) mu :=
    fun n => aestronglyMeasurable_matrix_inv (hOmega_meas n)
  have hOmega : TendstoInMeasure mu OmegaHat atTop (fun _ => Omega) := by
    simpa [OmegaHat, Omega] using hCov.omega_tendsto
  have hWhat : TendstoInMeasure mu What atTop (fun _ => Omega⁻¹) := by
    simpa [What] using
      tendstoInMeasure_matrix_inv hOmega_meas hOmega
        (fun _ => (Matrix.isUnit_iff_isUnit_det Omega).mp (by
          simpa [Omega] using h.omega_posDef.isUnit))
  let hMoment : GMMMomentCLTConditions mu Qhat What Z e Q Omega⁻¹ := by
    simpa [Qhat] using hGram.toGMMMomentCLTConditions
      What Omega⁻¹ hWhat_meas hWhat h.omega_posDef.inv
  have hGpos : G.PosDef := by
    exact LinearGMM.gram_posDef Q Omega⁻¹
      (by simpa [Omega] using h.omega_posDef.inv)
      (by simpa [Q] using h.qzx_rank)
  have hVpos : V.PosDef := by
    simpa [V] using hGpos.inv
  have hBeta : TendstoInDistribution
      (fun (n : ℕ) omega => Real.sqrt (n : ℝ) • (bhat n omega - b))
      atTop (fun z : EuclideanSpace ℝ k => z.ofLp) (fun _ => mu)
      (multivariateGaussian 0 V) := by
    simpa [bhat, What, OmegaHat, V, G, Q, Omega,
      gmmUncenteredTwoStepWeightStar] using
      gmmBetaOrZero_uncenteredTwoStep_tendstoInDistribution_observedRows h
  let hGaussian :
      GaussianLimit mu
        (fun (n : ℕ) omega => Real.sqrt (n : ℝ) • (bhat n omega - b)) V :=
    { covariance_posSemidef := hVpos.posSemidef
      limit := hBeta }
  have hVinv : V⁻¹ = G := by
    dsimp [V]
    exact Matrix.nonsing_inv_nonsing_inv G
      ((Matrix.isUnit_iff_isUnit_det G).mp hGpos.isUnit)
  have hlinear' :
      ConstrainedEstimatorLinearization mu
        (fun n => Real.sqrt (n : ℝ)) btilde b V⁻¹ Rderiv
        (fun (n : ℕ) omega => Real.sqrt (n : ℝ) • (bhat n omega - b)) := by
    rw [hVinv]
    simpa [Q, G, Omega, bhat, What, OmegaHat,
      gmmUncenteredTwoStepBetaOrZero,
      gmmUncenteredTwoStepWeightStar] using hlinear
  have hDiff : TendstoInDistribution
      (fun (n : ℕ) omega =>
        Real.sqrt (n : ℝ) • (bhat n omega - btilde n omega))
      atTop (fun z : EuclideanSpace ℝ k => z.ofLp) (fun _ => mu)
      (multivariateGaussian 0 (emdDifferenceAsymptoticVariance Rderiv V)) :=
  unrestrictedSubConstrainedEstimator_efficientDifference_tendstoInDistribution_multivariateGaussian
      (μ := mu) (root := fun n => Real.sqrt (n : ℝ))
      (bhat := bhat) (btilde := btilde) (β := b)
      (R := Rderiv) (V := V) hlinear' hGaussian
      ((Matrix.isUnit_iff_isUnit_det V).mp hVpos.isUnit)
  have hGhat_meas : ∀ n, AEStronglyMeasurable (Ghat n) mu := by
    intro n
    exact gmmPopulationGram_aestronglyMeasurable
      (Qhat n) (What n) (hMoment.q_meas n) (hWhat_meas n)
  have hGhat : TendstoInMeasure mu Ghat atTop (fun _ => G) := by
    simpa [Ghat, G] using
      gmmPopulationGram_tendstoInMeasure
        hMoment.toGMMWeightConvergenceConditions
  have hVhat_meas : ∀ n, AEStronglyMeasurable (Vhat n) mu :=
    fun n => aestronglyMeasurable_matrix_inv (hGhat_meas n)
  have hVhat : TendstoInMeasure mu Vhat atTop (fun _ => V) := by
    simpa [Vhat, V] using
      tendstoInMeasure_matrix_inv hGhat_meas hGhat
        (fun _ => (Matrix.isUnit_iff_isUnit_det G).mp hGpos.isUnit)
  have hLaw :=
    emdDifferenceCriterionQuadratic_hasLaw_chiSquared
      Rderiv V hVpos hR
  have hE : TendstoInDistribution E atTop (fun x : ℝ => x)
      (fun _ => mu) (chiSquared (Fintype.card q)) := by
    simpa [E] using
      emdJStatOrZero_tendstoInDistribution_chiSquared_of_limitLaw
        (μ := mu)
        (ν := multivariateGaussian 0
          (emdDifferenceAsymptoticVariance Rderiv V))
        (df := Fintype.card q)
        (bhat := bhat) (btilde := btilde)
        (root := fun n => Real.sqrt (n : ℝ))
        (Z := fun z : EuclideanSpace ℝ k => z.ofLp)
        (Vhat := Vhat) (V := V)
        hDiff hVhat_meas hVhat
        ((Matrix.isUnit_iff_isUnit_det V).mp hVpos.isUnit) hLaw
  have hbridge : TendstoInMeasure mu (D - E) atTop (fun _ => 0) := by
    have hsingular :=
      measure_gmmPopulationGram_singular_tendsto_zero
        hMoment.toGMMWeightConvergenceConditions
    intro epsilon hepsilon
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      hsingular (Eventually.of_forall (fun _ => zero_le _)) ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    refine measure_mono ?_
    intro omega homega
    simp only [Set.mem_setOf_eq] at homega ⊢
    intro hgram
    haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    have hWpsd : (What n omega).PosSemidef := by
      dsimp [What, OmegaHat]
      exact Matrix.PosSemidef.inv
        (twoSLSOmegaHatStar_posSemidef_local
          (stackRegressors Z n omega) (stackRegressors X n omega)
          (stackOutcomes Y n omega))
    have hDE : D n omega - E n omega = 0 := by
      rw [sub_eq_zero]
      simpa [D, E, Ghat, Qhat, Vhat, bhat, gmmNormalizedGram] using
        gmmDistanceStat_eq_emdJStatOrZero_of_commonWeight_isUnit
          (stackRegressors X n omega) (stackRegressors Z n omega)
          (stackOutcomes Y n omega) (What n omega)
          (btilde n omega) hWpsd hgram
    change epsilon ≤ edist (D n omega - E n omega) 0 at homega
    rw [hDE, edist_self] at homega
    exact absurd homega (not_le.mpr hepsilon)
  have hY : ∀ i, AEStronglyMeasurable (Y i) mu :=
    fun i => continuous_snd.comp_aestronglyMeasurable
      (h.observed_aestronglyMeasurable i)
  have hD_meas : ∀ n, AEMeasurable (D n) mu := by
    intro n
    have hZmat : AEStronglyMeasurable
        (fun omega => stackRegressors Z n omega) mu := by
      simpa [stackRegressors] using
        stackMatrix_aestronglyMeasurable (μ := mu)
          hCore.z_aestronglyMeasurable
    have hXmat : AEStronglyMeasurable
        (fun omega => stackRegressors X n omega) mu := by
      simpa [stackRegressors] using
        stackMatrix_aestronglyMeasurable (μ := mu)
          hCore.x_aestronglyMeasurable
    have hyvec : AEStronglyMeasurable
        (fun omega => stackOutcomes Y n omega) mu := by
      simpa [stackOutcomes] using
        stackScalar_aestronglyMeasurable (μ := mu) hY
    have hbhat : AEStronglyMeasurable (bhat n) mu := by
      simpa [bhat] using
        gmmBetaOrZero_aestronglyMeasurable_of_rows
          (mu := mu) (n := n) (Z := Z) (X := X) (Y := Y)
          (What := What n)
          hCore.z_aestronglyMeasurable hCore.x_aestronglyMeasurable hY
          (hWhat_meas n)
    have hrestricted := gmmCriterionValue_aestronglyMeasurable
      (mu := mu) hXmat hZmat hyvec (hWhat_meas n) (hbtilde_meas n)
    have hunrestricted := gmmCriterionValue_aestronglyMeasurable
      (mu := mu) hXmat hZmat hyvec (hWhat_meas n) hbhat
    simpa [D, gmmDistanceStat] using
      hrestricted.sub hunrestricted |>.aemeasurable
  have hD : TendstoInDistribution D atTop (fun x : ℝ => x)
      (fun _ => mu) (chiSquared (Fintype.card q)) :=
    gmmDistanceStat_tendstoInDistribution_chiSquared
      D E hE hbridge hD_meas
  simpa [D, gmmUncenteredTwoStepDistanceStatOrZero, bhat, What,
    OmegaHat, gmmUncenteredTwoStepWeightStar] using hD

/-- Conditional nonlinear observed-row endpoint toward Hansen Theorem 13.12.

`h73` is Hansen Assumption 7.3, while `hlinear` is an additional optimizer
regularity premise: it records the first-order expansion of the supplied
nonlinear constrained GMM estimator and is not implied by Assumption 7.3
alone. The exact linear-restriction endpoint below derives this expansion
from the concrete constrained estimator. -/
theorem
    gmmUncenteredTwoStepDistanceStatOrZero_tendstoInDistribution_observedRows_of_linearization
    {OmegaSpace : Type*} [MeasurableSpace OmegaSpace]
    {mu : Measure OmegaSpace} [IsProbabilityMeasure mu]
    {k l q : Type*} [Fintype k] [Fintype l] [Fintype q]
    [DecidableEq k] [DecidableEq l] [DecidableEq q]
    [Fact (0 < Fintype.card q)]
    {Z : ℕ → OmegaSpace → l → ℝ}
    {X : ℕ → OmegaSpace → k → ℝ}
    {e Y : ℕ → OmegaSpace → ℝ}
    {b : k → ℝ}
    (h : TwoSLSObservedIidFourthMomentPositiveCovarianceConditions
      mu Z X e Y b)
    (rfun : (k → ℝ) → (q → ℝ)) (theta0 : q → ℝ)
    (Rderiv : Matrix k q ℝ)
    (btilde : ℕ → OmegaSpace → k → ℝ)
    (h73 : SmoothFunctionCondition rfun b Rderiv)
    (hnull : rfun b = theta0)
    (hconstraint : ∀ n omega, rfun (btilde n omega) = theta0)
    (hbtilde_meas : ∀ n, AEStronglyMeasurable (btilde n) mu)
    (hlinear :
      let Q :=
        twoSLSCombinedQZX (popGram mu (twoSLSCombinedRegressors Z X))
      let G := gmmPopulationGram Q (scoreCovMat mu Z e)⁻¹
      ConstrainedEstimatorLinearization mu
        (fun n => Real.sqrt (n : ℝ)) btilde b G Rderiv
        (fun n omega =>
          Real.sqrt (n : ℝ) •
            (gmmUncenteredTwoStepBetaOrZero
              (stackRegressors X n omega) (stackRegressors Z n omega)
              (stackOutcomes Y n omega) - b))) :
    TendstoInDistribution
      (fun n omega =>
        gmmUncenteredTwoStepDistanceStatOrZero
          (stackRegressors X n omega) (stackRegressors Z n omega)
          (stackOutcomes Y n omega) (btilde n omega))
      atTop (fun x : ℝ => x) (fun _ => mu)
      (chiSquared (Fintype.card q)) := by
  have _ := hnull
  have _ := hconstraint
  exact
    gmmUncenteredTwoStepDistanceStatOrZero_tendstoInDistribution_of_linearization
      h Rderiv btilde hbtilde_meas h73.fullRank hlinear

/-- The actual common-weight linear-restriction distance statistic. The
constrained coefficient is Hansen equation (13.16), totalized through the
chapter's Star convention. -/
noncomputable def gmmUncenteredTwoStepLinearDistanceStatOrZero
    {n k l q : Type*} [Fintype n] [Fintype k] [Fintype l] [Fintype q]
    [DecidableEq k] [DecidableEq l] [DecidableEq q]
    (X : Matrix n k ℝ) (Z : Matrix n l ℝ) (y : n → ℝ)
    (R : Matrix k q ℝ) (c : q → ℝ) : ℝ :=
  let W := gmmUncenteredTwoStepWeightStar Z X y
  gmmUncenteredTwoStepDistanceStatOrZero X Z y
    (gmmConstrainedBetaStar X Z y W R c)

set_option maxHeartbeats 1200000 in
-- Random-weight MD supplies the constrained-estimator expansion for linear restrictions.
private theorem
    gmmUncenteredTwoStepLinearConstrained_linearization_observedRows
    {OmegaSpace : Type*} [MeasurableSpace OmegaSpace]
    {mu : Measure OmegaSpace} [IsProbabilityMeasure mu]
    {k l q : Type*} [Fintype k] [Fintype l] [Fintype q]
    [DecidableEq k] [DecidableEq l] [DecidableEq q]
    {Z : ℕ → OmegaSpace → l → ℝ}
    {X : ℕ → OmegaSpace → k → ℝ}
    {e Y : ℕ → OmegaSpace → ℝ}
    {b : k → ℝ}
    (h : TwoSLSObservedIidFourthMomentPositiveCovarianceConditions
      mu Z X e Y b)
    (R : Matrix k q ℝ) (c : q → ℝ)
    (hR : Function.Injective R.mulVec)
    (hnull : Rᵀ *ᵥ b = c) :
    let Q :=
      twoSLSCombinedQZX (popGram mu (twoSLSCombinedRegressors Z X))
    let G := gmmPopulationGram Q (scoreCovMat mu Z e)⁻¹
    let btilde : ℕ → OmegaSpace → k → ℝ := fun n omega =>
      let Xn := stackRegressors X n omega
      let Zn := stackRegressors Z n omega
      let yn := stackOutcomes Y n omega
      let Wn := gmmUncenteredTwoStepWeightStar Zn Xn yn
      gmmConstrainedBetaStar Xn Zn yn Wn R c
    ConstrainedEstimatorLinearization mu
        (fun n => Real.sqrt (n : ℝ)) btilde b G R
        (fun n omega =>
          Real.sqrt (n : ℝ) •
            (gmmUncenteredTwoStepBetaOrZero
              (stackRegressors X n omega) (stackRegressors Z n omega)
              (stackOutcomes Y n omega) - b)) ∧
      ∀ n, AEStronglyMeasurable (btilde n) mu := by
  classical
  let hCore := h.toJointIidMixedMomentConditions
  let hIid :=
    hCore.toTwoSLSResidualJointIidFourthMomentPositiveCovarianceConditions
      |>.toIidFourthConditions
  let hGram : TwoSLSGramScoreCLTPositiveCovarianceConditions mu Z X e :=
    hIid.toGramConditions
  let hCov := hCore.toCovarianceMomentConsistencyConditions b h.model
  let Q : Matrix l k ℝ :=
    twoSLSCombinedQZX (popGram mu (twoSLSCombinedRegressors Z X))
  let Omega : Matrix l l ℝ := scoreCovMat mu Z e
  let G : Matrix k k ℝ := gmmPopulationGram Q Omega⁻¹
  let OmegaHat : ℕ → OmegaSpace → Matrix l l ℝ := fun n omega =>
    twoSLSOmegaHatStar
      (stackRegressors Z n omega) (stackRegressors X n omega)
      (stackOutcomes Y n omega)
  let What : ℕ → OmegaSpace → Matrix l l ℝ := fun n omega =>
    (OmegaHat n omega)⁻¹
  let bhat : ℕ → OmegaSpace → k → ℝ := fun n omega =>
    gmmBetaOrZero
      (stackRegressors X n omega) (stackRegressors Z n omega)
      (stackOutcomes Y n omega) (What n omega)
  let Qhat : ℕ → OmegaSpace → Matrix l k ℝ := fun n omega =>
    sampleQZX (stackRegressors Z n omega)
      (stackRegressors X n omega)
  let Ghat : ℕ → OmegaSpace → Matrix k k ℝ := fun n omega =>
    gmmPopulationGram (Qhat n omega) (What n omega)
  let btilde : ℕ → OmegaSpace → k → ℝ := fun n omega =>
    gmmConstrainedBetaStar
      (stackRegressors X n omega) (stackRegressors Z n omega)
      (stackOutcomes Y n omega) (What n omega) R c
  have hOmegaMeas : ∀ n, AEStronglyMeasurable (OmegaHat n) mu := by
    intro n
    simpa [OmegaHat] using hCov.omega_meas n
  have hWhatMeas : ∀ n, AEStronglyMeasurable (What n) mu :=
    fun n => aestronglyMeasurable_matrix_inv (hOmegaMeas n)
  have hOmega : TendstoInMeasure mu OmegaHat atTop (fun _ => Omega) := by
    simpa [OmegaHat, Omega] using hCov.omega_tendsto
  have hWhat : TendstoInMeasure mu What atTop (fun _ => Omega⁻¹) := by
    simpa [What] using
      tendstoInMeasure_matrix_inv hOmegaMeas hOmega
        (fun _ => (Matrix.isUnit_iff_isUnit_det Omega).mp (by
          simpa [Omega] using h.omega_posDef.isUnit))
  let hMoment : GMMMomentCLTConditions mu Qhat What Z e Q Omega⁻¹ := by
    simpa [Qhat] using hGram.toGMMMomentCLTConditions
      What Omega⁻¹ hWhatMeas hWhat h.omega_posDef.inv
  have hGpos : G.PosDef := by
    exact LinearGMM.gram_posDef Q Omega⁻¹
      (by simpa [Omega] using h.omega_posDef.inv)
      (by simpa [Q] using h.qzx_rank)
  have hGhatMeas : ∀ n, AEStronglyMeasurable (Ghat n) mu := by
    intro n
    exact gmmPopulationGram_aestronglyMeasurable
      (Qhat n) (What n) (hMoment.q_meas n) (hWhatMeas n)
  have hGhat : TendstoInMeasure mu Ghat atTop (fun _ => G) := by
    simpa [Ghat, G] using
      gmmPopulationGram_tendstoInMeasure
        hMoment.toGMMWeightConvergenceConditions
  have hY : ∀ i, AEStronglyMeasurable (Y i) mu :=
    fun i => continuous_snd.comp_aestronglyMeasurable
      (h.observed_aestronglyMeasurable i)
  have hbhatMeas : ∀ n, AEStronglyMeasurable (bhat n) mu := by
    intro n
    simpa [bhat] using
      gmmBetaOrZero_aestronglyMeasurable_of_rows
        (mu := mu) (n := n) (Z := Z) (X := X) (Y := Y)
        (What := What n)
        hCore.z_aestronglyMeasurable hCore.x_aestronglyMeasurable hY
        (hWhatMeas n)
  have hBeta : TendstoInDistribution
      (fun (n : ℕ) omega => Real.sqrt (n : ℝ) • (bhat n omega - b))
      atTop (fun z : EuclideanSpace ℝ k => z.ofLp) (fun _ => mu)
      (multivariateGaussian 0 G⁻¹) := by
    simpa [bhat, What, OmegaHat, G, Q, Omega,
      gmmUncenteredTwoStepWeightStar] using
      gmmBetaOrZero_uncenteredTwoStep_tendstoInDistribution_observedRows h
  have hBetaBounded : ∀ j, BoundedInProbability mu
      (fun n omega =>
        (Real.sqrt (n : ℝ) • (bhat n omega - b)) j) := by
    intro j
    exact BoundedInProbability.of_tendstoInDistribution
      (hBeta.continuous_comp (continuous_apply j))
  let hLinear :=
    mdRandomWeight_asymptoticallyLinearEstimator
      (μ := mu) (fun n => Real.sqrt (n : ℝ)) bhat Ghat G R c b
      hbhatMeas hGhatMeas hGhat
      ((Matrix.isUnit_iff_isUnit_det G).mp hGpos.isUnit)
      (restrictionGram_det_isUnit_of_weight_posDef G R hGpos hR)
      hnull hBetaBounded
  refine ⟨?_, ?_⟩
  · refine
      { scaled_measurable := ?_
        expansion := ?_ }
    · simpa [constrainedScaledError, mdScaledError, btilde,
        gmmConstrainedBetaStar, gmmNormalizedGram, bhat, Ghat, Qhat,
        What, OmegaHat, gmmUncenteredTwoStepBetaOrZero,
        gmmUncenteredTwoStepWeightStar] using
        hLinear.scaled_measurable
    · simpa [constrainedScaledError, mdScaledError, btilde,
        gmmConstrainedBetaStar, gmmNormalizedGram, bhat, Ghat, Qhat,
        What, OmegaHat, gmmUncenteredTwoStepBetaOrZero,
        gmmUncenteredTwoStepWeightStar] using
        hLinear.expansion
  · intro n
    simpa [btilde, gmmConstrainedBetaStar, gmmNormalizedGram, bhat,
      Ghat, Qhat, What, OmegaHat, gmmUncenteredTwoStepWeightStar] using
      mdBetaStar_aestronglyMeasurable
        (Ghat n) R c (bhat n) (hGhatMeas n) (hbhatMeas n)

set_option maxHeartbeats 2400000 in
-- The endpoint derives the constrained-estimator expansion before invoking the distance core.
/-- **Hansen Theorem 13.12, exact linear-restriction observed-row form.**
Under Assumption 12.2 and the null `R' b = c`, the actual common-efficient-
weight restricted-minus-unrestricted GMM criterion converges to chi-square
with the number of restrictions as degrees of freedom. -/
theorem
    gmmUncenteredTwoStepLinearDistanceStatOrZero_tendstoInDistribution_observedRows
    {OmegaSpace : Type*} [MeasurableSpace OmegaSpace]
    {mu : Measure OmegaSpace} [IsProbabilityMeasure mu]
    {k l q : Type*} [Fintype k] [Fintype l] [Fintype q]
    [DecidableEq k] [DecidableEq l] [DecidableEq q]
    [Fact (0 < Fintype.card q)]
    {Z : ℕ → OmegaSpace → l → ℝ}
    {X : ℕ → OmegaSpace → k → ℝ}
    {e Y : ℕ → OmegaSpace → ℝ}
    {b : k → ℝ}
    (h : TwoSLSObservedIidFourthMomentPositiveCovarianceConditions
      mu Z X e Y b)
    (R : Matrix k q ℝ) (c : q → ℝ)
    (hR : Function.Injective R.mulVec)
    (hnull : Rᵀ *ᵥ b = c) :
    TendstoInDistribution
      (fun n omega =>
        gmmUncenteredTwoStepLinearDistanceStatOrZero
          (stackRegressors X n omega) (stackRegressors Z n omega)
          (stackOutcomes Y n omega) R c)
      atTop (fun x : ℝ => x) (fun _ => mu)
      (chiSquared (Fintype.card q)) := by
  let btilde : ℕ → OmegaSpace → k → ℝ := fun n omega =>
    let Xn := stackRegressors X n omega
    let Zn := stackRegressors Z n omega
    let yn := stackOutcomes Y n omega
    let Wn := gmmUncenteredTwoStepWeightStar Zn Xn yn
    gmmConstrainedBetaStar Xn Zn yn Wn R c
  have hdata :=
    gmmUncenteredTwoStepLinearConstrained_linearization_observedRows
      h R c hR hnull
  have hD :=
    gmmUncenteredTwoStepDistanceStatOrZero_tendstoInDistribution_of_linearization
      h R btilde hdata.2 hR hdata.1
  simpa [gmmUncenteredTwoStepLinearDistanceStatOrZero, btilde] using hD

/-- Size form of Hansen Theorem 13.12. -/
theorem gmmDistanceTest_rejectionProb_tendsto_alpha
    {OmegaSpace : Type*} [MeasurableSpace OmegaSpace]
    {mu : Measure OmegaSpace} [IsProbabilityMeasure mu]
    {r : ℕ} [Fact (0 < r)]
    {D : ℕ → OmegaSpace → ℝ} {crit : ℝ} {alpha : ℝ≥0∞}
    (hcrit : (chiSquared r) (Set.Ioi crit) = alpha)
    (hD : TendstoInDistribution D atTop (fun x : ℝ => x)
      (fun _ => mu) (chiSquared r)) :
    Tendsto (fun n => mu {omega | crit < D n omega}) atTop
      (𝓝 alpha) :=
  chiSquaredTest_rejectionProb_tendsto_alpha_of_stat hcrit hD

/-- Asymptotic-size conclusion for the exact linear-restriction form of
Hansen Theorem 13.12. -/
theorem
    gmmUncenteredTwoStepLinearDistanceTest_rejectionProb_tendsto_alpha_observedRows
    {OmegaSpace : Type*} [MeasurableSpace OmegaSpace]
    {mu : Measure OmegaSpace} [IsProbabilityMeasure mu]
    {k l q : Type*} [Fintype k] [Fintype l] [Fintype q]
    [DecidableEq k] [DecidableEq l] [DecidableEq q]
    [Fact (0 < Fintype.card q)]
    {Z : ℕ → OmegaSpace → l → ℝ}
    {X : ℕ → OmegaSpace → k → ℝ}
    {e Y : ℕ → OmegaSpace → ℝ}
    {b : k → ℝ}
    {crit : ℝ} {alpha : ℝ≥0∞}
    (hcrit : (chiSquared (Fintype.card q)) (Set.Ioi crit) = alpha)
    (h : TwoSLSObservedIidFourthMomentPositiveCovarianceConditions
      mu Z X e Y b)
    (R : Matrix k q ℝ) (c : q → ℝ)
    (hR : Function.Injective R.mulVec)
    (hnull : Rᵀ *ᵥ b = c) :
    Tendsto
      (fun n => mu {omega |
        crit <
          gmmUncenteredTwoStepLinearDistanceStatOrZero
            (stackRegressors X n omega) (stackRegressors Z n omega)
            (stackOutcomes Y n omega) R c})
      atTop (nhds alpha) :=
  chiSquaredTest_rejectionProb_tendsto_alpha_of_stat hcrit
    (gmmUncenteredTwoStepLinearDistanceStatOrZero_tendstoInDistribution_observedRows
      h R c hR hnull)

/-! ## Hansen J and subset specification tests -/

/-- Totalized residual-maker in the moment space,
`I - Q (Q'WQ)⁻¹ Q'W`. -/
noncomputable def gmmResidualMakerStar
    {k l : Type*} [Fintype k] [Fintype l]
    [DecidableEq k] [DecidableEq l]
    (Q : Matrix l k ℝ) (W : Matrix l l ℝ) : Matrix l l ℝ :=
  (1 : Matrix l l ℝ) - Q * gmmLinearizationMatrixStar Q W

/-- Measurability of the totalized GMM residual-maker follows from
measurability of the sample derivative and weight matrix. -/
theorem gmmResidualMakerStar_aestronglyMeasurable
    {OmegaSpace : Type*} [MeasurableSpace OmegaSpace]
    {mu : Measure OmegaSpace}
    {k l : Type*} [Fintype k] [Fintype l]
    [DecidableEq k] [DecidableEq l]
    (Qhat : OmegaSpace → Matrix l k ℝ)
    (What : OmegaSpace → Matrix l l ℝ)
    (hQ : AEStronglyMeasurable Qhat mu)
    (hW : AEStronglyMeasurable What mu) :
    AEStronglyMeasurable
      (fun omega => gmmResidualMakerStar (Qhat omega) (What omega)) mu := by
  have hA := gmmLinearizationMatrixStar_aestronglyMeasurable
    Qhat What hQ hW
  have hQA : AEStronglyMeasurable
      (fun omega => Qhat omega *
        gmmLinearizationMatrixStar (Qhat omega) (What omega)) mu :=
    (Continuous.matrix_mul continuous_fst continuous_snd)
      |>.comp_aestronglyMeasurable (hQ.prodMk hA)
  simpa [gmmResidualMakerStar] using
    (aestronglyMeasurable_const.sub hQA)

set_option maxHeartbeats 1200000 in
-- Product convergence through matrix multiplication needs extra elaboration time.
/-- The sample GMM residual-maker converges with the sample derivative and
weight matrix. -/
theorem gmmResidualMakerStar_tendstoInMeasure
    {OmegaSpace : Type*} [MeasurableSpace OmegaSpace]
    {mu : Measure OmegaSpace} [IsProbabilityMeasure mu]
    {k l : Type*} [Fintype k] [Fintype l]
    [DecidableEq k] [DecidableEq l]
    {Qhat : ℕ → OmegaSpace → Matrix l k ℝ}
    {What : ℕ → OmegaSpace → Matrix l l ℝ}
    {Q : Matrix l k ℝ} {W : Matrix l l ℝ}
    (h : GMMWeightConvergenceConditions mu Qhat What Q W) :
    TendstoInMeasure mu
      (fun n omega => gmmResidualMakerStar (Qhat n omega) (What n omega))
      atTop (fun _ => gmmResidualMakerStar Q W) := by
  have hAmeas : ∀ n, AEStronglyMeasurable
      (fun omega =>
        gmmLinearizationMatrixStar (Qhat n omega) (What n omega)) mu :=
    fun n => gmmLinearizationMatrixStar_aestronglyMeasurable
      (Qhat n) (What n) (h.q_meas n) (h.weight_meas n)
  have hA := gmmLinearizationMatrixStar_tendstoInMeasure h
  have hQAmeas : ∀ n, AEStronglyMeasurable
      (fun omega => Qhat n omega *
        gmmLinearizationMatrixStar (Qhat n omega) (What n omega)) mu :=
    fun n => (Continuous.matrix_mul continuous_fst continuous_snd)
      |>.comp_aestronglyMeasurable ((h.q_meas n).prodMk (hAmeas n))
  have hQA : TendstoInMeasure mu
      (fun n omega => Qhat n omega *
        gmmLinearizationMatrixStar (Qhat n omega) (What n omega))
      atTop (fun _ => Q * gmmLinearizationMatrixStar Q W) :=
    tendstoInMeasure_matrix_mul_rect h.q_meas hAmeas h.q_tendsto hA
  have hcont : Continuous
      (fun A : Matrix l l ℝ => (1 : Matrix l l ℝ) - A) :=
    continuous_const.sub continuous_id
  simpa [gmmResidualMakerStar] using
    tendstoInMeasure_continuous_comp hQAmeas hQA hcont

/-- Hansen's scaled residual sample moment
`sqrt(n) n⁻¹ Z'(Y-X betaHat_gmm)`. -/
noncomputable def gmmScaledResidualMomentOrZero
    {n k l : Type*} [Fintype n] [Fintype k] [Fintype l]
    [DecidableEq k]
    (X : Matrix n k ℝ) (Z : Matrix n l ℝ) (y : n → ℝ)
    (W : Matrix l l ℝ) : l → ℝ :=
  Real.sqrt (Fintype.card n : ℝ) •
    sampleCrossMoment Z
      (y - X *ᵥ gmmBetaOrZero X Z y W)

/-- On the nonsingular sample-Gram event, the scaled residual moment is
exactly the GMM residual-maker applied to the true scaled score. -/
theorem gmmScaledResidualMomentOrZero_linear_model_eq_residualMakerStar
    {n k l : Type*} [Fintype n] [Fintype k] [Fintype l]
    [DecidableEq k] [DecidableEq l] [Nonempty n]
    (X : Matrix n k ℝ) (Z : Matrix n l ℝ)
    (b : k → ℝ) (e : n → ℝ) (W : Matrix l l ℝ)
    (hunit : IsUnit
      (gmmPopulationGram (sampleQZX Z X) W).det) :
    gmmScaledResidualMomentOrZero X Z (X *ᵥ b + e) W =
      gmmResidualMakerStar (sampleQZX Z X) W *ᵥ
        (Real.sqrt (Fintype.card n : ℝ) • sampleCrossMoment Z e) := by
  let bhat := gmmBetaOrZero X Z (X *ᵥ b + e) W
  have hbeta :
      bhat - b =
        gmmLinearizationMatrixStar (sampleQZX Z X) W *ᵥ
          sampleCrossMoment Z e := by
    dsimp [bhat]
    rw [gmmBetaOrZero_eq_gmmBetaStar,
      gmmBetaStar_eq_normalized X Z (X *ᵥ b + e) W]
    exact gmmNormalizedBetaStar_sub_eq_linearizedScore_of_isUnit
      X Z b e W hunit
  have hres :
      X *ᵥ b + e - X *ᵥ bhat = e - X *ᵥ (bhat - b) := by
    rw [Matrix.mulVec_sub]
    abel
  unfold gmmScaledResidualMomentOrZero
  change Real.sqrt (Fintype.card n : ℝ) •
      sampleCrossMoment Z (X *ᵥ b + e - X *ᵥ bhat) = _
  rw [hres, sampleCrossMoment_sub_mulVec, hbeta]
  simp [gmmResidualMakerStar, Matrix.sub_mulVec, Matrix.mulVec_mulVec,
    Matrix.mulVec_smul, smul_sub]

set_option maxHeartbeats 800000 in
-- The row-to-matrix measurability assembly is elaboration intensive.
/-- Measurability of Hansen's scaled GMM residual moment from measurable
observation rows and a measurable weight matrix. -/
theorem gmmScaledResidualMomentOrZero_aestronglyMeasurable_of_rows
    {OmegaSpace : Type*} [MeasurableSpace OmegaSpace]
    {mu : Measure OmegaSpace}
    {k l : Type*} [Fintype k] [Fintype l]
    [DecidableEq k]
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
        gmmScaledResidualMomentOrZero
          (stackRegressors X n omega) (stackRegressors Z n omega)
          (stackOutcomes Y n omega) (What omega)) mu := by
  classical
  let Zmat : OmegaSpace → Matrix (Fin n) l ℝ :=
    fun omega => stackRegressors Z n omega
  let Xmat : OmegaSpace → Matrix (Fin n) k ℝ :=
    fun omega => stackRegressors X n omega
  let yvec : OmegaSpace → Fin n → ℝ :=
    fun omega => stackOutcomes Y n omega
  let bhat : OmegaSpace → k → ℝ := fun omega =>
    gmmBetaOrZero (Xmat omega) (Zmat omega) (yvec omega) (What omega)
  have hZmat : AEStronglyMeasurable Zmat mu := by
    simpa [Zmat, stackRegressors] using
      stackMatrix_aestronglyMeasurable (μ := mu) hZ
  have hXmat : AEStronglyMeasurable Xmat mu := by
    simpa [Xmat, stackRegressors] using
      stackMatrix_aestronglyMeasurable (μ := mu) hX
  have hyvec : AEStronglyMeasurable yvec mu := by
    simpa [yvec, stackOutcomes] using
      stackScalar_aestronglyMeasurable (μ := mu) hY
  have hbeta : AEStronglyMeasurable bhat mu := by
    simpa [bhat, Xmat, Zmat, yvec] using
      gmmBetaOrZero_aestronglyMeasurable_of_rows
        (mu := mu) (Z := Z) (X := X) (Y := Y)
        hZ hX hY hW
  have hfit : AEStronglyMeasurable
      (fun omega => Xmat omega *ᵥ bhat omega) mu :=
    (Continuous.matrix_mulVec continuous_fst continuous_snd)
      |>.comp_aestronglyMeasurable (hXmat.prodMk hbeta)
  have hres : AEStronglyMeasurable
      (fun omega => yvec omega - Xmat omega *ᵥ bhat omega) mu :=
    hyvec.sub hfit
  have hZt : AEStronglyMeasurable
      (fun omega => (Zmat omega)ᵀ) mu :=
    continuous_id.matrix_transpose.comp_aestronglyMeasurable hZmat
  have hcross : AEStronglyMeasurable
      (fun omega =>
        (Zmat omega)ᵀ *ᵥ
          (yvec omega - Xmat omega *ᵥ bhat omega)) mu :=
    (Continuous.matrix_mulVec continuous_fst continuous_snd)
      |>.comp_aestronglyMeasurable (hZt.prodMk hres)
  simpa [gmmScaledResidualMomentOrZero, sampleCrossMoment,
    Zmat, Xmat, yvec, bhat, smul_smul] using
    (hcross.const_smul
      (Real.sqrt (Fintype.card (Fin n) : ℝ) *
        (Fintype.card (Fin n) : ℝ)⁻¹))

set_option maxHeartbeats 1200000 in
-- Controlling the singular sample-Gram event expands several matrix definitions.
/-- The actual residual moment and its residual-maker expansion differ only
on the singular sample-Gram event, whose probability vanishes. -/
theorem gmmScaledResidualMomentOrZero_sub_residualMaker_tendstoInMeasure_zero
    {OmegaSpace : Type*} [MeasurableSpace OmegaSpace]
    {mu : Measure OmegaSpace} [IsProbabilityMeasure mu]
    {k l : Type*} [Fintype k] [Fintype l]
    [DecidableEq k] [DecidableEq l]
    {What : ℕ → OmegaSpace → Matrix l l ℝ}
    {Z : ℕ → OmegaSpace → l → ℝ}
    {X : ℕ → OmegaSpace → k → ℝ}
    {e Y : ℕ → OmegaSpace → ℝ}
    {Q : Matrix l k ℝ} {W : Matrix l l ℝ}
    (h : GMMWeightConvergenceConditions mu
      (fun n omega =>
        sampleQZX (stackRegressors Z n omega)
          (stackRegressors X n omega))
      What Q W)
    (b : k → ℝ)
    (hmodel : ∀ i omega, Y i omega = (X i omega) ⬝ᵥ b + e i omega) :
    TendstoInMeasure mu
      ((fun n omega =>
        gmmScaledResidualMomentOrZero
          (stackRegressors X n omega) (stackRegressors Z n omega)
          (stackOutcomes Y n omega) (What n omega)) -
        fun n omega =>
          gmmResidualMakerStar
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
      gmmScaledResidualMomentOrZero
          (stackRegressors X n omega) (stackRegressors Z n omega)
          (stackOutcomes Y n omega) (What n omega) -
        gmmResidualMakerStar
            (sampleQZX (stackRegressors Z n omega)
              (stackRegressors X n omega))
            (What n omega) *ᵥ
          (Real.sqrt (n : ℝ) •
            sampleCrossMoment (stackRegressors Z n omega)
              (stackErrors e n omega)) = 0 := by
    rw [hY]
    exact sub_eq_zero.mpr
      (by
        simpa using
          gmmScaledResidualMomentOrZero_linear_model_eq_residualMakerStar
            (stackRegressors X n omega) (stackRegressors Z n omega)
            b (stackErrors e n omega) (What n omega) hgram)
  change epsilon ≤ edist
      (gmmScaledResidualMomentOrZero
          (stackRegressors X n omega) (stackRegressors Z n omega)
          (stackOutcomes Y n omega) (What n omega) -
        gmmResidualMakerStar
            (sampleQZX (stackRegressors Z n omega)
              (stackRegressors X n omega))
            (What n omega) *ᵥ
          (Real.sqrt (n : ℝ) •
            sampleCrossMoment (stackRegressors Z n omega)
              (stackErrors e n omega))) 0 at homega
  rw [hR, edist_self] at homega
  exact absurd homega (not_le.mpr hepsilon)

set_option maxHeartbeats 1200000 in
-- The joint vector/matrix CMT elaborates a matrix-valued continuous map.
/-- The random GMM residual-maker applied to the scaled score converges to
the population residual-maker applied to the Gaussian score limit. -/
theorem gmmResidualMakerScore_tendstoInDistribution
    {OmegaSpace : Type*} [MeasurableSpace OmegaSpace]
    {mu : Measure OmegaSpace} [IsProbabilityMeasure mu]
    {k l : Type*} [Fintype k] [Fintype l]
    [DecidableEq k] [DecidableEq l]
    {Qhat : ℕ → OmegaSpace → Matrix l k ℝ}
    {What : ℕ → OmegaSpace → Matrix l l ℝ}
    {Z : ℕ → OmegaSpace → l → ℝ}
    {e : ℕ → OmegaSpace → ℝ}
    {Q : Matrix l k ℝ} {W : Matrix l l ℝ}
    (h : GMMMomentCLTConditions mu Qhat What Z e Q W) :
    TendstoInDistribution
      (fun n omega =>
        gmmResidualMakerStar (Qhat n omega) (What n omega) *ᵥ
          (Real.sqrt (n : ℝ) •
            sampleCrossMoment (stackRegressors Z n omega)
              (stackErrors e n omega)))
      atTop
      (fun z : EuclideanSpace ℝ l =>
        gmmResidualMakerStar Q W *ᵥ z.ofLp)
      (fun _ => mu) (multivariateGaussian 0 (scoreCovMat mu Z e)) := by
  let T : ℕ → OmegaSpace → EuclideanSpace ℝ l := fun n omega =>
    WithLp.toLp 2
      (Real.sqrt (n : ℝ) •
        sampleCrossMoment (stackRegressors Z n omega)
          (stackErrors e n omega))
  have hT : TendstoInDistribution T atTop
      (fun z : EuclideanSpace ℝ l => z) (fun _ => mu)
      (multivariateGaussian 0 (scoreCovMat mu Z e)) := by
    simpa [T] using
      scoreEuclidean_sampleCrossMoment_tendstoInDistribution_multivariateGaussian
        (μ := mu) (X := Z) (e := e) h.score_clt
  have hM := gmmResidualMakerStar_tendstoInMeasure
    h.toGMMWeightConvergenceConditions
  have hraw := matrixContinuousLinearMap_tendstoInDistribution_of_vector_and_matrix
    (μ := mu) (T := T) (Zlim := fun z : EuclideanSpace ℝ l => z)
    (Ahat := fun n omega =>
      gmmResidualMakerStar (Qhat n omega) (What n omega))
    (A := gmmResidualMakerStar Q W) hT
      (fun n => gmmResidualMakerStar_aestronglyMeasurable
        (Qhat n) (What n) (h.q_meas n) (h.weight_meas n)) hM
  have hout := hraw.continuous_comp
    (PiLp.continuous_ofLp 2 (fun _ : l => ℝ))
  refine TendstoInDistribution.congr ?_ EventuallyEq.rfl hout
  intro n
  exact ae_of_all mu (fun omega => by
    simp [T, matrixContinuousLinearMap_apply,
      Matrix.mulVec_smul, Matrix.mulVec_sum, Finset.smul_sum, smul_smul])

set_option maxHeartbeats 1200000 in
-- Slutsky assembly with the singular-event replacement needs extra elaboration time.
/-- Hansen's actual scaled residual moment has the residualized Gaussian
limit; the singular-design discrepancy is discharged internally. -/
theorem gmmScaledResidualMomentOrZero_tendstoInDistribution
    {OmegaSpace : Type*} [MeasurableSpace OmegaSpace]
    {mu : Measure OmegaSpace} [IsProbabilityMeasure mu]
    {k l : Type*} [Fintype k] [Fintype l]
    [DecidableEq k] [DecidableEq l]
    {What : ℕ → OmegaSpace → Matrix l l ℝ}
    {Z : ℕ → OmegaSpace → l → ℝ}
    {X : ℕ → OmegaSpace → k → ℝ}
    {e Y : ℕ → OmegaSpace → ℝ}
    {Q : Matrix l k ℝ} {W : Matrix l l ℝ}
    (h : GMMMomentCLTConditions mu
      (fun n omega =>
        sampleQZX (stackRegressors Z n omega)
          (stackRegressors X n omega))
      What Z e Q W)
    (b : k → ℝ)
    (hmodel : ∀ i omega, Y i omega = (X i omega) ⬝ᵥ b + e i omega)
    (hmeas : ∀ n, AEMeasurable
      (fun omega =>
        gmmScaledResidualMomentOrZero
          (stackRegressors X n omega) (stackRegressors Z n omega)
          (stackOutcomes Y n omega) (What n omega)) mu) :
    TendstoInDistribution
      (fun n omega =>
        gmmScaledResidualMomentOrZero
          (stackRegressors X n omega) (stackRegressors Z n omega)
          (stackOutcomes Y n omega) (What n omega))
      atTop
      (fun z : EuclideanSpace ℝ l =>
        gmmResidualMakerStar Q W *ᵥ z.ofLp)
      (fun _ => mu) (multivariateGaussian 0 (scoreCovMat mu Z e)) := by
  exact tendstoInDistribution_of_tendstoInMeasure_sub
    (X := fun n omega =>
      gmmResidualMakerStar
          (sampleQZX (stackRegressors Z n omega)
            (stackRegressors X n omega))
          (What n omega) *ᵥ
        (Real.sqrt (n : ℝ) •
          sampleCrossMoment (stackRegressors Z n omega)
            (stackErrors e n omega)))
    (Y := fun n omega =>
      gmmScaledResidualMomentOrZero
        (stackRegressors X n omega) (stackRegressors Z n omega)
        (stackOutcomes Y n omega) (What n omega))
    (Z := fun z : EuclideanSpace ℝ l =>
      gmmResidualMakerStar Q W *ᵥ z.ofLp)
    (gmmResidualMakerScore_tendstoInDistribution h)
    (gmmScaledResidualMomentOrZero_sub_residualMaker_tendstoInMeasure_zero
      h.toGMMWeightConvergenceConditions b hmodel)
    hmeas

/-- Hansen's efficient-GMM `J` statistic at the reusable score layer. The
input is the scaled residual sample moment and `OmegaHat` estimates its
covariance. -/
noncomputable def gmmJStatOrZero
    {l : Type*} [Fintype l] [DecidableEq l]
    (scaledResidualMoment : l → ℝ) (OmegaHat : Matrix l l ℝ) : ℝ :=
  criterionJStatOrZero scaledResidualMoment OmegaHat

/-- Hansen's efficient two-step GMM overidentification statistic
`n gbar(betaHat)' OmegaHat⁻¹ gbar(betaHat)`, using equation (13.8). -/
noncomputable def gmmUncenteredTwoStepJStatOrZero
    {n k l : Type*} [Fintype n] [Fintype k] [Fintype l]
    [DecidableEq k] [DecidableEq l]
    (X : Matrix n k ℝ) (Z : Matrix n l ℝ) (y : n → ℝ) : ℝ :=
  let OmegaHat := twoSLSOmegaHatStar Z X y
  gmmJStatOrZero
    (gmmScaledResidualMomentOrZero X Z y OmegaHat⁻¹) OmegaHat

/-- Generic feasible-quadratic transfer engine used by Hansen Theorem 13.14.
The observed-row theorem below derives its score and rank-law premises. -/
theorem gmmJStatOrZero_tendstoInDistribution_chiSquared
    {OmegaSpace OmegaLimit : Type*}
    [MeasurableSpace OmegaSpace] [MeasurableSpace OmegaLimit]
    {mu : Measure OmegaSpace} [IsProbabilityMeasure mu]
    {nu : Measure OmegaLimit} [IsProbabilityMeasure nu]
    {l : Type*} [Fintype l] [DecidableEq l]
    {df : ℕ} [Fact (0 < df)]
    {T : ℕ → OmegaSpace → l → ℝ} {G : OmegaLimit → l → ℝ}
    {OmegaHat : ℕ → OmegaSpace → Matrix l l ℝ}
    {Omega : Matrix l l ℝ}
    (hT : TendstoInDistribution T atTop G (fun _ => mu) nu)
    (hOmega_meas : ∀ n, AEStronglyMeasurable (OmegaHat n) mu)
    (hOmega : TendstoInMeasure mu OmegaHat atTop (fun _ => Omega))
    (hOmega_nonsing : IsUnit Omega.det)
    (hLaw : HasLaw
      (fun omega => G omega ⬝ᵥ (Omega⁻¹ *ᵥ G omega))
      (chiSquared df) nu) :
    TendstoInDistribution
      (fun n omega => gmmJStatOrZero (T n omega) (OmegaHat n omega))
      atTop (fun x : ℝ => x) (fun _ => mu) (chiSquared df) := by
  simpa [gmmJStatOrZero] using
    criterionJStatOrZero_tendstoInDistribution_chiSquared_of_limitLaw
      (μ := mu) (ν := nu) (df := df)
      (T := T) (Z := G) (Vhat := OmegaHat) (V := Omega)
      hT hOmega_meas hOmega hOmega_nonsing hLaw

/-- Generic Gaussian factor/symmetric-idempotent specialization of the
feasible-quadratic transfer engine used by Hansen Theorem 13.14. -/
theorem gmmJStatOrZero_tendstoInDistribution_chiSquared_of_factorSymmIdem
    {OmegaSpace : Type*} [MeasurableSpace OmegaSpace]
    {mu : Measure OmegaSpace} [IsProbabilityMeasure mu]
    {l : Type*} [Fintype l] [DecidableEq l]
    {df : ℕ} [Fact (0 < df)]
    {T : ℕ → OmegaSpace → l → ℝ}
    {OmegaHat : ℕ → OmegaSpace → Matrix l l ℝ}
    {Omega B : Matrix l l ℝ}
    (hT : TendstoInDistribution T atTop
      (fun z : EuclideanSpace ℝ l => z.ofLp) (fun _ => mu)
      (multivariateGaussian 0 (B * Bᵀ)))
    (hOmega_meas : ∀ n, AEStronglyMeasurable (OmegaHat n) mu)
    (hOmega : TendstoInMeasure mu OmegaHat atTop (fun _ => Omega))
    (hOmega_posDef : Omega.PosDef)
    (hH : (Bᵀ * Omega⁻¹ * B).IsHermitian)
    (hI : IsIdempotentElem (Bᵀ * Omega⁻¹ * B))
    (hrank : (Bᵀ * Omega⁻¹ * B).rank = df) :
    TendstoInDistribution
      (fun n omega => gmmJStatOrZero (T n omega) (OmegaHat n omega))
      atTop (fun x : ℝ => x) (fun _ => mu) (chiSquared df) := by
  have hLawRaw :=
    hasLaw_multivariateGaussian_zero_quadratic_of_factor_symmIdem
      (B := B) (A := Omega⁻¹) hH hI (by rw [hrank]; exact Fact.out)
  have hLaw : HasLaw
      (fun z : EuclideanSpace ℝ l =>
        z.ofLp ⬝ᵥ (Omega⁻¹ *ᵥ z.ofLp))
      (chiSquared df) (multivariateGaussian 0 (B * Bᵀ)) := by
    simpa [hrank] using hLawRaw
  exact gmmJStatOrZero_tendstoInDistribution_chiSquared
    (mu := mu) (nu := multivariateGaussian 0 (B * Bᵀ))
    (df := df) (T := T)
    (G := fun z : EuclideanSpace ℝ l => z.ofLp)
    (OmegaHat := OmegaHat) (Omega := Omega)
    hT hOmega_meas hOmega
      ((Matrix.isUnit_iff_isUnit_det _).mp hOmega_posDef.isUnit) hLaw

set_option maxHeartbeats 2000000 in
-- The endpoint assembles Assumption 12.2 covariance, score, and rank packages.
/-- **Hansen Theorem 13.14, observed-row form.** Under the literal
observed-row Assumption 12.2 package, the efficient two-step GMM criterion at
the GMM estimator converges to `chiSquared (card l - card k)`. -/
theorem gmmUncenteredTwoStepJStatOrZero_tendstoInDistribution_observedRows
    {OmegaSpace : Type*} [MeasurableSpace OmegaSpace]
    {mu : Measure OmegaSpace} [IsProbabilityMeasure mu]
    {k l : Type*} [Fintype k] [Fintype l]
    [DecidableEq k] [DecidableEq l]
    {Z : ℕ → OmegaSpace → l → ℝ}
    {X : ℕ → OmegaSpace → k → ℝ}
    {e Y : ℕ → OmegaSpace → ℝ}
    {b : k → ℝ}
    [Fact (0 < Fintype.card l - Fintype.card k)]
    (h : TwoSLSObservedIidFourthMomentPositiveCovarianceConditions
      mu Z X e Y b) :
    TendstoInDistribution
      (fun n omega =>
        gmmUncenteredTwoStepJStatOrZero
          (stackRegressors X n omega) (stackRegressors Z n omega)
          (stackOutcomes Y n omega))
      atTop (fun x : ℝ => x) (fun _ => mu)
      (chiSquared (Fintype.card l - Fintype.card k)) := by
  classical
  let hCore := h.toJointIidMixedMomentConditions
  let hIid :=
    hCore.toTwoSLSResidualJointIidFourthMomentPositiveCovarianceConditions
      |>.toIidFourthConditions
  let hGram : TwoSLSGramScoreCLTPositiveCovarianceConditions mu Z X e :=
    hIid.toGramConditions
  let hCov := hCore.toCovarianceMomentConsistencyConditions b h.model
  let Q : Matrix l k ℝ :=
    twoSLSCombinedQZX (popGram mu (twoSLSCombinedRegressors Z X))
  let Omega : Matrix l l ℝ := scoreCovMat mu Z e
  let OmegaHat : ℕ → OmegaSpace → Matrix l l ℝ := fun n omega =>
    twoSLSOmegaHatStar
      (stackRegressors Z n omega) (stackRegressors X n omega)
      (stackOutcomes Y n omega)
  let What : ℕ → OmegaSpace → Matrix l l ℝ := fun n omega =>
    (OmegaHat n omega)⁻¹
  have hOmega_meas : ∀ n, AEStronglyMeasurable (OmegaHat n) mu := by
    intro n
    simpa [OmegaHat] using hCov.omega_meas n
  have hWhat_meas : ∀ n, AEStronglyMeasurable (What n) mu :=
    fun n => aestronglyMeasurable_matrix_inv (hOmega_meas n)
  have hOmega : TendstoInMeasure mu OmegaHat atTop (fun _ => Omega) := by
    simpa [OmegaHat, Omega] using hCov.omega_tendsto
  have hWhat : TendstoInMeasure mu What atTop (fun _ => Omega⁻¹) := by
    simpa [What] using
      tendstoInMeasure_matrix_inv hOmega_meas hOmega
        (fun _ => (Matrix.isUnit_iff_isUnit_det Omega).mp (by
          simpa [Omega] using h.omega_posDef.isUnit))
  let hMoment : GMMMomentCLTConditions mu
      (fun n omega =>
        sampleQZX (stackRegressors Z n omega)
          (stackRegressors X n omega))
      What Z e Q Omega⁻¹ :=
    hGram.toGMMMomentCLTConditions
      What Omega⁻¹ hWhat_meas hWhat h.omega_posDef.inv
  have hY : ∀ i, AEStronglyMeasurable (Y i) mu :=
    fun i => continuous_snd.comp_aestronglyMeasurable
      (h.observed_aestronglyMeasurable i)
  have hT : TendstoInDistribution
      (fun n omega =>
        gmmScaledResidualMomentOrZero
          (stackRegressors X n omega) (stackRegressors Z n omega)
          (stackOutcomes Y n omega) (What n omega))
      atTop
      (fun z : EuclideanSpace ℝ l =>
        gmmResidualMakerStar Q Omega⁻¹ *ᵥ z.ofLp)
      (fun _ => mu) (multivariateGaussian 0 Omega) := by
    simpa [Omega] using
      gmmScaledResidualMomentOrZero_tendstoInDistribution
        hMoment b h.model
        (fun n =>
          (gmmScaledResidualMomentOrZero_aestronglyMeasurable_of_rows
            (mu := mu) (n := n) (Z := Z) (X := X) (Y := Y)
            (What := What n)
            hCore.z_aestronglyMeasurable hCore.x_aestronglyMeasurable hY
            (hWhat_meas n)).aemeasurable)
  let B : Matrix l l ℝ := CFC.sqrt Omega
  have hFactor : Omega = B * Bᵀ := by
    simpa [B] using (cfcSqrt_posDef_factor (by
      simpa [Omega] using h.omega_posDef)).symm
  have hH :
      (twoSLSOveridLimitCriterionPullback Qᵀ Omega Q 1 B).IsHermitian := by
    exact twoSLSOveridLimitCriterionPullback_isHermitian
      (QXZ := Qᵀ) (QZZ := Omega) (QZX := Q) (sigma2 := 1) B (by
        simpa [Omega] using h.omega_posDef)
  have hOmegaSymm : Omegaᵀ = Omega := by
    have hHerm : Omega.IsHermitian := by
      simpa [Omega] using h.omega_posDef.isHermitian
    simpa [Matrix.conjTranspose] using hHerm.eq
  have hOmegaUnit : IsUnit Omega.det :=
    (Matrix.isUnit_iff_isUnit_det Omega).mp (by
      simpa [Omega] using h.omega_posDef.isUnit)
  have hBreadUnit : IsUnit (twoSLSBread Qᵀ Omega Q).det :=
    isUnit_twoSLSBread_det_of_qzz_posDef_rank rfl
      (by simpa [Omega] using h.omega_posDef)
      (by simpa [Q] using h.qzx_rank)
  have hMidem :
      IsIdempotentElem
        (twoSLSOveridPopulationResidualMaker Qᵀ Omega Q) :=
    twoSLSOveridPopulationResidualMaker_idempotent hBreadUnit
  have hMselfQ :
      let M := twoSLSOveridPopulationResidualMaker Qᵀ Omega Q
      M * Omega = Omega * Mᵀ :=
    twoSLSOveridPopulationResidualMaker_weighted_selfAdjoint
      (QXZ := Qᵀ) (QZZ := Omega) (QZX := Q)
      rfl hOmegaSymm hOmegaUnit
  have hI :
      IsIdempotentElem
        (twoSLSOveridLimitCriterionPullback Qᵀ Omega Q 1 B) := by
    simpa [B] using
      twoSLSOveridLimitCriterionPullback_idempotent_of_weightedSelfAdjoint
        (QXZ := Qᵀ) (QZZ := Omega) (QZX := Q) (sigma2 := 1)
        (by simpa [Omega] using h.omega_posDef) hMidem
        (by simpa using hMselfQ)
  have hrank :
      (twoSLSOveridLimitCriterionPullback Qᵀ Omega Q 1 B).rank =
        Fintype.card l - Fintype.card k := by
    simpa [B] using
      twoSLSOveridLimitCriterionPullback_rank_sqrtCov
        (QXZ := Qᵀ) (QZZ := Omega) (QZX := Q) (sigma2 := 1)
        rfl (by simpa [Omega] using h.omega_posDef)
        (by simpa [Q] using h.qzx_rank) zero_lt_one
  have hLawRaw :=
    twoSLSOveridPopulationResidualMaker_quadratic_hasLaw_chiSquared_of_factor_symmIdem
      (μ := mu) (Z := Z) (e := e)
      (QXZ := Qᵀ) (QZZ := Omega) (QZX := Q) (sigma2 := 1)
      (df := Fintype.card l - Fintype.card k) (B := B)
      (by simpa [Omega] using hFactor) hH hI hrank
  have hLaw : HasLaw
      (fun z : EuclideanSpace ℝ l =>
        let g := gmmResidualMakerStar Q Omega⁻¹ *ᵥ z.ofLp
        g ⬝ᵥ (Omega⁻¹ *ᵥ g))
      (chiSquared (Fintype.card l - Fintype.card k))
      (multivariateGaussian 0 Omega) := by
    simpa [gmmResidualMakerStar, gmmLinearizationMatrixStar,
      LinearGMM.influenceMatrixStar, LinearGMM.gram,
      twoSLSOveridPopulationResidualMaker, twoSLSBread,
      Matrix.mul_assoc] using hLawRaw
  simpa [gmmUncenteredTwoStepJStatOrZero, OmegaHat, What] using
    gmmJStatOrZero_tendstoInDistribution_chiSquared
      (mu := mu) (nu := multivariateGaussian 0 Omega)
      (df := Fintype.card l - Fintype.card k)
      (T := fun n omega =>
        gmmScaledResidualMomentOrZero
          (stackRegressors X n omega) (stackRegressors Z n omega)
          (stackOutcomes Y n omega) (What n omega))
      (G := fun z : EuclideanSpace ℝ l =>
        gmmResidualMakerStar Q Omega⁻¹ *ᵥ z.ofLp)
      (OmegaHat := OmegaHat) (Omega := Omega)
      hT hOmega_meas hOmega hOmegaUnit hLaw

/-- Asymptotic-size conclusion in Hansen Theorem 13.14 for the actual
efficient two-step GMM overidentification criterion. -/
theorem
    gmmUncenteredTwoStepJTest_rejectionProb_tendsto_alpha_observedRows
    {OmegaSpace : Type*} [MeasurableSpace OmegaSpace]
    {mu : Measure OmegaSpace} [IsProbabilityMeasure mu]
    {k l : Type*} [Fintype k] [Fintype l]
    [DecidableEq k] [DecidableEq l]
    {Z : ℕ → OmegaSpace → l → ℝ}
    {X : ℕ → OmegaSpace → k → ℝ}
    {e Y : ℕ → OmegaSpace → ℝ}
    {b : k → ℝ}
    [Fact (0 < Fintype.card l - Fintype.card k)]
    {crit : ℝ} {alpha : ℝ≥0∞}
    (hcrit :
      (chiSquared (Fintype.card l - Fintype.card k))
        (Set.Ioi crit) = alpha)
    (h : TwoSLSObservedIidFourthMomentPositiveCovarianceConditions
      mu Z X e Y b) :
    Tendsto
      (fun n => mu {omega |
        crit <
          gmmUncenteredTwoStepJStatOrZero
            (stackRegressors X n omega) (stackRegressors Z n omega)
            (stackOutcomes Y n omega)})
      atTop (nhds alpha) :=
  chiSquaredTest_rejectionProb_tendsto_alpha_of_stat hcrit
    (gmmUncenteredTwoStepJStatOrZero_tendstoInDistribution_observedRows h)

/-- Size form of Hansen Theorem 13.14. -/
theorem gmmJTest_rejectionProb_tendsto_alpha
    {OmegaSpace : Type*} [MeasurableSpace OmegaSpace]
    {mu : Measure OmegaSpace} [IsProbabilityMeasure mu]
    {df : ℕ} [Fact (0 < df)]
    {J : ℕ → OmegaSpace → ℝ} {crit : ℝ} {alpha : ℝ≥0∞}
    (hcrit : (chiSquared df) (Set.Ioi crit) = alpha)
    (hJ : TendstoInDistribution J atTop (fun x : ℝ => x)
      (fun _ => mu) (chiSquared df)) :
    Tendsto (fun n => mu {omega | crit < J n omega}) atTop
      (nhds alpha) :=
  chiSquaredTest_rejectionProb_tendsto_alpha_of_stat hcrit hJ

/-- Moment-space quadratic matrix of the efficient-GMM residual score. -/
noncomputable def gmmResidualCriterionMatrixStar
    {k l : Type*} [Fintype k] [Fintype l]
    [DecidableEq k] [DecidableEq l]
    (Q : Matrix l k ℝ) (W : Matrix l l ℝ) : Matrix l l ℝ :=
  let M := gmmResidualMakerStar Q W
  Mᵀ * W * M

/-- Measurability of the GMM residual-score quadratic matrix. -/
theorem gmmResidualCriterionMatrixStar_aestronglyMeasurable
    {OmegaSpace : Type*} [MeasurableSpace OmegaSpace]
    {mu : Measure OmegaSpace}
    {k l : Type*} [Fintype k] [Fintype l]
    [DecidableEq k] [DecidableEq l]
    {Qhat : OmegaSpace → Matrix l k ℝ}
    {What : OmegaSpace → Matrix l l ℝ}
    (hQ : AEStronglyMeasurable Qhat mu)
    (hW : AEStronglyMeasurable What mu) :
    AEStronglyMeasurable
      (fun omega =>
        gmmResidualCriterionMatrixStar (Qhat omega) (What omega)) mu := by
  let M : OmegaSpace → Matrix l l ℝ := fun omega =>
    gmmResidualMakerStar (Qhat omega) (What omega)
  have hM : AEStronglyMeasurable M mu :=
    gmmResidualMakerStar_aestronglyMeasurable Qhat What hQ hW
  have hMt : AEStronglyMeasurable (fun omega => (M omega)ᵀ) mu :=
    continuous_id.matrix_transpose.comp_aestronglyMeasurable hM
  have hleft : AEStronglyMeasurable
      (fun omega => (M omega)ᵀ * What omega) mu :=
    (Continuous.matrix_mul continuous_fst continuous_snd)
      |>.comp_aestronglyMeasurable (hMt.prodMk hW)
  simpa [gmmResidualCriterionMatrixStar, M, Matrix.mul_assoc] using
    (Continuous.matrix_mul continuous_fst continuous_snd)
      |>.comp_aestronglyMeasurable (hleft.prodMk hM)

set_option maxHeartbeats 1200000 in
-- The matrix CMT passes through a residual maker, transpose, and two products.
/-- The feasible GMM residual-score quadratic matrix converges to its
population counterpart. -/
theorem gmmResidualCriterionMatrixStar_tendstoInMeasure
    {OmegaSpace : Type*} [MeasurableSpace OmegaSpace]
    {mu : Measure OmegaSpace} [IsProbabilityMeasure mu]
    {k l : Type*} [Fintype k] [Fintype l]
    [DecidableEq k] [DecidableEq l]
    {Qhat : ℕ → OmegaSpace → Matrix l k ℝ}
    {What : ℕ → OmegaSpace → Matrix l l ℝ}
    {Q : Matrix l k ℝ} {W : Matrix l l ℝ}
    (h : GMMWeightConvergenceConditions mu Qhat What Q W) :
    TendstoInMeasure mu
      (fun n omega =>
        gmmResidualCriterionMatrixStar (Qhat n omega) (What n omega))
      atTop (fun _ => gmmResidualCriterionMatrixStar Q W) := by
  let Mhat : ℕ → OmegaSpace → Matrix l l ℝ := fun n omega =>
    gmmResidualMakerStar (Qhat n omega) (What n omega)
  let M : Matrix l l ℝ := gmmResidualMakerStar Q W
  have hM_meas : ∀ n, AEStronglyMeasurable (Mhat n) mu :=
    fun n => gmmResidualMakerStar_aestronglyMeasurable
      (Qhat n) (What n) (h.q_meas n) (h.weight_meas n)
  have hM : TendstoInMeasure mu Mhat atTop (fun _ => M) := by
    simpa [Mhat, M] using gmmResidualMakerStar_tendstoInMeasure h
  have hMt_meas : ∀ n,
      AEStronglyMeasurable (fun omega => (Mhat n omega)ᵀ) mu :=
    fun n => continuous_id.matrix_transpose.comp_aestronglyMeasurable
      (hM_meas n)
  have hMt : TendstoInMeasure mu (fun n omega => (Mhat n omega)ᵀ)
      atTop (fun _ => Mᵀ) := by
    simpa using tendstoInMeasure_continuous_comp hM_meas hM
      continuous_id.matrix_transpose
  have hleft_meas : ∀ n, AEStronglyMeasurable
      (fun omega => (Mhat n omega)ᵀ * What n omega) mu :=
    fun n => (Continuous.matrix_mul continuous_fst continuous_snd)
      |>.comp_aestronglyMeasurable ((hMt_meas n).prodMk (h.weight_meas n))
  have hleft : TendstoInMeasure mu
      (fun n omega => (Mhat n omega)ᵀ * What n omega)
      atTop (fun _ => Mᵀ * W) :=
    tendstoInMeasure_matrix_mul_rect hMt_meas h.weight_meas hMt h.weight_tendsto
  simpa [gmmResidualCriterionMatrixStar, Mhat, M, Matrix.mul_assoc] using
    tendstoInMeasure_matrix_mul_rect hleft_meas hM_meas hleft hM

/-- Quadratic matrix for the full-minus-maintained efficient-GMM criteria.
The maintained matrix is embedded in the left instrument block. -/
noncomputable def gmmSubsetCriterionMatrixStar
    {k la lb : Type*} [Fintype k] [Fintype la] [Fintype lb]
    [DecidableEq k] [DecidableEq la] [DecidableEq lb]
    (Qfull : Matrix (la ⊕ lb) k ℝ)
    (Wfull : Matrix (la ⊕ lb) (la ⊕ lb) ℝ)
    (Qmaintained : Matrix la k ℝ) (Wmaintained : Matrix la la ℝ) :
    Matrix (la ⊕ lb) (la ⊕ lb) ℝ :=
  gmmResidualCriterionMatrixStar Qfull Wfull -
    Matrix.fromBlocks
      (gmmResidualCriterionMatrixStar Qmaintained Wmaintained)
      0 0 0

/-- Population quadratic matrix in Hansen Theorem 13.15. -/
noncomputable def gmmSubsetLimitCriterionMatrix
    {k la lb : Type*} [Fintype k] [Fintype la] [Fintype lb]
    [DecidableEq k] [DecidableEq la] [DecidableEq lb]
    (Q : Matrix (la ⊕ lb) k ℝ)
    (Omega : Matrix (la ⊕ lb) (la ⊕ lb) ℝ) :
    Matrix (la ⊕ lb) (la ⊕ lb) ℝ :=
  gmmSubsetCriterionMatrixStar Q Omega⁻¹
    (Q.submatrix Sum.inl id)
    (Omega.submatrix Sum.inl Sum.inl)⁻¹

/-- Measurability of the full-minus-maintained GMM criterion matrix. -/
theorem gmmSubsetCriterionMatrixStar_aestronglyMeasurable
    {OmegaSpace : Type*} [MeasurableSpace OmegaSpace]
    {mu : Measure OmegaSpace}
    {k la lb : Type*} [Fintype k] [Fintype la] [Fintype lb]
    [DecidableEq k] [DecidableEq la] [DecidableEq lb]
    {Qfull : OmegaSpace → Matrix (la ⊕ lb) k ℝ}
    {Wfull : OmegaSpace → Matrix (la ⊕ lb) (la ⊕ lb) ℝ}
    {Qmaintained : OmegaSpace → Matrix la k ℝ}
    {Wmaintained : OmegaSpace → Matrix la la ℝ}
    (hQfull : AEStronglyMeasurable Qfull mu)
    (hWfull : AEStronglyMeasurable Wfull mu)
    (hQmaintained : AEStronglyMeasurable Qmaintained mu)
    (hWmaintained : AEStronglyMeasurable Wmaintained mu) :
    AEStronglyMeasurable
      (fun omega =>
        gmmSubsetCriterionMatrixStar
          (Qfull omega) (Wfull omega)
          (Qmaintained omega) (Wmaintained omega)) mu := by
  have hfull := gmmResidualCriterionMatrixStar_aestronglyMeasurable
    hQfull hWfull
  have hmaintained := gmmResidualCriterionMatrixStar_aestronglyMeasurable
    hQmaintained hWmaintained
  have hlift : AEStronglyMeasurable
      (fun omega : OmegaSpace =>
        Matrix.fromBlocks
          (gmmResidualCriterionMatrixStar
            (Qmaintained omega) (Wmaintained omega))
          (0 : Matrix la lb ℝ) (0 : Matrix lb la ℝ)
          (0 : Matrix lb lb ℝ)) mu := by
    fun_prop
  exact hfull.sub hlift

set_option maxHeartbeats 1200000 in
-- Two residual-score matrix CMT chains are assembled into one block difference.
/-- Joint convergence of the full-minus-maintained GMM criterion matrix. -/
theorem gmmSubsetCriterionMatrixStar_tendstoInMeasure
    {OmegaSpace : Type*} [MeasurableSpace OmegaSpace]
    {mu : Measure OmegaSpace} [IsProbabilityMeasure mu]
    {k la lb : Type*} [Fintype k] [Fintype la] [Fintype lb]
    [DecidableEq k] [DecidableEq la] [DecidableEq lb]
    {QfullHat : ℕ → OmegaSpace → Matrix (la ⊕ lb) k ℝ}
    {WfullHat : ℕ → OmegaSpace → Matrix (la ⊕ lb) (la ⊕ lb) ℝ}
    {QmaintainedHat : ℕ → OmegaSpace → Matrix la k ℝ}
    {WmaintainedHat : ℕ → OmegaSpace → Matrix la la ℝ}
    {Qfull : Matrix (la ⊕ lb) k ℝ}
    {Wfull : Matrix (la ⊕ lb) (la ⊕ lb) ℝ}
    {Qmaintained : Matrix la k ℝ}
    {Wmaintained : Matrix la la ℝ}
    (hfull : GMMWeightConvergenceConditions
      mu QfullHat WfullHat Qfull Wfull)
    (hmaintained : GMMWeightConvergenceConditions
      mu QmaintainedHat WmaintainedHat Qmaintained Wmaintained) :
    TendstoInMeasure mu
      (fun n omega =>
        gmmSubsetCriterionMatrixStar
          (QfullHat n omega) (WfullHat n omega)
          (QmaintainedHat n omega) (WmaintainedHat n omega))
      atTop
      (fun _ =>
        gmmSubsetCriterionMatrixStar
          Qfull Wfull Qmaintained Wmaintained) := by
  let Afull : ℕ → OmegaSpace → Matrix (la ⊕ lb) (la ⊕ lb) ℝ :=
    fun n omega =>
      gmmResidualCriterionMatrixStar
        (QfullHat n omega) (WfullHat n omega)
  let Amaintained : ℕ → OmegaSpace → Matrix la la ℝ :=
    fun n omega =>
      gmmResidualCriterionMatrixStar
        (QmaintainedHat n omega) (WmaintainedHat n omega)
  have hAfull_meas : ∀ n, AEStronglyMeasurable (Afull n) mu :=
    fun n => gmmResidualCriterionMatrixStar_aestronglyMeasurable
      (hfull.q_meas n) (hfull.weight_meas n)
  have hAmaintained_meas : ∀ n,
      AEStronglyMeasurable (Amaintained n) mu :=
    fun n => gmmResidualCriterionMatrixStar_aestronglyMeasurable
      (hmaintained.q_meas n) (hmaintained.weight_meas n)
  have hAfull : TendstoInMeasure mu Afull atTop
      (fun _ => gmmResidualCriterionMatrixStar Qfull Wfull) := by
    simpa [Afull] using gmmResidualCriterionMatrixStar_tendstoInMeasure hfull
  have hAmaintained : TendstoInMeasure mu Amaintained atTop
      (fun _ => gmmResidualCriterionMatrixStar Qmaintained Wmaintained) := by
    simpa [Amaintained] using
      gmmResidualCriterionMatrixStar_tendstoInMeasure hmaintained
  let lift : Matrix la la ℝ → Matrix (la ⊕ lb) (la ⊕ lb) ℝ :=
    fun A => Matrix.fromBlocks A 0 0 0
  have hlift_cont : Continuous lift := by
    fun_prop
  have hlift_meas : ∀ n,
      AEStronglyMeasurable (fun omega => lift (Amaintained n omega)) mu :=
    fun n => hlift_cont.comp_aestronglyMeasurable (hAmaintained_meas n)
  have hlift : TendstoInMeasure mu
      (fun n omega => lift (Amaintained n omega)) atTop
      (fun _ => lift (gmmResidualCriterionMatrixStar
        Qmaintained Wmaintained)) :=
    tendstoInMeasure_continuous_comp hAmaintained_meas hAmaintained hlift_cont
  have hsub_cont : Continuous
      (fun p : Matrix (la ⊕ lb) (la ⊕ lb) ℝ ×
          Matrix (la ⊕ lb) (la ⊕ lb) ℝ => p.1 - p.2) :=
    continuous_fst.sub continuous_snd
  have hpair : TendstoInMeasure mu
      (fun n omega =>
        (Afull n omega, lift (Amaintained n omega))) atTop
      (fun _ =>
        (gmmResidualCriterionMatrixStar Qfull Wfull,
          lift (gmmResidualCriterionMatrixStar
            Qmaintained Wmaintained))) :=
    tendstoInMeasure_prodMk hAfull hlift
  simpa [gmmSubsetCriterionMatrixStar, Afull, Amaintained, lift] using
    tendstoInMeasure_continuous_comp
      (fun n => (hAfull_meas n).prodMk (hlift_meas n))
      hpair hsub_cont

private noncomputable def sumLeftSelector
    {la lb : Type*} [Fintype la] [Fintype lb]
    [DecidableEq la] [DecidableEq lb] :
    Matrix la (la ⊕ lb) ℝ :=
  (1 : Matrix (la ⊕ lb) (la ⊕ lb) ℝ).submatrix Sum.inl id

private theorem sumLeftSelector_mul
    {la lb j : Type*} [Fintype la] [Fintype lb]
    [DecidableEq la] [DecidableEq lb]
    (A : Matrix (la ⊕ lb) j ℝ) :
    sumLeftSelector (la := la) (lb := lb) * A =
      A.submatrix Sum.inl id := by
  classical
  ext a j
  simp [sumLeftSelector, Matrix.mul_apply, Matrix.one_apply]

private theorem sumLeftSelector_mulVec
    {la lb : Type*} [Fintype la] [Fintype lb]
    [DecidableEq la] [DecidableEq lb]
    (x : (la ⊕ lb) → ℝ) :
    sumLeftSelector (la := la) (lb := lb) *ᵥ x =
      x ∘ Sum.inl := by
  classical
  funext a
  simp [sumLeftSelector, Matrix.mulVec, dotProduct, Matrix.one_apply]

private theorem sumLeftSelector_mul_transpose
    {la lb : Type*} [Fintype la] [Fintype lb]
    [DecidableEq la] [DecidableEq lb]
    (A : Matrix (la ⊕ lb) (la ⊕ lb) ℝ) :
    sumLeftSelector (la := la) (lb := lb) * A *
        (sumLeftSelector (la := la) (lb := lb))ᵀ =
      A.submatrix Sum.inl Sum.inl := by
  classical
  ext a b
  simp [sumLeftSelector, Matrix.mul_apply, Matrix.one_apply]

private theorem sumLeftSelector_transpose_mul_mul
    {la lb : Type*} [Fintype la] [Fintype lb]
    [DecidableEq la] [DecidableEq lb]
    (A : Matrix la la ℝ) :
    (sumLeftSelector (la := la) (lb := lb))ᵀ * A *
        sumLeftSelector (la := la) (lb := lb) =
      Matrix.fromBlocks A 0 0 0 := by
  classical
  ext i j
  cases i <;> cases j <;>
    simp [sumLeftSelector, Matrix.mul_apply, Matrix.one_apply]

private theorem gmmResidualMakerStar_eq_twoSLS
    {k l : Type*} [Fintype k] [Fintype l]
    [DecidableEq k] [DecidableEq l]
    (Q : Matrix l k ℝ) (V : Matrix l l ℝ) :
    gmmResidualMakerStar Q V⁻¹ =
      twoSLSOveridPopulationResidualMaker Qᵀ V Q := by
  simp [gmmResidualMakerStar, gmmLinearizationMatrixStar,
    LinearGMM.influenceMatrixStar, LinearGMM.gram,
    twoSLSOveridPopulationResidualMaker, twoSLSBread,
    Matrix.mul_assoc]

private theorem gmmResidualCriterionMatrixStar_eq_twoSLS
    {k l : Type*} [Fintype k] [Fintype l]
    [DecidableEq k] [DecidableEq l]
    (Q : Matrix l k ℝ) (V : Matrix l l ℝ) :
    gmmResidualCriterionMatrixStar Q V⁻¹ =
      twoSLSOveridLimitCriterionMatrix Qᵀ V Q 1 := by
  simp [gmmResidualCriterionMatrixStar,
    gmmResidualMakerStar_eq_twoSLS,
    twoSLSOveridLimitCriterionMatrix]

private theorem gmmResidualCriterionMatrixStar_eq_inv_mul_residualMaker
    {k l : Type*} [Fintype k] [Fintype l]
    [DecidableEq k] [DecidableEq l]
    (Q : Matrix l k ℝ) (V : Matrix l l ℝ)
    (hV : V.PosDef) (hQ : Function.Injective Q.mulVec) :
    gmmResidualCriterionMatrixStar Q V⁻¹ =
      V⁻¹ * gmmResidualMakerStar Q V⁻¹ := by
  let M := twoSLSOveridPopulationResidualMaker Qᵀ V Q
  have hVsymm : Vᵀ = V := by
    have hHerm : V.IsHermitian := hV.isHermitian
    simpa [Matrix.conjTranspose] using hHerm.eq
  have hVunit : IsUnit V.det :=
    (Matrix.isUnit_iff_isUnit_det V).mp hV.isUnit
  have hBread : IsUnit (twoSLSBread Qᵀ V Q).det :=
    isUnit_twoSLSBread_det_of_qzz_posDef_rank rfl hV hQ
  have hMidem : IsIdempotentElem M := by
    simpa [M] using
      twoSLSOveridPopulationResidualMaker_idempotent hBread
  have hMself : M * V = V * Mᵀ := by
    simpa [M] using
      twoSLSOveridPopulationResidualMaker_weighted_selfAdjoint
        (QXZ := Qᵀ) (QZZ := V) (QZX := Q)
        rfl hVsymm hVunit
  have hMtVinv : Mᵀ * V⁻¹ = V⁻¹ * M := by
    calc
      Mᵀ * V⁻¹ = (1 : Matrix l l ℝ) * (Mᵀ * V⁻¹) := by simp
      _ = (V⁻¹ * V) * (Mᵀ * V⁻¹) := by
        rw [Matrix.nonsing_inv_mul V hVunit]
      _ = V⁻¹ * (V * Mᵀ) * V⁻¹ := by
        simp [Matrix.mul_assoc]
      _ = V⁻¹ * (M * V) * V⁻¹ := by rw [← hMself]
      _ = V⁻¹ * M * (V * V⁻¹) := by
        simp [Matrix.mul_assoc]
      _ = V⁻¹ * M * 1 := by
        rw [Matrix.mul_nonsing_inv V hVunit]
      _ = V⁻¹ * M := by simp
  have hMM : M * M = M := by
    simpa [IsIdempotentElem, M] using hMidem
  rw [gmmResidualCriterionMatrixStar_eq_twoSLS]
  dsimp [twoSLSOveridLimitCriterionMatrix]
  rw [show twoSLSOveridPopulationResidualMaker Qᵀ V Q = M by rfl]
  simp only [one_smul]
  rw [hMtVinv, Matrix.mul_assoc, hMM]
  rw [gmmResidualMakerStar_eq_twoSLS]

private theorem gmmResidualMakerStar_mul_derivative_eq_zero
    {k l : Type*} [Fintype k] [Fintype l]
    [DecidableEq k] [DecidableEq l]
    (Q : Matrix l k ℝ) (V : Matrix l l ℝ)
    (hV : V.PosDef) (hQ : Function.Injective Q.mulVec) :
    gmmResidualMakerStar Q V⁻¹ * Q = 0 := by
  let G : Matrix k k ℝ := LinearGMM.gram Q V⁻¹
  have hG : IsUnit G.det := by
    simpa [G] using
      LinearGMM.gram_det_isUnit_of_posDef_rank Q V⁻¹ hV.inv hQ
  have hAQ : gmmLinearizationMatrixStar Q V⁻¹ * Q = 1 := by
    calc
      gmmLinearizationMatrixStar Q V⁻¹ * Q =
          G⁻¹ * (Qᵀ * V⁻¹ * Q) := by
            simp [gmmLinearizationMatrixStar,
              LinearGMM.influenceMatrixStar, G, Matrix.mul_assoc]
      _ = G⁻¹ * G := by rfl
      _ = 1 := Matrix.nonsing_inv_mul G hG
  simp [gmmResidualMakerStar, Matrix.sub_mul, Matrix.mul_assoc, hAQ]

private theorem gmmResidualMakerStar_idempotent
    {k l : Type*} [Fintype k] [Fintype l]
    [DecidableEq k] [DecidableEq l]
    (Q : Matrix l k ℝ) (V : Matrix l l ℝ)
    (hV : V.PosDef) (hQ : Function.Injective Q.mulVec) :
    IsIdempotentElem (gmmResidualMakerStar Q V⁻¹) := by
  rw [gmmResidualMakerStar_eq_twoSLS]
  exact twoSLSOveridPopulationResidualMaker_idempotent
    (isUnit_twoSLSBread_det_of_qzz_posDef_rank rfl hV hQ)

private theorem gmmResidualMakerStar_trace
    {k l : Type*} [Fintype k] [Fintype l]
    [DecidableEq k] [DecidableEq l]
    (Q : Matrix l k ℝ) (V : Matrix l l ℝ)
    (hV : V.PosDef) (hQ : Function.Injective Q.mulVec) :
    Matrix.trace (gmmResidualMakerStar Q V⁻¹) =
      (Fintype.card l : ℝ) - Fintype.card k := by
  rw [gmmResidualMakerStar_eq_twoSLS]
  exact twoSLSOveridPopulationResidualMaker_trace
    (isUnit_twoSLSBread_det_of_qzz_posDef_rank rfl hV hQ)

private theorem gmmResidualCriterionMatrixStar_isHermitian
    {k l : Type*} [Fintype k] [Fintype l]
    [DecidableEq k] [DecidableEq l]
    (Q : Matrix l k ℝ) (V : Matrix l l ℝ)
    (hV : V.PosDef) :
    (gmmResidualCriterionMatrixStar Q V⁻¹).IsHermitian := by
  let M := gmmResidualMakerStar Q V⁻¹
  simpa [gmmResidualCriterionMatrixStar, M,
    Matrix.conjTranspose_eq_transpose_of_trivial] using
    Matrix.isHermitian_conjTranspose_mul_mul M hV.inv.isHermitian

private theorem gmmResidualCriterionMatrixStar_mul_cov_mul_self
    {k l : Type*} [Fintype k] [Fintype l]
    [DecidableEq k] [DecidableEq l]
    (Q : Matrix l k ℝ) (V : Matrix l l ℝ)
    (hV : V.PosDef) (hQ : Function.Injective Q.mulVec) :
    gmmResidualCriterionMatrixStar Q V⁻¹ * V *
        gmmResidualCriterionMatrixStar Q V⁻¹ =
      gmmResidualCriterionMatrixStar Q V⁻¹ := by
  let M := gmmResidualMakerStar Q V⁻¹
  have hVunit : IsUnit V.det :=
    (Matrix.isUnit_iff_isUnit_det V).mp hV.isUnit
  have hMM : M * M = M := by
    simpa [IsIdempotentElem, M] using
      gmmResidualMakerStar_idempotent Q V hV hQ
  rw [gmmResidualCriterionMatrixStar_eq_inv_mul_residualMaker Q V hV hQ]
  change (V⁻¹ * M) * V * (V⁻¹ * M) = V⁻¹ * M
  calc
    (V⁻¹ * M) * V * (V⁻¹ * M) =
        V⁻¹ * M * (V * V⁻¹) * M := by
          simp [Matrix.mul_assoc]
    _ = V⁻¹ * M * (1 : Matrix l l ℝ) * M := by
      rw [Matrix.mul_nonsing_inv V hVunit]
    _ = V⁻¹ * (M * M) := by simp [Matrix.mul_assoc]
    _ = V⁻¹ * M := by rw [hMM]

private theorem gmmResidualCriterionMatrixStar_trace_mul_cov
    {k l : Type*} [Fintype k] [Fintype l]
    [DecidableEq k] [DecidableEq l]
    (Q : Matrix l k ℝ) (V : Matrix l l ℝ)
    (hV : V.PosDef) (hQ : Function.Injective Q.mulVec) :
    Matrix.trace (gmmResidualCriterionMatrixStar Q V⁻¹ * V) =
      (Fintype.card l : ℝ) - Fintype.card k := by
  have hVunit : IsUnit V.det :=
    (Matrix.isUnit_iff_isUnit_det V).mp hV.isUnit
  rw [gmmResidualCriterionMatrixStar_eq_inv_mul_residualMaker Q V hV hQ]
  calc
    Matrix.trace (V⁻¹ * gmmResidualMakerStar Q V⁻¹ * V) =
        Matrix.trace (V * V⁻¹ * gmmResidualMakerStar Q V⁻¹) := by
          rw [Matrix.trace_mul_cycle]
    _ = Matrix.trace (gmmResidualMakerStar Q V⁻¹) := by
      rw [Matrix.mul_nonsing_inv V hVunit]
      simp
    _ = (Fintype.card l : ℝ) - Fintype.card k :=
      gmmResidualMakerStar_trace Q V hV hQ

private theorem gmmResidualCriterionMatrixStar_mul_derivative_eq_zero
    {k l : Type*} [Fintype k] [Fintype l]
    [DecidableEq k] [DecidableEq l]
    (Q : Matrix l k ℝ) (V : Matrix l l ℝ)
    (hV : V.PosDef) (hQ : Function.Injective Q.mulVec) :
    gmmResidualCriterionMatrixStar Q V⁻¹ * Q = 0 := by
  rw [gmmResidualCriterionMatrixStar_eq_inv_mul_residualMaker Q V hV hQ]
  rw [Matrix.mul_assoc,
    gmmResidualMakerStar_mul_derivative_eq_zero Q V hV hQ]
  simp

private theorem gmmResidualCriterionMatrixStar_mul_cov_eq_transpose_residualMaker
    {k l : Type*} [Fintype k] [Fintype l]
    [DecidableEq k] [DecidableEq l]
    (Q : Matrix l k ℝ) (V : Matrix l l ℝ)
    (hV : V.PosDef) (hQ : Function.Injective Q.mulVec) :
    gmmResidualCriterionMatrixStar Q V⁻¹ * V =
      (gmmResidualMakerStar Q V⁻¹)ᵀ := by
  let M := gmmResidualMakerStar Q V⁻¹
  have hVunit : IsUnit V.det :=
    (Matrix.isUnit_iff_isUnit_det V).mp hV.isUnit
  have hVsymm : Vᵀ = V := by
    have hHerm : V.IsHermitian := hV.isHermitian
    simpa [Matrix.conjTranspose] using hHerm.eq
  have hMself : M * V = V * Mᵀ := by
    rw [show M = twoSLSOveridPopulationResidualMaker Qᵀ V Q by
      simpa [M] using gmmResidualMakerStar_eq_twoSLS Q V]
    exact twoSLSOveridPopulationResidualMaker_weighted_selfAdjoint
      (QXZ := Qᵀ) (QZZ := V) (QZX := Q)
      rfl hVsymm hVunit
  rw [gmmResidualCriterionMatrixStar_eq_inv_mul_residualMaker Q V hV hQ]
  change (V⁻¹ * M) * V = Mᵀ
  calc
    (V⁻¹ * M) * V = V⁻¹ * (M * V) := by
      rw [Matrix.mul_assoc]
    _ = V⁻¹ * (V * Mᵀ) := by rw [hMself]
    _ = (V⁻¹ * V) * Mᵀ := by rw [Matrix.mul_assoc]
    _ = (1 : Matrix l l ℝ) * Mᵀ := by
      rw [Matrix.nonsing_inv_mul V hVunit]
    _ = Mᵀ := by simp

private theorem posDef_submatrix_sum_inl_local
    {a b : Type*}
    {M : Matrix (a ⊕ b) (a ⊕ b) ℝ} (hM : M.PosDef) :
    (M.submatrix Sum.inl Sum.inl).PosDef := by
  refine ⟨hM.isHermitian.submatrix Sum.inl, ?_⟩
  intro x hx
  let y := x.mapDomain (Sum.inl : a → a ⊕ b)
  have hy : y ≠ 0 :=
    (Finsupp.mapDomain_injective Sum.inl_injective).ne hx
  simpa [y, Finsupp.sum_mapDomain_index, add_mul, mul_add] using hM.2 hy

private theorem gmmSubsetCriterionMatrixStar_quadratic
    {k la lb : Type*} [Fintype k] [Fintype la] [Fintype lb]
    [DecidableEq k] [DecidableEq la] [DecidableEq lb]
    (Qfull : Matrix (la ⊕ lb) k ℝ)
    (Wfull : Matrix (la ⊕ lb) (la ⊕ lb) ℝ)
    (Qmaintained : Matrix la k ℝ)
    (Wmaintained : Matrix la la ℝ)
    (s : (la ⊕ lb) → ℝ) :
    s ⬝ᵥ
        (gmmSubsetCriterionMatrixStar
          Qfull Wfull Qmaintained Wmaintained *ᵥ s) =
      s ⬝ᵥ
          (gmmResidualCriterionMatrixStar Qfull Wfull *ᵥ s) -
        (s ∘ Sum.inl) ⬝ᵥ
          (gmmResidualCriterionMatrixStar
            Qmaintained Wmaintained *ᵥ (s ∘ Sum.inl)) := by
  let L : Matrix la (la ⊕ lb) ℝ :=
    sumLeftSelector (la := la) (lb := lb)
  let C : Matrix la la ℝ :=
    gmmResidualCriterionMatrixStar Qmaintained Wmaintained
  have hblock : Matrix.fromBlocks C 0 0 0 = Lᵀ * C * L := by
    simpa [L] using
      (sumLeftSelector_transpose_mul_mul
        (la := la) (lb := lb) C).symm
  have hLs : L *ᵥ s = s ∘ Sum.inl := by
    simpa [L] using sumLeftSelector_mulVec (la := la) (lb := lb) s
  have hquad :
      s ⬝ᵥ ((Lᵀ * C * L) *ᵥ s) =
        (s ∘ Sum.inl) ⬝ᵥ (C *ᵥ (s ∘ Sum.inl)) := by
    rw [← hLs]
    exact
      (quadraticForm_mulVec_eq_pullback_rect
        (B := L) (A := C) (x := s)).symm
  rw [gmmSubsetCriterionMatrixStar, Matrix.sub_mulVec, dotProduct_sub]
  rw [show
    Matrix.fromBlocks
        (gmmResidualCriterionMatrixStar Qmaintained Wmaintained)
        0 0 0 = Lᵀ * C * L by simpa [C] using hblock]
  rw [hquad]

private theorem gmmJStatOrZero_aestronglyMeasurable
    {OmegaSpace l : Type*} [MeasurableSpace OmegaSpace]
    {mu : Measure OmegaSpace} [Fintype l] [DecidableEq l]
    {T : OmegaSpace → l → ℝ}
    {OmegaHat : OmegaSpace → Matrix l l ℝ}
    (hT : AEStronglyMeasurable T mu)
    (hOmega : AEStronglyMeasurable OmegaHat mu) :
    AEStronglyMeasurable
      (fun omega => gmmJStatOrZero (T omega) (OmegaHat omega)) mu := by
  have hInv : AEStronglyMeasurable
      (fun omega => (OmegaHat omega)⁻¹) mu :=
    aestronglyMeasurable_matrix_inv hOmega
  have hMul : AEStronglyMeasurable
      (fun omega => (OmegaHat omega)⁻¹ *ᵥ T omega) mu :=
    (Continuous.matrix_mulVec continuous_fst continuous_snd)
      |>.comp_aestronglyMeasurable (hInv.prodMk hT)
  simpa [gmmJStatOrZero, criterionJStatOrZero] using
    (Continuous.dotProduct continuous_fst continuous_snd)
      |>.comp_aestronglyMeasurable (hT.prodMk hMul)

private theorem
    gmmUncenteredTwoStepJStatOrZero_linear_model_eq_scoreCriterionMatrix_of_isUnit
    {n k l : Type*} [Fintype n] [Fintype k] [Fintype l]
    [DecidableEq k] [DecidableEq l] [Nonempty n]
    (X : Matrix n k ℝ) (Z : Matrix n l ℝ)
    (b : k → ℝ) (e : n → ℝ)
    (hunit : IsUnit
      (gmmPopulationGram (sampleQZX Z X)
        (twoSLSOmegaHatStar Z X (X *ᵥ b + e))⁻¹).det) :
    gmmUncenteredTwoStepJStatOrZero X Z (X *ᵥ b + e) =
      let score :=
        Real.sqrt (Fintype.card n : ℝ) • sampleCrossMoment Z e
      score ⬝ᵥ
        (gmmResidualCriterionMatrixStar
          (sampleQZX Z X)
          (twoSLSOmegaHatStar Z X (X *ᵥ b + e))⁻¹ *ᵥ score) := by
  let OmegaHat := twoSLSOmegaHatStar Z X (X *ᵥ b + e)
  let score :=
    Real.sqrt (Fintype.card n : ℝ) • sampleCrossMoment Z e
  have hres :
      gmmScaledResidualMomentOrZero X Z (X *ᵥ b + e) OmegaHat⁻¹ =
        gmmResidualMakerStar (sampleQZX Z X) OmegaHat⁻¹ *ᵥ score := by
    simpa [OmegaHat, score] using
      gmmScaledResidualMomentOrZero_linear_model_eq_residualMakerStar
        X Z b e OmegaHat⁻¹ (by simpa [OmegaHat] using hunit)
  rw [gmmUncenteredTwoStepJStatOrZero, gmmJStatOrZero,
    criterionJStatOrZero]
  change
    gmmScaledResidualMomentOrZero X Z (X *ᵥ b + e) OmegaHat⁻¹ ⬝ᵥ
        (OmegaHat⁻¹ *ᵥ
          gmmScaledResidualMomentOrZero X Z (X *ᵥ b + e) OmegaHat⁻¹) =
      score ⬝ᵥ
        (gmmResidualCriterionMatrixStar
          (sampleQZX Z X) OmegaHat⁻¹ *ᵥ score)
  rw [hres]
  simpa [gmmResidualCriterionMatrixStar] using
    quadraticForm_mulVec_eq_pullback_rect
      (gmmResidualMakerStar (sampleQZX Z X) OmegaHat⁻¹)
      OmegaHat⁻¹ score

set_option maxHeartbeats 1200000 in
-- The singular-event bridge expands both GMM criteria and the score quadratic.
private theorem gmmUncenteredTwoStepJStatOrZero_sub_scoreCriterion_tendstoInMeasure_zero
    {OmegaSpace : Type*} [MeasurableSpace OmegaSpace]
    {mu : Measure OmegaSpace} [IsProbabilityMeasure mu]
    {k l : Type*} [Fintype k] [Fintype l]
    [DecidableEq k] [DecidableEq l]
    {Z : ℕ → OmegaSpace → l → ℝ}
    {X : ℕ → OmegaSpace → k → ℝ}
    {e Y : ℕ → OmegaSpace → ℝ}
    {Q : Matrix l k ℝ} {W : Matrix l l ℝ}
    (h : GMMWeightConvergenceConditions mu
      (fun n omega =>
        sampleQZX (stackRegressors Z n omega)
          (stackRegressors X n omega))
      (fun n omega =>
        (twoSLSOmegaHatStar
          (stackRegressors Z n omega) (stackRegressors X n omega)
          (stackOutcomes Y n omega))⁻¹)
      Q W)
    (b : k → ℝ)
    (hmodel : ∀ i omega, Y i omega = (X i omega) ⬝ᵥ b + e i omega) :
    TendstoInMeasure mu
      (fun n omega =>
        gmmUncenteredTwoStepJStatOrZero
            (stackRegressors X n omega) (stackRegressors Z n omega)
            (stackOutcomes Y n omega) -
          let score :=
            Real.sqrt (n : ℝ) •
              sampleCrossMoment (stackRegressors Z n omega)
                (stackErrors e n omega)
          score ⬝ᵥ
            (gmmResidualCriterionMatrixStar
              (sampleQZX (stackRegressors Z n omega)
                (stackRegressors X n omega))
              (twoSLSOmegaHatStar
                (stackRegressors Z n omega) (stackRegressors X n omega)
                (stackOutcomes Y n omega))⁻¹ *ᵥ score))
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
  have hdiff :
      gmmUncenteredTwoStepJStatOrZero
          (stackRegressors X n omega) (stackRegressors Z n omega)
          (stackOutcomes Y n omega) -
        (let score :=
          Real.sqrt (n : ℝ) •
            sampleCrossMoment (stackRegressors Z n omega)
              (stackErrors e n omega)
         score ⬝ᵥ
          (gmmResidualCriterionMatrixStar
            (sampleQZX (stackRegressors Z n omega)
              (stackRegressors X n omega))
            (twoSLSOmegaHatStar
              (stackRegressors Z n omega) (stackRegressors X n omega)
              (stackOutcomes Y n omega))⁻¹ *ᵥ score)) = 0 := by
    have hgram' := hgram
    rw [hY] at hgram'
    rw [hY]
    exact sub_eq_zero.mpr
      (by
        simpa using
          gmmUncenteredTwoStepJStatOrZero_linear_model_eq_scoreCriterionMatrix_of_isUnit
            (stackRegressors X n omega) (stackRegressors Z n omega)
            b (stackErrors e n omega) hgram')
  change epsilon ≤ edist
    (gmmUncenteredTwoStepJStatOrZero
        (stackRegressors X n omega) (stackRegressors Z n omega)
        (stackOutcomes Y n omega) -
      (let score :=
        Real.sqrt (n : ℝ) •
          sampleCrossMoment (stackRegressors Z n omega)
            (stackErrors e n omega)
       score ⬝ᵥ
        (gmmResidualCriterionMatrixStar
          (sampleQZX (stackRegressors Z n omega)
            (stackRegressors X n omega))
          (twoSLSOmegaHatStar
            (stackRegressors Z n omega) (stackRegressors X n omega)
            (stackOutcomes Y n omega))⁻¹ *ᵥ score))) 0 at homega
  rw [hdiff, edist_self] at homega
  exact absurd homega (not_le.mpr hepsilon)

set_option maxHeartbeats 2000000 in
-- The nested-projection rank calculation uses several noncommutative matrix identities.
private theorem gmmSubsetLimitCriterionPullback_symmIdem_rank
    {k la lb : Type*} [Fintype k] [Fintype la] [Fintype lb]
    [DecidableEq k] [DecidableEq la] [DecidableEq lb]
    (Q : Matrix (la ⊕ lb) k ℝ)
    (V : Matrix (la ⊕ lb) (la ⊕ lb) ℝ)
    (hV : V.PosDef)
    (hQ : Function.Injective Q.mulVec)
    (hQa : Function.Injective (Q.submatrix Sum.inl id).mulVec)
    [Fact (0 < Fintype.card lb)] :
    let B := CFC.sqrt V
    let P := Bᵀ * gmmSubsetLimitCriterionMatrix Q V * B
    P.IsHermitian ∧ IsIdempotentElem P ∧
      P.rank = Fintype.card lb := by
  classical
  let L : Matrix la (la ⊕ lb) ℝ :=
    sumLeftSelector (la := la) (lb := lb)
  let Qa : Matrix la k ℝ := Q.submatrix Sum.inl id
  let Va : Matrix la la ℝ := V.submatrix Sum.inl Sum.inl
  let Cf : Matrix (la ⊕ lb) (la ⊕ lb) ℝ :=
    gmmResidualCriterionMatrixStar Q V⁻¹
  let Ca : Matrix la la ℝ :=
    gmmResidualCriterionMatrixStar Qa Va⁻¹
  let Mf : Matrix (la ⊕ lb) (la ⊕ lb) ℝ :=
    gmmResidualMakerStar Q V⁻¹
  let B : Matrix (la ⊕ lb) (la ⊕ lb) ℝ := CFC.sqrt V
  let Pf : Matrix (la ⊕ lb) (la ⊕ lb) ℝ := Bᵀ * Cf * B
  let Pa : Matrix (la ⊕ lb) (la ⊕ lb) ℝ :=
    Bᵀ * Lᵀ * Ca * L * B
  let P : Matrix (la ⊕ lb) (la ⊕ lb) ℝ := Pf - Pa
  have hVa : Va.PosDef := by
    simpa [Va] using posDef_submatrix_sum_inl_local hV
  have hLQ : L * Q = Qa := by
    simpa [L, Qa] using
      sumLeftSelector_mul (la := la) (lb := lb) Q
  have hLVLt : L * V * Lᵀ = Va := by
    simpa [L, Va] using
      sumLeftSelector_mul_transpose (la := la) (lb := lb) V
  have hFactor : B * Bᵀ = V := by
    simpa [B] using cfcSqrt_posDef_factor hV
  have hCfH : Cf.IsHermitian := by
    simpa [Cf] using
      gmmResidualCriterionMatrixStar_isHermitian Q V hV
  have hCaH : Ca.IsHermitian := by
    simpa [Ca] using
      gmmResidualCriterionMatrixStar_isHermitian Qa Va hVa
  have hCfVCf : Cf * V * Cf = Cf := by
    simpa [Cf] using
      gmmResidualCriterionMatrixStar_mul_cov_mul_self Q V hV hQ
  have hCaVaCa : Ca * Va * Ca = Ca := by
    simpa [Ca] using
      gmmResidualCriterionMatrixStar_mul_cov_mul_self Qa Va hVa hQa
  have hCaQa : Ca * Qa = 0 := by
    simpa [Ca] using
      gmmResidualCriterionMatrixStar_mul_derivative_eq_zero
        Qa Va hVa hQa
  have hCfV : Cf * V = Mfᵀ := by
    simpa [Cf, Mf] using
      gmmResidualCriterionMatrixStar_mul_cov_eq_transpose_residualMaker
        Q V hV hQ
  have hPfH : Pf.IsHermitian := by
    simpa [Pf, Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.isHermitian_conjTranspose_mul_mul B hCfH
  have hPaH : Pa.IsHermitian := by
    have hraw :=
      Matrix.isHermitian_conjTranspose_mul_mul (L * B) hCaH
    simpa [Pa, Matrix.transpose_mul, Matrix.mul_assoc,
      Matrix.conjTranspose_eq_transpose_of_trivial] using hraw
  have hPfI : IsIdempotentElem Pf := by
    unfold IsIdempotentElem
    dsimp [Pf]
    calc
      (Bᵀ * Cf * B) * (Bᵀ * Cf * B) =
          Bᵀ * Cf * (B * Bᵀ) * Cf * B := by
            simp [Matrix.mul_assoc]
      _ = Bᵀ * (Cf * V * Cf) * B := by
        rw [hFactor]
        simp [Matrix.mul_assoc]
      _ = Bᵀ * Cf * B := by rw [hCfVCf]
  have hPaI : IsIdempotentElem Pa := by
    unfold IsIdempotentElem
    dsimp [Pa]
    calc
      (Bᵀ * Lᵀ * Ca * L * B) * (Bᵀ * Lᵀ * Ca * L * B) =
          Bᵀ * Lᵀ * Ca * (L * (B * Bᵀ) * Lᵀ) * Ca * L * B := by
            simp [Matrix.mul_assoc]
      _ = Bᵀ * Lᵀ * Ca * (L * V * Lᵀ) * Ca * L * B := by
        rw [hFactor]
      _ = Bᵀ * Lᵀ * (Ca * Va * Ca) * L * B := by
        rw [hLVLt]
        simp [Matrix.mul_assoc]
      _ = Bᵀ * Lᵀ * Ca * L * B := by rw [hCaVaCa]
  have hCaLMf : Ca * L * Mf = Ca * L := by
    have hzero : Ca * L * Q = 0 := by
      rw [Matrix.mul_assoc, hLQ, hCaQa]
    have hzeroA : Ca * L *
        (Q * gmmLinearizationMatrixStar Q V⁻¹) = 0 := by
      calc
        Ca * L * (Q * gmmLinearizationMatrixStar Q V⁻¹) =
            (Ca * L * Q) * gmmLinearizationMatrixStar Q V⁻¹ := by
              simp [Matrix.mul_assoc]
        _ = 0 := by rw [hzero]; simp
    dsimp [Mf]
    rw [gmmResidualMakerStar, Matrix.mul_sub]
    rw [hzeroA, sub_zero]
    simp
  have hMfLTCa : Mfᵀ * Lᵀ * Ca = Lᵀ * Ca := by
    have htranspose := congrArg Matrix.transpose hCaLMf
    have hCaT : Caᵀ = Ca := by
      simpa [Matrix.conjTranspose] using hCaH.eq
    simpa [Matrix.transpose_mul, hCaT, Matrix.mul_assoc] using htranspose
  have hPfPa : Pf * Pa = Pa := by
    dsimp [Pf, Pa]
    calc
      (Bᵀ * Cf * B) * (Bᵀ * Lᵀ * Ca * L * B) =
          Bᵀ * Cf * (B * Bᵀ) * Lᵀ * Ca * L * B := by
            simp [Matrix.mul_assoc]
      _ = Bᵀ * (Cf * V) * Lᵀ * Ca * L * B := by
        rw [hFactor]
        simp [Matrix.mul_assoc]
      _ = Bᵀ * Mfᵀ * Lᵀ * Ca * L * B := by rw [hCfV]
      _ = Bᵀ * (Mfᵀ * Lᵀ * Ca) * L * B := by
        simp [Matrix.mul_assoc]
      _ = Bᵀ * Lᵀ * Ca * L * B := by
        rw [hMfLTCa]
        simp only [← Matrix.mul_assoc]
  have hPaPf : Pa * Pf = Pa := by
    have htranspose := congrArg Matrix.transpose hPfPa
    have hPfT : Pfᵀ = Pf := by
      simpa [Matrix.conjTranspose] using hPfH.eq
    have hPaT : Paᵀ = Pa := by
      simpa [Matrix.conjTranspose] using hPaH.eq
    simpa [Matrix.transpose_mul, hPfT, hPaT] using htranspose
  have hPH : P.IsHermitian := hPfH.sub hPaH
  have hPI : IsIdempotentElem P := by
    unfold IsIdempotentElem
    dsimp [P]
    simp [Matrix.sub_mul, Matrix.mul_sub, hPfPa, hPaPf,
      show Pf * Pf = Pf by simpa [IsIdempotentElem] using hPfI,
      show Pa * Pa = Pa by simpa [IsIdempotentElem] using hPaI]
  have hPfTrace :
      Matrix.trace Pf =
        (Fintype.card (la ⊕ lb) : ℝ) - Fintype.card k := by
    calc
      Matrix.trace Pf = Matrix.trace ((B * Bᵀ) * Cf) := by
        dsimp [Pf]
        rw [Matrix.trace_mul_cycle]
      _ = Matrix.trace (Cf * (B * Bᵀ)) := by
        rw [Matrix.trace_mul_comm]
      _ = Matrix.trace (Cf * V) := by rw [hFactor]
      _ = (Fintype.card (la ⊕ lb) : ℝ) - Fintype.card k := by
        simpa [Cf] using
          gmmResidualCriterionMatrixStar_trace_mul_cov Q V hV hQ
  have hPaTrace :
      Matrix.trace Pa =
        (Fintype.card la : ℝ) - Fintype.card k := by
    let R : Matrix la (la ⊕ lb) ℝ := L * B
    have hPaR : Pa = Rᵀ * Ca * R := by
      simp [Pa, R, Matrix.transpose_mul, Matrix.mul_assoc]
    have hRR : R * Rᵀ = Va := by
      calc
        R * Rᵀ = L * (B * Bᵀ) * Lᵀ := by
          dsimp [R]
          rw [Matrix.transpose_mul]
          calc
            (L * B) * (Bᵀ * Lᵀ) =
                ((L * B) * Bᵀ) * Lᵀ :=
              (Matrix.mul_assoc (L * B) Bᵀ Lᵀ).symm
            _ = (L * (B * Bᵀ)) * Lᵀ := by
              rw [Matrix.mul_assoc L B Bᵀ]
        _ = Va := by rw [hFactor, hLVLt]
    calc
      Matrix.trace Pa = Matrix.trace ((R * Rᵀ) * Ca) := by
        rw [hPaR]
        rw [Matrix.trace_mul_cycle]
      _ = Matrix.trace (Ca * (R * Rᵀ)) := by
        rw [Matrix.trace_mul_comm]
      _ = Matrix.trace (Ca * Va) := by rw [hRR]
      _ = (Fintype.card la : ℝ) - Fintype.card k := by
        simpa [Ca] using
          gmmResidualCriterionMatrixStar_trace_mul_cov Qa Va hVa hQa
  have hRankTrace :=
    rank_eq_natCast_trace_of_isHermitian_idempotent hPH
      (by simpa [IsIdempotentElem] using hPI)
  have hPrank : P.rank = Fintype.card lb := by
    have hreal : (P.rank : ℝ) = Fintype.card lb := by
      calc
        (P.rank : ℝ) = Matrix.trace P := hRankTrace
        _ = Matrix.trace Pf - Matrix.trace Pa := by
          simp [P, Matrix.trace_sub]
        _ = ((Fintype.card (la ⊕ lb) : ℝ) - Fintype.card k) -
            ((Fintype.card la : ℝ) - Fintype.card k) := by
              rw [hPfTrace, hPaTrace]
        _ = Fintype.card lb := by
          rw [Fintype.card_sum, Nat.cast_add]
          ring
    exact_mod_cast hreal
  have hPtarget :
      Bᵀ * gmmSubsetLimitCriterionMatrix Q V * B = P := by
    dsimp [P, Pf, Pa, Cf, Ca, Qa, Va]
    rw [gmmSubsetLimitCriterionMatrix, gmmSubsetCriterionMatrixStar]
    rw [← sumLeftSelector_transpose_mul_mul
      (la := la) (lb := lb)
      (gmmResidualCriterionMatrixStar
        (Q.submatrix Sum.inl id)
        (V.submatrix Sum.inl Sum.inl)⁻¹)]
    simp [L, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
  simpa [B, hPtarget] using And.intro hPH (And.intro hPI hPrank)

/-- Hansen's subset overidentification statistic formed from the efficient
two-step GMM criteria for the full and maintained instrument sets. -/
noncomputable def gmmUncenteredTwoStepSubsetJStatOrZero
    {n k la lb : Type*} [Fintype n] [Fintype k]
    [Fintype la] [Fintype lb]
    [DecidableEq k] [DecidableEq la] [DecidableEq lb]
    (X : Matrix n k ℝ) (Za : Matrix n la ℝ) (Zb : Matrix n lb ℝ)
    (y : n → ℝ) : ℝ :=
  gmmUncenteredTwoStepJStatOrZero X (Matrix.fromCols Za Zb) y -
    gmmUncenteredTwoStepJStatOrZero X Za y

set_option maxHeartbeats 4000000 in
-- This endpoint combines two feasible weights, a quadratic CMT, and two singular-event bridges.
/-- **Hansen Theorem 13.15, observed-row form.** Under Assumption 12.2 for
the full instrument vector and full rank of the maintained moment derivative,
the full-minus-maintained efficient-GMM criterion converges to chi-square with
degrees of freedom equal to the number of tested moments. This result is
slightly more general than Hansen's displayed context because it also covers
an exactly identified maintained model. -/
theorem gmmUncenteredTwoStepSubsetJStatOrZero_tendstoInDistribution_observedRows
    {OmegaSpace : Type*} [MeasurableSpace OmegaSpace]
    {mu : Measure OmegaSpace} [IsProbabilityMeasure mu]
    {k la lb : Type*} [Fintype k] [Fintype la] [Fintype lb]
    [DecidableEq k] [DecidableEq la] [DecidableEq lb]
    {Za : ℕ → OmegaSpace → la → ℝ}
    {Zb : ℕ → OmegaSpace → lb → ℝ}
    {X : ℕ → OmegaSpace → k → ℝ}
    {e Y : ℕ → OmegaSpace → ℝ}
    {b : k → ℝ}
    [Fact (0 < Fintype.card lb)]
    (hFull : TwoSLSObservedIidFourthMomentPositiveCovarianceConditions
      mu (fun i omega => Sum.elim (Za i omega) (Zb i omega)) X e Y b)
    (hMaintainedRelevance : Function.Injective
      (twoSLSCombinedQZX
        (popGram mu (twoSLSCombinedRegressors Za X))).mulVec) :
    TendstoInDistribution
      (fun n omega =>
        gmmUncenteredTwoStepSubsetJStatOrZero
          (stackRegressors X n omega)
          (stackRegressors Za n omega) (stackRegressors Zb n omega)
          (stackOutcomes Y n omega))
      atTop (fun x : ℝ => x) (fun _ => mu)
      (chiSquared (Fintype.card lb)) := by
  classical
  let Zfull : ℕ → OmegaSpace → (la ⊕ lb) → ℝ :=
    fun i omega => Sum.elim (Za i omega) (Zb i omega)
  let hMaintained := hFull.leftBlock
    (Za := Za) (Zb := Zb) hMaintainedRelevance
  let hFullCore := hFull.toJointIidMixedMomentConditions
  let hMaintainedCore := hMaintained.toJointIidMixedMomentConditions
  let hFullGram : TwoSLSGramScoreCLTPositiveCovarianceConditions
      mu Zfull X e :=
    hFullCore.toTwoSLSResidualJointIidFourthMomentPositiveCovarianceConditions
      |>.toIidFourthConditions
      |>.toGramConditions
  let hMaintainedGram : TwoSLSGramScoreCLTPositiveCovarianceConditions
      mu Za X e :=
    hMaintainedCore.toTwoSLSResidualJointIidFourthMomentPositiveCovarianceConditions
      |>.toIidFourthConditions
      |>.toGramConditions
  let Qfull : Matrix (la ⊕ lb) k ℝ :=
    twoSLSCombinedQZX (popGram mu (twoSLSCombinedRegressors Zfull X))
  let Qmaintained : Matrix la k ℝ :=
    twoSLSCombinedQZX (popGram mu (twoSLSCombinedRegressors Za X))
  let Omega : Matrix (la ⊕ lb) (la ⊕ lb) ℝ :=
    scoreCovMat mu Zfull e
  let OmegaMaintained : Matrix la la ℝ := scoreCovMat mu Za e
  have hQeq : Qfull.submatrix Sum.inl id = Qmaintained := by
    simpa [Qfull, Qmaintained, Zfull] using
      twoSLSCombinedQZX_fullInstrument_submatrix_inl
        (μ := mu) Za Zb X
        hMaintainedGram.combined_gram.int_outer
        hFullGram.combined_gram.int_outer
  have hOmegaEq :
      Omega.submatrix Sum.inl Sum.inl = OmegaMaintained := by
    ext a c
    rfl
  let hFullCov :=
    hFullCore.toCovarianceMomentConsistencyConditions b hFull.model
  let hMaintainedCov :=
    hMaintainedCore.toCovarianceMomentConsistencyConditions b hMaintained.model
  let OmegaFullHat : ℕ → OmegaSpace →
      Matrix (la ⊕ lb) (la ⊕ lb) ℝ := fun n omega =>
    twoSLSOmegaHatStar
      (stackRegressors Zfull n omega) (stackRegressors X n omega)
      (stackOutcomes Y n omega)
  let OmegaMaintainedHat : ℕ → OmegaSpace → Matrix la la ℝ :=
    fun n omega =>
      twoSLSOmegaHatStar
        (stackRegressors Za n omega) (stackRegressors X n omega)
        (stackOutcomes Y n omega)
  let Wfull : ℕ → OmegaSpace → Matrix (la ⊕ lb) (la ⊕ lb) ℝ :=
    fun n omega => (OmegaFullHat n omega)⁻¹
  let Wmaintained : ℕ → OmegaSpace → Matrix la la ℝ :=
    fun n omega => (OmegaMaintainedHat n omega)⁻¹
  have hOmegaFullMeas : ∀ n,
      AEStronglyMeasurable (OmegaFullHat n) mu := by
    intro n
    simpa [OmegaFullHat, Zfull] using hFullCov.omega_meas n
  have hOmegaMaintainedMeas : ∀ n,
      AEStronglyMeasurable (OmegaMaintainedHat n) mu := by
    intro n
    simpa [OmegaMaintainedHat] using hMaintainedCov.omega_meas n
  have hWfullMeas : ∀ n, AEStronglyMeasurable (Wfull n) mu :=
    fun n => aestronglyMeasurable_matrix_inv (hOmegaFullMeas n)
  have hWmaintainedMeas : ∀ n,
      AEStronglyMeasurable (Wmaintained n) mu :=
    fun n => aestronglyMeasurable_matrix_inv (hOmegaMaintainedMeas n)
  have hOmegaFull : TendstoInMeasure mu OmegaFullHat atTop
      (fun _ => Omega) := by
    simpa [OmegaFullHat, Omega, Zfull] using hFullCov.omega_tendsto
  have hOmegaMaintained : TendstoInMeasure mu OmegaMaintainedHat atTop
      (fun _ => OmegaMaintained) := by
    simpa [OmegaMaintainedHat, OmegaMaintained] using
      hMaintainedCov.omega_tendsto
  have hWfull : TendstoInMeasure mu Wfull atTop
      (fun _ => Omega⁻¹) := by
    simpa [Wfull] using
      tendstoInMeasure_matrix_inv hOmegaFullMeas hOmegaFull
        (fun _ => (Matrix.isUnit_iff_isUnit_det Omega).mp (by
          simpa [Omega, Zfull] using hFull.omega_posDef.isUnit))
  have hWmaintained : TendstoInMeasure mu Wmaintained atTop
      (fun _ => OmegaMaintained⁻¹) := by
    simpa [Wmaintained] using
      tendstoInMeasure_matrix_inv
        hOmegaMaintainedMeas hOmegaMaintained
        (fun _ => (Matrix.isUnit_iff_isUnit_det OmegaMaintained).mp (by
          simpa [OmegaMaintained] using hMaintained.omega_posDef.isUnit))
  let hFullMoment : GMMMomentCLTConditions mu
      (fun n omega =>
        sampleQZX (stackRegressors Zfull n omega)
          (stackRegressors X n omega))
      Wfull Zfull e Qfull Omega⁻¹ :=
    hFullGram.toGMMMomentCLTConditions
      Wfull Omega⁻¹ hWfullMeas hWfull (by
        simpa [Omega, Zfull] using hFull.omega_posDef.inv)
  let hMaintainedMoment : GMMMomentCLTConditions mu
      (fun n omega =>
        sampleQZX (stackRegressors Za n omega)
          (stackRegressors X n omega))
      Wmaintained Za e Qmaintained OmegaMaintained⁻¹ :=
    hMaintainedGram.toGMMMomentCLTConditions
      Wmaintained OmegaMaintained⁻¹ hWmaintainedMeas hWmaintained
        (by simpa [OmegaMaintained] using hMaintained.omega_posDef.inv)
  let hFullWeight := hFullMoment.toGMMWeightConvergenceConditions
  let hMaintainedWeight :=
    hMaintainedMoment.toGMMWeightConvergenceConditions
  let scoreFull : ℕ → OmegaSpace → (la ⊕ lb) → ℝ :=
    fun n omega =>
      Real.sqrt (n : ℝ) •
        sampleCrossMoment (stackRegressors Zfull n omega)
          (stackErrors e n omega)
  let scoreMaintained : ℕ → OmegaSpace → la → ℝ :=
    fun n omega =>
      Real.sqrt (n : ℝ) •
        sampleCrossMoment (stackRegressors Za n omega)
          (stackErrors e n omega)
  let QfullHat : ℕ → OmegaSpace → Matrix (la ⊕ lb) k ℝ :=
    fun n omega =>
      sampleQZX (stackRegressors Zfull n omega)
        (stackRegressors X n omega)
  let QmaintainedHat : ℕ → OmegaSpace → Matrix la k ℝ :=
    fun n omega =>
      sampleQZX (stackRegressors Za n omega)
        (stackRegressors X n omega)
  let Ahat : ℕ → OmegaSpace →
      Matrix (la ⊕ lb) (la ⊕ lb) ℝ := fun n omega =>
    gmmSubsetCriterionMatrixStar
      (QfullHat n omega) (Wfull n omega)
      (QmaintainedHat n omega) (Wmaintained n omega)
  let A : Matrix (la ⊕ lb) (la ⊕ lb) ℝ :=
    gmmSubsetLimitCriterionMatrix Qfull Omega
  have hAmeas : ∀ n, AEStronglyMeasurable (Ahat n) mu := by
    intro n
    exact gmmSubsetCriterionMatrixStar_aestronglyMeasurable
      (hFullWeight.q_meas n) (hFullWeight.weight_meas n)
      (hMaintainedWeight.q_meas n) (hMaintainedWeight.weight_meas n)
  have hA : TendstoInMeasure mu Ahat atTop (fun _ => A) := by
    have hraw := gmmSubsetCriterionMatrixStar_tendstoInMeasure
      hFullWeight hMaintainedWeight
    simpa [Ahat, A, QfullHat, QmaintainedHat,
      gmmSubsetLimitCriterionMatrix, hQeq, hOmegaEq] using hraw
  have hScore :
      TendstoInDistribution scoreFull atTop
        (fun z : EuclideanSpace ℝ (la ⊕ lb) => z.ofLp)
        (fun _ => mu) (multivariateGaussian 0 Omega) := by
    simpa [scoreFull, Omega, Zfull] using
      scoreVector_sampleCrossMoment_tendstoInDistribution_multivariateGaussian
        (μ := mu) (X := Zfull) (e := e) hFullGram.score_clt
  have hQuadraticRaw :=
    quadraticForm_tendstoInDistribution_of_vector_and_matrix
      (μ := mu) (ν := multivariateGaussian 0 Omega)
      (T := scoreFull)
      (Z := fun z : EuclideanSpace ℝ (la ⊕ lb) => z.ofLp)
      (Ahat := Ahat) (A := A) hScore hAmeas hA
  let B : Matrix (la ⊕ lb) (la ⊕ lb) ℝ := CFC.sqrt Omega
  have hFactor : B * Bᵀ = Omega := by
    simpa [B] using cfcSqrt_posDef_factor (by
      simpa [Omega, Zfull] using hFull.omega_posDef)
  have hProps :=
    gmmSubsetLimitCriterionPullback_symmIdem_rank
      Qfull Omega
      (by simpa [Omega, Zfull] using hFull.omega_posDef)
      (by simpa [Qfull, Zfull] using hFull.qzx_rank)
      (by simpa [Qfull, Qmaintained, hQeq] using
        hMaintainedRelevance)
  have hLawRaw :=
    hasLaw_multivariateGaussian_zero_quadratic_of_factor_symmIdem
      (B := B) (A := A) hProps.1 hProps.2.1 (by
        rw [hProps.2.2]
        exact Fact.out)
  have hLaw : HasLaw
      (fun z : EuclideanSpace ℝ (la ⊕ lb) =>
        z.ofLp ⬝ᵥ (A *ᵥ z.ofLp))
      (chiSquared (Fintype.card lb))
      (multivariateGaussian 0 Omega) := by
    have hRank :
        (Bᵀ * A * B).rank = Fintype.card lb := by
      simpa [B, A] using hProps.2.2
    simpa [hFactor, hRank] using hLawRaw
  have hQuadratic : TendstoInDistribution
      (fun n omega =>
        scoreFull n omega ⬝ᵥ (Ahat n omega *ᵥ scoreFull n omega))
      atTop (fun x : ℝ => x) (fun _ => mu)
      (chiSquared (Fintype.card lb)) :=
    tendstoInDistribution_id_of_hasLaw_limit_real hQuadraticRaw hLaw
  let fullJ : ℕ → OmegaSpace → ℝ := fun n omega =>
    gmmUncenteredTwoStepJStatOrZero
      (stackRegressors X n omega) (stackRegressors Zfull n omega)
      (stackOutcomes Y n omega)
  let maintainedJ : ℕ → OmegaSpace → ℝ := fun n omega =>
    gmmUncenteredTwoStepJStatOrZero
      (stackRegressors X n omega) (stackRegressors Za n omega)
      (stackOutcomes Y n omega)
  let rawFull : ℕ → OmegaSpace → ℝ := fun n omega =>
    scoreFull n omega ⬝ᵥ
      (gmmResidualCriterionMatrixStar
        (QfullHat n omega) (Wfull n omega) *ᵥ scoreFull n omega)
  let rawMaintained : ℕ → OmegaSpace → ℝ := fun n omega =>
    scoreMaintained n omega ⬝ᵥ
      (gmmResidualCriterionMatrixStar
        (QmaintainedHat n omega) (Wmaintained n omega) *ᵥ
          scoreMaintained n omega)
  have hFullBridge : TendstoInMeasure mu
      (fullJ - rawFull) atTop (fun _ => 0) := by
    simpa [fullJ, rawFull, scoreFull, QfullHat, Wfull,
      OmegaFullHat] using
      gmmUncenteredTwoStepJStatOrZero_sub_scoreCriterion_tendstoInMeasure_zero
        hFullWeight b hFull.model
  have hMaintainedBridge : TendstoInMeasure mu
      (maintainedJ - rawMaintained) atTop (fun _ => 0) := by
    simpa [maintainedJ, rawMaintained, scoreMaintained,
      QmaintainedHat, Wmaintained, OmegaMaintainedHat] using
      gmmUncenteredTwoStepJStatOrZero_sub_scoreCriterion_tendstoInMeasure_zero
        hMaintainedWeight b hMaintained.model
  have hScoreBlock : ∀ n omega,
      scoreFull n omega ∘ Sum.inl = scoreMaintained n omega := by
    intro n omega
    funext a
    rfl
  have hRaw : ∀ n omega,
      scoreFull n omega ⬝ᵥ (Ahat n omega *ᵥ scoreFull n omega) =
        rawFull n omega - rawMaintained n omega := by
    intro n omega
    simpa [Ahat, rawFull, rawMaintained] using
      gmmSubsetCriterionMatrixStar_quadratic
        (QfullHat n omega) (Wfull n omega)
        (QmaintainedHat n omega) (Wmaintained n omega)
        (scoreFull n omega)
  have hBridge : TendstoInMeasure mu
      (fun n omega =>
        (fullJ n omega - maintainedJ n omega) -
          scoreFull n omega ⬝ᵥ
            (Ahat n omega *ᵥ scoreFull n omega))
      atTop (fun _ => 0) := by
    have hboth :=
      TendstoInMeasure.sub_zero_real hFullBridge hMaintainedBridge
    refine TendstoInMeasure.congr (fun n => ?_) EventuallyEq.rfl hboth
    exact ae_of_all mu fun omega => by
      change
        (fullJ n omega - rawFull n omega) -
            (maintainedJ n omega - rawMaintained n omega) =
          (fullJ n omega - maintainedJ n omega) -
            scoreFull n omega ⬝ᵥ
              (Ahat n omega *ᵥ scoreFull n omega)
      rw [hRaw n omega]
      ring
  have hY : ∀ i, AEStronglyMeasurable (Y i) mu :=
    fun i => continuous_snd.comp_aestronglyMeasurable
      (hFull.observed_aestronglyMeasurable i)
  have hFullJMeas : ∀ n, AEStronglyMeasurable (fullJ n) mu := by
    intro n
    have hT := gmmScaledResidualMomentOrZero_aestronglyMeasurable_of_rows
      (mu := mu) (n := n) (Z := Zfull) (X := X) (Y := Y)
      (What := Wfull n)
      hFullCore.z_aestronglyMeasurable hFullCore.x_aestronglyMeasurable
      hY (hWfullMeas n)
    simpa [fullJ, gmmUncenteredTwoStepJStatOrZero,
      OmegaFullHat, Wfull] using
      gmmJStatOrZero_aestronglyMeasurable hT (hOmegaFullMeas n)
  have hMaintainedJMeas : ∀ n,
      AEStronglyMeasurable (maintainedJ n) mu := by
    intro n
    have hT := gmmScaledResidualMomentOrZero_aestronglyMeasurable_of_rows
      (mu := mu) (n := n) (Z := Za) (X := X) (Y := Y)
      (What := Wmaintained n)
      hMaintainedCore.z_aestronglyMeasurable
      hMaintainedCore.x_aestronglyMeasurable hY
      (hWmaintainedMeas n)
    simpa [maintainedJ, gmmUncenteredTwoStepJStatOrZero,
      OmegaMaintainedHat, Wmaintained] using
      gmmJStatOrZero_aestronglyMeasurable hT
        (hOmegaMaintainedMeas n)
  have hCMeas : ∀ n, AEMeasurable
      (fun omega => fullJ n omega - maintainedJ n omega) mu :=
    fun n => ((hFullJMeas n).sub (hMaintainedJMeas n)).aemeasurable
  have hC := tendstoInDistribution_of_tendstoInMeasure_sub
    (X := fun n omega =>
      scoreFull n omega ⬝ᵥ (Ahat n omega *ᵥ scoreFull n omega))
    (Y := fun n omega => fullJ n omega - maintainedJ n omega)
    (Z := fun x : ℝ => x) hQuadratic hBridge hCMeas
  simpa [gmmUncenteredTwoStepSubsetJStatOrZero, fullJ, maintainedJ,
    Zfull, stackRegressors, Matrix.fromCols] using hC

/-- Asymptotic-size conclusion in Hansen Theorem 13.15 for the actual
full-minus-maintained efficient two-step GMM criterion. -/
theorem
    gmmUncenteredTwoStepSubsetJTest_rejectionProb_tendsto_alpha_observedRows
    {OmegaSpace : Type*} [MeasurableSpace OmegaSpace]
    {mu : Measure OmegaSpace} [IsProbabilityMeasure mu]
    {k la lb : Type*} [Fintype k] [Fintype la] [Fintype lb]
    [DecidableEq k] [DecidableEq la] [DecidableEq lb]
    {Za : ℕ → OmegaSpace → la → ℝ}
    {Zb : ℕ → OmegaSpace → lb → ℝ}
    {X : ℕ → OmegaSpace → k → ℝ}
    {e Y : ℕ → OmegaSpace → ℝ}
    {b : k → ℝ}
    [Fact (0 < Fintype.card lb)]
    {crit : ℝ} {alpha : ℝ≥0∞}
    (hcrit : (chiSquared (Fintype.card lb)) (Set.Ioi crit) = alpha)
    (hFull : TwoSLSObservedIidFourthMomentPositiveCovarianceConditions
      mu (fun i omega => Sum.elim (Za i omega) (Zb i omega)) X e Y b)
    (hMaintainedRelevance : Function.Injective
      (twoSLSCombinedQZX
        (popGram mu (twoSLSCombinedRegressors Za X))).mulVec) :
    Tendsto
      (fun n => mu {omega |
        crit <
          gmmUncenteredTwoStepSubsetJStatOrZero
            (stackRegressors X n omega)
            (stackRegressors Za n omega) (stackRegressors Zb n omega)
            (stackOutcomes Y n omega)})
      atTop (nhds alpha) :=
  chiSquaredTest_rejectionProb_tendsto_alpha_of_stat hcrit
    (gmmUncenteredTwoStepSubsetJStatOrZero_tendstoInDistribution_observedRows
      hFull hMaintainedRelevance)

/-- Difference between the full and maintained efficient-GMM criteria. -/
noncomputable def gmmSubsetOveridentificationStatOrZero
    (fullJ maintainedJ : ℝ) : ℝ :=
  fullJ - maintainedJ

/-- Generic feasible-quadratic transfer engine for a subset
overidentification statistic. The observed-row theorem above derives these
premises for Hansen's actual efficient-GMM criterion difference. -/
theorem gmmSubsetOveridentificationStatOrZero_tendstoInDistribution_chiSquared
    {OmegaSpace OmegaLimit : Type*}
    [MeasurableSpace OmegaSpace] [MeasurableSpace OmegaLimit]
    {mu : Measure OmegaSpace} [IsProbabilityMeasure mu]
    {nu : Measure OmegaLimit} [IsProbabilityMeasure nu]
    {df : ℕ} [Fact (0 < df)]
    {fullJ maintainedJ : ℕ → OmegaSpace → ℝ}
    {T : ℕ → OmegaSpace → Fin df → ℝ}
    {G : OmegaLimit → Fin df → ℝ}
    {Vhat : ℕ → OmegaSpace → Matrix (Fin df) (Fin df) ℝ}
    {V : Matrix (Fin df) (Fin df) ℝ}
    (hT : TendstoInDistribution T atTop G (fun _ => mu) nu)
    (hV_meas : ∀ n, AEStronglyMeasurable (Vhat n) mu)
    (hV : TendstoInMeasure mu Vhat atTop (fun _ => V))
    (hV_nonsing : IsUnit V.det)
    (hLaw : HasLaw (fun omega => G omega ⬝ᵥ (V⁻¹ *ᵥ G omega))
      (chiSquared df) nu)
    (hbridge : TendstoInMeasure mu
      (fun n omega =>
        gmmSubsetOveridentificationStatOrZero
            (fullJ n omega) (maintainedJ n omega) -
          criterionJStatOrZero (T n omega) (Vhat n omega))
      atTop (fun _ => 0))
    (hC_meas : ∀ n, AEMeasurable
      (fun omega => gmmSubsetOveridentificationStatOrZero
        (fullJ n omega) (maintainedJ n omega)) mu) :
    TendstoInDistribution
      (fun n omega => gmmSubsetOveridentificationStatOrZero
        (fullJ n omega) (maintainedJ n omega))
      atTop (fun x : ℝ => x) (fun _ => mu) (chiSquared df) := by
  have hcriterion :=
    criterionJStatOrZero_tendstoInDistribution_chiSquared_of_limitLaw
      (μ := mu) (ν := nu) (df := df)
      (T := T) (Z := G) (Vhat := Vhat) (V := V)
      hT hV_meas hV hV_nonsing hLaw
  exact tendstoInDistribution_of_tendstoInMeasure_sub
    (X := fun n omega => criterionJStatOrZero (T n omega) (Vhat n omega))
    (Y := fun n omega => gmmSubsetOveridentificationStatOrZero
      (fullJ n omega) (maintainedJ n omega))
    (Z := fun x : ℝ => x) hcriterion hbridge hC_meas

/-- Generic Gaussian specialization of the subset-overidentification transfer
engine. Chapter 5's Mahalanobis theorem supplies the chi-square law. -/
theorem gmmSubsetOveridentificationStatOrZero_tendstoInDistribution_of_gaussian
    {OmegaSpace : Type*} [MeasurableSpace OmegaSpace]
    {mu : Measure OmegaSpace} [IsProbabilityMeasure mu]
    {df : ℕ} [Fact (0 < df)]
    {fullJ maintainedJ : ℕ → OmegaSpace → ℝ}
    {T : ℕ → OmegaSpace → Fin df → ℝ}
    {Vhat : ℕ → OmegaSpace → Matrix (Fin df) (Fin df) ℝ}
    {V : Matrix (Fin df) (Fin df) ℝ}
    (hT : TendstoInDistribution T atTop
      (fun z : EuclideanSpace ℝ (Fin df) => z.ofLp) (fun _ => mu)
      (multivariateGaussian 0 V))
    (hV_meas : ∀ n, AEStronglyMeasurable (Vhat n) mu)
    (hV : TendstoInMeasure mu Vhat atTop (fun _ => V))
    (hV_posDef : V.PosDef)
    (hbridge : TendstoInMeasure mu
      (fun n omega =>
        gmmSubsetOveridentificationStatOrZero
            (fullJ n omega) (maintainedJ n omega) -
          criterionJStatOrZero (T n omega) (Vhat n omega))
      atTop (fun _ => 0))
    (hC_meas : ∀ n, AEMeasurable
      (fun omega => gmmSubsetOveridentificationStatOrZero
        (fullJ n omega) (maintainedJ n omega)) mu) :
    TendstoInDistribution
      (fun n omega => gmmSubsetOveridentificationStatOrZero
        (fullJ n omega) (maintainedJ n omega))
      atTop (fun x : ℝ => x) (fun _ => mu) (chiSquared df) := by
  have hLaw :=
    hasLaw_multivariateGaussian_zero_mahalanobis_chiSquared
      (n := df) Fact.out hV_posDef
  exact
    gmmSubsetOveridentificationStatOrZero_tendstoInDistribution_chiSquared
      (mu := mu) (nu := multivariateGaussian 0 V) (df := df)
      (fullJ := fullJ) (maintainedJ := maintainedJ)
      (T := T) (G := fun z : EuclideanSpace ℝ (Fin df) => z.ofLp)
      (Vhat := Vhat) (V := V) hT hV_meas hV
      ((Matrix.isUnit_iff_isUnit_det _).mp hV_posDef.isUnit)
      hLaw hbridge hC_meas

/-- Size form of Hansen Theorem 13.15. -/
theorem gmmSubsetOveridentificationTest_rejectionProb_tendsto_alpha
    {OmegaSpace : Type*} [MeasurableSpace OmegaSpace]
    {mu : Measure OmegaSpace} [IsProbabilityMeasure mu]
    {df : ℕ} [Fact (0 < df)]
    {C : ℕ → OmegaSpace → ℝ} {crit : ℝ} {alpha : ℝ≥0∞}
    (hcrit : (chiSquared df) (Set.Ioi crit) = alpha)
    (hC : TendstoInDistribution C atTop (fun x : ℝ => x)
      (fun _ => mu) (chiSquared df)) :
    Tendsto (fun n => mu {omega | crit < C n omega}) atTop
      (nhds alpha) :=
  chiSquaredTest_rejectionProb_tendsto_alpha_of_stat hcrit hC

/-- Observed-row regularity for Hansen's Theorem 13.16.

The package records Assumption 12.2 for the augmented instrument vector,
Hansen's displayed rank condition `rank E[Z₂Y₂'] = k₂`, and the maintained-fit
relevance condition required by the subset-overidentification theorem. -/
structure GMMEndogeneityObservedRowsConditions
    {OmegaSpace : Type*} [MeasurableSpace OmegaSpace]
    (mu : Measure OmegaSpace) [IsProbabilityMeasure mu]
    {k1 k2 l2 : Type*} [Fintype k1] [Fintype k2] [Fintype l2]
    (Z1 : ℕ → OmegaSpace → k1 → ℝ)
    (Z2 : ℕ → OmegaSpace → l2 → ℝ)
    (Y2 : ℕ → OmegaSpace → k2 → ℝ)
    (e Y : ℕ → OmegaSpace → ℝ)
    (b : (k1 ⊕ k2) → ℝ) : Prop where
  assumption12_2 :
    TwoSLSObservedIidFourthMomentPositiveCovarianceConditions
      mu
      (fun i omega =>
        Sum.elim
          (Sum.elim (Z1 i omega) (Z2 i omega))
          (Y2 i omega))
      (fun i omega => Sum.elim (Z1 i omega) (Y2 i omega))
      e Y b
  maintained_relevance : Function.Injective
    (twoSLSCombinedQZX
      (popGram mu
        (twoSLSCombinedRegressors
          (fun i omega => Sum.elim (Z1 i omega) (Z2 i omega))
          (fun i omega => Sum.elim (Z1 i omega) (Y2 i omega))))).mulVec
  displayed_rank : Function.Injective
    (twoSLSCombinedQZX
      (popGram mu (twoSLSCombinedRegressors Z2 Y2))).mulVec

/-- Hansen's Theorem 13.16 criterion difference: efficient two-step GMM with
instruments `(Z₁,Z₂,Y₂)` minus efficient two-step GMM with `(Z₁,Z₂)`, both
using regressors `(Z₁,Y₂)`. -/
noncomputable def gmmEndogeneityTwoStepStatOrZero
    {n k1 k2 l2 : Type*} [Fintype n] [Fintype k1]
    [Fintype k2] [Fintype l2]
    [DecidableEq k1] [DecidableEq k2] [DecidableEq l2]
    (Z1 : Matrix n k1 ℝ) (Y2 : Matrix n k2 ℝ)
    (Z2 : Matrix n l2 ℝ) (Y : n → ℝ) : ℝ :=
  gmmUncenteredTwoStepSubsetJStatOrZero
    (Matrix.fromCols Z1 Y2) (Matrix.fromCols Z1 Z2) Y2 Y

/-- **Hansen Theorem 13.16, observed-row form.** The actual full-minus-
maintained two-step GMM criterion for testing exogeneity of `Y₂` converges to
chi-square with `k₂` degrees of freedom. -/
theorem gmmEndogeneityTwoStepStatOrZero_tendstoInDistribution_observedRows
    {OmegaSpace : Type*} [MeasurableSpace OmegaSpace]
    {mu : Measure OmegaSpace} [IsProbabilityMeasure mu]
    {k1 k2 l2 : Type*} [Fintype k1] [Fintype k2] [Fintype l2]
    [DecidableEq k1] [DecidableEq k2] [DecidableEq l2]
    {Z1 : ℕ → OmegaSpace → k1 → ℝ}
    {Z2 : ℕ → OmegaSpace → l2 → ℝ}
    {Y2 : ℕ → OmegaSpace → k2 → ℝ}
    {e Y : ℕ → OmegaSpace → ℝ}
    {b : (k1 ⊕ k2) → ℝ}
    [Fact (0 < Fintype.card k2)]
    (h : GMMEndogeneityObservedRowsConditions mu Z1 Z2 Y2 e Y b) :
    TendstoInDistribution
      (fun n omega =>
        gmmEndogeneityTwoStepStatOrZero
          (stackRegressors Z1 n omega)
          (stackRegressors Y2 n omega)
          (stackRegressors Z2 n omega)
          (stackOutcomes Y n omega))
      atTop (fun x : ℝ => x) (fun _ => mu)
      (chiSquared (Fintype.card k2)) := by
  simpa [gmmEndogeneityTwoStepStatOrZero, stackRegressors,
    Matrix.fromCols] using
    gmmUncenteredTwoStepSubsetJStatOrZero_tendstoInDistribution_observedRows
      h.assumption12_2 h.maintained_relevance

/-- Asymptotic-size conclusion in Hansen Theorem 13.16 for the concrete
observed-row endogeneity statistic. -/
theorem
    gmmEndogeneityTwoStepTest_rejectionProb_tendsto_alpha_observedRows
    {OmegaSpace : Type*} [MeasurableSpace OmegaSpace]
    {mu : Measure OmegaSpace} [IsProbabilityMeasure mu]
    {k1 k2 l2 : Type*} [Fintype k1] [Fintype k2] [Fintype l2]
    [DecidableEq k1] [DecidableEq k2] [DecidableEq l2]
    {Z1 : ℕ → OmegaSpace → k1 → ℝ}
    {Z2 : ℕ → OmegaSpace → l2 → ℝ}
    {Y2 : ℕ → OmegaSpace → k2 → ℝ}
    {e Y : ℕ → OmegaSpace → ℝ}
    {b : (k1 ⊕ k2) → ℝ}
    [Fact (0 < Fintype.card k2)]
    {crit : ℝ} {alpha : ℝ≥0∞}
    (hcrit : (chiSquared (Fintype.card k2)) (Set.Ioi crit) = alpha)
    (h : GMMEndogeneityObservedRowsConditions mu Z1 Z2 Y2 e Y b) :
    Tendsto
      (fun n => mu {omega |
        crit <
          gmmEndogeneityTwoStepStatOrZero
            (stackRegressors Z1 n omega)
            (stackRegressors Y2 n omega)
            (stackRegressors Z2 n omega)
            (stackOutcomes Y n omega)})
      atTop (nhds alpha) :=
  chiSquaredTest_rejectionProb_tendsto_alpha_of_stat hcrit
    (gmmEndogeneityTwoStepStatOrZero_tendstoInDistribution_observedRows h)

/-- Observed-row regularity for Hansen's Theorem 13.17.

The package records Assumption 12.2 for the augmented instrument vector,
Hansen's displayed rank condition `rank E[Z₂(Y₂',Y₃')] = k₂+k₃`, and the
maintained-fit relevance condition required by the subset test. -/
structure GMMSubsetEndogeneityObservedRowsConditions
    {OmegaSpace : Type*} [MeasurableSpace OmegaSpace]
    (mu : Measure OmegaSpace) [IsProbabilityMeasure mu]
    {k1 k2 k3 l2 : Type*}
    [Fintype k1] [Fintype k2] [Fintype k3] [Fintype l2]
    (Z1 : ℕ → OmegaSpace → k1 → ℝ)
    (Z2 : ℕ → OmegaSpace → l2 → ℝ)
    (Y2 : ℕ → OmegaSpace → k2 → ℝ)
    (Y3 : ℕ → OmegaSpace → k3 → ℝ)
    (e Y : ℕ → OmegaSpace → ℝ)
    (b : (k1 ⊕ (k2 ⊕ k3)) → ℝ) : Prop where
  assumption12_2 :
    TwoSLSObservedIidFourthMomentPositiveCovarianceConditions
      mu
      (fun i omega =>
        Sum.elim
          (Sum.elim (Z1 i omega) (Z2 i omega))
          (Y2 i omega))
      (fun i omega =>
        Sum.elim (Z1 i omega)
          (Sum.elim (Y2 i omega) (Y3 i omega)))
      e Y b
  maintained_relevance : Function.Injective
    (twoSLSCombinedQZX
      (popGram mu
        (twoSLSCombinedRegressors
          (fun i omega => Sum.elim (Z1 i omega) (Z2 i omega))
          (fun i omega =>
            Sum.elim (Z1 i omega)
              (Sum.elim (Y2 i omega) (Y3 i omega)))))).mulVec
  displayed_rank : Function.Injective
    (twoSLSCombinedQZX
      (popGram mu
        (twoSLSCombinedRegressors Z2
          (fun i omega => Sum.elim (Y2 i omega) (Y3 i omega))))).mulVec

/-- Hansen's Theorem 13.17 criterion difference: efficient two-step GMM with
instruments `(Z₁,Z₂,Y₂)` minus efficient two-step GMM with `(Z₁,Z₂)`, both
using regressors `(Z₁,Y₂,Y₃)`. -/
noncomputable def gmmSubsetEndogeneityTwoStepStatOrZero
    {n k1 k2 k3 l2 : Type*} [Fintype n] [Fintype k1]
    [Fintype k2] [Fintype k3] [Fintype l2]
    [DecidableEq k1] [DecidableEq k2] [DecidableEq k3]
    [DecidableEq l2]
    (Z1 : Matrix n k1 ℝ) (Y2 : Matrix n k2 ℝ)
    (Y3 : Matrix n k3 ℝ) (Z2 : Matrix n l2 ℝ)
    (Y : n → ℝ) : ℝ :=
  gmmUncenteredTwoStepSubsetJStatOrZero
    (Matrix.fromCols Z1 (Matrix.fromCols Y2 Y3))
    (Matrix.fromCols Z1 Z2) Y2 Y

/-- **Hansen Theorem 13.17, observed-row form.** The actual full-minus-
maintained two-step GMM criterion for testing the `Y₂` block while retaining
endogenous block `Y₃` converges to chi-square with `k₂` degrees of freedom. -/
theorem
    gmmSubsetEndogeneityTwoStepStatOrZero_tendstoInDistribution_observedRows
    {OmegaSpace : Type*} [MeasurableSpace OmegaSpace]
    {mu : Measure OmegaSpace} [IsProbabilityMeasure mu]
    {k1 k2 k3 l2 : Type*}
    [Fintype k1] [Fintype k2] [Fintype k3] [Fintype l2]
    [DecidableEq k1] [DecidableEq k2] [DecidableEq k3]
    [DecidableEq l2]
    {Z1 : ℕ → OmegaSpace → k1 → ℝ}
    {Z2 : ℕ → OmegaSpace → l2 → ℝ}
    {Y2 : ℕ → OmegaSpace → k2 → ℝ}
    {Y3 : ℕ → OmegaSpace → k3 → ℝ}
    {e Y : ℕ → OmegaSpace → ℝ}
    {b : (k1 ⊕ (k2 ⊕ k3)) → ℝ}
    [Fact (0 < Fintype.card k2)]
    (h : GMMSubsetEndogeneityObservedRowsConditions
      mu Z1 Z2 Y2 Y3 e Y b) :
    TendstoInDistribution
      (fun n omega =>
        gmmSubsetEndogeneityTwoStepStatOrZero
          (stackRegressors Z1 n omega)
          (stackRegressors Y2 n omega)
          (stackRegressors Y3 n omega)
          (stackRegressors Z2 n omega)
          (stackOutcomes Y n omega))
      atTop (fun x : ℝ => x) (fun _ => mu)
      (chiSquared (Fintype.card k2)) := by
  simpa [gmmSubsetEndogeneityTwoStepStatOrZero, stackRegressors,
    Matrix.fromCols] using
    gmmUncenteredTwoStepSubsetJStatOrZero_tendstoInDistribution_observedRows
      h.assumption12_2 h.maintained_relevance

/-- Asymptotic-size conclusion in Hansen Theorem 13.17 for the concrete
observed-row subset-endogeneity statistic. -/
theorem
    gmmSubsetEndogeneityTwoStepTest_rejectionProb_tendsto_alpha_observedRows
    {OmegaSpace : Type*} [MeasurableSpace OmegaSpace]
    {mu : Measure OmegaSpace} [IsProbabilityMeasure mu]
    {k1 k2 k3 l2 : Type*}
    [Fintype k1] [Fintype k2] [Fintype k3] [Fintype l2]
    [DecidableEq k1] [DecidableEq k2] [DecidableEq k3]
    [DecidableEq l2]
    {Z1 : ℕ → OmegaSpace → k1 → ℝ}
    {Z2 : ℕ → OmegaSpace → l2 → ℝ}
    {Y2 : ℕ → OmegaSpace → k2 → ℝ}
    {Y3 : ℕ → OmegaSpace → k3 → ℝ}
    {e Y : ℕ → OmegaSpace → ℝ}
    {b : (k1 ⊕ (k2 ⊕ k3)) → ℝ}
    [Fact (0 < Fintype.card k2)]
    {crit : ℝ} {alpha : ℝ≥0∞}
    (hcrit : (chiSquared (Fintype.card k2)) (Set.Ioi crit) = alpha)
    (h : GMMSubsetEndogeneityObservedRowsConditions
      mu Z1 Z2 Y2 Y3 e Y b) :
    Tendsto
      (fun n => mu {omega |
        crit <
          gmmSubsetEndogeneityTwoStepStatOrZero
            (stackRegressors Z1 n omega)
            (stackRegressors Y2 n omega)
            (stackRegressors Y3 n omega)
            (stackRegressors Z2 n omega)
            (stackOutcomes Y n omega)})
      atTop (nhds alpha) :=
  chiSquaredTest_rejectionProb_tendsto_alpha_of_stat hcrit
    (gmmSubsetEndogeneityTwoStepStatOrZero_tendstoInDistribution_observedRows h)

/-- GMM endogeneity statistic, defined as the corresponding subset
overidentification criterion difference. -/
noncomputable def gmmEndogeneityStatOrZero
    (augmentedJ maintainedJ : ℝ) : ℝ :=
  gmmSubsetOveridentificationStatOrZero augmentedJ maintainedJ

/-- Generic Gaussian transfer engine for an endogeneity criterion difference.
The observed-row theorem above fixes Hansen's regressor and instrument blocks. -/
theorem gmmEndogeneityStatOrZero_tendstoInDistribution_chiSquared
    {OmegaSpace : Type*} [MeasurableSpace OmegaSpace]
    {mu : Measure OmegaSpace} [IsProbabilityMeasure mu]
    {df : ℕ} [Fact (0 < df)]
    {augmentedJ maintainedJ : ℕ → OmegaSpace → ℝ}
    {T : ℕ → OmegaSpace → Fin df → ℝ}
    {Vhat : ℕ → OmegaSpace → Matrix (Fin df) (Fin df) ℝ}
    {V : Matrix (Fin df) (Fin df) ℝ}
    (hT : TendstoInDistribution T atTop
      (fun z : EuclideanSpace ℝ (Fin df) => z.ofLp) (fun _ => mu)
      (multivariateGaussian 0 V))
    (hV_meas : ∀ n, AEStronglyMeasurable (Vhat n) mu)
    (hV : TendstoInMeasure mu Vhat atTop (fun _ => V))
    (hV_posDef : V.PosDef)
    (hbridge : TendstoInMeasure mu
      (fun n omega =>
        gmmEndogeneityStatOrZero
            (augmentedJ n omega) (maintainedJ n omega) -
          criterionJStatOrZero (T n omega) (Vhat n omega))
      atTop (fun _ => 0))
    (hC_meas : ∀ n, AEMeasurable
      (fun omega => gmmEndogeneityStatOrZero
        (augmentedJ n omega) (maintainedJ n omega)) mu) :
    TendstoInDistribution
      (fun n omega => gmmEndogeneityStatOrZero
        (augmentedJ n omega) (maintainedJ n omega))
      atTop (fun x : ℝ => x) (fun _ => mu) (chiSquared df) := by
  simpa [gmmEndogeneityStatOrZero] using
    gmmSubsetOveridentificationStatOrZero_tendstoInDistribution_of_gaussian
      (mu := mu) (df := df)
      (fullJ := augmentedJ) (maintainedJ := maintainedJ)
      (T := T) (Vhat := Vhat) (V := V)
      hT hV_meas hV hV_posDef hbridge hC_meas

/-- Size form of Hansen Theorem 13.16. -/
theorem gmmEndogeneityTest_rejectionProb_tendsto_alpha
    {OmegaSpace : Type*} [MeasurableSpace OmegaSpace]
    {mu : Measure OmegaSpace} [IsProbabilityMeasure mu]
    {df : ℕ} [Fact (0 < df)]
    {C : ℕ → OmegaSpace → ℝ} {crit : ℝ} {alpha : ℝ≥0∞}
    (hcrit : (chiSquared df) (Set.Ioi crit) = alpha)
    (hC : TendstoInDistribution C atTop (fun x : ℝ => x)
      (fun _ => mu) (chiSquared df)) :
    Tendsto (fun n => mu {omega | crit < C n omega}) atTop
      (nhds alpha) :=
  chiSquaredTest_rejectionProb_tendsto_alpha_of_stat hcrit hC

/-- GMM subset-endogeneity statistic, again represented by a subset
overidentification criterion difference. -/
noncomputable def gmmSubsetEndogeneityStatOrZero
    (augmentedJ maintainedJ : ℝ) : ℝ :=
  gmmSubsetOveridentificationStatOrZero augmentedJ maintainedJ

/-- Generic Gaussian transfer engine for a subset-endogeneity criterion
difference. The observed-row theorem above fixes Hansen's `Y₂` and `Y₃`
blocks. -/
theorem gmmSubsetEndogeneityStatOrZero_tendstoInDistribution_chiSquared
    {OmegaSpace : Type*} [MeasurableSpace OmegaSpace]
    {mu : Measure OmegaSpace} [IsProbabilityMeasure mu]
    {df : ℕ} [Fact (0 < df)]
    {augmentedJ maintainedJ : ℕ → OmegaSpace → ℝ}
    {T : ℕ → OmegaSpace → Fin df → ℝ}
    {Vhat : ℕ → OmegaSpace → Matrix (Fin df) (Fin df) ℝ}
    {V : Matrix (Fin df) (Fin df) ℝ}
    (hT : TendstoInDistribution T atTop
      (fun z : EuclideanSpace ℝ (Fin df) => z.ofLp) (fun _ => mu)
      (multivariateGaussian 0 V))
    (hV_meas : ∀ n, AEStronglyMeasurable (Vhat n) mu)
    (hV : TendstoInMeasure mu Vhat atTop (fun _ => V))
    (hV_posDef : V.PosDef)
    (hbridge : TendstoInMeasure mu
      (fun n omega =>
        gmmSubsetEndogeneityStatOrZero
            (augmentedJ n omega) (maintainedJ n omega) -
          criterionJStatOrZero (T n omega) (Vhat n omega))
      atTop (fun _ => 0))
    (hC_meas : ∀ n, AEMeasurable
      (fun omega => gmmSubsetEndogeneityStatOrZero
        (augmentedJ n omega) (maintainedJ n omega)) mu) :
    TendstoInDistribution
      (fun n omega => gmmSubsetEndogeneityStatOrZero
        (augmentedJ n omega) (maintainedJ n omega))
      atTop (fun x : ℝ => x) (fun _ => mu) (chiSquared df) := by
  simpa [gmmSubsetEndogeneityStatOrZero] using
    gmmSubsetOveridentificationStatOrZero_tendstoInDistribution_of_gaussian
      (mu := mu) (df := df)
      (fullJ := augmentedJ) (maintainedJ := maintainedJ)
      (T := T) (Vhat := Vhat) (V := V)
      hT hV_meas hV hV_posDef hbridge hC_meas

/-- Size form of Hansen Theorem 13.17. -/
theorem gmmSubsetEndogeneityTest_rejectionProb_tendsto_alpha
    {OmegaSpace : Type*} [MeasurableSpace OmegaSpace]
    {mu : Measure OmegaSpace} [IsProbabilityMeasure mu]
    {df : ℕ} [Fact (0 < df)]
    {C : ℕ → OmegaSpace → ℝ} {crit : ℝ} {alpha : ℝ≥0∞}
    (hcrit : (chiSquared df) (Set.Ioi crit) = alpha)
    (hC : TendstoInDistribution C atTop (fun x : ℝ => x)
      (fun _ => mu) (chiSquared df)) :
    Tendsto (fun n => mu {omega | crit < C n omega}) atTop
      (nhds alpha) :=
  chiSquaredTest_rejectionProb_tendsto_alpha_of_stat hcrit hC

end HansenEconometrics
