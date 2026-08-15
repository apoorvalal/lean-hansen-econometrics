import HansenEconometrics.Chapter13GMM.Primitives
import HansenEconometrics.Chapter12InstrumentalVariables.Basic

/-!
# Chapter 13 — Generalized Method of Moments

This file gives the textbook-facing linear GMM definitions and results.
Generic weighted-moment optimization, linearization, and covariance algebra is
in `HansenEconometrics.Chapter13GMM.Primitives`.

The current public surface includes:

* `gmmMoment`, `gmmCriterion`, and the GMM Gram and cross moments;
* base, Star, and OrZero forms of the one-step linear GMM estimator;
* Hansen Theorem 13.1, which identifies the unique criterion minimizer;
* Hansen Theorem 13.2, which identifies GMM with 2SLS and just-identified IV;
* the sandwich covariance and efficient-GMM comparison in Theorems 13.4–13.5.

The criterion omits Hansen's positive scalar factor `n`. This does not change
its minimizer.
-/

open scoped Matrix

namespace HansenEconometrics

open Matrix

variable {n k l : Type*}
variable [Fintype n] [Fintype k] [Fintype l] [DecidableEq k]

/-- Sample linear moment vector `Z'(Y - Xb)`. -/
noncomputable def gmmMoment (X : Matrix n k ℝ) (Z : Matrix n l ℝ)
    (y : n → ℝ) (b : k → ℝ) : l → ℝ :=
  Zᵀ *ᵥ (y - X *ᵥ b)

omit [Fintype l] [DecidableEq k] in
/-- The sample moment is affine in the coefficient. -/
theorem gmmMoment_eq_linear (X : Matrix n k ℝ) (Z : Matrix n l ℝ)
    (y : n → ℝ) (b : k → ℝ) :
    gmmMoment X Z y b = Zᵀ *ᵥ y - (Zᵀ * X) *ᵥ b := by
  unfold gmmMoment
  rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec]

omit [Fintype l] [DecidableEq k] in
/-- A normalized instrument cross moment commutes with subtracting a linear
predictor. This is the shared finite-sample score identity used by the
two-step and specification-test developments. -/
theorem sampleCrossMoment_sub_mulVec
    (Z : Matrix n l ℝ) (X : Matrix n k ℝ) (u : n → ℝ) (d : k → ℝ) :
    sampleCrossMoment Z (u - X *ᵥ d) =
      sampleCrossMoment Z u - sampleQZX Z X *ᵥ d := by
  unfold sampleCrossMoment sampleQZX
  rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec]
  ext a
  simp only [Pi.smul_apply, Pi.sub_apply, Matrix.smul_mulVec, smul_eq_mul]
  ring

/-- GMM Gram matrix `X'Z W Z'X`. -/
noncomputable abbrev gmmGram (X : Matrix n k ℝ) (Z : Matrix n l ℝ)
    (W : Matrix l l ℝ) : Matrix k k ℝ :=
  LinearGMM.gram (Zᵀ * X) W

omit [Fintype k] [DecidableEq k] in
/-- Textbook formula for the GMM Gram matrix. -/
@[simp]
theorem gmmGram_eq_formula (X : Matrix n k ℝ) (Z : Matrix n l ℝ)
    (W : Matrix l l ℝ) :
    gmmGram X Z W = Xᵀ * Z * W * Zᵀ * X := by
  simp [gmmGram, LinearGMM.gram, Matrix.transpose_mul, Matrix.mul_assoc]

/-- GMM cross moment `X'Z W Z'Y`. -/
noncomputable def gmmCross (X : Matrix n k ℝ) (Z : Matrix n l ℝ)
    (y : n → ℝ) (W : Matrix l l ℝ) : k → ℝ :=
  LinearGMM.cross (Zᵀ * X) W (Zᵀ *ᵥ y)

omit [Fintype k] [DecidableEq k] in
/-- Textbook formula for the GMM cross moment. -/
@[simp]
theorem gmmCross_eq_formula (X : Matrix n k ℝ) (Z : Matrix n l ℝ)
    (y : n → ℝ) (W : Matrix l l ℝ) :
    gmmCross X Z y W = (Xᵀ * Z * W) *ᵥ (Zᵀ *ᵥ y) := by
  simp [gmmCross, LinearGMM.cross, Matrix.transpose_mul, Matrix.mul_assoc]

/-- Hansen's linear GMM criterion, without its positive scalar factor `n`. -/
noncomputable def gmmCriterion (X : Matrix n k ℝ) (Z : Matrix n l ℝ)
    (y : n → ℝ) (W : Matrix l l ℝ) (b : k → ℝ) : ℝ :=
  LinearGMM.criterion (Zᵀ * X) (Zᵀ *ᵥ y) W b

omit [DecidableEq k] in
/-- The generic linear criterion agrees with the textbook moment formula. -/
@[simp]
theorem gmmCriterion_eq_moment (X : Matrix n k ℝ) (Z : Matrix n l ℝ)
    (y : n → ℝ) (W : Matrix l l ℝ) (b : k → ℝ) :
    gmmCriterion X Z y W b =
      gmmMoment X Z y b ⬝ᵥ (W *ᵥ gmmMoment X Z y b) := by
  unfold gmmCriterion LinearGMM.criterion
  rw [← gmmMoment_eq_linear X Z y b]

/-- Hansen equation (13.6): the base one-step linear GMM estimator. -/
noncomputable def gmmBeta (X : Matrix n k ℝ) (Z : Matrix n l ℝ)
    (y : n → ℝ) (W : Matrix l l ℝ) [Invertible (gmmGram X Z W)] :
    k → ℝ :=
  LinearGMM.beta (Zᵀ * X) (Zᵀ *ᵥ y) W

/-- Star GMM estimator, totalized with `Matrix.nonsingInv`. -/
noncomputable def gmmBetaStar (X : Matrix n k ℝ) (Z : Matrix n l ℝ)
    (y : n → ℝ) (W : Matrix l l ℝ) : k → ℝ :=
  LinearGMM.betaStar (Zᵀ * X) (Zᵀ *ᵥ y) W

/-- Textbook-facing totalized GMM estimator. -/
noncomputable def gmmBetaOrZero (X : Matrix n k ℝ) (Z : Matrix n l ℝ)
    (y : n → ℝ) (W : Matrix l l ℝ) : k → ℝ :=
  LinearGMM.betaOrZero (Zᵀ * X) (Zᵀ *ᵥ y) W

/-- The base and Star GMM estimators agree on nonsingular Gram matrices. -/
theorem gmmBetaStar_eq_gmmBeta (X : Matrix n k ℝ) (Z : Matrix n l ℝ)
    (y : n → ℝ) (W : Matrix l l ℝ) [Invertible (gmmGram X Z W)] :
    gmmBetaStar X Z y W = gmmBeta X Z y W := by
  exact LinearGMM.betaStar_eq_beta (Zᵀ * X) (Zᵀ *ᵥ y) W

/-- The OrZero and Star GMM estimators are identical. -/
@[simp]
theorem gmmBetaOrZero_eq_gmmBetaStar (X : Matrix n k ℝ) (Z : Matrix n l ℝ)
    (y : n → ℝ) (W : Matrix l l ℝ) :
    gmmBetaOrZero X Z y W = gmmBetaStar X Z y W := by
  exact LinearGMM.betaOrZero_eq_betaStar (Zᵀ * X) (Zᵀ *ᵥ y) W

/-- A nonzero scalar rescaling of the weight does not change Star GMM. -/
theorem gmmBetaStar_smul_weight (c : ℝ) (X : Matrix n k ℝ)
    (Z : Matrix n l ℝ) (y : n → ℝ) (W : Matrix l l ℝ)
    (hc : c ≠ 0) :
    gmmBetaStar X Z y (c • W) = gmmBetaStar X Z y W :=
  LinearGMM.betaStar_smul_weight c (Zᵀ * X) (Zᵀ *ᵥ y) W hc

/-- A nonzero scalar rescaling of the weight does not change textbook-facing
OrZero GMM. -/
theorem gmmBetaOrZero_smul_weight (c : ℝ) (X : Matrix n k ℝ)
    (Z : Matrix n l ℝ) (y : n → ℝ) (W : Matrix l l ℝ)
    (hc : c ≠ 0) :
    gmmBetaOrZero X Z y (c • W) = gmmBetaOrZero X Z y W := by
  simp only [gmmBetaOrZero_eq_gmmBetaStar]
  exact gmmBetaStar_smul_weight c X Z y W hc

/-- On a nonsingular Gram matrix, OrZero GMM agrees with base GMM. -/
theorem gmmBetaOrZero_eq_gmmBeta (X : Matrix n k ℝ) (Z : Matrix n l ℝ)
    (y : n → ℝ) (W : Matrix l l ℝ) [Invertible (gmmGram X Z W)] :
    gmmBetaOrZero X Z y W = gmmBeta X Z y W := by
  rw [gmmBetaOrZero_eq_gmmBetaStar, gmmBetaStar_eq_gmmBeta]

/-! ## Hansen Theorem 13.1 -/

/-- **Hansen Theorem 13.1 (existence).** The one-step GMM estimator minimizes
the GMM criterion. -/
theorem gmmCriterion_gmmBeta_le (X : Matrix n k ℝ) (Z : Matrix n l ℝ)
    (y : n → ℝ) (W : Matrix l l ℝ) (b : k → ℝ)
    [Invertible (gmmGram X Z W)] (hW : W.PosSemidef) :
    gmmCriterion X Z y W (gmmBeta X Z y W) ≤
      gmmCriterion X Z y W b := by
  exact LinearGMM.beta_minimizes (Zᵀ * X) (Zᵀ *ᵥ y) W b hW

/-- **Hansen Theorem 13.1 (existence),** packaged as `IsMinOn`. -/
theorem gmmBeta_isMinOn (X : Matrix n k ℝ) (Z : Matrix n l ℝ)
    (y : n → ℝ) (W : Matrix l l ℝ) [Invertible (gmmGram X Z W)]
    (hW : W.PosSemidef) :
    IsMinOn (gmmCriterion X Z y W) Set.univ (gmmBeta X Z y W) := by
  exact LinearGMM.beta_isMinOn (Zᵀ * X) (Zᵀ *ᵥ y) W hW

/-- **Hansen Theorem 13.1 (uniqueness).** A coefficient that attains the
minimum equals the one-step GMM estimator. -/
theorem gmmBeta_eq_of_minimizer (X : Matrix n k ℝ) (Z : Matrix n l ℝ)
    (y : n → ℝ) (W : Matrix l l ℝ) (b : k → ℝ)
    [Invertible (gmmGram X Z W)] (hW : W.PosSemidef)
    (hb : gmmCriterion X Z y W b =
      gmmCriterion X Z y W (gmmBeta X Z y W)) :
    b = gmmBeta X Z y W := by
  exact LinearGMM.beta_eq_of_minimizer (Zᵀ * X) (Zᵀ *ᵥ y) W b hW hb

/-! ## Hansen Theorem 13.2 -/

section TwoSLS

variable [DecidableEq l]

omit [Fintype k] [DecidableEq k] in
/-- With the inverse instrument Gram as weight, the GMM Gram is the Star
2SLS moment matrix. -/
@[simp]
theorem gmmGram_twoSLSWeight_eq (X : Matrix n k ℝ) (Z : Matrix n l ℝ) :
    gmmGram X Z ((Zᵀ * Z)⁻¹) = twoSLSMomentMatrixStar Z X := by
  simp [gmmGram, LinearGMM.gram, twoSLSMomentMatrixStar,
    instrumentProjectionStar, Matrix.transpose_mul, Matrix.mul_assoc]

omit [Fintype k] [DecidableEq k] in
/-- With the inverse instrument Gram as weight, the GMM cross moment is the
Star 2SLS moment vector. -/
@[simp]
theorem gmmCross_twoSLSWeight_eq (X : Matrix n k ℝ) (Z : Matrix n l ℝ)
    (y : n → ℝ) :
    gmmCross X Z y ((Zᵀ * Z)⁻¹) = twoSLSMomentVectorStar Z X y := by
  simp [gmmCross, LinearGMM.cross, twoSLSMomentVectorStar,
    instrumentProjectionStar, Matrix.transpose_mul, Matrix.mulVec_mulVec,
    Matrix.mul_assoc]

/-- **Hansen Theorem 13.2 (2SLS, Star form).** GMM with weight
`(Z'Z)⁻¹` equals 2SLS. -/
theorem gmmBetaStar_eq_twoSLSBetaStar (X : Matrix n k ℝ)
    (Z : Matrix n l ℝ) (y : n → ℝ) :
    gmmBetaStar X Z y ((Zᵀ * Z)⁻¹) = twoSLSBetaStar Z X y := by
  unfold gmmBetaStar LinearGMM.betaStar twoSLSBetaStar
  change (gmmGram X Z ((Zᵀ * Z)⁻¹))⁻¹ *ᵥ
      gmmCross X Z y ((Zᵀ * Z)⁻¹) =
    (twoSLSMomentMatrixStar Z X)⁻¹ *ᵥ twoSLSMomentVectorStar Z X y
  rw [gmmGram_twoSLSWeight_eq, gmmCross_twoSLSWeight_eq]

/-- **Hansen Theorem 13.2 (2SLS, textbook-facing form).** Totalized GMM with
weight `(Z'Z)⁻¹` equals totalized 2SLS, including singular designs. -/
@[simp]
theorem gmmBetaOrZero_eq_twoSLSBetaOrZero (X : Matrix n k ℝ)
    (Z : Matrix n l ℝ) (y : n → ℝ) :
    gmmBetaOrZero X Z y ((Zᵀ * Z)⁻¹) = twoSLSBetaOrZero Z X y := by
  rw [gmmBetaOrZero_eq_gmmBetaStar, twoSLSBetaOrZero_eq_twoSLSBetaStar,
    gmmBetaStar_eq_twoSLSBetaStar]

/-- **Hansen Theorem 13.2 (2SLS, nonsingular form).** With the ordinary
inverse weight, textbook-facing GMM equals the ordinary 2SLS estimator. -/
theorem gmmBetaOrZero_eq_twoSLSBeta (X : Matrix n k ℝ)
    (Z : Matrix n l ℝ) (y : n → ℝ) [Invertible (Zᵀ * Z)]
    [Invertible (twoSLSMomentMatrix Z X)] :
    gmmBetaOrZero X Z y (⅟ (Zᵀ * Z)) = twoSLSBeta Z X y := by
  rw [Matrix.invOf_eq_nonsing_inv, gmmBetaOrZero_eq_twoSLSBetaOrZero,
    twoSLSBetaOrZero_eq_twoSLSBeta]

end TwoSLS

/-- **Hansen Theorem 13.2 (just-identified form).** If the moment map is
square and nonsingular, GMM equals IV for every invertible weight. -/
theorem gmmBetaOrZero_eq_ivBeta_of_justIdentified (X Z : Matrix n k ℝ)
    (y : n → ℝ) (W : Matrix k k ℝ) [Invertible (Zᵀ * X)]
    [Invertible W] :
    gmmBetaOrZero X Z y W = ivBeta Z X y := by
  exact LinearGMM.betaOrZero_eq_direct (Zᵀ * X) (Zᵀ *ᵥ y) W

/-! ## Population covariance formulas for Theorems 13.3–13.5 -/

/-- Population GMM Gram matrix `Q'WQ`. -/
noncomputable abbrev gmmPopulationGram (Q : Matrix l k ℝ)
    (W : Matrix l l ℝ) : Matrix k k ℝ :=
  LinearGMM.gram Q W

/-- Hansen equation (13.7), the linear GMM sandwich covariance. -/
noncomputable abbrev gmmAsymptoticVariance (Q : Matrix l k ℝ)
    (W Omega : Matrix l l ℝ) [Invertible (gmmPopulationGram Q W)] :
    Matrix k k ℝ :=
  LinearGMM.asymptoticVariance Q W Omega

/-- Star form of Hansen equation (13.7), available without a typeclass
inverse. -/
noncomputable abbrev gmmAsymptoticVarianceStar (Q : Matrix l k ℝ)
    (W Omega : Matrix l l ℝ) : Matrix k k ℝ :=
  LinearGMM.asymptoticVarianceStar Q W Omega

/-- The Star and base population GMM covariances agree under identification. -/
theorem gmmAsymptoticVarianceStar_eq_asymptoticVariance
    (Q : Matrix l k ℝ) (W Omega : Matrix l l ℝ)
    [Invertible (gmmPopulationGram Q W)] :
    gmmAsymptoticVarianceStar Q W Omega =
      gmmAsymptoticVariance Q W Omega :=
  LinearGMM.asymptoticVarianceStar_eq_asymptoticVariance Q W Omega

/-- Hansen equation (13.7) in its displayed symmetric-weight form. -/
theorem gmmAsymptoticVariance_eq_formula (Q : Matrix l k ℝ)
    (W Omega : Matrix l l ℝ) [Invertible (gmmPopulationGram Q W)]
    (hW : W.PosSemidef) :
    gmmAsymptoticVariance Q W Omega =
      ⅟ (gmmPopulationGram Q W) * Qᵀ * W * Omega * W * Q *
        ⅟ (gmmPopulationGram Q W) := by
  exact LinearGMM.asymptoticVariance_eq_hansen Q W Omega hW

/-- The GMM sandwich covariance is positive semidefinite when the moment
covariance is positive semidefinite. -/
theorem gmmAsymptoticVariance_posSemidef (Q : Matrix l k ℝ)
    (W Omega : Matrix l l ℝ) [Invertible (gmmPopulationGram Q W)]
    (hOmega : Omega.PosSemidef) :
    (gmmAsymptoticVariance Q W Omega).PosSemidef :=
  LinearGMM.asymptoticVariance_posSemidef Q W Omega hOmega

/-- The Star GMM sandwich covariance is positive semidefinite when the moment
covariance is positive semidefinite. -/
theorem gmmAsymptoticVarianceStar_posSemidef (Q : Matrix l k ℝ)
    (W Omega : Matrix l l ℝ) (hOmega : Omega.PosSemidef) :
    (gmmAsymptoticVarianceStar Q W Omega).PosSemidef :=
  LinearGMM.asymptoticVarianceStar_posSemidef Q W Omega hOmega

/-- **Hansen Theorem 13.4 (covariance formula).** With efficient weight
`Omega⁻¹`, the sandwich covariance is `(Q'Omega⁻¹Q)⁻¹`. -/
theorem gmmAsymptoticVariance_efficient (Q : Matrix l k ℝ)
    (Omega : Matrix l l ℝ) [DecidableEq l] [Invertible Omega]
    [Invertible (gmmPopulationGram Q (⅟Omega))]
    (hOmega : Omega.PosSemidef) :
    gmmAsymptoticVariance Q (⅟Omega) Omega =
      ⅟ (gmmPopulationGram Q (⅟Omega)) :=
  LinearGMM.asymptoticVariance_efficient Q Omega hOmega

/-- **Hansen Theorem 13.4 (Star covariance formula).** With a
positive-definite moment covariance and a full-rank derivative, efficient GMM
has covariance `(Q'Omega⁻¹Q)⁻¹`. -/
theorem gmmAsymptoticVarianceStar_efficient (Q : Matrix l k ℝ)
    (Omega : Matrix l l ℝ) [DecidableEq l] (hOmega : Omega.PosDef)
    (hQ : Function.Injective Q.mulVec) :
    gmmAsymptoticVarianceStar Q Omega⁻¹ Omega =
      (gmmPopulationGram Q Omega⁻¹)⁻¹ :=
  LinearGMM.asymptoticVarianceStar_efficient Q Omega hOmega hQ

/-- **Hansen Theorem 13.6 (population core).** If the score covariance is a
positive scalar multiple of the instrument Gram, the 2SLS weight attains the
efficient GMM covariance. -/
theorem gmmAsymptoticVarianceStar_twoSLSWeight_efficient
    (Q : Matrix l k ℝ) (QZZ Omega : Matrix l l ℝ) (sigma2 : ℝ)
    [DecidableEq l] (hOmega : Omega.PosDef)
    (hQ : Function.Injective Q.mulVec)
    (hHomo : Omega = sigma2 • QZZ) (hsigma2 : sigma2 ≠ 0) :
    gmmAsymptoticVarianceStar Q QZZ⁻¹ Omega =
      (gmmPopulationGram Q Omega⁻¹)⁻¹ := by
  have hweight : QZZ⁻¹ = sigma2 • Omega⁻¹ := by
    rw [hHomo, nonsingInv_smul]
    simp [smul_smul, hsigma2]
  calc
    gmmAsymptoticVarianceStar Q QZZ⁻¹ Omega =
        gmmAsymptoticVarianceStar Q (sigma2 • Omega⁻¹) Omega := by
          rw [hweight]
    _ = gmmAsymptoticVarianceStar Q Omega⁻¹ Omega :=
      LinearGMM.asymptoticVarianceStar_smul_weight
        sigma2 Q Omega⁻¹ Omega hsigma2
    _ = (gmmPopulationGram Q Omega⁻¹)⁻¹ :=
      gmmAsymptoticVarianceStar_efficient Q Omega hOmega hQ

/-- **Hansen Theorem 13.5.** The covariance of any identified linear GMM
estimator dominates the efficient GMM covariance in Loewner order. -/
theorem gmmAsymptoticVariance_sub_efficient_posSemidef
    (Q : Matrix l k ℝ) (W Omega : Matrix l l ℝ) [DecidableEq l]
    [Invertible Omega] [Invertible (gmmPopulationGram Q (⅟Omega))]
    [Invertible (gmmPopulationGram Q W)] (hOmega : Omega.PosSemidef) :
    (gmmAsymptoticVariance Q W Omega -
      gmmAsymptoticVariance Q (⅟Omega) Omega).PosSemidef :=
  LinearGMM.asymptoticVariance_sub_efficient_posSemidef Q W Omega hOmega

end HansenEconometrics
