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
* Hansen Theorem 13.1, which identifies the unique criterion minimizer.

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

end HansenEconometrics
