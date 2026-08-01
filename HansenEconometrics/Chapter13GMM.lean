import HansenEconometrics.LinearAlgebraUtils
import HansenEconometrics.Chapter2LinearProjection

/-!
# Chapter 13 — Generalized Method of Moments

This file begins the formalization of Hansen's Chapter 13. The current public surface is
**Theorem 13.1**: for the overidentified linear IV / moment-equation model with moment function
`gᵢ(β) = Zᵢ(Yᵢ − Xᵢ'β)`, the one-step GMM estimator `gmmBeta = (X'Z W Z'X)⁻¹ (X'Z W Z'Y)`
(Hansen equation 13.6) is the unique minimizer of the GMM criterion
`gmmCriterion = (Z'(Y − Xβ))' W (Z'(Y − Xβ))`.

* `gmmCriterion` — the GMM criterion kernel. Hansen's `n·` prefactor is omitted: it is a
  positive scalar and does not affect the minimizer (Hansen notes the estimator "depends on `W`
  only up to scale"). This mirrors `sumSquaredErrors`, which omits `1/n`.
* `gmmBeta` — the closed-form one-step GMM estimator (Hansen eq. 13.6).
* `gmmCriterion_gmmBeta_le` / `gmmBeta_isMinOn` — Theorem 13.1, existence half: `gmmBeta`
  minimizes the criterion when `W` is positive semidefinite.
* `gmmBeta_eq_of_minimizer` — Theorem 13.1, uniqueness half. Positive semidefiniteness of `W`
  and the invertibility required by `gmmBeta` make the GMM Gram matrix positive definite.

Hansen assumes `W > 0`. The results below use the weaker Mathlib condition `W.PosSemidef`;
invertibility of `X'Z W Z'X` supplies the strictness needed for uniqueness.

The proof reduces the GMM criterion to the Chapter 2 abstract quadratic
`linearProjectionMSE QXX QXY QYY` with `QXX = X'Z W Z'X`, `QXY = X'Z W Z'Y`,
`QYY = (Z'Y)' W (Z'Y)` — exactly as Chapter 3's Theorem 3.1 reduces OLS — so
`gmmBeta = linearProjectionBeta QXX QXY` and the Chapter 2 minimization theorems apply directly.

Theorem 13.2 can now reuse the Chapter 12 IV and 2SLS estimators. It is deferred to the next
Chapter 13 change. The asymptotic GMM results (Theorems 13.3+) depend on Chapter 12's
`Assumption 12.2`. Detailed status lives in `inventory/ch13-inventory.md`.
-/

open scoped Matrix

namespace HansenEconometrics

open Matrix

variable {n k l : Type*}
variable [Fintype n] [Fintype k] [Fintype l] [DecidableEq k]

/-- Hansen §13.6: the GMM criterion kernel `(Z'(Y − Xβ))' W (Z'(Y − Xβ))`.

Hansen writes `J(β) = n (Z'Y − Z'Xβ)' W (Z'Y − Z'Xβ)`; the positive scalar `n` is omitted here
because it does not affect the minimizer (cf. `sumSquaredErrors`, which omits `1/n`). -/
noncomputable def gmmCriterion (X : Matrix n k ℝ) (Z : Matrix n l ℝ) (y : n → ℝ)
    (W : Matrix l l ℝ) (b : k → ℝ) : ℝ :=
  (Zᵀ *ᵥ (y - X *ᵥ b)) ⬝ᵥ (W *ᵥ (Zᵀ *ᵥ (y - X *ᵥ b)))

/-- Hansen Theorem 13.1 / equation (13.6): the closed-form one-step linear GMM estimator
`β̂_gmm = (X'Z W Z'X)⁻¹ (X'Z W Z'Y)`. -/
noncomputable def gmmBeta (X : Matrix n k ℝ) (Z : Matrix n l ℝ) (y : n → ℝ)
    (W : Matrix l l ℝ) [Invertible (Xᵀ * Z * W * Zᵀ * X)] : k → ℝ :=
  ⅟ (Xᵀ * Z * W * Zᵀ * X) *ᵥ ((Xᵀ * Z * W) *ᵥ (Zᵀ *ᵥ y))

omit [Fintype k] [DecidableEq k] in
/-- A positive-semidefinite weight matrix induces a positive-semidefinite GMM Gram matrix. -/
private lemma gmmGram_posSemidef (X : Matrix n k ℝ) (Z : Matrix n l ℝ) (W : Matrix l l ℝ)
    [Finite k] (hW : W.PosSemidef) :
    (Xᵀ * Z * W * Zᵀ * X).PosSemidef := by
  simpa [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.mul_assoc] using
    hW.conjTranspose_mul_mul_same (Zᵀ * X)

omit [DecidableEq k] in
/-- Bridge: the GMM criterion equals the Chapter 2 abstract quadratic `linearProjectionMSE` with
`QXX = X'Z W Z'X`, `QXY = X'Z W Z'Y`, `QYY = (Z'Y)' W (Z'Y)`. Private — file-local notation
bridge, reused only inside this file (cf. `sumSquaredErrors_eq_linearProjectionMSE`). -/
private lemma gmmCriterion_eq_linearProjectionMSE (X : Matrix n k ℝ) (Z : Matrix n l ℝ)
    (y : n → ℝ) (W : Matrix l l ℝ) (hW : W.PosSemidef) (b : k → ℝ) :
    gmmCriterion X Z y W b =
      linearProjectionMSE (Xᵀ * Z * W * Zᵀ * X) ((Xᵀ * Z * W) *ᵥ (Zᵀ *ᵥ y))
        ((Zᵀ *ᵥ y) ⬝ᵥ (W *ᵥ (Zᵀ *ᵥ y))) b := by
  have hWsymm : Wᵀ = W :=
    (Matrix.conjTranspose_eq_transpose_of_trivial W).symm.trans hW.isHermitian.eq
  have hr : Zᵀ *ᵥ (y - X *ᵥ b) = (Zᵀ *ᵥ y) - ((Zᵀ * X) *ᵥ b) := by
    rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec]
  have hquad : ((Zᵀ * X) *ᵥ b) ⬝ᵥ (W *ᵥ ((Zᵀ * X) *ᵥ b)) =
      b ⬝ᵥ ((Xᵀ * Z * W * Zᵀ * X) *ᵥ b) := by
    simpa [Matrix.mul_assoc] using
      quadraticForm_mulVec_eq_pullback_rect (Zᵀ * X) W b
  have hcross : (Zᵀ *ᵥ y) ⬝ᵥ (W *ᵥ ((Zᵀ * X) *ᵥ b)) =
      b ⬝ᵥ ((Xᵀ * Z * W) *ᵥ (Zᵀ *ᵥ y)) := by
    have key : (Zᵀ *ᵥ y) ⬝ᵥ (W *ᵥ ((Zᵀ * X) *ᵥ b)) =
        (Wᵀ *ᵥ (Zᵀ *ᵥ y)) ⬝ᵥ ((Zᵀ * X) *ᵥ b) := by
      rw [Matrix.dotProduct_mulVec, vecMul_eq_mulVec_transpose]
    rw [key, hWsymm, Matrix.dotProduct_mulVec, vecMul_eq_mulVec_transpose, dotProduct_comm]
    congr 1
    rw [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  have hcross2 : ((Zᵀ * X) *ᵥ b) ⬝ᵥ (W *ᵥ (Zᵀ *ᵥ y)) =
      b ⬝ᵥ ((Xᵀ * Z * W) *ᵥ (Zᵀ *ᵥ y)) := by
    rw [dotProduct_comm, Matrix.dotProduct_mulVec, vecMul_eq_mulVec_transpose, dotProduct_comm]
    congr 1
    rw [Matrix.mulVec_mulVec, Matrix.transpose_mul, Matrix.transpose_transpose,
      Matrix.mulVec_mulVec, Matrix.mul_assoc]
  unfold gmmCriterion linearProjectionMSE
  simp only [hr]
  rw [Matrix.mulVec_sub, dotProduct_sub, sub_dotProduct, sub_dotProduct, hquad, hcross, hcross2]
  ring

/-- The GMM estimator coincides with the Chapter 2 projection coefficient for the GMM Gram
moments. Private bridge; holds by `rfl` thanks to the parenthesized `QXY` form. -/
private lemma gmmBeta_eq_linearProjectionBeta (X : Matrix n k ℝ) (Z : Matrix n l ℝ) (y : n → ℝ)
    (W : Matrix l l ℝ) [Invertible (Xᵀ * Z * W * Zᵀ * X)] :
    gmmBeta X Z y W =
      linearProjectionBeta (Xᵀ * Z * W * Zᵀ * X) ((Xᵀ * Z * W) *ᵥ (Zᵀ *ᵥ y)) :=
  rfl

/-- **Hansen Theorem 13.1 (existence half).** The one-step GMM estimator `gmmBeta` attains the
minimum of the GMM criterion: for any coefficient vector `b`, `J(gmmBeta) ≤ J(b)`. -/
theorem gmmCriterion_gmmBeta_le (X : Matrix n k ℝ) (Z : Matrix n l ℝ) (y : n → ℝ)
    (W : Matrix l l ℝ) (b : k → ℝ) [Invertible (Xᵀ * Z * W * Zᵀ * X)]
    (hW : W.PosSemidef) :
    gmmCriterion X Z y W (gmmBeta X Z y W) ≤ gmmCriterion X Z y W b := by
  have hQ := gmmGram_posSemidef X Z W hW
  rw [gmmCriterion_eq_linearProjectionMSE X Z y W hW b,
      gmmCriterion_eq_linearProjectionMSE X Z y W hW (gmmBeta X Z y W),
      gmmBeta_eq_linearProjectionBeta X Z y W]
  exact linearProjectionBeta_minimizes_MSE (Xᵀ * Z * W * Zᵀ * X) ((Xᵀ * Z * W) *ᵥ (Zᵀ *ᵥ y))
    ((Zᵀ *ᵥ y) ⬝ᵥ (W *ᵥ (Zᵀ *ᵥ y)))
    ((Matrix.conjTranspose_eq_transpose_of_trivial _).symm.trans hQ.isHermitian.eq)
    (by simpa using hQ.dotProduct_mulVec_nonneg) b

/-- **Hansen Theorem 13.1 (existence half), packaged as `IsMinOn`.** -/
theorem gmmBeta_isMinOn (X : Matrix n k ℝ) (Z : Matrix n l ℝ) (y : n → ℝ) (W : Matrix l l ℝ)
    [Invertible (Xᵀ * Z * W * Zᵀ * X)] (hW : W.PosSemidef) :
    IsMinOn (gmmCriterion X Z y W) Set.univ (gmmBeta X Z y W) := by
  intro b _
  exact gmmCriterion_gmmBeta_le X Z y W b hW

/-- **Hansen Theorem 13.1 (uniqueness half).** If `b` attains the minimum of the GMM criterion,
then `b = gmmBeta`. Requires a positive-semidefinite weight and an invertible GMM Gram matrix. -/
theorem gmmBeta_eq_of_minimizer (X : Matrix n k ℝ) (Z : Matrix n l ℝ) (y : n → ℝ)
    (W : Matrix l l ℝ) (b : k → ℝ) [Invertible (Xᵀ * Z * W * Zᵀ * X)]
    (hW : W.PosSemidef)
    (hb : gmmCriterion X Z y W b = gmmCriterion X Z y W (gmmBeta X Z y W)) :
    b = gmmBeta X Z y W := by
  have hQ := gmmGram_posSemidef X Z W hW
  have hQpd : (Xᵀ * Z * W * Zᵀ * X).PosDef :=
    hQ.posDef_iff_isUnit.mpr (isUnit_of_invertible _)
  rw [gmmCriterion_eq_linearProjectionMSE X Z y W hW b,
      gmmCriterion_eq_linearProjectionMSE X Z y W hW (gmmBeta X Z y W),
      gmmBeta_eq_linearProjectionBeta X Z y W] at hb
  rw [gmmBeta_eq_linearProjectionBeta X Z y W]
  exact linearProjectionBeta_eq_of_MSE_eq (Xᵀ * Z * W * Zᵀ * X) ((Xᵀ * Z * W) *ᵥ (Zᵀ *ᵥ y))
    ((Zᵀ *ᵥ y) ⬝ᵥ (W *ᵥ (Zᵀ *ᵥ y))) b
    ((Matrix.conjTranspose_eq_transpose_of_trivial _).symm.trans hQ.isHermitian.eq)
    (fun _ hv => by simpa using hQpd.dotProduct_mulVec_pos hv) hb

end HansenEconometrics
