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
  minimizes the criterion, under `W` symmetric positive semidefinite.
* `gmmBeta_eq_of_minimizer` — Theorem 13.1, uniqueness half, under `W` symmetric positive
  definite.

Hansen's weight-matrix assumption `W > 0` is encoded as `Wᵀ = W` together with positive
(semi)definiteness; the existence half uses only PSD, the uniqueness half uses PD.

The proof reduces the GMM criterion to the Chapter 2 abstract quadratic
`linearProjectionMSE QXX QXY QYY` with `QXX = X'Z W Z'X`, `QXY = X'Z W Z'Y`,
`QYY = (Z'Y)' W (Z'Y)` — exactly as Chapter 3's Theorem 3.1 reduces OLS — so
`gmmBeta = linearProjectionBeta QXX QXY` and the Chapter 2 minimization theorems apply directly.

The asymptotic GMM results (Theorems 13.3+) and the 13.2 bridge (`2SLS = one-step GMM`) depend
on Chapter 12's `Assumption 12.2` and are deferred. Detailed status lives in
`inventory/ch13-inventory.md`.
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
/-- The GMM Gram matrix `X'Z W Z'X` is symmetric when `W` is. -/
private lemma gmm_QXX_transpose (X : Matrix n k ℝ) (Z : Matrix n l ℝ) (W : Matrix l l ℝ)
    (hWsymm : Wᵀ = W) :
    (Xᵀ * Z * W * Zᵀ * X)ᵀ = Xᵀ * Z * W * Zᵀ * X := by
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, hWsymm, Matrix.mul_assoc]

omit [DecidableEq k] in
/-- The GMM Gram quadratic form pulls back through `Z'X` to a `W`-quadratic form. -/
private lemma gmm_QXX_quad (X : Matrix n k ℝ) (Z : Matrix n l ℝ) (W : Matrix l l ℝ) (v : k → ℝ) :
    v ⬝ᵥ ((Xᵀ * Z * W * Zᵀ * X) *ᵥ v) = ((Zᵀ * X) *ᵥ v) ⬝ᵥ (W *ᵥ ((Zᵀ * X) *ᵥ v)) := by
  have hM : (Xᵀ * Z * W * Zᵀ * X) = (Zᵀ * X)ᵀ * W * (Zᵀ * X) := by
    rw [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc (Xᵀ * Z * W) Zᵀ X]
  rw [hM, quadraticForm_mulVec_eq_pullback_rect (Zᵀ * X) W v]

omit [DecidableEq k] in
/-- The GMM Gram quadratic form is nonnegative when `W` is positive semidefinite. -/
private lemma gmm_QXX_nonneg (X : Matrix n k ℝ) (Z : Matrix n l ℝ) (W : Matrix l l ℝ)
    (hWpsd : ∀ u : l → ℝ, 0 ≤ u ⬝ᵥ (W *ᵥ u)) (v : k → ℝ) :
    0 ≤ v ⬝ᵥ ((Xᵀ * Z * W * Zᵀ * X) *ᵥ v) := by
  rw [gmm_QXX_quad X Z W v]
  exact hWpsd ((Zᵀ * X) *ᵥ v)

/-- The GMM Gram quadratic form is positive definite when `W` is positive definite and the Gram
matrix is invertible (so `Z'X v = 0 ⇒ v = 0`). -/
private lemma gmm_QXX_pos (X : Matrix n k ℝ) (Z : Matrix n l ℝ) (W : Matrix l l ℝ)
    [Invertible (Xᵀ * Z * W * Zᵀ * X)]
    (hWpd : ∀ u : l → ℝ, u ≠ 0 → 0 < u ⬝ᵥ (W *ᵥ u)) (v : k → ℝ) (hv : v ≠ 0) :
    0 < v ⬝ᵥ ((Xᵀ * Z * W * Zᵀ * X) *ᵥ v) := by
  rw [gmm_QXX_quad X Z W v]
  by_cases hzero : (Zᵀ * X) *ᵥ v = 0
  · exfalso
    have hQv : (Xᵀ * Z * W * Zᵀ * X) *ᵥ v = 0 := by
      have hfact : (Xᵀ * Z * W * Zᵀ * X) *ᵥ v = (Xᵀ * Z * W) *ᵥ ((Zᵀ * X) *ᵥ v) := by
        rw [Matrix.mulVec_mulVec, Matrix.mul_assoc (Xᵀ * Z * W) Zᵀ X]
      rw [hfact, hzero, Matrix.mulVec_zero]
    have hv0 : v = 0 := by
      have h1 : ⅟ (Xᵀ * Z * W * Zᵀ * X) *ᵥ ((Xᵀ * Z * W * Zᵀ * X) *ᵥ v) = 0 := by
        rw [hQv, Matrix.mulVec_zero]
      rwa [Matrix.mulVec_mulVec, invOf_mul_self, Matrix.one_mulVec] at h1
    exact hv hv0
  · exact hWpd ((Zᵀ * X) *ᵥ v) hzero

omit [DecidableEq k] in
/-- Bridge: the GMM criterion equals the Chapter 2 abstract quadratic `linearProjectionMSE` with
`QXX = X'Z W Z'X`, `QXY = X'Z W Z'Y`, `QYY = (Z'Y)' W (Z'Y)`. Private — file-local notation
bridge, reused only inside this file (cf. `sumSquaredErrors_eq_linearProjectionMSE`). -/
private lemma gmmCriterion_eq_linearProjectionMSE (X : Matrix n k ℝ) (Z : Matrix n l ℝ)
    (y : n → ℝ) (W : Matrix l l ℝ) (hWsymm : Wᵀ = W) (b : k → ℝ) :
    gmmCriterion X Z y W b =
      linearProjectionMSE (Xᵀ * Z * W * Zᵀ * X) ((Xᵀ * Z * W) *ᵥ (Zᵀ *ᵥ y))
        ((Zᵀ *ᵥ y) ⬝ᵥ (W *ᵥ (Zᵀ *ᵥ y))) b := by
  have hr : Zᵀ *ᵥ (y - X *ᵥ b) = (Zᵀ *ᵥ y) - ((Zᵀ * X) *ᵥ b) := by
    rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec]
  have hquad : ((Zᵀ * X) *ᵥ b) ⬝ᵥ (W *ᵥ ((Zᵀ * X) *ᵥ b)) =
      b ⬝ᵥ ((Xᵀ * Z * W * Zᵀ * X) *ᵥ b) := (gmm_QXX_quad X Z W b).symm
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
minimum of the GMM criterion: for any coefficient vector `b`, `J(gmmBeta) ≤ J(b)`. Requires the
weight matrix `W` to be symmetric (`Wᵀ = W`) and positive semidefinite. -/
theorem gmmCriterion_gmmBeta_le (X : Matrix n k ℝ) (Z : Matrix n l ℝ) (y : n → ℝ)
    (W : Matrix l l ℝ) (b : k → ℝ) [Invertible (Xᵀ * Z * W * Zᵀ * X)]
    (hWsymm : Wᵀ = W) (hWpsd : ∀ u : l → ℝ, 0 ≤ u ⬝ᵥ (W *ᵥ u)) :
    gmmCriterion X Z y W (gmmBeta X Z y W) ≤ gmmCriterion X Z y W b := by
  rw [gmmCriterion_eq_linearProjectionMSE X Z y W hWsymm b,
      gmmCriterion_eq_linearProjectionMSE X Z y W hWsymm (gmmBeta X Z y W),
      gmmBeta_eq_linearProjectionBeta X Z y W]
  exact linearProjectionBeta_minimizes_MSE (Xᵀ * Z * W * Zᵀ * X) ((Xᵀ * Z * W) *ᵥ (Zᵀ *ᵥ y))
    ((Zᵀ *ᵥ y) ⬝ᵥ (W *ᵥ (Zᵀ *ᵥ y))) (gmm_QXX_transpose X Z W hWsymm)
    (gmm_QXX_nonneg X Z W hWpsd) b

/-- **Hansen Theorem 13.1 (existence half), packaged as `IsMinOn`.** -/
theorem gmmBeta_isMinOn (X : Matrix n k ℝ) (Z : Matrix n l ℝ) (y : n → ℝ) (W : Matrix l l ℝ)
    [Invertible (Xᵀ * Z * W * Zᵀ * X)] (hWsymm : Wᵀ = W)
    (hWpsd : ∀ u : l → ℝ, 0 ≤ u ⬝ᵥ (W *ᵥ u)) :
    IsMinOn (gmmCriterion X Z y W) Set.univ (gmmBeta X Z y W) := by
  intro b _
  exact gmmCriterion_gmmBeta_le X Z y W b hWsymm hWpsd

/-- **Hansen Theorem 13.1 (uniqueness half).** If `b` attains the minimum of the GMM criterion,
then `b = gmmBeta`. Requires `W` symmetric and positive definite. -/
theorem gmmBeta_eq_of_minimizer (X : Matrix n k ℝ) (Z : Matrix n l ℝ) (y : n → ℝ)
    (W : Matrix l l ℝ) (b : k → ℝ) [Invertible (Xᵀ * Z * W * Zᵀ * X)]
    (hWsymm : Wᵀ = W) (hWpd : ∀ u : l → ℝ, u ≠ 0 → 0 < u ⬝ᵥ (W *ᵥ u))
    (hb : gmmCriterion X Z y W b = gmmCriterion X Z y W (gmmBeta X Z y W)) :
    b = gmmBeta X Z y W := by
  rw [gmmCriterion_eq_linearProjectionMSE X Z y W hWsymm b,
      gmmCriterion_eq_linearProjectionMSE X Z y W hWsymm (gmmBeta X Z y W),
      gmmBeta_eq_linearProjectionBeta X Z y W] at hb
  rw [gmmBeta_eq_linearProjectionBeta X Z y W]
  exact linearProjectionBeta_eq_of_MSE_eq (Xᵀ * Z * W * Zᵀ * X) ((Xᵀ * Z * W) *ᵥ (Zᵀ *ᵥ y))
    ((Zᵀ *ᵥ y) ⬝ᵥ (W *ᵥ (Zᵀ *ᵥ y))) b (gmm_QXX_transpose X Z W hWsymm)
    (fun v hv => gmm_QXX_pos X Z W hWpd v hv) hb

end HansenEconometrics
