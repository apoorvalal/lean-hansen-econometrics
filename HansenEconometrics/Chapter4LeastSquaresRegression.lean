import Mathlib
import HansenEconometrics.Basic
import HansenEconometrics.Chapter3Projections

open scoped Matrix

namespace HansenEconometrics

open Matrix

variable {n k : Type*}
variable [Fintype n] [Fintype k] [DecidableEq k]

/-- Hansen equation (4.6): OLS equals the true coefficient plus the projected error. -/
theorem olsBeta_linear_decomposition
    (X : Matrix n k ℝ) (β : k → ℝ) (e : n → ℝ) [Invertible (Xᵀ * X)] :
    olsBeta X (X *ᵥ β + e) = β + (⅟ (Xᵀ * X)) *ᵥ (Xᵀ *ᵥ e) := by
  unfold olsBeta
  rw [Matrix.mulVec_add]
  have hxx : Xᵀ *ᵥ (X *ᵥ β) = (Xᵀ * X) *ᵥ β := by
    rw [Matrix.mulVec_mulVec]
  rw [hxx, Matrix.mulVec_add]
  rw [Matrix.mulVec_mulVec β (⅟ (Xᵀ * X)) (Xᵀ * X)]
  rw [invOf_mul_self]
  simp

/-- If the model error is orthogonal to the regressors, the closed-form OLS coefficient is `β`. -/
theorem olsBeta_eq_of_regressors_orthogonal_error
    (X : Matrix n k ℝ) (β : k → ℝ) (e : n → ℝ) [Invertible (Xᵀ * X)]
    (he : Xᵀ *ᵥ e = 0) :
    olsBeta X (X *ᵥ β + e) = β := by
  rw [olsBeta_linear_decomposition, he]
  simp

/-- In the finite-sample linear model, fitted values equal signal plus projected error. -/
theorem fitted_linear_model
    (X : Matrix n k ℝ) (β : k → ℝ) (e : n → ℝ) [Invertible (Xᵀ * X)] :
    fitted X (X *ᵥ β + e) = X *ᵥ β + hatMatrix X *ᵥ e := by
  unfold fitted
  rw [olsBeta_linear_decomposition, Matrix.mulVec_add]
  rw [← hat_mul_y_eq_closed_form_fit]

/-- In the finite-sample linear model, OLS residuals are the annihilator applied to the error. -/
theorem residual_linear_model
    (X : Matrix n k ℝ) (β : k → ℝ) (e : n → ℝ) [DecidableEq n]
    [Invertible (Xᵀ * X)] :
    residual X (X *ᵥ β + e) = annihilatorMatrix X *ᵥ e := by
  unfold residual annihilatorMatrix
  rw [fitted_linear_model, Matrix.sub_mulVec, Matrix.one_mulVec]
  ext i
  simp [sub_eq_add_neg, add_assoc, add_comm]

/-- Hansen Theorem 4.2 matrix core: conditional covariance formula for OLS. -/
noncomputable def olsConditionalVarianceMatrix
    (X : Matrix n k ℝ) (D : Matrix n n ℝ) [Invertible (Xᵀ * X)] : Matrix k k ℝ :=
  ⅟ (Xᵀ * X) * Xᵀ * D * X * ⅟ (Xᵀ * X)

/-- The covariance formula written as `Aᵀ D A`, where `A = X (XᵀX)⁻¹`. -/
theorem olsConditionalVarianceMatrix_eq_Atranspose_D_A
    (X : Matrix n k ℝ) (D : Matrix n n ℝ) [Invertible (Xᵀ * X)] :
    (X * ⅟ (Xᵀ * X))ᵀ * D * (X * ⅟ (Xᵀ * X)) =
      olsConditionalVarianceMatrix X D := by
  unfold olsConditionalVarianceMatrix
  rw [Matrix.transpose_mul, inv_gram_transpose]
  simp [Matrix.mul_assoc]

/-- Hansen Theorem 4.2 homoskedastic simplification: `D = σ² I`. -/
theorem olsConditionalVarianceMatrix_homoskedastic
    (X : Matrix n k ℝ) (σ2 : ℝ) [DecidableEq n] [Invertible (Xᵀ * X)] :
    olsConditionalVarianceMatrix X (σ2 • (1 : Matrix n n ℝ)) =
      σ2 • ⅟ (Xᵀ * X) := by
  unfold olsConditionalVarianceMatrix
  rw [Matrix.mul_assoc (⅟ (Xᵀ * X) * Xᵀ) (σ2 • (1 : Matrix n n ℝ)) X]
  simp [Matrix.mul_assoc]

end HansenEconometrics
