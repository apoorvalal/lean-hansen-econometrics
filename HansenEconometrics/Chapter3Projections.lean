import Mathlib
import HansenEconometrics.Basic
import HansenEconometrics.Chapter3LeastSquaresAlgebra

open scoped Matrix

namespace HansenEconometrics

open Matrix

variable {n k : Type*}
variable [Fintype n] [Fintype k] [DecidableEq n] [DecidableEq k]

/-- The OLS projection / hat matrix. -/
noncomputable def hatMatrix (X : Matrix n k ℝ) [Invertible (Xᵀ * X)] : Matrix n n ℝ :=
  X * ⅟ (Xᵀ * X) * Xᵀ

/-- The annihilator matrix. -/
noncomputable def annihilatorMatrix (X : Matrix n k ℝ) [Invertible (Xᵀ * X)] : Matrix n n ℝ :=
  (1 : Matrix n n ℝ) - hatMatrix X

/-- The closed-form OLS fitted vector equals the hat matrix times the data vector. -/
theorem hat_mul_y_eq_closed_form_fit
    (X : Matrix n k ℝ) (y : n → ℝ) [Invertible (Xᵀ * X)] :
    hatMatrix X *ᵥ y = X *ᵥ ((⅟ (Xᵀ * X)) *ᵥ (Xᵀ *ᵥ y)) := by
  unfold hatMatrix
  calc
    (X * ⅟ (Xᵀ * X) * Xᵀ) *ᵥ y = (X * (⅟ (Xᵀ * X) * Xᵀ)) *ᵥ y := by rw [Matrix.mul_assoc]
    _ = X *ᵥ ((⅟ (Xᵀ * X) * Xᵀ) *ᵥ y) := by
          simpa using (Matrix.mulVec_mulVec y X (⅟ (Xᵀ * X) * Xᵀ))
    _ = X *ᵥ ((⅟ (Xᵀ * X)) *ᵥ (Xᵀ *ᵥ y)) := by
          simpa using (Matrix.mulVec_mulVec y (⅟ (Xᵀ * X)) Xᵀ)

/-- The closed-form OLS residual vector equals the annihilator matrix times the data vector. -/
theorem annihilator_mul_y_eq_closed_form_residual
    (X : Matrix n k ℝ) (y : n → ℝ) [Invertible (Xᵀ * X)] :
    annihilatorMatrix X *ᵥ y = y - X *ᵥ ((⅟ (Xᵀ * X)) *ᵥ (Xᵀ *ᵥ y)) := by
  unfold annihilatorMatrix
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, hat_mul_y_eq_closed_form_fit]

/-- The hat matrix fixes the regressor matrix. -/
theorem hat_mul_X
    (X : Matrix n k ℝ) [Invertible (Xᵀ * X)] :
    hatMatrix X * X = X := by
  unfold hatMatrix
  calc
    X * ⅟ (Xᵀ * X) * Xᵀ * X = X * (⅟ (Xᵀ * X) * (Xᵀ * X)) := by
      simp [Matrix.mul_assoc]
    _ = X * (1 : Matrix k k ℝ) := by rw [invOf_mul_self]
    _ = X := by simp

/-- The annihilator matrix kills the regressor matrix. -/
theorem annihilator_mul_X
    (X : Matrix n k ℝ) [Invertible (Xᵀ * X)] :
    annihilatorMatrix X * X = 0 := by
  unfold annihilatorMatrix
  rw [Matrix.sub_mul, Matrix.one_mul, hat_mul_X]
  simp

end HansenEconometrics
