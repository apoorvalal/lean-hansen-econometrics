import Mathlib
import HansenEconometrics.Basic
import HansenEconometrics.Chapter2CondExp

open scoped Matrix

namespace HansenEconometrics

open Matrix

variable {n k : Type*}
variable [Fintype n] [Fintype k] [DecidableEq n] [DecidableEq k]

/-- Closed-form OLS coefficient under invertibility of `Xᵀ X`. -/
noncomputable def olsBeta (X : Matrix n k ℝ) (y : n → ℝ) [Invertible (Xᵀ * X)] : k → ℝ :=
  (⅟ (Xᵀ * X)) *ᵥ (Xᵀ *ᵥ y)

/-- Fitted values. -/
noncomputable def fitted (X : Matrix n k ℝ) (y : n → ℝ) [Invertible (Xᵀ * X)] : n → ℝ :=
  X *ᵥ olsBeta X y

/-- OLS residual vector. -/
noncomputable def residual (X : Matrix n k ℝ) (y : n → ℝ) [Invertible (Xᵀ * X)] : n → ℝ :=
  y - fitted X y

/-- Normal equations in closed-form OLS notation. -/
theorem normal_equations
    (X : Matrix n k ℝ) (y : n → ℝ) [Invertible (Xᵀ * X)] :
    Xᵀ *ᵥ residual X y = 0 := by
  unfold residual fitted olsBeta
  rw [mulVec_sub]
  have hmul : Xᵀ *ᵥ (X *ᵥ (⅟ (Xᵀ * X) *ᵥ (Xᵀ *ᵥ y))) = (Xᵀ * (X * ⅟ (Xᵀ * X))) *ᵥ (Xᵀ *ᵥ y) := by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  calc
    Xᵀ *ᵥ y - Xᵀ *ᵥ (X *ᵥ (⅟ (Xᵀ * X) *ᵥ (Xᵀ *ᵥ y)))
        = Xᵀ *ᵥ y - (Xᵀ * (X * ⅟ (Xᵀ * X))) *ᵥ (Xᵀ *ᵥ y) := by rw [hmul]
    _ = Xᵀ *ᵥ y - (((Xᵀ * X) * ⅟ (Xᵀ * X)) *ᵥ (Xᵀ *ᵥ y)) := by rw [Matrix.mul_assoc]
    _ = Xᵀ *ᵥ y - (1 *ᵥ (Xᵀ *ᵥ y)) := by rw [mul_invOf_self]
    _ = 0 := by simp

/-- Residual orthogonality: the regressors are orthogonal to the OLS residual vector. -/
theorem regressors_orthogonal_to_residual
    (X : Matrix n k ℝ) (y : n → ℝ) [Invertible (Xᵀ * X)] :
    Xᵀ *ᵥ residual X y = 0 :=
  normal_equations X y

/-- Fitted values plus residuals recover the data vector. -/
theorem fitted_add_residual
    (X : Matrix n k ℝ) (y : n → ℝ) [Invertible (Xᵀ * X)] :
    fitted X y + residual X y = y := by
  unfold residual
  simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]

end HansenEconometrics
