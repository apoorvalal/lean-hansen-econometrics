import Mathlib
import HansenEconometrics.Basic
import HansenEconometrics.LinearAlgebraUtils
import HansenEconometrics.Chapter2CondExp

open scoped Matrix

namespace HansenEconometrics

open Matrix

variable {n k : Type*}
variable [Fintype n] [Fintype k] [DecidableEq k]

/-- Hansen Definition 3.1: sum of squared errors, written in matrix notation. -/
noncomputable def sumSquaredErrors (X : Matrix n k ℝ) (y : n → ℝ) (b : k → ℝ) : ℝ :=
  (y - X *ᵥ b) ⬝ᵥ (y - X *ᵥ b)

/-- Hansen Theorem 3.2: closed-form OLS coefficient under invertibility of `Xᵀ X`. -/
noncomputable def olsBeta (X : Matrix n k ℝ) (y : n → ℝ) [Invertible (Xᵀ * X)] : k → ℝ :=
  (⅟ (Xᵀ * X)) *ᵥ (Xᵀ *ᵥ y)

/-- Hansen Section 3.10: fitted values `X β̂`. -/
noncomputable def fitted (X : Matrix n k ℝ) (y : n → ℝ) [Invertible (Xᵀ * X)] : n → ℝ :=
  X *ᵥ olsBeta X y

/-- Hansen Theorem 3.2: OLS residual vector `Y - X β̂`. -/
noncomputable def residual (X : Matrix n k ℝ) (y : n → ℝ) [Invertible (Xᵀ * X)] : n → ℝ :=
  y - fitted X y

/-- Hansen Theorem 3.2: normal equations in closed-form OLS notation. -/
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

/-- Hansen Theorem 3.2: the regressors are orthogonal to the OLS residual vector. -/
theorem regressors_orthogonal_to_residual
    (X : Matrix n k ℝ) (y : n → ℝ) [Invertible (Xᵀ * X)] :
    Xᵀ *ᵥ residual X y = 0 :=
  normal_equations X y

/-- The closed-form OLS coefficient is the unique vector satisfying the normal equations. -/
theorem olsBeta_eq_of_normal_equations
    (X : Matrix n k ℝ) (y : n → ℝ) (b : k → ℝ) [Invertible (Xᵀ * X)]
    (hb : Xᵀ *ᵥ (y - X *ᵥ b) = 0) :
    olsBeta X y = b := by
  unfold olsBeta
  have hxy : Xᵀ *ᵥ y = (Xᵀ * X) *ᵥ b := by
    rw [Matrix.mulVec_sub] at hb
    have hmul : Xᵀ *ᵥ (X *ᵥ b) = (Xᵀ * X) *ᵥ b := by
      rw [Matrix.mulVec_mulVec]
    rw [hmul] at hb
    exact sub_eq_zero.mp hb
  rw [hxy]
  rw [Matrix.mulVec_mulVec b (⅟ (Xᵀ * X)) (Xᵀ * X)]
  rw [invOf_mul_self]
  simp

/-- Fitted values plus residuals recover the data vector. -/
theorem fitted_add_residual
    (X : Matrix n k ℝ) (y : n → ℝ) [Invertible (Xᵀ * X)] :
    fitted X y + residual X y = y := by
  unfold residual
  simp [sub_eq_add_neg, add_left_comm]

/-- Hansen Definition 3.1 / Theorem 3.2: at `β̂`, SSE is the residual sum of squares. -/
theorem sumSquaredErrors_olsBeta
    (X : Matrix n k ℝ) (y : n → ℝ) [Invertible (Xᵀ * X)] :
    sumSquaredErrors X y (olsBeta X y) = residual X y ⬝ᵥ residual X y := by
  rfl

/-- Hansen equation (3.17): if the regressor matrix contains a constant column,
residuals sum to zero. -/
theorem residual_sum_zero_of_one_mem_colspan
    (X : Matrix n k ℝ) (y : n → ℝ) [Invertible (Xᵀ * X)]
    {c : k → ℝ} (hc : X *ᵥ c = 1) :
    ∑ i, residual X y i = 0 := by
  calc
    ∑ i, residual X y i = residual X y ⬝ᵥ 1 := by
      rw [dotProduct_one]
    _ = residual X y ⬝ᵥ (X *ᵥ c) := by
      rw [hc]
    _ = (Matrix.vecMul (residual X y) X) ⬝ᵥ c := by
      rw [Matrix.dotProduct_mulVec]
    _ = 0 := by
      have h : Matrix.vecMul (residual X y) X = 0 := by
        simpa [vecMul_eq_mulVec_transpose] using (normal_equations X y)
      rw [h]
      simp

end HansenEconometrics
