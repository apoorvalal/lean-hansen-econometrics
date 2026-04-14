import Mathlib
import HansenEconometrics.Basic

open scoped Matrix

namespace HansenEconometrics

open Matrix

variable {k : Type*}
variable [Fintype k] [DecidableEq k]

/-- Hansen Definition 2.5: population linear projection coefficient `β = QXX⁻¹ QXY`. -/
noncomputable def linearProjectionBeta
    (QXX : Matrix k k ℝ) (QXY : k → ℝ) [Invertible QXX] : k → ℝ :=
  ⅟ QXX *ᵥ QXY

/-- The population linear-projection mean squared error, up to the scalar `E[Y²]`. -/
noncomputable def linearProjectionMSE
    (QXX : Matrix k k ℝ) (QXY : k → ℝ) (QYY : ℝ) (b : k → ℝ) : ℝ :=
  QYY - 2 * (b ⬝ᵥ QXY) + b ⬝ᵥ (QXX *ᵥ b)

/-- Hansen Theorem 2.9: the projection coefficient satisfies the population normal equations. -/
theorem linearProjectionBeta_normal_equations
    (QXX : Matrix k k ℝ) (QXY : k → ℝ) [Invertible QXX] :
    QXX *ᵥ linearProjectionBeta QXX QXY = QXY := by
  unfold linearProjectionBeta
  rw [Matrix.mulVec_mulVec]
  rw [mul_invOf_self]
  simp

/-- Hansen Theorem 2.9: population projection residuals are orthogonal to the regressors. -/
theorem linearProjectionBeta_orthogonal_moment
    (QXX : Matrix k k ℝ) (QXY : k → ℝ) [Invertible QXX] :
    QXY - QXX *ᵥ linearProjectionBeta QXX QXY = 0 := by
  rw [linearProjectionBeta_normal_equations]
  simp

/-- The population normal equations uniquely identify the linear projection coefficient. -/
theorem linearProjectionBeta_eq_of_normal_equations
    (QXX : Matrix k k ℝ) (QXY b : k → ℝ) [Invertible QXX]
    (hb : QXX *ᵥ b = QXY) :
    linearProjectionBeta QXX QXY = b := by
  unfold linearProjectionBeta
  rw [← hb]
  rw [Matrix.mulVec_mulVec]
  rw [invOf_mul_self]
  simp

/-- At the projection coefficient, the quadratic criterion simplifies to `E[Y²] - β'QXY`. -/
theorem linearProjectionMSE_at_beta
    (QXX : Matrix k k ℝ) (QXY : k → ℝ) (QYY : ℝ) [Invertible QXX] :
    linearProjectionMSE QXX QXY QYY (linearProjectionBeta QXX QXY) =
      QYY - linearProjectionBeta QXX QXY ⬝ᵥ QXY := by
  unfold linearProjectionMSE
  rw [linearProjectionBeta_normal_equations]
  ring

end HansenEconometrics
