import Mathlib
import HansenEconometrics.Basic
import HansenEconometrics.LinearAlgebraUtils

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

/-- Quadratic completion for the population projection criterion. This is the deterministic algebra
behind the best-linear-predictor minimization statement. -/
theorem linearProjectionMSE_eq_at_beta_add_quadratic_form
    (QXX : Matrix k k ℝ) (QXY : k → ℝ) (QYY : ℝ) (b : k → ℝ)
    [Invertible QXX]
    (hQXXt : QXXᵀ = QXX) :
    linearProjectionMSE QXX QXY QYY b =
      linearProjectionMSE QXX QXY QYY (linearProjectionBeta QXX QXY) +
        (b - linearProjectionBeta QXX QXY) ⬝ᵥ
          (QXX *ᵥ (b - linearProjectionBeta QXX QXY)) := by
  have hβ :
      QXX *ᵥ linearProjectionBeta QXX QXY = QXY :=
    linearProjectionBeta_normal_equations QXX QXY
  have hsymm :
      linearProjectionBeta QXX QXY ⬝ᵥ (QXX *ᵥ b) =
        b ⬝ᵥ (QXX *ᵥ linearProjectionBeta QXX QXY) := by
    calc
      linearProjectionBeta QXX QXY ⬝ᵥ (QXX *ᵥ b) =
          Matrix.vecMul (linearProjectionBeta QXX QXY) QXX ⬝ᵥ b := by
        rw [Matrix.dotProduct_mulVec]
      _ = (QXX *ᵥ linearProjectionBeta QXX QXY) ⬝ᵥ b := by
        rw [vecMul_eq_mulVec_of_transpose_eq_self QXX hQXXt]
      _ = b ⬝ᵥ (QXX *ᵥ linearProjectionBeta QXX QXY) := by
        rw [dotProduct_comm]
  have hcross :
      linearProjectionBeta QXX QXY ⬝ᵥ (QXX *ᵥ b) = b ⬝ᵥ QXY := by
    rw [hsymm, hβ]
  rw [linearProjectionMSE_at_beta]
  unfold linearProjectionMSE
  rw [Matrix.mulVec_sub, sub_dotProduct, dotProduct_sub, dotProduct_sub]
  rw [hcross]
  rw [hβ]
  ring_nf

/-- Hansen Definition 2.5 / Theorem 2.9: the projection coefficient minimizes the population
linear-prediction mean squared error. -/
theorem linearProjectionBeta_minimizes_MSE
    (QXX : Matrix k k ℝ) (QXY : k → ℝ) (QYY : ℝ) [Invertible QXX]
    (hQXXt : QXXᵀ = QXX)
    (hQXX_nonneg : ∀ v : k → ℝ, 0 ≤ v ⬝ᵥ (QXX *ᵥ v))
    (b : k → ℝ) :
    linearProjectionMSE QXX QXY QYY (linearProjectionBeta QXX QXY) ≤
      linearProjectionMSE QXX QXY QYY b := by
  rw [linearProjectionMSE_eq_at_beta_add_quadratic_form QXX QXY QYY b hQXXt]
  linarith [hQXX_nonneg (b - linearProjectionBeta QXX QXY)]

/-- Hansen Theorem 2.9 in textbook moment notation: if `EXX = E[XXᵀ]`, `EXY = E[XY]`, and
`EY2 = E[Y²]`, then `β = (EXX)⁻¹ EXY` minimizes the population linear-prediction criterion. -/
theorem linearProjectionBeta_minimizes_MSE_of_moments
    (EXX : Matrix k k ℝ) (EXY : k → ℝ) (EY2 : ℝ) [Invertible EXX]
    (hEXXt : EXXᵀ = EXX)
    (hEXX_nonneg : ∀ v : k → ℝ, 0 ≤ v ⬝ᵥ (EXX *ᵥ v))
    (b : k → ℝ) :
    linearProjectionMSE EXX EXY EY2 (linearProjectionBeta EXX EXY) ≤
      linearProjectionMSE EXX EXY EY2 b := by
  exact linearProjectionBeta_minimizes_MSE EXX EXY EY2 hEXXt hEXX_nonneg b

/-- Under strict positive definiteness of the quadratic form, the projection coefficient is the
unique minimizer of the population linear-prediction criterion. -/
theorem linearProjectionBeta_eq_of_MSE_eq
    (QXX : Matrix k k ℝ) (QXY : k → ℝ) (QYY : ℝ) (b : k → ℝ)
    [Invertible QXX]
    (hQXXt : QXXᵀ = QXX)
    (hQXX_pos : ∀ v : k → ℝ, v ≠ 0 → 0 < v ⬝ᵥ (QXX *ᵥ v))
    (hb : linearProjectionMSE QXX QXY QYY b =
      linearProjectionMSE QXX QXY QYY (linearProjectionBeta QXX QXY)) :
    b = linearProjectionBeta QXX QXY := by
  by_contra hbne
  have hneq : b - linearProjectionBeta QXX QXY ≠ 0 := sub_ne_zero.mpr hbne
  have hpos :
      0 < (b - linearProjectionBeta QXX QXY) ⬝ᵥ
        (QXX *ᵥ (b - linearProjectionBeta QXX QXY)) :=
    hQXX_pos (b - linearProjectionBeta QXX QXY) hneq
  rw [linearProjectionMSE_eq_at_beta_add_quadratic_form QXX QXY QYY b hQXXt] at hb
  linarith

end HansenEconometrics
