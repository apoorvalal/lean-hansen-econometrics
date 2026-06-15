import HansenEconometrics.Chapter4LeastSquaresRegression

/-!
# Chapter 11 — multivariate regression systems

This file contains deterministic system-regression notation used by the Chapter 11
formalization. The public surface treats a multivariate regression system through
its stacked least-squares representation; equation-specific block structure is
recorded by thin matrix wrappers when Hansen writes common-regressor formulas.
-/

open scoped Matrix

namespace HansenEconometrics

open Matrix

variable {n k q m : Type*}
variable [Fintype n] [Fintype k] [Fintype q] [Fintype m]
variable [DecidableEq n] [DecidableEq k] [DecidableEq q] [DecidableEq m]

/-- Stacked systems least-squares coefficient estimator. -/
noncomputable def systemLeastSquaresBeta
    (X : Matrix n k ℝ) (Y : n → ℝ) [Invertible (Xᵀ * X)] : k → ℝ :=
  olsBeta X Y

/-- Stacked systems residual. -/
noncomputable def systemResidual
    (X : Matrix n k ℝ) (Y : n → ℝ) [Invertible (Xᵀ * X)] : n → ℝ :=
  residual X Y

omit [Fintype q] [Fintype m] [DecidableEq n] [DecidableEq q] [DecidableEq m] in
/-- Stacked systems least squares has the usual linear-model decomposition. -/
theorem systemLeastSquaresBeta_linear_model
    (X : Matrix n k ℝ) (β : k → ℝ) (e : n → ℝ) [Invertible (Xᵀ * X)] :
    systemLeastSquaresBeta X (X *ᵥ β + e) =
      β + (⅟ (Xᵀ * X)) *ᵥ (Xᵀ *ᵥ e) := by
  exact olsBeta_linear_decomposition X β e

omit [Fintype q] [Fintype m] [DecidableEq n] [DecidableEq q] [DecidableEq m] in
/-- Stacked systems residuals are ordinary OLS residuals in the stacked system. -/
@[simp]
theorem systemResidual_eq_residual
    (X : Matrix n k ℝ) (Y : n → ℝ) [Invertible (Xᵀ * X)] :
    systemResidual X Y = residual X Y :=
  rfl

omit [Fintype n] [Fintype q] [Fintype m] [DecidableEq n] [DecidableEq q] [DecidableEq m] in
/-- Hansen Chapter 11 asymptotic covariance formula `Q⁻¹ Ω Q⁻¹`. -/
noncomputable def systemAsymptoticVariance
    (Q Ω : Matrix k k ℝ) : Matrix k k ℝ :=
  Q⁻¹ * Ω * Q⁻¹

omit [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m] in
/-- Delta-method covariance for a function of the stacked system coefficients. -/
noncomputable def systemDeltaVariance
    (Vβ : Matrix k k ℝ) (R : Matrix k q ℝ) : Matrix q q ℝ :=
  Rᵀ * Vβ * R

omit [Fintype n] [Fintype q] [DecidableEq n] [DecidableEq q] in
/-- Common-regressor block moment `I_m ⊗ Q`, written on product indices. -/
def commonRegressorMoment (Q : Matrix k k ℝ) : Matrix (m × k) (m × k) ℝ :=
  fun a b => if a.1 = b.1 then Q a.2 b.2 else 0

omit [Fintype n] [Fintype k] [Fintype q] [Fintype m] [DecidableEq n] [DecidableEq k]
  [DecidableEq q] in
@[simp]
theorem commonRegressorMoment_same
    (Q : Matrix k k ℝ) (j : m) (a b : k) :
    commonRegressorMoment (m := m) Q (j, a) (j, b) = Q a b := by
  simp [commonRegressorMoment]

omit [Fintype n] [Fintype k] [Fintype q] [Fintype m] [DecidableEq n] [DecidableEq k]
  [DecidableEq q] in
@[simp]
theorem commonRegressorMoment_ne
    (Q : Matrix k k ℝ) {j l : m} (hjl : j ≠ l) (a b : k) :
    commonRegressorMoment (m := m) Q (j, a) (l, b) = 0 := by
  simp [commonRegressorMoment, hjl]

omit [Fintype n] [Fintype q] [DecidableEq n] [DecidableEq q] in
/-- Common-regressor homoskedastic variance `Σ ⊗ Q⁻¹`, written on product indices. -/
noncomputable def commonRegressorHomoskedasticVariance
    (Sigma : Matrix m m ℝ) (Q : Matrix k k ℝ) : Matrix (m × k) (m × k) ℝ :=
  fun a b => Sigma a.1 b.1 * Q⁻¹ a.2 b.2

omit [Fintype n] [Fintype q] [Fintype m] [DecidableEq n] [DecidableEq q]
  [DecidableEq m] in
@[simp]
theorem commonRegressorHomoskedasticVariance_apply
    (Sigma : Matrix m m ℝ) (Q : Matrix k k ℝ) (j l : m) (a b : k) :
    commonRegressorHomoskedasticVariance Sigma Q (j, a) (l, b) =
      Sigma j l * Q⁻¹ a b :=
  rfl

end HansenEconometrics
