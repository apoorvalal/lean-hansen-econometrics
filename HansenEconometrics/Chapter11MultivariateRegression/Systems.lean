import HansenEconometrics.Chapter7Asymptotics.Basic

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

omit [DecidableEq n] in
/-- Totalized stacked systems least-squares estimator, using the Chapter 7 Star convention. -/
noncomputable def systemLeastSquaresBetaStar
    (X : Matrix n k ℝ) (Y : n → ℝ) : k → ℝ :=
  olsBetaStar X Y

omit [DecidableEq n] in
/-- The system Star estimator is the totalized OLS estimator on the stacked system. -/
@[simp]
theorem systemLeastSquaresBetaStar_eq
    (X : Matrix n k ℝ) (Y : n → ℝ) :
    systemLeastSquaresBetaStar X Y = olsBetaStar X Y :=
  rfl

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
/-- One-observation system score `Xᵢ' eᵢ`. Here `Xᵢ` is Hansen's per-observation
system design matrix and `eᵢ` is the vector of equation errors. -/
noncomputable def systemScore
    (Xi : Matrix m k ℝ) (ei : m → ℝ) : k → ℝ :=
  Xiᵀ *ᵥ ei

omit [Fintype n] [Fintype q] [DecidableEq n] [DecidableEq q] in
/-- One-observation system covariance middle matrix `Xᵢ' Eᵢ Xᵢ`, where
`Eᵢ` is typically `eᵢeᵢ'` or a common error covariance estimate. -/
noncomputable def systemMiddleTerm
    (Xi : Matrix m k ℝ) (Ei : Matrix m m ℝ) : Matrix k k ℝ :=
  Xiᵀ * Ei * Xi

omit [Fintype n] [Fintype q] [DecidableEq n] [DecidableEq q] in
/-- One-observation robust middle contribution `Xᵢ' eᵢeᵢ' Xᵢ`. -/
noncomputable def systemRobustMiddleTerm
    (Xi : Matrix m k ℝ) (ei : m → ℝ) : Matrix k k ℝ :=
  systemMiddleTerm Xi (Matrix.vecMulVec ei ei)

omit [Fintype q] [DecidableEq q] in
/-- Normalized system Gram matrix `n⁻¹∑ Xᵢ'Xᵢ`. -/
noncomputable def systemNormalizedGram
    (X : n → Matrix m k ℝ) : Matrix k k ℝ :=
  (Fintype.card n : ℝ)⁻¹ • ∑ i : n, (X i)ᵀ * X i

omit [Fintype q] [DecidableEq q] in
/-- Normalized robust system covariance middle matrix
`n⁻¹∑ Xᵢ' êᵢêᵢ' Xᵢ`. -/
noncomputable def systemRobustMiddle
    (X : n → Matrix m k ℝ) (ehat : n → m → ℝ) : Matrix k k ℝ :=
  (Fintype.card n : ℝ)⁻¹ • ∑ i : n, systemRobustMiddleTerm (X i) (ehat i)

omit [Fintype q] [DecidableEq q] in
/-- Normalized homoskedastic system covariance middle matrix
`n⁻¹∑ Xᵢ'Σ̂Xᵢ`. -/
noncomputable def systemHomoskedasticMiddle
    (X : n → Matrix m k ℝ) (SigmaHat : Matrix m m ℝ) : Matrix k k ℝ :=
  (Fintype.card n : ℝ)⁻¹ • ∑ i : n, systemMiddleTerm (X i) SigmaHat

omit [Fintype n] [Fintype q] [Fintype m] [DecidableEq n] [DecidableEq q]
  [DecidableEq m] in
/-- Sandwich covariance assembled from normalized system moments:
`Q̂⁻¹ Ω̂ Q̂⁻¹`. This is the normalized form of Hansen's `n V̂_β`. -/
noncomputable def systemSandwichCovariance
    (Qhat Omegahat : Matrix k k ℝ) : Matrix k k ℝ :=
  Qhat⁻¹ * Omegahat * Qhat⁻¹

omit [Fintype q] [DecidableEq q] in
/-- Normalized robust covariance estimator `Q̂⁻¹ Ω̂_HC Q̂⁻¹`, the matrix
corresponding to Hansen's `n V̂_{β̂}`. -/
noncomputable def systemRobustCovariance
    (X : n → Matrix m k ℝ) (ehat : n → m → ℝ) : Matrix k k ℝ :=
  systemSandwichCovariance (systemNormalizedGram X) (systemRobustMiddle X ehat)

omit [Fintype q] [DecidableEq q] in
/-- Normalized homoskedastic covariance estimator `Q̂⁻¹ Ω̂₀ Q̂⁻¹`, the matrix
corresponding to Hansen's `n V̂⁰_{β̂}`. -/
noncomputable def systemHomoskedasticCovariance
    (X : n → Matrix m k ℝ) (SigmaHat : Matrix m m ℝ) : Matrix k k ℝ :=
  systemSandwichCovariance (systemNormalizedGram X) (systemHomoskedasticMiddle X SigmaHat)

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
