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

omit [Fintype q] [DecidableEq q] in
/-- Stack observation-level system regressors into scalar rows indexed by
observation and equation. For `X i : Matrix m k ℝ`, row `(i, j)` is the
regressor row for equation `j` in observation `i`. -/
noncomputable def systemStackRegressors
    (X : n → Matrix m k ℝ) : Matrix (n × m) k ℝ :=
  fun im a => X im.1 im.2 a

omit [Fintype k] [Fintype q] [DecidableEq k] [DecidableEq q] in
/-- Stack observation-level system outcomes into scalar rows indexed by
observation and equation. -/
def systemStackOutcomes (Y : n → m → ℝ) : n × m → ℝ :=
  fun im => Y im.1 im.2

omit [Fintype q] [DecidableEq q] in
/-- Hansen observation-level systems least-squares estimator, totalized through
the Chapter 7 Star convention after stacking observation/equation rows. -/
noncomputable def systemLeastSquaresBetaStarObs
    (X : n → Matrix m k ℝ) (Y : n → m → ℝ) : k → ℝ :=
  systemLeastSquaresBetaStar (systemStackRegressors X) (systemStackOutcomes Y)

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

omit [Fintype q] [DecidableEq q] in
/-- Normalized system score mean `n⁻¹∑ Xᵢ'eᵢ`. -/
noncomputable def systemScoreMean
    (X : n → Matrix m k ℝ) (e : n → m → ℝ) : k → ℝ :=
  (Fintype.card n : ℝ)⁻¹ • ∑ i : n, systemScore (X i) (e i)

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

omit [Fintype n] [Fintype k] [Fintype q] [DecidableEq n] [DecidableEq k]
  [DecidableEq q] [DecidableEq m] in
/-- The one-observation robust middle `Xᵢ'eᵢeᵢ'Xᵢ` is the score outer product
`(Xᵢ'eᵢ)(Xᵢ'eᵢ)'`. -/
theorem systemRobustMiddleTerm_eq_vecMulVec_score
    (Xi : Matrix m k ℝ) (ei : m → ℝ) :
    systemRobustMiddleTerm Xi ei =
      Matrix.vecMulVec (systemScore Xi ei) (systemScore Xi ei) := by
  ext a b
  simp [systemRobustMiddleTerm, systemMiddleTerm, systemScore, Matrix.mul_apply,
    Matrix.mulVec, Matrix.vecMulVec_apply, dotProduct, Finset.mul_sum,
    mul_comm, mul_left_comm]

omit [Fintype q] [DecidableEq q] in
/-- Observation-level residual covariance `n⁻¹∑ êᵢêᵢ'` used in Hansen's
feasible homoskedastic system and SUR covariance estimators. -/
noncomputable def systemSigmaHat
    (ehat : n → m → ℝ) : Matrix m m ℝ :=
  (Fintype.card n : ℝ)⁻¹ • ∑ i : n, Matrix.vecMulVec (ehat i) (ehat i)

omit [Fintype k] [Fintype q] [DecidableEq n] [DecidableEq k]
  [DecidableEq q] [DecidableEq m] in
/-- The stacked system Gram matrix is the unnormalized sum of Hansen's
per-observation Gram contributions `Xᵢ'Xᵢ`. -/
theorem systemStackRegressors_transpose_mul_self_eq_sum
    (X : n → Matrix m k ℝ) :
    (systemStackRegressors X)ᵀ * systemStackRegressors X =
      ∑ i : n, (X i)ᵀ * X i := by
  ext a b
  simp [systemStackRegressors, Matrix.mul_apply, Matrix.sum_apply,
    ← Finset.univ_product_univ, Finset.sum_product]

omit [Fintype k] [Fintype q] [DecidableEq n] [DecidableEq k] [DecidableEq q]
  [DecidableEq m] in
/-- The stacked system cross moment with vector outcomes is the unnormalized
sum `∑ Xᵢ'Yᵢ`. -/
theorem systemStackRegressors_transpose_mulVec_stackOutcomes_eq_sum
    (X : n → Matrix m k ℝ) (Y : n → m → ℝ) :
    (systemStackRegressors X)ᵀ *ᵥ systemStackOutcomes Y =
      ∑ i : n, systemScore (X i) (Y i) := by
  ext a
  simp [systemStackRegressors, systemStackOutcomes, systemScore, Matrix.mulVec,
    dotProduct, ← Finset.univ_product_univ, Finset.sum_product]

omit [Fintype n] [Fintype q] [Fintype m] [DecidableEq n] [DecidableEq k]
  [DecidableEq q] [DecidableEq m] in
/-- Observation/equation stacking preserves the system linear model
`Yᵢ = Xᵢ β + eᵢ`. -/
theorem systemStackOutcomes_linear_model
    (X : n → Matrix m k ℝ) (e Y : n → m → ℝ) (β : k → ℝ)
    (hmodel : ∀ i j, Y i j = (X i j) ⬝ᵥ β + e i j) :
    systemStackOutcomes Y =
      systemStackRegressors X *ᵥ β + systemStackOutcomes e := by
  ext im
  simp [systemStackOutcomes, systemStackRegressors, Matrix.mulVec, dotProduct,
    hmodel im.1 im.2]

omit [Fintype q] [DecidableEq n] [DecidableEq k] [DecidableEq q] [DecidableEq m] in
/-- Observation-level system scores split into Gram times coefficient plus error score
under the system linear model. -/
theorem systemScore_sum_outcomes_linear_model
    (X : n → Matrix m k ℝ) (e Y : n → m → ℝ) (β : k → ℝ)
    (hmodel : ∀ i j, Y i j = (X i j) ⬝ᵥ β + e i j) :
    ∑ i : n, systemScore (X i) (Y i) =
      (∑ i : n, (X i)ᵀ * X i) *ᵥ β +
        ∑ i : n, systemScore (X i) (e i) := by
  rw [← systemStackRegressors_transpose_mulVec_stackOutcomes_eq_sum X Y,
      systemStackOutcomes_linear_model X e Y β hmodel,
      Matrix.mulVec_add, Matrix.mulVec_mulVec,
      systemStackRegressors_transpose_mul_self_eq_sum,
      systemStackRegressors_transpose_mulVec_stackOutcomes_eq_sum]

omit [Fintype q] [DecidableEq n] [DecidableEq q] [DecidableEq m] in
/-- Totalized observation-level system least squares equals the inverse stacked Gram times
the unnormalized system cross moment. -/
theorem systemLeastSquaresBetaStarObs_eq_sum_moments
    (X : n → Matrix m k ℝ) (Y : n → m → ℝ) :
    systemLeastSquaresBetaStarObs X Y =
      (∑ i : n, (X i)ᵀ * X i)⁻¹ *ᵥ
        ∑ i : n, systemScore (X i) (Y i) := by
  unfold systemLeastSquaresBetaStarObs systemLeastSquaresBetaStar olsBetaStar
  rw [systemStackRegressors_transpose_mul_self_eq_sum,
      systemStackRegressors_transpose_mulVec_stackOutcomes_eq_sum]

omit [Fintype q] [DecidableEq n] [DecidableEq q] [DecidableEq m] in
/-- System analogue of Chapter 7's totalized OLS residual identity. Under the linear
model, the estimator error equals the system score term plus the singular-design
totalization remainder. -/
theorem systemLeastSquaresBetaStarObs_sub_identity
    (X : n → Matrix m k ℝ) (e Y : n → m → ℝ) (β : k → ℝ)
    (hmodel : ∀ i j, Y i j = (X i j) ⬝ᵥ β + e i j) :
    systemLeastSquaresBetaStarObs X Y - β -
        (∑ i : n, (X i)ᵀ * X i)⁻¹ *ᵥ
          ∑ i : n, systemScore (X i) (e i) =
      (((∑ i : n, (X i)ᵀ * X i)⁻¹ *
          ∑ i : n, (X i)ᵀ * X i) - 1) *ᵥ β := by
  rw [systemLeastSquaresBetaStarObs_eq_sum_moments,
      systemScore_sum_outcomes_linear_model X e Y β hmodel,
      Matrix.mulVec_add, Matrix.mulVec_mulVec,
      Matrix.sub_mulVec, Matrix.one_mulVec]
  abel

omit [Fintype q] [DecidableEq q] in
/-- Normalized system Gram matrix `n⁻¹∑ Xᵢ'Xᵢ`. -/
noncomputable def systemNormalizedGram
    (X : n → Matrix m k ℝ) : Matrix k k ℝ :=
  (Fintype.card n : ℝ)⁻¹ • ∑ i : n, (X i)ᵀ * X i

omit [Fintype q] [DecidableEq n] [DecidableEq k] [DecidableEq q]
  [DecidableEq m] in
/-- Normalized observation-level system scores split into normalized Gram times
coefficient plus normalized error score under the system linear model. -/
theorem systemScoreMean_outcomes_linear_model
    (X : n → Matrix m k ℝ) (e Y : n → m → ℝ) (β : k → ℝ)
    (hmodel : ∀ i j, Y i j = (X i j) ⬝ᵥ β + e i j) :
    systemScoreMean X Y =
      systemNormalizedGram X *ᵥ β + systemScoreMean X e := by
  unfold systemScoreMean systemNormalizedGram
  rw [systemScore_sum_outcomes_linear_model X e Y β hmodel,
      Matrix.smul_mulVec, smul_add]

omit [Fintype q] [DecidableEq n] [DecidableEq q] [DecidableEq m] in
/-- Totalized observation-level system least squares equals normalized system
Gram inverse times normalized system cross moment. This is the Hansen-facing
`Q̂ₙ⁻¹ ĝₙ` form of `systemLeastSquaresBetaStarObs_eq_sum_moments`. -/
theorem systemLeastSquaresBetaStarObs_eq_normalized_moments
    (X : n → Matrix m k ℝ) (Y : n → m → ℝ) :
    systemLeastSquaresBetaStarObs X Y =
      (systemNormalizedGram X)⁻¹ *ᵥ systemScoreMean X Y := by
  by_cases hn0 : Fintype.card n = 0
  · haveI : IsEmpty n := Fintype.card_eq_zero_iff.mp hn0
    simp [systemLeastSquaresBetaStarObs_eq_sum_moments, systemNormalizedGram,
      systemScoreMean]
  · have hne : (Fintype.card n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn0
    rw [systemLeastSquaresBetaStarObs_eq_sum_moments]
    unfold systemNormalizedGram systemScoreMean
    rw [nonsingInv_smul, Matrix.smul_mulVec, Matrix.mulVec_smul, smul_smul,
      inv_inv, mul_inv_cancel₀ hne, one_smul]

omit [Fintype q] [DecidableEq n] [DecidableEq q] [DecidableEq m] in
/-- Hansen-facing normalized version of the Chapter 7 totalized OLS residual identity
for observation-level systems. -/
theorem systemLeastSquaresBetaStarObs_sub_identity_normalized
    (X : n → Matrix m k ℝ) (e Y : n → m → ℝ) (β : k → ℝ)
    (hmodel : ∀ i j, Y i j = (X i j) ⬝ᵥ β + e i j) :
    systemLeastSquaresBetaStarObs X Y - β -
        (systemNormalizedGram X)⁻¹ *ᵥ systemScoreMean X e =
      ((systemNormalizedGram X)⁻¹ * systemNormalizedGram X - 1) *ᵥ β := by
  rw [systemLeastSquaresBetaStarObs_eq_normalized_moments,
      systemScoreMean_outcomes_linear_model X e Y β hmodel,
      Matrix.mulVec_add, Matrix.mulVec_mulVec,
      Matrix.sub_mulVec, Matrix.one_mulVec]
  abel

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
