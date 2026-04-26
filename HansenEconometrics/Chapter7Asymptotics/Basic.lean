import HansenEconometrics.Basic
import HansenEconometrics.LinearAlgebraUtils
import HansenEconometrics.Chapter3LeastSquaresAlgebra
import HansenEconometrics.Chapter4LeastSquaresRegression
import HansenEconometrics.AsymptoticUtils
import HansenEconometrics.ProbabilityUtils
import HansenEconometrics.ChiSquared

/-!
# Chapter 7 Asymptotics: Basic Definitions

This file contains the finite-sample algebra shared by the Chapter 7
asymptotic modules:

* sample Gram, cross-moment, and squared-error averages;
* totalized OLS wrappers used to make sample estimators total random variables;
* residual-variance and leverage-adjusted covariance definitions;
* stacking bridges from triangular-array sequences to finite matrices.
-/

open scoped Matrix Real

namespace HansenEconometrics

open Matrix

variable {n k : Type*}
variable [Fintype n] [Fintype k] [DecidableEq k]

/-- Hansen §7.2: the sample Gram matrix `Q̂ₙ := Xᵀ X / n`. -/
noncomputable def sampleGram (X : Matrix n k ℝ) : Matrix k k ℝ :=
  (Fintype.card n : ℝ)⁻¹ • (Xᵀ * X)

/-- Hansen §7.2: the sample cross moment `g̑ₙ := (Xᵀ e) / n`. -/
noncomputable def sampleCrossMoment (X : Matrix n k ℝ) (e : n → ℝ) : k → ℝ :=
  (Fintype.card n : ℝ)⁻¹ • (Xᵀ *ᵥ e)

/-- Sample average of true squared errors, `n⁻¹∑ eᵢ²`. This is the first term in
Hansen's decomposition of `σ̂²`. -/
noncomputable def sampleErrorSecondMoment (e : n → ℝ) : ℝ :=
  (Fintype.card n : ℝ)⁻¹ * dotProduct e e

/-- Textbook-facing totalization of ordinary OLS: use `olsBeta` on nonsingular designs and
return `0` on singular designs. This exposes the ordinary-OLS formula on the high-probability
nonsingularity event while remaining a genuine random variable for every sample size. -/
noncomputable def olsBetaOrZero (X : Matrix n k ℝ) (y : n → ℝ) : k → ℝ :=
  letI : Decidable (IsUnit (Xᵀ * X).det) := Classical.propDecidable _
  if h : IsUnit (Xᵀ * X).det then
    letI : Invertible (Xᵀ * X) := Matrix.invertibleOfIsUnitDet (A := Xᵀ * X) h
    olsBeta X y
  else
    0

/-- `olsBetaOrZero` is exactly the previously used totalized estimator `olsBetaStar`. -/
theorem olsBetaOrZero_eq_olsBetaStar
    (X : Matrix n k ℝ) (y : n → ℝ) :
    olsBetaOrZero X y = olsBetaStar X y := by
  classical
  unfold olsBetaOrZero
  by_cases h : IsUnit (Xᵀ * X).det
  · rw [dif_pos h]
    letI : Invertible (Xᵀ * X) := Matrix.invertibleOfIsUnitDet (A := Xᵀ * X) h
    exact (olsBetaStar_eq_olsBeta X y).symm
  · rw [dif_neg h]
    unfold olsBetaStar
    rw [Matrix.nonsing_inv_apply_not_isUnit _ h, Matrix.zero_mulVec]

/-- On nonsingular designs, `olsBetaOrZero` agrees with ordinary `olsBeta`. -/
theorem olsBetaOrZero_eq_olsBeta
    (X : Matrix n k ℝ) (y : n → ℝ) [Invertible (Xᵀ * X)] :
    olsBetaOrZero X y = olsBeta X y := by
  rw [olsBetaOrZero_eq_olsBetaStar, olsBetaStar_eq_olsBeta]

/-- Totalized OLS residuals, defined for every design matrix via `olsBetaStar`. -/
noncomputable def olsResidualStar (X : Matrix n k ℝ) (y : n → ℝ) : n → ℝ :=
  y - X *ᵥ olsBetaStar X y

/-- Hansen's `σ̂² = n⁻¹∑ êᵢ²`, using totalized OLS residuals. -/
noncomputable def olsSigmaSqHatStar (X : Matrix n k ℝ) (y : n → ℝ) : ℝ :=
  (Fintype.card n : ℝ)⁻¹ * dotProduct (olsResidualStar X y) (olsResidualStar X y)

/-- Hansen's `s² = (n-k)⁻¹∑ êᵢ²`, using totalized OLS residuals. -/
noncomputable def olsS2Star (X : Matrix n k ℝ) (y : n → ℝ) : ℝ :=
  ((Fintype.card n : ℝ) - Fintype.card k)⁻¹ *
    dotProduct (olsResidualStar X y) (olsResidualStar X y)

/-- **Theorem 7.4 residual expansion, pointwise form.**

Under the linear model, each totalized OLS residual is the structural error
minus the fitted coefficient error evaluated at that row:
`êᵢ = eᵢ - Xᵢ'(β̂* - β)`. -/
theorem olsResidualStar_linear_model_apply
    (X : Matrix n k ℝ) (β : k → ℝ) (e : n → ℝ) (i : n) :
    olsResidualStar X (X *ᵥ β + e) i =
      e i - X i ⬝ᵥ (olsBetaStar X (X *ᵥ β + e) - β) := by
  unfold olsResidualStar
  have hrow :
      X i ⬝ᵥ (olsBetaStar X (X *ᵥ β + e) - β) =
        (X *ᵥ (olsBetaStar X (X *ᵥ β + e) - β)) i := by
    simp [Matrix.mulVec, dotProduct]
  rw [hrow, Matrix.mulVec_sub]
  simp
  ring

/-- **Theorem 7.4 residual expansion, vector form.**

This is the vector version of `êᵢ = eᵢ - Xᵢ'(β̂* - β)`, used before
summing squared residuals in the `σ̂²` consistency proof. -/
theorem olsResidualStar_linear_model
    (X : Matrix n k ℝ) (β : k → ℝ) (e : n → ℝ) :
    olsResidualStar X (X *ᵥ β + e) =
      e - X *ᵥ (olsBetaStar X (X *ᵥ β + e) - β) := by
  ext i
  rw [olsResidualStar_linear_model_apply]
  simp [Matrix.mulVec, dotProduct]

/-- On nonsingular designs, totalized residuals agree with ordinary OLS residuals. -/
theorem olsResidualStar_eq_residual
    (X : Matrix n k ℝ) (y : n → ℝ) [Invertible (Xᵀ * X)] :
    olsResidualStar X y = residual X y := by
  unfold olsResidualStar residual fitted
  rw [olsBetaStar_eq_olsBeta]

omit [DecidableEq k] in
/-- Finite-dimensional dot products are bounded by sup norms, with the explicit
dimension factor used by the deterministic residual-uniformity layer. -/
theorem abs_dotProduct_le_card_mul_norm_mul_norm (x y : k → ℝ) :
    |x ⬝ᵥ y| ≤ (Fintype.card k : ℝ) * ‖x‖ * ‖y‖ := by
  calc
    |x ⬝ᵥ y|
        = |∑ j : k, x j * y j| := by simp [dotProduct]
    _ ≤ ∑ j : k, |x j * y j| := by
          simpa using
            (Finset.abs_sum_le_sum_abs (fun j : k => x j * y j) Finset.univ)
    _ ≤ ∑ _j : k, ‖x‖ * ‖y‖ := by
          refine Finset.sum_le_sum ?_
          intro j _
          rw [abs_mul]
          have hxj : |x j| ≤ ‖x‖ := by
            simpa [Real.norm_eq_abs] using norm_le_pi_norm x j
          have hyj : |y j| ≤ ‖y‖ := by
            simpa [Real.norm_eq_abs] using norm_le_pi_norm y j
          exact mul_le_mul hxj hyj (abs_nonneg _) (norm_nonneg _)
    _ = (Fintype.card k : ℝ) * ‖x‖ * ‖y‖ := by
          simp [Finset.sum_const, nsmul_eq_mul, mul_assoc]

/-- **Hansen Theorem 7.16, deterministic pointwise residual bound.**

For the totalized estimator, the finite-sample residual error at row `i` is
bounded by the row norm times the coefficient error, with the explicit
finite-dimensional sup-norm factor. This is the pointwise algebra behind the
uniform residual consistency rate. -/
theorem residualStar_sub_error_abs_le_card_mul_row_norm_mul_beta_error_norm
    (X : Matrix n k ℝ) (β : k → ℝ) (e : n → ℝ) (i : n) :
    |olsResidualStar X (X *ᵥ β + e) i - e i| ≤
      (Fintype.card k : ℝ) * ‖X i‖ *
        ‖olsBetaStar X (X *ᵥ β + e) - β‖ := by
  let d : k → ℝ := olsBetaStar X (X *ᵥ β + e) - β
  have hres :
      olsResidualStar X (X *ᵥ β + e) i - e i = -(X i ⬝ᵥ d) := by
    rw [olsResidualStar_linear_model_apply]
    dsimp [d]
    ring
  rw [hres, abs_neg]
  exact abs_dotProduct_le_card_mul_norm_mul_norm (X i) d

/-- **Hansen Theorem 7.16, ordinary OLS pointwise residual bound.**

On nonsingular finite samples, the same pointwise residual-error inequality
holds for ordinary OLS residuals. -/
theorem residual_sub_error_abs_le_card_mul_row_norm_mul_beta_error_norm
    (X : Matrix n k ℝ) (β : k → ℝ) (e : n → ℝ) (i : n)
    [Invertible (Xᵀ * X)] :
    |residual X (X *ᵥ β + e) i - e i| ≤
      (Fintype.card k : ℝ) * ‖X i‖ *
        ‖olsBeta X (X *ᵥ β + e) - β‖ := by
  simpa [olsResidualStar_eq_residual, olsBetaStar_eq_olsBeta] using
    residualStar_sub_error_abs_le_card_mul_row_norm_mul_beta_error_norm
      (X := X) (β := β) (e := e) i

/-- **Theorem 7.4 residual expansion, squared pointwise form.**

This is Hansen equation (7.17) for the totalized estimator:
`êᵢ² = eᵢ² - 2 eᵢ Xᵢ'(β̂* - β) + (Xᵢ'(β̂* - β))²`. -/
theorem olsResidualStar_sq_linear_model_apply
    (X : Matrix n k ℝ) (β : k → ℝ) (e : n → ℝ) (i : n) :
    olsResidualStar X (X *ᵥ β + e) i ^ 2 =
      e i ^ 2 -
        2 * e i * (X i ⬝ᵥ (olsBetaStar X (X *ᵥ β + e) - β)) +
          (X i ⬝ᵥ (olsBetaStar X (X *ᵥ β + e) - β)) ^ 2 := by
  rw [olsResidualStar_linear_model_apply]
  ring

/-- **Theorem 7.4 residual sum-of-squares expansion, unscaled form.**

Writing `d = β̂* - β`, the totalized residual sum of squares is
`e'e - 2(X'e)'d + d'(X'X)d`. This is the matrix form behind Hansen's averaged
display (7.18). -/
theorem olsResidualStar_sumSquares_linear_model
    (X : Matrix n k ℝ) (β : k → ℝ) (e : n → ℝ) :
    dotProduct (olsResidualStar X (X *ᵥ β + e))
        (olsResidualStar X (X *ᵥ β + e)) =
      dotProduct e e -
        2 * ((Xᵀ *ᵥ e) ⬝ᵥ (olsBetaStar X (X *ᵥ β + e) - β)) +
          (olsBetaStar X (X *ᵥ β + e) - β) ⬝ᵥ
            ((Xᵀ * X) *ᵥ (olsBetaStar X (X *ᵥ β + e) - β)) := by
  let d : k → ℝ := olsBetaStar X (X *ᵥ β + e) - β
  have hcross : e ⬝ᵥ (X *ᵥ d) = (Xᵀ *ᵥ e) ⬝ᵥ d := by
    rw [Matrix.dotProduct_mulVec, vecMul_eq_mulVec_transpose]
  have hquad : (X *ᵥ d) ⬝ᵥ (X *ᵥ d) = d ⬝ᵥ ((Xᵀ * X) *ᵥ d) := by
    rw [Matrix.dotProduct_mulVec, vecMul_eq_mulVec_transpose, Matrix.mulVec_mulVec,
      dotProduct_comm]
  rw [olsResidualStar_linear_model]
  change (e - X *ᵥ d) ⬝ᵥ (e - X *ᵥ d) =
    e ⬝ᵥ e - 2 * ((Xᵀ *ᵥ e) ⬝ᵥ d) + d ⬝ᵥ ((Xᵀ * X) *ᵥ d)
  rw [sub_dotProduct, dotProduct_sub, dotProduct_sub, hcross,
    dotProduct_comm (X *ᵥ d) e, hcross, hquad]
  ring

/-- **Theorem 7.4 `σ̂²` decomposition for the totalized estimator.**

This is Hansen display (7.18) in sample-moment notation:
`σ̂² = n⁻¹e'e - 2 ĝₙ(e)'(β̂* - β) + (β̂* - β)'Q̂ₙ(β̂* - β)`. -/
theorem olsSigmaSqHatStar_linear_model
    (X : Matrix n k ℝ) (β : k → ℝ) (e : n → ℝ) :
    olsSigmaSqHatStar X (X *ᵥ β + e) =
      (Fintype.card n : ℝ)⁻¹ * dotProduct e e -
        2 * (sampleCrossMoment X e ⬝ᵥ (olsBetaStar X (X *ᵥ β + e) - β)) +
          (olsBetaStar X (X *ᵥ β + e) - β) ⬝ᵥ
            (sampleGram X *ᵥ (olsBetaStar X (X *ᵥ β + e) - β)) := by
  let d : k → ℝ := olsBetaStar X (X *ᵥ β + e) - β
  unfold olsSigmaSqHatStar
  rw [olsResidualStar_sumSquares_linear_model]
  change (Fintype.card n : ℝ)⁻¹ *
      (dotProduct e e - 2 * ((Xᵀ *ᵥ e) ⬝ᵥ d) + d ⬝ᵥ ((Xᵀ * X) *ᵥ d)) =
    (Fintype.card n : ℝ)⁻¹ * dotProduct e e -
      2 * (sampleCrossMoment X e ⬝ᵥ d) + d ⬝ᵥ (sampleGram X *ᵥ d)
  simp [sampleCrossMoment, sampleGram, Matrix.smul_mulVec, mul_add, mul_sub, smul_eq_mul]
  ring

/-- **Theorem 7.4 degrees-of-freedom bridge.**

For nonempty samples, Hansen's `s²` estimator is the degrees-of-freedom rescaling
`(n/(n-k)) σ̂²` of the average squared residual estimator. -/
theorem olsS2Star_eq_card_div_df_mul_olsSigmaSqHatStar
    (X : Matrix n k ℝ) (y : n → ℝ) [Nonempty n] :
    olsS2Star X y =
      ((Fintype.card n : ℝ) / ((Fintype.card n : ℝ) - Fintype.card k)) *
        olsSigmaSqHatStar X y := by
  have hn : (Fintype.card n : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  unfold olsS2Star olsSigmaSqHatStar
  rw [div_eq_mul_inv]
  let a : ℝ := Fintype.card n
  let b : ℝ := (Fintype.card n : ℝ) - Fintype.card k
  let R : ℝ := dotProduct (olsResidualStar X y) (olsResidualStar X y)
  have ha : a ≠ 0 := by simp [a, hn]
  change b⁻¹ * R = (a * b⁻¹) * (a⁻¹ * R)
  calc
    b⁻¹ * R = (a * a⁻¹) * (b⁻¹ * R) := by rw [mul_inv_cancel₀ ha, one_mul]
    _ = (a * b⁻¹) * (a⁻¹ * R) := by ring

omit [Fintype k] [DecidableEq k] in
/-- Scaling `Q̂ₙ` by the sample size recovers the unnormalized Gram `Xᵀ X`. -/
theorem smul_card_sampleGram (X : Matrix n k ℝ) [Nonempty n] :
    (Fintype.card n : ℝ) • sampleGram X = Xᵀ * X := by
  have hne : (Fintype.card n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  unfold sampleGram
  rw [smul_smul, mul_inv_cancel₀ hne, one_smul]

omit [Fintype k] [DecidableEq k] in
/-- Scaling `g̑ₙ` by the sample size recovers `Xᵀ e`. -/
theorem smul_card_sampleCrossMoment (X : Matrix n k ℝ) (e : n → ℝ) [Nonempty n] :
    (Fintype.card n : ℝ) • sampleCrossMoment X e = Xᵀ *ᵥ e := by
  have hne : (Fintype.card n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  unfold sampleCrossMoment
  rw [smul_smul, mul_inv_cancel₀ hne, one_smul]

/-- If `Xᵀ X` is invertible and the sample is nonempty, `Q̂ₙ` is invertible, with
inverse `n · (Xᵀ X)⁻¹`. -/
noncomputable instance sampleGram.invertible
    (X : Matrix n k ℝ) [Nonempty n] [Invertible (Xᵀ * X)] :
    Invertible (sampleGram X) := by
  have hne : (Fintype.card n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  refine ⟨(Fintype.card n : ℝ) • ⅟ (Xᵀ * X), ?_, ?_⟩
  · unfold sampleGram
    rw [Matrix.smul_mul, Matrix.mul_smul, invOf_mul_self,
        smul_smul, mul_inv_cancel₀ hne, one_smul]
  · unfold sampleGram
    rw [Matrix.smul_mul, Matrix.mul_smul, mul_invOf_self,
        smul_smul, inv_mul_cancel₀ hne, one_smul]

/-- Explicit formula for the inverse of the sample Gram matrix. -/
theorem invOf_sampleGram
    (X : Matrix n k ℝ) [Nonempty n] [Invertible (Xᵀ * X)] :
    ⅟ (sampleGram X) = (Fintype.card n : ℝ) • ⅟ (Xᵀ * X) := rfl

/-- Hansen §7.2 deterministic identity:
in the linear model `Y = X β + e`, the OLS error decomposes as
`β̂ₙ - β = Q̂ₙ⁻¹ *ᵥ g̑ₙ`. This is the algebraic engine behind
Theorem 7.1 (Consistency of Least Squares). -/
theorem olsBeta_sub_eq_sampleGram_inv_mulVec_sampleCrossMoment
    (X : Matrix n k ℝ) (β : k → ℝ) (e : n → ℝ)
    [Nonempty n] [Invertible (Xᵀ * X)] :
    olsBeta X (X *ᵥ β + e) - β = ⅟ (sampleGram X) *ᵥ sampleCrossMoment X e := by
  have hne : (Fintype.card n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hcore : olsBeta X (X *ᵥ β + e) - β = (⅟ (Xᵀ * X)) *ᵥ (Xᵀ *ᵥ e) := by
    rw [olsBeta_linear_decomposition]; abel
  rw [hcore, invOf_sampleGram]
  unfold sampleCrossMoment
  rw [Matrix.smul_mulVec, Matrix.mulVec_smul,
      smul_smul, mul_inv_cancel₀ hne, one_smul]

section Stacking

variable {Ω : Type*} {k : Type*} [Fintype k] [DecidableEq k]

/-- Stack the first `n` observations of an `ℕ`-indexed regressor sequence into an
`Fin n`-row design matrix at a fixed sample point `ω`. -/
def stackRegressors (X : ℕ → Ω → (k → ℝ)) (n : ℕ) (ω : Ω) : Matrix (Fin n) k ℝ :=
  Matrix.of fun i j => X i.val ω j

/-- Stack the first `n` scalar errors into a `Fin n`-indexed vector. -/
def stackErrors (e : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : Fin n → ℝ :=
  fun i => e i.val ω

/-- Stack the first `n` outcomes into a `Fin n`-indexed vector. -/
def stackOutcomes (y : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : Fin n → ℝ :=
  fun i => y i.val ω

omit [DecidableEq k] in
/-- Pointwise linear model implies stacked linear model: if `yᵢ = Xᵢ·β + eᵢ`
for each `i`, then
`stackOutcomes y n ω = stackRegressors X n ω *ᵥ β + stackErrors e n ω`. -/
theorem stack_linear_model
    (X : ℕ → Ω → (k → ℝ)) (e : ℕ → Ω → ℝ) (y : ℕ → Ω → ℝ) (β : k → ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (n : ℕ) (ω : Ω) :
    stackOutcomes y n ω = stackRegressors X n ω *ᵥ β + stackErrors e n ω := by
  funext i
  simp [stackOutcomes, stackRegressors, stackErrors, Matrix.mulVec, Matrix.of_apply,
        dotProduct, hmodel i.val ω]

omit [Fintype k] [DecidableEq k] in
/-- The unnormalized Gram matrix of the stacked design is the sum of rank-1 outer
products of each row. -/
theorem stackRegressors_transpose_mul_self_eq_sum
    (X : ℕ → Ω → (k → ℝ)) (n : ℕ) (ω : Ω) :
    (stackRegressors X n ω)ᵀ * stackRegressors X n ω =
      ∑ i : Fin n, Matrix.vecMulVec (X i.val ω) (X i.val ω) := by
  ext a b
  simp [stackRegressors, Matrix.mul_apply, Matrix.sum_apply, Matrix.vecMulVec_apply]

omit [Fintype k] [DecidableEq k] in
/-- The sample Gram matrix of the stacked design equals the sample mean of rank-1
outer products `Xᵢ Xᵢᵀ`. -/
theorem sampleGram_stackRegressors_eq_avg
    (X : ℕ → Ω → (k → ℝ)) (n : ℕ) (ω : Ω) :
    sampleGram (stackRegressors X n ω) =
      (n : ℝ)⁻¹ • ∑ i : Fin n, Matrix.vecMulVec (X i.val ω) (X i.val ω) := by
  unfold sampleGram
  rw [stackRegressors_transpose_mul_self_eq_sum]
  simp [Fintype.card_fin]

omit [Fintype k] [DecidableEq k] in
/-- The unnormalized cross moment of the stacked design with stacked errors
equals the sum of error-weighted regressor vectors. -/
theorem stackRegressors_transpose_mulVec_stackErrors_eq_sum
    (X : ℕ → Ω → (k → ℝ)) (e : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    (stackRegressors X n ω)ᵀ *ᵥ stackErrors e n ω =
      ∑ i : Fin n, e i.val ω • X i.val ω := by
  funext a
  simp [stackRegressors, stackErrors, Matrix.mulVec, dotProduct, mul_comm]

omit [Fintype k] [DecidableEq k] in
/-- The sample cross moment of the stacked design with stacked errors equals the
sample mean of error-weighted regressors. -/
theorem sampleCrossMoment_stackRegressors_stackErrors_eq_avg
    (X : ℕ → Ω → (k → ℝ)) (e : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω) =
      (n : ℝ)⁻¹ • ∑ i : Fin n, e i.val ω • X i.val ω := by
  unfold sampleCrossMoment
  rw [stackRegressors_transpose_mulVec_stackErrors_eq_sum]
  simp [Fintype.card_fin]

omit [Fintype k] [DecidableEq k] in
/-- Bridge `Fin n` summation to `Finset.range n` summation for outer products of
regressors — matches the indexing of Mathlib's WLLN. -/
theorem sum_fin_eq_sum_range_vecMulVec
    (X : ℕ → Ω → (k → ℝ)) (n : ℕ) (ω : Ω) :
    (∑ i : Fin n, Matrix.vecMulVec (X i.val ω) (X i.val ω)) =
      ∑ i ∈ Finset.range n, Matrix.vecMulVec (X i ω) (X i ω) :=
  Fin.sum_univ_eq_sum_range (fun i => Matrix.vecMulVec (X i ω) (X i ω)) n

omit [Fintype k] [DecidableEq k] in
/-- Bridge `Fin n` summation to `Finset.range n` summation for error-weighted
regressors — matches the indexing of Mathlib's WLLN. -/
theorem sum_fin_eq_sum_range_smul
    (X : ℕ → Ω → (k → ℝ)) (e : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    (∑ i : Fin n, e i.val ω • X i.val ω) =
      ∑ i ∈ Finset.range n, e i ω • X i ω :=
  Fin.sum_univ_eq_sum_range (fun i => e i ω • X i ω) n

omit [Fintype k] [DecidableEq k] in
/-- The Hansen CLT scaling `√n · ĝₙ(e)` equals the normalized score sum
`(1 / √n) ∑_{i<n} eᵢXᵢ`, including the harmless `n = 0` totalized case. -/
theorem sqrt_smul_sampleCrossMoment_stackRegressors_stackErrors_eq_inv_sqrt_sum
    (X : ℕ → Ω → (k → ℝ)) (e : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    Real.sqrt (n : ℝ) • sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω) =
      (Real.sqrt (n : ℝ))⁻¹ • ∑ i ∈ Finset.range n, e i ω • X i ω := by
  rw [sampleCrossMoment_stackRegressors_stackErrors_eq_avg, sum_fin_eq_sum_range_smul]
  by_cases hn : n = 0
  · subst n
    simp
  · have hnpos : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    have hsqrt_ne : Real.sqrt (n : ℝ) ≠ 0 := Real.sqrt_ne_zero'.mpr hnpos
    have hscale : Real.sqrt (n : ℝ) * (n : ℝ)⁻¹ = (Real.sqrt (n : ℝ))⁻¹ := by
      have hsqr_mul : Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = (n : ℝ) := by
        exact Real.mul_self_sqrt hnpos.le
      calc
        Real.sqrt (n : ℝ) * (n : ℝ)⁻¹ =
            Real.sqrt (n : ℝ) * (Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ))⁻¹ := by
          rw [hsqr_mul]
        _ = (Real.sqrt (n : ℝ))⁻¹ := by
          field_simp [hsqrt_ne]
    rw [smul_smul, hscale]

omit [Fintype k] [DecidableEq k] in
/-- The stacked true squared-error average is the range-indexed average used by
Mathlib's WLLN. -/
theorem sampleErrorSecondMoment_stackErrors_eq_avg
    (e : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    sampleErrorSecondMoment (stackErrors e n ω) =
      (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, e i ω ^ 2 := by
  unfold sampleErrorSecondMoment stackErrors
  rw [Fintype.card_fin]
  congr 1
  simp only [dotProduct, pow_two]
  exact Fin.sum_univ_eq_sum_range (fun i => e i ω * e i ω) n

omit [DecidableEq k] in
/-- **Linear-model decomposition of the sample cross moment.**
Under the linear model `yᵢ = Xᵢ·β + eᵢ`, the stacked cross moment splits as
`ĝₙ(y) = Q̂ₙ β + ĝₙ(e)`. This is the algebraic engine that, combined with F2,
decomposes `olsBetaStar − β` into the error-driven term `Q̂ₙ⁻¹ *ᵥ ĝₙ(e)` plus a
residual supported on the singular event `{Q̂ₙ not invertible}`. -/
theorem sampleCrossMoment_stackOutcomes_linear_model
    (X : ℕ → Ω → (k → ℝ)) (e : ℕ → Ω → ℝ) (y : ℕ → Ω → ℝ) (β : k → ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (n : ℕ) (ω : Ω) :
    sampleCrossMoment (stackRegressors X n ω) (stackOutcomes y n ω) =
      sampleGram (stackRegressors X n ω) *ᵥ β +
        sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω) := by
  rw [stack_linear_model X e y β hmodel]
  unfold sampleCrossMoment sampleGram
  rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, smul_add, ← Matrix.smul_mulVec]

/-- **Theorem 7.4 `σ̂²` decomposition for stacked samples.**

Under the linear model, the residual average `σ̂²` splits into the true
squared-error average plus the two Hansen remainder terms. -/
theorem olsSigmaSqHatStar_stack_linear_model
    (X : ℕ → Ω → (k → ℝ)) (e : ℕ → Ω → ℝ) (y : ℕ → Ω → ℝ) (β : k → ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (n : ℕ) (ω : Ω) :
    olsSigmaSqHatStar (stackRegressors X n ω) (stackOutcomes y n ω) =
      sampleErrorSecondMoment (stackErrors e n ω) -
        2 * (sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω) ⬝ᵥ
          (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β)) +
          (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β) ⬝ᵥ
            (sampleGram (stackRegressors X n ω) *ᵥ
              (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β)) := by
  rw [stack_linear_model X e y β hmodel, olsSigmaSqHatStar_linear_model]
  rfl

/-- **Unconditional sample-moment form of `olsBetaStar`.**
For every sample size `n` and every `ω`,
`olsBetaStar X y = Q̂ₙ⁻¹ *ᵥ ĝₙ(y)`, where `Q̂ₙ = n⁻¹ Xᵀ X` and `ĝₙ(y) = n⁻¹ Xᵀ y`.
Unlike Phase 1's `olsBeta_sub_eq_sampleGram_inv_mulVec_sampleCrossMoment`, this
version uses `Matrix.nonsingInv` throughout and so holds on *all* of `Ω`,
including the null event `{Q̂ₙ singular}` where both sides collapse to `0`. -/
theorem olsBetaStar_stack_eq_sampleGramInv_mulVec_sampleCrossMoment
    (X : ℕ → Ω → (k → ℝ)) (y : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) =
      (sampleGram (stackRegressors X n ω))⁻¹ *ᵥ
        sampleCrossMoment (stackRegressors X n ω) (stackOutcomes y n ω) := by
  unfold olsBetaStar sampleGram sampleCrossMoment
  rw [nonsingInv_smul, Matrix.smul_mulVec, Matrix.mulVec_smul, smul_smul,
      Fintype.card_fin]
  by_cases hn : n = 0
  · subst hn
    have h0 : ((stackRegressors X 0 ω)ᵀ *ᵥ (stackOutcomes y 0 ω)) = 0 := by
      funext j
      simp [Matrix.mulVec, dotProduct]
    rw [h0, Matrix.mulVec_zero, smul_zero]
  · have hne : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    rw [inv_inv, mul_inv_cancel₀ hne, one_smul]

/-- **Unconditional residual identity.** Under `yᵢ = Xᵢ·β + eᵢ`,
`β̂ₙ − β − Q̂ₙ⁻¹ *ᵥ ĝₙ(e) = (Q̂ₙ⁻¹ * Q̂ₙ − 1) *ᵥ β`. On the event
`{Q̂ₙ invertible}` the RHS is `0` (since `Q̂ₙ⁻¹ * Q̂ₙ = 1`); off it, `Q̂ₙ⁻¹ = 0`
by `Matrix.nonsing_inv_apply_not_isUnit`, so the RHS is `−β`. The identity
itself holds on all of `Ω`. -/
theorem olsBetaStar_sub_identity
    (X : ℕ → Ω → (k → ℝ)) (e : ℕ → Ω → ℝ) (y : ℕ → Ω → ℝ) (β : k → ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (n : ℕ) (ω : Ω) :
    olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β
      - (sampleGram (stackRegressors X n ω))⁻¹ *ᵥ
          sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω) =
      ((sampleGram (stackRegressors X n ω))⁻¹ *
          sampleGram (stackRegressors X n ω) - 1) *ᵥ β := by
  rw [olsBetaStar_stack_eq_sampleGramInv_mulVec_sampleCrossMoment,
      sampleCrossMoment_stackOutcomes_linear_model X e y β hmodel,
      Matrix.mulVec_add, Matrix.mulVec_mulVec,
      Matrix.sub_mulVec, Matrix.one_mulVec]
  abel

end Stacking

end HansenEconometrics
