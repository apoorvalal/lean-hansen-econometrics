import Mathlib
import HansenEconometrics.Basic
import HansenEconometrics.Chapter3LeastSquaresAlgebra
import HansenEconometrics.Chapter4LeastSquaresRegression

/-!
# Chapter 7 — Asymptotic Theory (Phase 1 deterministic scaffold)

This file lays the deterministic groundwork for Hansen's asymptotic chapter.
It introduces the finite-sample empirical moment objects

* `sampleGram X        = Xᵀ X / n`   — sample analogue of `Q := E[X Xᵀ]`
* `sampleCrossMoment X e = (Xᵀ e) / n` — sample analogue of `E[X e]`

and proves the algebraic identity that is the deterministic engine behind
Hansen Theorem 7.1 (Consistency of Least Squares):

  β̂ₙ - β = Q̂ₙ⁻¹ *ᵥ g̑ₙ.

No probabilistic infrastructure is imported here beyond what Chapter 4 already
uses. The iid-sample bridge, WLLN wrapper, and continuous-mapping steps that
upgrade this identity into `β̂ₙ →ₚ β` live in a separate module and are
scheduled for Phase 2.
-/

open scoped Matrix

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

end Stacking

end HansenEconometrics
