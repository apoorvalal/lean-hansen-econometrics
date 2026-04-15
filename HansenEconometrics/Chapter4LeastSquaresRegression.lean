import Mathlib
import HansenEconometrics.Basic
import HansenEconometrics.Chapter3Projections
import HansenEconometrics.Chapter2CondExp

open scoped Matrix

namespace HansenEconometrics

open Matrix

variable {n k : Type*}
variable [Fintype n] [Fintype k] [DecidableEq k]

/-- Hansen equation (4.6): OLS equals the true coefficient plus the projected error. -/
theorem olsBeta_linear_decomposition
    (X : Matrix n k ℝ) (β : k → ℝ) (e : n → ℝ) [Invertible (Xᵀ * X)] :
    olsBeta X (X *ᵥ β + e) = β + (⅟ (Xᵀ * X)) *ᵥ (Xᵀ *ᵥ e) := by
  unfold olsBeta
  rw [Matrix.mulVec_add]
  have hxx : Xᵀ *ᵥ (X *ᵥ β) = (Xᵀ * X) *ᵥ β := by
    rw [Matrix.mulVec_mulVec]
  rw [hxx, Matrix.mulVec_add]
  rw [Matrix.mulVec_mulVec β (⅟ (Xᵀ * X)) (Xᵀ * X)]
  rw [invOf_mul_self]
  simp

/-- If the model error is orthogonal to the regressors, the closed-form OLS coefficient is `β`. -/
theorem olsBeta_eq_of_regressors_orthogonal_error
    (X : Matrix n k ℝ) (β : k → ℝ) (e : n → ℝ) [Invertible (Xᵀ * X)]
    (he : Xᵀ *ᵥ e = 0) :
    olsBeta X (X *ᵥ β + e) = β := by
  rw [olsBeta_linear_decomposition, he]
  simp

/-- In the finite-sample linear model, fitted values equal signal plus projected error. -/
theorem fitted_linear_model
    (X : Matrix n k ℝ) (β : k → ℝ) (e : n → ℝ) [Invertible (Xᵀ * X)] :
    fitted X (X *ᵥ β + e) = X *ᵥ β + hatMatrix X *ᵥ e := by
  unfold fitted
  rw [olsBeta_linear_decomposition, Matrix.mulVec_add]
  rw [← hat_mul_y_eq_closed_form_fit]

/-- In the finite-sample linear model, OLS residuals are the annihilator applied to the error. -/
theorem residual_linear_model
    (X : Matrix n k ℝ) (β : k → ℝ) (e : n → ℝ) [DecidableEq n]
    [Invertible (Xᵀ * X)] :
    residual X (X *ᵥ β + e) = annihilatorMatrix X *ᵥ e := by
  unfold residual annihilatorMatrix
  rw [fitted_linear_model, Matrix.sub_mulVec, Matrix.one_mulVec]
  ext i
  simp [sub_eq_add_neg, add_assoc, add_comm]

/-- Hansen Theorem 4.2 matrix core: conditional covariance formula for OLS. -/
noncomputable def olsConditionalVarianceMatrix
    (X : Matrix n k ℝ) (D : Matrix n n ℝ) [Invertible (Xᵀ * X)] : Matrix k k ℝ :=
  ⅟ (Xᵀ * X) * Xᵀ * D * X * ⅟ (Xᵀ * X)

/-- The covariance formula written as `Aᵀ D A`, where `A = X (XᵀX)⁻¹`. -/
theorem olsConditionalVarianceMatrix_eq_Atranspose_D_A
    (X : Matrix n k ℝ) (D : Matrix n n ℝ) [Invertible (Xᵀ * X)] :
    (X * ⅟ (Xᵀ * X))ᵀ * D * (X * ⅟ (Xᵀ * X)) =
      olsConditionalVarianceMatrix X D := by
  unfold olsConditionalVarianceMatrix
  rw [Matrix.transpose_mul, inv_gram_transpose]
  simp [Matrix.mul_assoc]

/-- Hansen Theorem 4.2 homoskedastic simplification: `D = σ² I`. -/
theorem olsConditionalVarianceMatrix_homoskedastic
    (X : Matrix n k ℝ) (σ2 : ℝ) [DecidableEq n] [Invertible (Xᵀ * X)] :
    olsConditionalVarianceMatrix X (σ2 • (1 : Matrix n n ℝ)) =
      σ2 • ⅟ (Xᵀ * X) := by
  unfold olsConditionalVarianceMatrix
  rw [Matrix.mul_assoc (⅟ (Xᵀ * X) * Xᵀ) (σ2 • (1 : Matrix n n ℝ)) X]
  simp [Matrix.mul_assoc]

/-- Deterministic core of the Gauss-Markov theorem: the variance-gap matrix is positive semidefinite. -/
theorem gaussMarkov_variance_gap_posSemidef
    (X A : Matrix n k ℝ) [Invertible (Xᵀ * X)]
    (hAX : Aᵀ * X = (1 : Matrix k k ℝ)) :
    (Aᵀ * A - ⅟ (Xᵀ * X)).PosSemidef := by
  let C : Matrix k n ℝ := Aᵀ - ⅟ (Xᵀ * X) * Xᵀ
  have hgap : C * Cᵀ = Aᵀ * A - ⅟ (Xᵀ * X) := by
    have hXA : Xᵀ * A = (1 : Matrix k k ℝ) := by
      simpa using congrArg Matrix.transpose hAX
    dsimp [C]
    rw [Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_transpose, inv_gram_transpose]
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub]
    have h1 : Aᵀ * (X * ⅟ (Xᵀ * X)) = ⅟ (Xᵀ * X) := by
      calc
        Aᵀ * (X * ⅟ (Xᵀ * X)) = (Aᵀ * X) * ⅟ (Xᵀ * X) := by rw [Matrix.mul_assoc]
        _ = 1 * ⅟ (Xᵀ * X) := by rw [hAX]
        _ = ⅟ (Xᵀ * X) := by simp
    have h2' : (Xᵀ * X)⁻¹ - (Xᵀ * X)⁻¹ * (Xᵀ * (X * (Xᵀ * X)⁻¹)) = 0 := by
      have hcancel : Xᵀ * (X * (Xᵀ * X)⁻¹) = (1 : Matrix k k ℝ) := by
        rw [← Matrix.mul_assoc]
        simpa using (mul_invOf_self (Xᵀ * X))
      rw [hcancel]
      simp
    have h1' : Aᵀ * (X * (Xᵀ * X)⁻¹) = (Xᵀ * X)⁻¹ := by
      simpa using h1
    simp [Matrix.transpose_transpose, Matrix.mul_assoc, hXA]
    rw [h1', h2']
    abel_nf
  have hpsd : (C * Cᵀ).PosSemidef := by
    simpa [Matrix.conjTranspose, Matrix.transpose_transpose] using
      (Matrix.posSemidef_self_mul_conjTranspose C)
  simpa [hgap] using hpsd

section ConditionalUnbiasedness

open scoped ENNReal Topology MeasureTheory ProbabilityTheory
open MeasureTheory

variable {Ω : Type*}
variable {m m₀ : MeasurableSpace Ω} {μ : Measure Ω}

/-- Componentwise conditional unbiasedness of OLS under conditional mean-zero errors. -/
theorem ols_condExp_coordinate_eq_beta
    (X : Matrix n k ℝ) (β : k → ℝ) (e : Ω → n → ℝ) (j : k)
    [Invertible (Xᵀ * X)] [IsProbabilityMeasure μ]
    (hm : m ≤ m₀) [SigmaFinite (μ.trim hm)]
    (he_int : ∀ i, Integrable (fun ω => e ω i) μ)
    (he_zero : ∀ i, μ[fun ω => e ω i | m] =ᵐ[μ] 0) :
    μ[fun ω => olsBeta X (X *ᵥ β + e ω) j | m] =ᵐ[μ] fun _ => β j := by
  let w : Matrix k n ℝ := ⅟ (Xᵀ * X) * Xᵀ
  have hrepr : (fun ω => olsBeta X (X *ᵥ β + e ω) j) =
      fun ω => β j + ∑ i, w j i * e ω i := by
    funext ω
    rw [olsBeta_linear_decomposition]
    simp [w, Matrix.mulVec, dotProduct]
  rw [hrepr]
  have hsum_int : Integrable (fun ω => ∑ i, w j i * e ω i) μ := by
    simpa using MeasureTheory.integrable_finset_sum (s := Finset.univ)
      (f := fun i ω => w j i * e ω i)
      (fun i _ => (he_int i).const_mul (w j i))
  have hconst : μ[(fun _ : Ω => β j) | m] = fun _ => β j := by
    simpa using MeasureTheory.condExp_const (μ := μ) (m := m) (m₀ := m₀) hm (β j)
  have hsum_repr : (fun ω => ∑ i, w j i * e ω i) = ∑ i, fun ω => w j i * e ω i := by
    funext ω
    simp
  have hsum_ce : μ[(fun ω => ∑ i, w j i * e ω i) | m] =ᵐ[μ]
      ∑ i, μ[(fun ω => w j i * e ω i) | m] := by
    rw [hsum_repr]
    simpa using MeasureTheory.condExp_finset_sum (μ := μ) (m := m)
      (s := Finset.univ) (f := fun i ω => w j i * e ω i)
      (fun i _ => (he_int i).const_mul (w j i))
  have hsum_smul : (∑ i, μ[(fun ω => w j i * e ω i) | m]) =ᵐ[μ]
      ∑ i, (fun ω => w j i * μ[fun ω => e ω i | m] ω) := by
    classical
    refine Finset.induction_on (Finset.univ : Finset n) ?_ ?_
    · simp
    · intro a s ha ih
      have ha' : μ[(fun ω => w j a * e ω a) | m] =ᵐ[μ]
          (fun ω => w j a * μ[fun ω => e ω a | m] ω) := by
        simpa [Pi.smul_apply, smul_eq_mul] using
          (MeasureTheory.condExp_smul (μ := μ) (m := m) (w j a) (fun ω => e ω a))
      simpa [Finset.sum_insert, ha] using ha'.add ih
  have hsum_zero : (∑ i, (fun ω => w j i * μ[fun ω => e ω i | m] ω)) =ᵐ[μ] 0 := by
    classical
    refine Finset.induction_on (Finset.univ : Finset n) ?_ ?_
    · simp
    · intro a s ha ih
      have hzeroa : (fun ω => w j a * μ[fun ω => e ω a | m] ω) =ᵐ[μ] 0 := by
        filter_upwards [he_zero a] with ω hω
        simp [hω]
      simpa [Finset.sum_insert, ha] using hzeroa.add ih
  have hsum_final : μ[(fun ω => ∑ i, w j i * e ω i) | m] =ᵐ[μ] 0 :=
    hsum_ce.trans (hsum_smul.trans hsum_zero)
  calc
    μ[(fun ω => β j + ∑ i, w j i * e ω i) | m]
        =ᵐ[μ] μ[(fun _ : Ω => β j) | m] + μ[(fun ω => ∑ i, w j i * e ω i) | m] := by
          simpa using MeasureTheory.condExp_add (μ := μ) (m := m)
            (integrable_const (β j)) hsum_int
    _ =ᵐ[μ] (fun _ => β j) + 0 := by
          rw [hconst]
          exact Filter.EventuallyEq.add Filter.EventuallyEq.rfl hsum_final
    _ =ᵐ[μ] fun _ => β j := by simp

/-- Componentwise unconditional unbiasedness from the conditional mean-zero assumption. -/
theorem ols_integral_coordinate_eq_beta
    (X : Matrix n k ℝ) (β : k → ℝ) (e : Ω → n → ℝ) (j : k)
    [Invertible (Xᵀ * X)] [IsProbabilityMeasure μ]
    (hm : m ≤ m₀) [SigmaFinite (μ.trim hm)]
    (he_int : ∀ i, Integrable (fun ω => e ω i) μ)
    (he_zero : ∀ i, μ[fun ω => e ω i | m] =ᵐ[μ] 0) :
    ∫ ω, olsBeta X (X *ᵥ β + e ω) j ∂μ = β j := by
  calc
    ∫ ω, olsBeta X (X *ᵥ β + e ω) j ∂μ = ∫ ω, μ[fun ω => olsBeta X (X *ᵥ β + e ω) j | m] ω ∂μ := by
      symm
      exact MeasureTheory.integral_condExp (μ := μ) (m := m) (m₀ := m₀)
        (f := fun ω => olsBeta X (X *ᵥ β + e ω) j) hm
    _ = ∫ ω, β j ∂μ := by
      refine MeasureTheory.integral_congr_ae ?_
      exact ols_condExp_coordinate_eq_beta (μ := μ) (m := m) X β e j hm he_int he_zero
    _ = β j := by simp

/-- Uniform coordinatewise conditional unbiasedness of OLS. -/
theorem ols_condExp_all_coordinates_eq_beta
    (X : Matrix n k ℝ) (β : k → ℝ) (e : Ω → n → ℝ)
    [Invertible (Xᵀ * X)] [IsProbabilityMeasure μ]
    (hm : m ≤ m₀) [SigmaFinite (μ.trim hm)]
    (he_int : ∀ i, Integrable (fun ω => e ω i) μ)
    (he_zero : ∀ i, μ[fun ω => e ω i | m] =ᵐ[μ] 0) :
    ∀ j, μ[fun ω => olsBeta X (X *ᵥ β + e ω) j | m] =ᵐ[μ] fun _ => β j := by
  intro j
  exact ols_condExp_coordinate_eq_beta (μ := μ) (m := m) X β e j hm he_int he_zero

/-- Vector-valued conditional unbiasedness of OLS. -/
theorem ols_condExp_eq_beta
    (X : Matrix n k ℝ) (β : k → ℝ) (e : Ω → n → ℝ)
    [Invertible (Xᵀ * X)] [IsProbabilityMeasure μ]
    (hm : m ≤ m₀) [SigmaFinite (μ.trim hm)]
    (he_int : ∀ i, Integrable (fun ω => e ω i) μ)
    (he_zero : ∀ i, μ[fun ω => e ω i | m] =ᵐ[μ] 0) :
    μ[(fun ω => olsBeta X (X *ᵥ β + e ω)) | m] =ᵐ[μ] fun _ => β := by
  let f : Ω → k → ℝ := fun ω => olsBeta X (X *ᵥ β + e ω)
  have hf_int : Integrable f μ := by
    refine Integrable.of_eval ?_
    intro j
    let w : Matrix k n ℝ := ⅟ (Xᵀ * X) * Xᵀ
    have hrepr : (fun ω => f ω j) = fun ω => β j + ∑ i, w j i * e ω i := by
      funext ω
      simp [f, olsBeta_linear_decomposition, w, Matrix.mulVec, dotProduct]
    rw [hrepr]
    have hsum_int : Integrable (fun ω => ∑ i, w j i * e ω i) μ := by
      simpa using MeasureTheory.integrable_finset_sum (s := Finset.univ)
        (f := fun i ω => w j i * e ω i)
        (fun i _ => (he_int i).const_mul (w j i))
    exact (integrable_const (β j)).add hsum_int
  rw [Filter.EventuallyEq]
  change ∀ᵐ ω ∂μ, μ[f | m] ω = β
  have hcoord : ∀ j : k, ∀ᵐ ω ∂μ, μ[f | m] ω j = β j := by
    intro j
    have happly : (fun ω => μ[f | m] ω j) =ᵐ[μ] μ[(fun ω => f ω j) | m] := by
      simpa [f] using
        (ContinuousLinearMap.proj (R := ℝ) j).comp_condExp_comm (μ := μ) (m := m)
          (f := f) hf_int
    exact happly.trans <|
      ols_condExp_coordinate_eq_beta (μ := μ) (m := m) X β e j hm he_int he_zero
  have hall : ∀ᵐ ω ∂μ, ∀ j : k, μ[f | m] ω j = β j := by
    exact ae_all_iff.2 hcoord
  exact hall.mono fun ω hω => by
    funext j
    exact hω j

/-- Uniform coordinatewise unconditional unbiasedness of OLS. -/
theorem ols_integral_all_coordinates_eq_beta
    (X : Matrix n k ℝ) (β : k → ℝ) (e : Ω → n → ℝ)
    [Invertible (Xᵀ * X)] [IsProbabilityMeasure μ]
    (hm : m ≤ m₀) [SigmaFinite (μ.trim hm)]
    (he_int : ∀ i, Integrable (fun ω => e ω i) μ)
    (he_zero : ∀ i, μ[fun ω => e ω i | m] =ᵐ[μ] 0) :
    ∀ j, ∫ ω, olsBeta X (X *ᵥ β + e ω) j ∂μ = β j := by
  intro j
  exact ols_integral_coordinate_eq_beta (μ := μ) (m := m) X β e j hm he_int he_zero

/-- Vector-valued unconditional unbiasedness of OLS. -/
theorem ols_integral_eq_beta
    (X : Matrix n k ℝ) (β : k → ℝ) (e : Ω → n → ℝ)
    [Invertible (Xᵀ * X)] [IsProbabilityMeasure μ]
    (hm : m ≤ m₀) [SigmaFinite (μ.trim hm)]
    (he_int : ∀ i, Integrable (fun ω => e ω i) μ)
    (he_zero : ∀ i, μ[fun ω => e ω i | m] =ᵐ[μ] 0) :
    ∫ ω, olsBeta X (X *ᵥ β + e ω) ∂μ = β := by
  let f : Ω → k → ℝ := fun ω => olsBeta X (X *ᵥ β + e ω)
  have hf_int : Integrable f μ := by
    refine Integrable.of_eval ?_
    intro j
    let w : Matrix k n ℝ := ⅟ (Xᵀ * X) * Xᵀ
    have hrepr : (fun ω => f ω j) = fun ω => β j + ∑ i, w j i * e ω i := by
      funext ω
      simp [f, olsBeta_linear_decomposition, w, Matrix.mulVec, dotProduct]
    rw [hrepr]
    have hsum_int : Integrable (fun ω => ∑ i, w j i * e ω i) μ := by
      simpa using MeasureTheory.integrable_finset_sum (s := Finset.univ)
        (f := fun i ω => w j i * e ω i)
        (fun i _ => (he_int i).const_mul (w j i))
    exact (integrable_const (β j)).add hsum_int
  funext j
  calc
    (∫ ω, olsBeta X (X *ᵥ β + e ω) ∂μ) j = ∫ ω, olsBeta X (X *ᵥ β + e ω) j ∂μ := by
      simpa [f] using MeasureTheory.eval_integral (μ := μ)
        (f := f) (hf := fun j => Integrable.eval hf_int j) j
    _ = β j := ols_integral_coordinate_eq_beta (μ := μ) (m := m) X β e j hm he_int he_zero

end ConditionalUnbiasedness

/-- Generalized least squares estimator with weight matrix `Ω⁻¹`. -/
noncomputable def glsBeta
    (X : Matrix n k ℝ) (Ω : Matrix n n ℝ) (y : n → ℝ)
    [DecidableEq n] [Invertible Ω] [Invertible (Xᵀ * ⅟Ω * X)] : k → ℝ :=
  (⅟ (Xᵀ * ⅟Ω * X)) *ᵥ (Xᵀ *ᵥ ((⅟Ω) *ᵥ y))

/-- GLS equals the true coefficient plus the weighted projected error. -/
theorem glsBeta_linear_decomposition
    (X : Matrix n k ℝ) (Ω : Matrix n n ℝ) (β : k → ℝ) (e : n → ℝ)
    [DecidableEq n] [Invertible Ω] [Invertible (Xᵀ * ⅟Ω * X)] :
    glsBeta X Ω (X *ᵥ β + e) = β + (⅟ (Xᵀ * ⅟Ω * X)) *ᵥ (Xᵀ *ᵥ ((⅟Ω) *ᵥ e)) := by
  unfold glsBeta
  rw [Matrix.mulVec_add, Matrix.mulVec_add]
  have hmain : Xᵀ *ᵥ ((⅟Ω) *ᵥ (X *ᵥ β)) = (Xᵀ * ⅟Ω * X) *ᵥ β := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  rw [hmain]
  rw [Matrix.mulVec_add]
  rw [Matrix.mulVec_mulVec β (⅟ (Xᵀ * ⅟Ω * X)) (Xᵀ * ⅟Ω * X)]
  rw [invOf_mul_self]
  simp

/-- If the GLS-weighted error is orthogonal to the regressors, GLS recovers `β`. -/
theorem glsBeta_eq_of_weighted_regressors_orthogonal_error
    (X : Matrix n k ℝ) (Ω : Matrix n n ℝ) (β : k → ℝ) (e : n → ℝ)
    [DecidableEq n] [Invertible Ω] [Invertible (Xᵀ * ⅟Ω * X)]
    (he : Xᵀ *ᵥ ((⅟Ω) *ᵥ e) = 0) :
    glsBeta X Ω (X *ᵥ β + e) = β := by
  rw [glsBeta_linear_decomposition, he]
  simp

end HansenEconometrics
