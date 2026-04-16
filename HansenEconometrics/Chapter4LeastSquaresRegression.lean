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

/-- Coordinatewise conditional covariance bridge for OLS. -/
theorem ols_condExp_centered_mul_eq_variance_entry
    (X : Matrix n k ℝ) (β : k → ℝ) (e : Ω → n → ℝ) (D : Matrix n n ℝ) (j l : k)
    [Invertible (Xᵀ * X)] [IsProbabilityMeasure μ]
    (hm : m ≤ m₀) [SigmaFinite (μ.trim hm)]
    (hee_int : ∀ i r, Integrable (fun ω => e ω i * e ω r) μ)
    (hD : ∀ i r, μ[fun ω => e ω i * e ω r | m] =ᵐ[μ] fun _ => D i r) :
    μ[fun ω => (olsBeta X (X *ᵥ β + e ω) j - β j) *
        (olsBeta X (X *ᵥ β + e ω) l - β l) | m] =ᵐ[μ]
      fun _ => olsConditionalVarianceMatrix X D j l := by
  let w : Matrix k n ℝ := ⅟ (Xᵀ * X) * Xᵀ
  have hj : (fun ω => olsBeta X (X *ᵥ β + e ω) j - β j) = fun ω => ∑ i, w j i * e ω i := by
    funext ω
    rw [olsBeta_linear_decomposition]
    simp [w, Matrix.mulVec, dotProduct]
  have hl : (fun ω => olsBeta X (X *ᵥ β + e ω) l - β l) = fun ω => ∑ r, w l r * e ω r := by
    funext ω
    rw [olsBeta_linear_decomposition]
    simp [w, Matrix.mulVec, dotProduct]
  have hprod :
      (fun ω => (olsBeta X (X *ᵥ β + e ω) j - β j) *
        (olsBeta X (X *ᵥ β + e ω) l - β l)) =
      fun ω => ∑ i, ∑ r, (w j i * w l r) * (e ω i * e ω r) := by
    funext ω
    rw [show olsBeta X (X *ᵥ β + e ω) j - β j = ∑ i, w j i * e ω i by exact congrFun hj ω]
    rw [show olsBeta X (X *ᵥ β + e ω) l - β l = ∑ r, w l r * e ω r by exact congrFun hl ω]
    calc
      (∑ i, w j i * e ω i) * (∑ r, w l r * e ω r)
          = ∑ r, (∑ i, w j i * e ω i) * (w l r * e ω r) := by rw [Finset.mul_sum]
      _ = ∑ r, ∑ i, (w j i * e ω i) * (w l r * e ω r) := by simp [Finset.sum_mul]
      _ = ∑ i, ∑ r, (w j i * w l r) * (e ω i * e ω r) := by
            rw [Finset.sum_comm]
            simp [mul_assoc, mul_left_comm, mul_comm]
  rw [hprod]
  have hint : Integrable (fun ω => ∑ i, ∑ r, (w j i * w l r) * (e ω i * e ω r)) μ := by
    simpa using MeasureTheory.integrable_finset_sum (s := Finset.univ)
      (f := fun i ω => ∑ r, (w j i * w l r) * (e ω i * e ω r))
      (fun i _ => by
        simpa using MeasureTheory.integrable_finset_sum (s := Finset.univ)
          (f := fun r ω => (w j i * w l r) * (e ω i * e ω r))
          (fun r _ => (hee_int i r).const_mul (w j i * w l r)))
  have hsum1 :
      μ[(fun ω => ∑ i, ∑ r, (w j i * w l r) * (e ω i * e ω r)) | m] =ᵐ[μ]
        ∑ i, μ[(fun ω => ∑ r, (w j i * w l r) * (e ω i * e ω r)) | m] := by
    have hrepr :
        (fun ω => ∑ i, ∑ r, (w j i * w l r) * (e ω i * e ω r)) =
          ∑ i, fun ω => ∑ r, (w j i * w l r) * (e ω i * e ω r) := by
      funext ω
      simp
    rw [hrepr]
    simpa using MeasureTheory.condExp_finset_sum (μ := μ) (m := m)
      (s := Finset.univ)
      (f := fun i ω => ∑ r, (w j i * w l r) * (e ω i * e ω r))
      (fun i _ => by
        simpa using MeasureTheory.integrable_finset_sum (s := Finset.univ)
          (f := fun r ω => (w j i * w l r) * (e ω i * e ω r))
          (fun r _ => (hee_int i r).const_mul (w j i * w l r)))
  have hsum2 :
      (∑ i, μ[(fun ω => ∑ r, (w j i * w l r) * (e ω i * e ω r)) | m]) =ᵐ[μ]
        ∑ i, ∑ r, (fun ω => (w j i * w l r) * D i r) := by
    have hinner : ∀ i,
        μ[(fun ω => ∑ r, (w j i * w l r) * (e ω i * e ω r)) | m] =ᵐ[μ]
          ∑ r, μ[(fun ω => (w j i * w l r) * (e ω i * e ω r)) | m] := by
      intro i
      have hrepr :
          (fun ω => ∑ r, (w j i * w l r) * (e ω i * e ω r)) =
            ∑ r, fun ω => (w j i * w l r) * (e ω i * e ω r) := by
        funext ω
        simp
      rw [hrepr]
      simpa using MeasureTheory.condExp_finset_sum (μ := μ) (m := m)
        (s := Finset.univ)
        (f := fun r ω => (w j i * w l r) * (e ω i * e ω r))
        (fun r _ => (hee_int i r).const_mul (w j i * w l r))
    have hcoord : ∀ i r,
        μ[(fun ω => (w j i * w l r) * (e ω i * e ω r)) | m] =ᵐ[μ]
          (fun ω => (w j i * w l r) * D i r) := by
      intro i r
      refine (MeasureTheory.condExp_smul (μ := μ) (m := m) (w j i * w l r)
        (fun ω => e ω i * e ω r)).trans ?_
      filter_upwards [hD i r] with ω hω
      simp [Pi.smul_apply, smul_eq_mul, hω]
    have hall1 : ∀ᵐ ω ∂μ, ∀ i, μ[(fun ω => ∑ r, (w j i * w l r) * (e ω i * e ω r)) | m] ω =
        ∑ r, μ[(fun ω => (w j i * w l r) * (e ω i * e ω r)) | m] ω := by
      exact ae_all_iff.2 fun i => by simpa [Filter.EventuallyEq] using hinner i
    have hall2 : ∀ᵐ ω ∂μ, ∀ i, ∀ r,
        μ[(fun ω => (w j i * w l r) * (e ω i * e ω r)) | m] ω = (w j i * w l r) * D i r := by
      exact ae_all_iff.2 fun i => ae_all_iff.2 fun r => hcoord i r
    filter_upwards [hall1, hall2] with ω h1 h2
    simp [h1, h2]
  have hvar_repr : olsConditionalVarianceMatrix X D = w * D * wᵀ := by
    unfold olsConditionalVarianceMatrix w
    rw [Matrix.transpose_mul, Matrix.transpose_transpose, inv_gram_transpose]
    simp [Matrix.mul_assoc]
  have hentry : olsConditionalVarianceMatrix X D j l = ∑ i, ∑ r, (w j i * w l r) * D i r := by
    rw [hvar_repr, Matrix.mul_apply]
    calc
      ∑ t, (w * D) j t * wᵀ t l = ∑ t, (w * D) j t * w l t := by
        simp [Matrix.transpose_apply]
      _ = ∑ t, (∑ r, w j r * D r t) * w l t := by
        simp [Matrix.mul_apply]
      _ = ∑ t, ∑ r, w j r * D r t * w l t := by
        simp [Finset.sum_mul, mul_assoc]
      _ = ∑ r, ∑ t, w j r * D r t * w l t := by
        rw [Finset.sum_comm]
      _ = ∑ i, ∑ r, (w j i * w l r) * D i r := by
        simp [mul_assoc, mul_comm]
  exact (hsum1.trans hsum2).trans <| by
    filter_upwards [] with ω
    simp [hentry]

/-- Matrix-valued conditional covariance bridge for OLS. -/
theorem ols_condExp_centered_mul_eq_variance_matrix
    (X : Matrix n k ℝ) (β : k → ℝ) (e : Ω → n → ℝ) (D : Matrix n n ℝ)
    [Invertible (Xᵀ * X)] [IsProbabilityMeasure μ]
    (hm : m ≤ m₀) [SigmaFinite (μ.trim hm)]
    (hee_int : ∀ i r, Integrable (fun ω => e ω i * e ω r) μ)
    (hD : ∀ i r, μ[fun ω => e ω i * e ω r | m] =ᵐ[μ] fun _ => D i r) :
    μ[(fun ω => fun j l =>
      (olsBeta X (X *ᵥ β + e ω) j - β j) *
        (olsBeta X (X *ᵥ β + e ω) l - β l)) | m] =ᵐ[μ]
      fun _ => olsConditionalVarianceMatrix X D := by
  let f : Ω → k → k → ℝ := fun ω j l =>
    (olsBeta X (X *ᵥ β + e ω) j - β j) *
      (olsBeta X (X *ᵥ β + e ω) l - β l)
  have hf_eval_int : ∀ j l, Integrable (fun ω => f ω j l) μ := by
    intro j l
    let w : Matrix k n ℝ := ⅟ (Xᵀ * X) * Xᵀ
    have hrepr :
        (fun ω => f ω j l) =
          fun ω => ∑ i, ∑ r, (w j i * w l r) * (e ω i * e ω r) := by
      funext ω
      dsimp [f]
      rw [show olsBeta X (X *ᵥ β + e ω) j - β j = ∑ i, w j i * e ω i by
          rw [olsBeta_linear_decomposition]
          simp [w, Matrix.mulVec, dotProduct]]
      rw [show olsBeta X (X *ᵥ β + e ω) l - β l = ∑ r, w l r * e ω r by
          rw [olsBeta_linear_decomposition]
          simp [w, Matrix.mulVec, dotProduct]]
      calc
        (∑ i, w j i * e ω i) * (∑ r, w l r * e ω r)
            = ∑ r, (∑ i, w j i * e ω i) * (w l r * e ω r) := by rw [Finset.mul_sum]
        _ = ∑ r, ∑ i, (w j i * e ω i) * (w l r * e ω r) := by simp [Finset.sum_mul]
        _ = ∑ i, ∑ r, (w j i * w l r) * (e ω i * e ω r) := by
              rw [Finset.sum_comm]
              simp [mul_assoc, mul_left_comm, mul_comm]
    rw [hrepr]
    simpa using MeasureTheory.integrable_finset_sum (s := Finset.univ)
      (f := fun i ω => ∑ r, (w j i * w l r) * (e ω i * e ω r))
      (fun i _ => by
        simpa using MeasureTheory.integrable_finset_sum (s := Finset.univ)
          (f := fun r ω => (w j i * w l r) * (e ω i * e ω r))
          (fun r _ => (hee_int i r).const_mul (w j i * w l r)))
  have hf_int : Integrable f μ := by
    refine Integrable.of_eval ?_
    intro j
    refine Integrable.of_eval ?_
    intro l
    exact hf_eval_int j l
  rw [Filter.EventuallyEq]
  change ∀ᵐ ω ∂μ, μ[f | m] ω = olsConditionalVarianceMatrix X D
  have hcoord : ∀ j l : k, ∀ᵐ ω ∂μ, μ[f | m] ω j l = olsConditionalVarianceMatrix X D j l := by
    intro j l
    have happly_j : (fun ω => μ[f | m] ω j) =ᵐ[μ] μ[(fun ω => f ω j) | m] := by
      simpa [f] using
        (ContinuousLinearMap.proj (R := ℝ) j).comp_condExp_comm (μ := μ) (m := m)
          (f := f) hf_int
    have happly_l : (fun ω => μ[(fun ω => f ω j) | m] ω l) =ᵐ[μ] μ[(fun ω => f ω j l) | m] := by
      simpa [f] using
        (ContinuousLinearMap.proj (R := ℝ) l).comp_condExp_comm (μ := μ) (m := m)
          (f := fun ω => f ω j) (Integrable.eval hf_int j)
    have happly_jl : (fun ω => μ[f | m] ω j l) =ᵐ[μ] fun ω => μ[(fun ω => f ω j) | m] ω l := by
      filter_upwards [happly_j] with ω hω
      exact congrFun hω l
    exact happly_jl.trans <| happly_l.trans <|
      ols_condExp_centered_mul_eq_variance_entry
        (μ := μ) (m := m) X β e D j l hm hee_int hD
  have hall : ∀ᵐ ω ∂μ, ∀ j l : k, μ[f | m] ω j l = olsConditionalVarianceMatrix X D j l := by
    exact ae_all_iff.2 fun j => ae_all_iff.2 fun l => hcoord j l
  exact hall.mono fun ω hω => by
    funext j l
    exact hω j l

/-- Matrix-valued unconditional covariance bridge for OLS. -/
theorem ols_integral_centered_mul_eq_variance_matrix
    (X : Matrix n k ℝ) (β : k → ℝ) (e : Ω → n → ℝ) (D : Matrix n n ℝ)
    [Invertible (Xᵀ * X)] [IsProbabilityMeasure μ]
    (hm : m ≤ m₀) [SigmaFinite (μ.trim hm)]
    (hee_int : ∀ i r, Integrable (fun ω => e ω i * e ω r) μ)
    (hD : ∀ i r, μ[fun ω => e ω i * e ω r | m] =ᵐ[μ] fun _ => D i r) :
    ∫ ω, (fun j l =>
      (olsBeta X (X *ᵥ β + e ω) j - β j) *
        (olsBeta X (X *ᵥ β + e ω) l - β l)) ∂μ =
      olsConditionalVarianceMatrix X D := by
  let f : Ω → k → k → ℝ := fun ω j l =>
    (olsBeta X (X *ᵥ β + e ω) j - β j) *
      (olsBeta X (X *ᵥ β + e ω) l - β l)
  have hf_eval_int : ∀ j l, Integrable (fun ω => f ω j l) μ := by
    intro j l
    let w : Matrix k n ℝ := ⅟ (Xᵀ * X) * Xᵀ
    have hrepr :
        (fun ω => f ω j l) =
          fun ω => ∑ i, ∑ r, (w j i * w l r) * (e ω i * e ω r) := by
      funext ω
      dsimp [f]
      rw [show olsBeta X (X *ᵥ β + e ω) j - β j = ∑ i, w j i * e ω i by
          rw [olsBeta_linear_decomposition]
          simp [w, Matrix.mulVec, dotProduct]]
      rw [show olsBeta X (X *ᵥ β + e ω) l - β l = ∑ r, w l r * e ω r by
          rw [olsBeta_linear_decomposition]
          simp [w, Matrix.mulVec, dotProduct]]
      calc
        (∑ i, w j i * e ω i) * (∑ r, w l r * e ω r)
            = ∑ r, (∑ i, w j i * e ω i) * (w l r * e ω r) := by rw [Finset.mul_sum]
        _ = ∑ r, ∑ i, (w j i * e ω i) * (w l r * e ω r) := by simp [Finset.sum_mul]
        _ = ∑ i, ∑ r, (w j i * w l r) * (e ω i * e ω r) := by
              rw [Finset.sum_comm]
              simp [mul_assoc, mul_left_comm, mul_comm]
    rw [hrepr]
    simpa using MeasureTheory.integrable_finset_sum (s := Finset.univ)
      (f := fun i ω => ∑ r, (w j i * w l r) * (e ω i * e ω r))
      (fun i _ => by
        simpa using MeasureTheory.integrable_finset_sum (s := Finset.univ)
          (f := fun r ω => (w j i * w l r) * (e ω i * e ω r))
          (fun r _ => (hee_int i r).const_mul (w j i * w l r)))
  have hf_int : Integrable f μ := by
    refine Integrable.of_eval ?_
    intro j
    refine Integrable.of_eval ?_
    intro l
    exact hf_eval_int j l
  funext j l
  have houter : (∫ ω, f ω ∂μ) j = ∫ ω, f ω j ∂μ := by
    simpa using MeasureTheory.eval_integral (μ := μ)
      (f := f) (hf := fun j => Integrable.eval hf_int j) j
  have hinner : (∫ ω, f ω j ∂μ) l = ∫ ω, f ω j l ∂μ := by
    simpa using MeasureTheory.eval_integral (μ := μ)
      (f := fun ω => f ω j) (hf := fun l => hf_eval_int j l) l
  calc
    (∫ ω, f ω ∂μ) j l = (∫ ω, f ω j ∂μ) l := by rw [houter]
    _ = ∫ ω, f ω j l ∂μ := by rw [hinner]
    _ = olsConditionalVarianceMatrix X D j l := by
      calc
        ∫ ω, f ω j l ∂μ = ∫ ω, μ[(fun ω => f ω j l) | m] ω ∂μ := by
          symm
          exact MeasureTheory.integral_condExp (μ := μ) (m := m) (m₀ := m₀)
            (f := fun ω => f ω j l) hm
        _ = ∫ ω, olsConditionalVarianceMatrix X D j l ∂μ := by
          refine MeasureTheory.integral_congr_ae ?_
          simpa [f] using
            ols_condExp_centered_mul_eq_variance_entry
              (μ := μ) (m := m) X β e D j l hm hee_int hD
        _ = olsConditionalVarianceMatrix X D j l := by simp

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
