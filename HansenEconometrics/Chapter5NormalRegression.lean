import Mathlib
import HansenEconometrics.Basic
import HansenEconometrics.ChiSquared
import HansenEconometrics.LinearAlgebraUtils
import HansenEconometrics.ProbabilityUtils
import HansenEconometrics.Chapter3Projections
import HansenEconometrics.Chapter4LeastSquaresRegression

open MeasureTheory ProbabilityTheory
open scoped ENNReal Topology MeasureTheory ProbabilityTheory

open scoped Matrix

namespace HansenEconometrics

open Matrix

variable {n k : Type*}
variable [Fintype n] [Fintype k] [DecidableEq n] [DecidableEq k]

/-- Finite-sample residual variance estimator in the homoskedastic normal regression model. -/
noncomputable def olsResidualVarianceEstimator
    (X : Matrix n k ℝ) (y : n → ℝ) [Invertible (Xᵀ * X)] : ℝ :=
  (dotProduct (annihilatorMatrix X *ᵥ y) (annihilatorMatrix X *ᵥ y)) /
    (Fintype.card n - Fintype.card k : ℝ)

/-- Hansen Theorem 5.7 statistic `(n-k)s²/σ²`, written as a reusable random variable on the
probability space carrying the regression error. -/
noncomputable def scaledOlsResidualVarianceStatistic
    {Ω : Type*}
    (X : Matrix n k ℝ) (β : k → ℝ) (σ2 : ℝ) [Invertible (Xᵀ * X)]
    (ε : Ω → EuclideanSpace ℝ n) : Ω → ℝ :=
  fun ω =>
    ((Fintype.card n - Fintype.card k : ℝ) *
      olsResidualVarianceEstimator X (X *ᵥ β + WithLp.ofLp (ε ω))) / σ2

/-- A lightweight deterministic record of the Chapter 5 normal regression setup. -/
structure NormalRegressionModel (X : Matrix n k ℝ) (β : k → ℝ) (σ2 : ℝ) where
  sigma2_nonneg : 0 ≤ σ2

/-- Under the linear model, the residual variance estimator is the residual quadratic form divided by
`n-k`, expressed directly in terms of the model error. -/
theorem olsResidualVarianceEstimator_linear_model
    (X : Matrix n k ℝ) (β : k → ℝ) (e : n → ℝ) [Invertible (Xᵀ * X)] :
    olsResidualVarianceEstimator X (X *ᵥ β + e)
      = (dotProduct (annihilatorMatrix X *ᵥ e) (annihilatorMatrix X *ᵥ e)) /
          (Fintype.card n - Fintype.card k : ℝ) := by
  unfold olsResidualVarianceEstimator
  have hMXβ : annihilatorMatrix X *ᵥ (X *ᵥ β) = 0 := by
    simpa [Matrix.mulVec_mulVec] using
      congrArg (fun M : Matrix n k ℝ => M *ᵥ β) (annihilator_mul_X X)
  rw [Matrix.mulVec_add, hMXβ, zero_add]

/-- The residual sum of squares in the linear model is the annihilator quadratic form `e'Me`. -/
theorem residual_quadratic_form_of_linear_model
    (X : Matrix n k ℝ) (e : n → ℝ) [Invertible (Xᵀ * X)] :
    dotProduct (annihilatorMatrix X *ᵥ e) (annihilatorMatrix X *ᵥ e)
      = e ⬝ᵥ (annihilatorMatrix X) *ᵥ e := by
  symm
  exact quadratic_form_eq_dotProduct_of_symm_idempotent
    (annihilatorMatrix X)
    (annihilatorMatrix_transpose X)
    (annihilatorMatrix_idempotent X)
    e

/-- Under the linear model, the residual variance estimator is the annihilator quadratic form divided
by `n-k`. This is the deterministic identity underlying the chi-square step. -/
theorem olsResidualVarianceEstimator_linear_model_quadratic_form
    (X : Matrix n k ℝ) (β : k → ℝ) (e : n → ℝ) [Invertible (Xᵀ * X)] :
    olsResidualVarianceEstimator X (X *ᵥ β + e)
      = (e ⬝ᵥ (annihilatorMatrix X) *ᵥ e) /
          (Fintype.card n - Fintype.card k : ℝ) := by
  rw [olsResidualVarianceEstimator_linear_model, residual_quadratic_form_of_linear_model]

/-- If the error vector has a Gaussian law, then the OLS coefficient vector is Gaussian as an affine
image of the error vector. -/
theorem olsBeta_hasGaussianLaw_of_error
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (X : Matrix n k ℝ) (β : k → ℝ) (e : Ω → n → ℝ)
    [Invertible (Xᵀ * X)]
    (he : HasGaussianLaw e μ) :
    HasGaussianLaw (fun ω => olsBeta X (X *ᵥ β + e ω)) μ := by
  let L : (n → ℝ) →L[ℝ] (k → ℝ) :=
    (Matrix.toLin' (⅟ (Xᵀ * X) * Xᵀ)).toContinuousLinearMap
  have hLin : HasGaussianLaw (fun ω => L (e ω)) μ := he.map_fun L
  have hAff : HasGaussianLaw (fun ω => β + L (e ω)) μ := by
    refine ⟨?_⟩
    have hmap : (μ.map fun ω => L (e ω)).map (fun x => β + x) = μ.map (fun ω => β + L (e ω)) := by
      simpa using
        (AEMeasurable.map_map_of_aemeasurable
          (μ := μ)
          (f := fun ω => L (e ω))
          (g := fun x => β + x)
          (Measurable.aemeasurable <| by fun_prop)
          hLin.aemeasurable)
    rw [← hmap]
    letI : IsGaussian (μ.map fun ω => L (e ω)) := hLin.isGaussian_map
    infer_instance
  refine hAff.congr ?_
  filter_upwards with ω
  rw [olsBeta_linear_decomposition]
  simp [L]

/-- If the error vector has a Gaussian law, then the OLS residual vector is Gaussian as a linear image
of the error vector. -/
theorem residual_hasGaussianLaw_of_error
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (X : Matrix n k ℝ) (β : k → ℝ) (e : Ω → n → ℝ)
    [Invertible (Xᵀ * X)]
    (he : HasGaussianLaw e μ) :
    HasGaussianLaw (fun ω => residual X (X *ᵥ β + e ω)) μ := by
  let L : (n → ℝ) →L[ℝ] (n → ℝ) := (Matrix.toLin' (annihilatorMatrix X)).toContinuousLinearMap
  have hLin : HasGaussianLaw (fun ω => L (e ω)) μ := he.map_fun L
  refine hLin.congr ?_
  filter_upwards with ω
  rw [residual_linear_model]
  simp [L]

/-- The annihilator quadratic form is the sum of squared eigenbasis coordinates on the `1`-eigenspace.
This is the deterministic bridge behind Hansen Theorem 5.7. -/
theorem residual_quadratic_form_eq_sum_sq_eigenvector_coords
    (X : Matrix n k ℝ) (e : n → ℝ) [Invertible (Xᵀ * X)] :
    let M := annihilatorMatrix X
    let hM : M.IsHermitian := annihilatorMatrix_isHermitian X
    let b : OrthonormalBasis n ℝ (EuclideanSpace ℝ n) := hM.eigenvectorBasis
    e ⬝ᵥ M *ᵥ e =
      ∑ i : {j : n // hM.eigenvalues j = 1}, (b.repr (WithLp.toLp 2 e) i.1) ^ 2 := by
  classical
  let M := annihilatorMatrix X
  let hM : M.IsHermitian := annihilatorMatrix_isHermitian X
  let b : OrthonormalBasis n ℝ (EuclideanSpace ℝ n) := hM.eigenvectorBasis
  let z : EuclideanSpace ℝ n := WithLp.toLp 2 e
  have hcoord : ∀ i : n,
      b.repr (Matrix.toEuclideanLin M z) i = hM.eigenvalues i * b.repr z i := by
    intro i
    let T : EuclideanSpace ℝ n →ₗ[ℝ] EuclideanSpace ℝ n := Matrix.toEuclideanLin M
    have hSymm : T.IsSymmetric := Matrix.isHermitian_iff_isSymmetric.mp hM
    have hEig : T (b i) = hM.eigenvalues i • b i := by
      simpa [T] using congrArg (WithLp.toLp 2) (hM.mulVec_eigenvectorBasis i)
    calc
      b.repr (T z) i = inner ℝ (b i) (T z) := by
        simpa using (OrthonormalBasis.repr_apply_apply (b := b) (v := T z) (i := i))
      _ = inner ℝ (T (b i)) z := by rw [← hSymm (b i) z]
      _ = inner ℝ (hM.eigenvalues i • b i) z := by rw [hEig]
      _ = hM.eigenvalues i * b.repr z i := by
        rw [real_inner_smul_left, OrthonormalBasis.repr_apply_apply]
  have hnorm :
      dotProduct (M *ᵥ e) (M *ᵥ e)
        = ∑ i : n, (hM.eigenvalues i * b.repr z i) ^ 2 := by
    let T : EuclideanSpace ℝ n →ₗ[ℝ] EuclideanSpace ℝ n := Matrix.toEuclideanLin M
    calc
      dotProduct (M *ᵥ e) (M *ᵥ e) = ‖T z‖ ^ 2 := by
        change dotProduct (M *ᵥ e) (M *ᵥ e) = ‖WithLp.toLp 2 (M *ᵥ e)‖ ^ 2
        simpa [pow_two] using
          (EuclideanSpace.real_norm_sq_eq (WithLp.toLp 2 (M *ᵥ e))).symm
      _ = ∑ i : n, ‖inner ℝ (b i) (T z)‖ ^ 2 := by
        symm
        exact OrthonormalBasis.sum_sq_norm_inner_right b (T z)
      _ = ∑ i : n, (b.repr (T z) i) ^ 2 := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        rw [OrthonormalBasis.repr_apply_apply]
        simpa [sq_abs]
      _ = ∑ i : n, (hM.eigenvalues i * b.repr z i) ^ 2 := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        rw [hcoord i]
  have heig01 := eigenvalues_zero_or_one_of_isHermitian_idempotent hM (annihilatorMatrix_idempotent X)
  have hsum :
      ∑ i : n, (hM.eigenvalues i * b.repr z i) ^ 2
        = ∑ i : {j : n // hM.eigenvalues j = 1}, (b.repr z i.1) ^ 2 := by
    calc
      ∑ i : n, (hM.eigenvalues i * b.repr z i) ^ 2
          = ∑ i : n, if hM.eigenvalues i = 1 then (b.repr z i) ^ 2 else 0 := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              by_cases h1 : hM.eigenvalues i = 1
              · simp [h1]
              · have h0 : hM.eigenvalues i = 0 := (heig01 i).resolve_right h1
                simp [h0]
      _ = ∑ i : n with hM.eigenvalues i = 1, (b.repr z i) ^ 2 := by
            rw [Finset.sum_filter]
      _ = ∑ i : {j : n // hM.eigenvalues j = 1}, (b.repr z i.1) ^ 2 := by
            rw [Finset.sum_subtype]
            intro x
            simp
  simpa [M, hM, b, z] using
    ((residual_quadratic_form_of_linear_model X e).symm.trans hnorm).trans hsum

end HansenEconometrics
