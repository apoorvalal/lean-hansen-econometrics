import Mathlib
import HansenEconometrics.Basic
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
  have hvec : Matrix.vecMul e (annihilatorMatrix X) = annihilatorMatrix X *ᵥ e := by
    simpa [annihilatorMatrix_transpose] using
      (Matrix.vecMul_transpose (annihilatorMatrix X) e)
  have h := Matrix.dotProduct_mulVec e (annihilatorMatrix X) (annihilatorMatrix X *ᵥ e)
  rw [hvec, Matrix.mulVec_mulVec, annihilatorMatrix_idempotent] at h
  exact h.symm

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

end HansenEconometrics
