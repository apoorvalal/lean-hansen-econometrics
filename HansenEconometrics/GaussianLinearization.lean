import HansenEconometrics.AsymptoticInterfaces
import HansenEconometrics.AsymptoticUtils.StochasticOrder
import HansenEconometrics.ProbabilityUtils

/-!
# Gaussian limits for linearized estimators

This module contains estimator-independent Gaussian continuous-mapping and
Slutsky results. These workhorse theorems were first proved for the Chapter 8
minimum-distance development, but their statements apply to any finite-
dimensional estimator with an asymptotic linear representation.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped Matrix Matrix.Norms.Elementwise Topology MeasureTheory ProbabilityTheory

namespace HansenEconometrics

open Matrix

variable {k : Type*} [Fintype k] [DecidableEq k]

/-- Fixed linear maps preserve centered multivariate Gaussian limits, with
covariance transformed as `M S Mᵀ`. -/
theorem fixedMatrix_mulVec_tendstoInDistribution_multivariateGaussian
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (M S : Matrix k k ℝ) (hS : S.PosSemidef) (T : ℕ → Ω → k → ℝ)
    (hT : TendstoInDistribution T atTop (fun z : EuclideanSpace ℝ k => z.ofLp)
      (fun _ => μ) (multivariateGaussian 0 S)) :
    TendstoInDistribution (fun n ω => M *ᵥ T n ω) atTop
      (fun z : EuclideanSpace ℝ k => z.ofLp) (fun _ => μ)
      (multivariateGaussian 0 (M * S * Mᵀ)) := by
  let Te : ℕ → Ω → EuclideanSpace ℝ k := fun n ω => WithLp.toLp 2 (T n ω)
  have hTe : TendstoInDistribution Te atTop (fun z : EuclideanSpace ℝ k => z)
      (fun _ => μ) (multivariateGaussian 0 S) := by
    have hmap := hT.continuous_comp (PiLp.continuous_toLp 2 (fun _ : k => ℝ))
    simpa [Te, Function.comp_def] using hmap
  have hlin : TendstoInDistribution
      (fun n => matrixContinuousLinearMap M ∘ Te n)
      atTop (matrixContinuousLinearMap M ∘ fun z : EuclideanSpace ℝ k => z)
      (fun _ => μ) (multivariateGaussian 0 S) :=
    hTe.continuous_comp (matrixContinuousLinearMap M).continuous
  have hLaw : HasLaw (fun z : EuclideanSpace ℝ k => matrixContinuousLinearMap M z)
      (multivariateGaussian 0 (M * S * Mᵀ)) (multivariateGaussian 0 S) := by
    simpa [matrixContinuousLinearMap, Matrix.conjTranspose_eq_transpose_of_trivial] using
      hasLaw_multivariateGaussian_zero_linearMap (n := k) (q := k) hS M
  have htargetE : TendstoInDistribution
      (fun n ω => matrixContinuousLinearMap M (Te n ω))
      atTop (fun z : EuclideanSpace ℝ k => z)
      (fun _ => μ) (multivariateGaussian 0 (M * S * Mᵀ)) := by
    simpa [Function.comp_def] using
      tendstoInDistribution_id_of_hasLaw_limit (E := EuclideanSpace ℝ k) hlin hLaw
  have htarget := htargetE.continuous_comp (PiLp.continuous_ofLp 2 (fun _ : k => ℝ))
  simpa [Te, Function.comp_def, matrixContinuousLinearMap_apply] using htarget

/-- Fixed affine maps preserve centered multivariate Gaussian limits, shifting
the mean by `bias` and transforming covariance as `M S Mᵀ`. -/
theorem fixedMatrix_mulVec_add_const_tendstoInDistribution_multivariateGaussian
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (M S : Matrix k k ℝ) (bias : k → ℝ) (hS : S.PosSemidef)
    (T : ℕ → Ω → k → ℝ)
    (hT : TendstoInDistribution T atTop (fun z : EuclideanSpace ℝ k => z.ofLp)
      (fun _ => μ) (multivariateGaussian 0 S)) :
    TendstoInDistribution (fun n ω => M *ᵥ T n ω + bias) atTop
      (fun z : EuclideanSpace ℝ k => z.ofLp) (fun _ => μ)
      (multivariateGaussian (WithLp.toLp 2 bias) (M * S * Mᵀ)) := by
  let biasE : EuclideanSpace ℝ k := WithLp.toLp 2 bias
  let Te : ℕ → Ω → EuclideanSpace ℝ k := fun n ω => WithLp.toLp 2 (T n ω)
  have hTe : TendstoInDistribution Te atTop (fun z : EuclideanSpace ℝ k => z)
      (fun _ => μ) (multivariateGaussian 0 S) := by
    have hmap := hT.continuous_comp (PiLp.continuous_toLp 2 (fun _ : k => ℝ))
    simpa [Te, Function.comp_def] using hmap
  have hlin : TendstoInDistribution
      (fun n => (fun z : EuclideanSpace ℝ k => biasE + matrixContinuousLinearMap M z) ∘ Te n)
      atTop ((fun z : EuclideanSpace ℝ k => biasE + matrixContinuousLinearMap M z) ∘
        fun z : EuclideanSpace ℝ k => z)
      (fun _ => μ) (multivariateGaussian 0 S) := by
    exact hTe.continuous_comp
      ((continuous_const : Continuous (fun _ : EuclideanSpace ℝ k => biasE)).add
        (matrixContinuousLinearMap M).continuous)
  have hLaw : HasLaw
      (fun z : EuclideanSpace ℝ k => biasE + matrixContinuousLinearMap M z)
      (multivariateGaussian biasE (M * S * Mᵀ)) (multivariateGaussian 0 S) := by
    constructor
    · exact Measurable.aemeasurable (Continuous.measurable
        ((continuous_const : Continuous (fun _ : EuclideanSpace ℝ k => biasE)).add
          (matrixContinuousLinearMap M).continuous))
    · simpa [biasE, matrixContinuousLinearMap,
        Matrix.conjTranspose_eq_transpose_of_trivial] using
        map_affine_multivariateGaussian (μ := (0 : EuclideanSpace ℝ k)) hS biasE M
  have htargetE : TendstoInDistribution
      (fun n ω => biasE + matrixContinuousLinearMap M (Te n ω))
      atTop (fun z : EuclideanSpace ℝ k => z)
      (fun _ => μ) (multivariateGaussian biasE (M * S * Mᵀ)) := by
    simpa [Function.comp_def] using
      tendstoInDistribution_id_of_hasLaw_limit (E := EuclideanSpace ℝ k) hlin hLaw
  have htarget := htargetE.continuous_comp (PiLp.continuous_ofLp 2 (fun _ : k => ℝ))
  simpa [Te, biasE, Function.comp_def, matrixContinuousLinearMap_apply, add_comm] using htarget

/-- A stable asymptotically linear representation and a centered Gaussian
driving limit imply the transformed Gaussian estimator limit. -/
theorem asymptoticallyLinearEstimator_tendstoInDistribution_multivariateGaussian
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (Y : ℕ → Ω → k → ℝ) (A : Matrix k k ℝ) (S : Matrix k k ℝ)
    (T : ℕ → Ω → k → ℝ)
    (hS : S.PosSemidef)
    (hlinear : AsymptoticallyLinearEstimator μ Y A T)
    (hT : TendstoInDistribution T atTop (fun z : EuclideanSpace ℝ k => z.ofLp)
      (fun _ => μ) (multivariateGaussian 0 S)) :
    TendstoInDistribution Y atTop (fun z : EuclideanSpace ℝ k => z.ofLp)
      (fun _ => μ) (multivariateGaussian 0 (A * S * Aᵀ)) := by
  have hA := fixedMatrix_mulVec_tendstoInDistribution_multivariateGaussian
    (M := A) (S := S) hS T hT
  exact tendstoInDistribution_of_tendstoInMeasure_sub
    (X := fun n ω => A *ᵥ T n ω) (Y := Y)
    (Z := fun z : EuclideanSpace ℝ k => z.ofLp) hA hlinear.expansion
    hlinear.scaled_measurable

/-- Interface form of
`asymptoticallyLinearEstimator_tendstoInDistribution_multivariateGaussian`. -/
theorem asymptoticallyLinearEstimator_tendstoInDistribution_multivariateGaussian_of_gaussianLimit
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (Y : ℕ → Ω → k → ℝ) (A : Matrix k k ℝ) (S : Matrix k k ℝ)
    (T : ℕ → Ω → k → ℝ)
    (hlinear : AsymptoticallyLinearEstimator μ Y A T)
    (hT : GaussianLimit μ T S) :
    TendstoInDistribution Y atTop (fun z : EuclideanSpace ℝ k => z.ofLp)
      (fun _ => μ) (multivariateGaussian 0 (A * S * Aᵀ)) :=
  asymptoticallyLinearEstimator_tendstoInDistribution_multivariateGaussian
    Y A S T hT.covariance_posSemidef hlinear hT.limit

/-- A biased asymptotically linear representation and a centered Gaussian
driving limit imply the corresponding shifted Gaussian estimator limit. -/
theorem biasedAsymptoticallyLinearEstimator_tendstoInDistribution_multivariateGaussian
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (Y : ℕ → Ω → k → ℝ) (A : Matrix k k ℝ) (S : Matrix k k ℝ)
    (T : ℕ → Ω → k → ℝ) (bias : k → ℝ)
    (hlinear : BiasedAsymptoticallyLinearEstimator μ Y A T bias)
    (hT : GaussianLimit μ T S) :
    TendstoInDistribution Y atTop (fun z : EuclideanSpace ℝ k => z.ofLp)
      (fun _ => μ) (multivariateGaussian (WithLp.toLp 2 bias) (A * S * Aᵀ)) := by
  have hA := fixedMatrix_mulVec_add_const_tendstoInDistribution_multivariateGaussian
    (M := A) (S := S) (bias := bias) hT.covariance_posSemidef T hT.limit
  exact tendstoInDistribution_of_tendstoInMeasure_sub
    (X := fun n ω => A *ᵥ T n ω + bias) (Y := Y)
    (Z := fun z : EuclideanSpace ℝ k => z.ofLp) hA hlinear.expansion
    hlinear.scaled_measurable

end HansenEconometrics
