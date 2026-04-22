import Mathlib
import HansenEconometrics.Basic
import HansenEconometrics.ChiSquared
import HansenEconometrics.LinearAlgebraUtils
import HansenEconometrics.ProbabilityUtils
import HansenEconometrics.Chapter3Projections
import HansenEconometrics.Chapter3FWL
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

/-- The OLS residual sum of squares `RSS = ê'ê`. This is the likelihood-scale quadratic form that
appears in Hansen's Chapter 5 likelihood-ratio / F-test derivation. -/
noncomputable def olsResidualSumSquares
    (X : Matrix n k ℝ) (y : n → ℝ) [Invertible (Xᵀ * X)] : ℝ :=
  dotProduct (annihilatorMatrix X *ᵥ y) (annihilatorMatrix X *ᵥ y)

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

/-- Under the linear model, the residual sum of squares can be written directly in terms of the
model error. -/
theorem olsResidualSumSquares_linear_model
    (X : Matrix n k ℝ) (β : k → ℝ) (e : n → ℝ) [Invertible (Xᵀ * X)] :
    olsResidualSumSquares X (X *ᵥ β + e) =
      dotProduct (annihilatorMatrix X *ᵥ e) (annihilatorMatrix X *ᵥ e) := by
  unfold olsResidualSumSquares
  have hMXβ : annihilatorMatrix X *ᵥ (X *ᵥ β) = 0 := by
    simpa [Matrix.mulVec_mulVec] using
      congrArg (fun M : Matrix n k ℝ => M *ᵥ β) (annihilator_mul_X X)
  rw [Matrix.mulVec_add, hMXβ, zero_add]

/-- Under the linear model, the residual sum of squares is the annihilator quadratic form `e'Me`.
This is the likelihood-scale version of the Chapter 5 variance identity. -/
theorem olsResidualSumSquares_linear_model_quadratic_form
    (X : Matrix n k ℝ) (β : k → ℝ) (e : n → ℝ) [Invertible (Xᵀ * X)] :
    olsResidualSumSquares X (X *ᵥ β + e) = e ⬝ᵥ (annihilatorMatrix X) *ᵥ e := by
  rw [olsResidualSumSquares_linear_model]
  exact residual_quadratic_form_of_linear_model X e

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

set_option maxHeartbeats 800000 in
-- The deterministic normalization and eigenspace rewrite expand several large `let`-bound terms.
theorem scaledOlsResidualVarianceStatistic_eq_sum_sq_eigenvector_coords
    {Ω : Type*} [MeasurableSpace Ω]
    (X : Matrix n k ℝ) (β : k → ℝ) {σ2 : ℝ}
    (hσ2 : 0 < σ2) (hdf : Fintype.card k < Fintype.card n)
    (ε : Ω → EuclideanSpace ℝ n)
    [Invertible (Xᵀ * X)] :
    let M := annihilatorMatrix X
    let hM : M.IsHermitian := annihilatorMatrix_isHermitian X
    let b : OrthonormalBasis n ℝ (EuclideanSpace ℝ n) := hM.eigenvectorBasis
    scaledOlsResidualVarianceStatistic X β σ2 ε =
      sumSquaresRV (restrictedStandardizedCoords b (fun i : {j : n // hM.eigenvalues j = 1} => i.1) σ2 ε) := by
  classical
  let M : Matrix n n ℝ := annihilatorMatrix X
  let hM : M.IsHermitian := annihilatorMatrix_isHermitian X
  let b : OrthonormalBasis n ℝ (EuclideanSpace ℝ n) := hM.eigenvectorBasis
  funext ω
  let df : ℝ := (Fintype.card n : ℝ) - Fintype.card k
  let e : n → ℝ := WithLp.ofLp (ε ω)
  have hneq_df : df ≠ 0 := by
    dsimp [df]
    exact sub_ne_zero.mpr (by exact_mod_cast (Nat.ne_of_gt hdf))
  have hquad :
      e ⬝ᵥ M *ᵥ e = ∑ i : {j : n // hM.eigenvalues j = 1}, (b.repr (ε ω) i.1)^2 := by
    simpa [M, hM, b, e] using residual_quadratic_form_eq_sum_sq_eigenvector_coords X e
  have hscaled :
      scaledOlsResidualVarianceStatistic X β σ2 ε ω
        = (df * ((e ⬝ᵥ M *ᵥ e) / df)) / σ2 := by
    simp [scaledOlsResidualVarianceStatistic, df, e, M,
      olsResidualVarianceEstimator_linear_model_quadratic_form]
  have hcancel : df * ((e ⬝ᵥ M *ᵥ e) / df) = e ⬝ᵥ M *ᵥ e := by
    field_simp [hneq_df]
  calc
    scaledOlsResidualVarianceStatistic X β σ2 ε ω
        = (df * ((e ⬝ᵥ M *ᵥ e) / df)) / σ2 := hscaled
    _ = (e ⬝ᵥ M *ᵥ e) / σ2 := by rw [hcancel]
    _ = (∑ i : {j : n // hM.eigenvalues j = 1}, (b.repr (ε ω) i.1)^2) / σ2 := by rw [hquad]
    _ = ∑ i : {j : n // hM.eigenvalues j = 1}, ((b.repr (ε ω) i.1) / Real.sqrt σ2)^2 := by
          rw [Finset.sum_div]
          refine Finset.sum_congr rfl ?_
          intro i hi
          field_simp [Real.sq_sqrt hσ2.le, hσ2.ne']
          rw [Real.sq_sqrt hσ2.le]
    _ = sumSquaresRV
          (restrictedStandardizedCoords b
            (fun i : {j : n // hM.eigenvalues j = 1} => i.1) σ2 ε) ω := by
          simp [sumSquaresRV, restrictedStandardizedCoords, standardizedCoords]

/-- Hansen Theorem 5.7, chi-square component: in the homoskedastic normal regression model,
`(n-k) s² / σ²` has a chi-square distribution with `n-k` degrees of freedom. -/
theorem scaledOlsResidualVarianceStatistic_hasLaw_chiSquared
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (X : Matrix n k ℝ) (β : k → ℝ) {σ2 : ℝ}
    (hσ2 : 0 < σ2) (hdf : Fintype.card k < Fintype.card n)
    (ε : Ω → EuclideanSpace ℝ n)
    [Invertible (Xᵀ * X)]
    (hε : HasLaw ε (multivariateGaussian 0 ((σ2 : ℝ) • (1 : Matrix n n ℝ))) μ) :
    HasLaw (scaledOlsResidualVarianceStatistic X β σ2 ε)
      (chiSquared (Fintype.card n - Fintype.card k)) μ := by
  classical
  let hM : (annihilatorMatrix X).IsHermitian := annihilatorMatrix_isHermitian X
  let W : {j : n // hM.eigenvalues j = 1} → Ω → ℝ :=
    restrictedStandardizedCoords hM.eigenvectorBasis
      (fun i : {j : n // hM.eigenvalues j = 1} => i.1) σ2 ε
  have hRankEqCard :
      (annihilatorMatrix X).rank = Fintype.card {j : n // hM.eigenvalues j = 1} := by
    simpa [hM] using rank_eq_card_eigenvalues_eq_one_of_isHermitian_idempotent hM
      (annihilatorMatrix_idempotent X)
  have hCardPos : 0 < Fintype.card {j : n // hM.eigenvalues j = 1} := by
    rw [← hRankEqCard, Nat.eq_sub_of_add_eq (rank_annihilatorMatrix_add X)]
    exact Nat.sub_pos_of_lt hdf
  have hcoords := orthonormalBasis_coords_div_sqrt_iIndep_standardGaussian
    (b := hM.eigenvectorBasis) hσ2 ε hε
  have hLawW : ∀ i, HasLaw (W i) (gaussianReal 0 1) μ := by
    intro i
    simpa [W, restrictedStandardizedCoords, standardizedCoords] using hcoords.1 i.1
  have hIndepW : ProbabilityTheory.iIndepFun W μ := by
    simpa [W, restrictedStandardizedCoords, standardizedCoords] using
      hcoords.2.precomp Subtype.val_injective
  letI : MeasureSpace Ω := ⟨μ⟩
  have hLawSumSq : HasLaw (sumSquaresRV W)
      (chiSquared (Fintype.card {j : n // hM.eigenvalues j = 1})) μ := by
    simpa [W, sumSquaresRV] using hasLaw_sum_sq_chiSquared_fintype hCardPos hLawW hIndepW
  have hEq := scaledOlsResidualVarianceStatistic_eq_sum_sq_eigenvector_coords X β hσ2 hdf ε
  convert hLawSumSq.congr ?_ using 1
  · rw [← hRankEqCard, Nat.eq_sub_of_add_eq (rank_annihilatorMatrix_add X)]
  · simpa [hM, W] using hEq.symm

/-- The Chapter 5 statistic `((n-k)s²)/σ²` is the residual sum of squares divided by `σ²`. -/
theorem scaledOlsResidualVarianceStatistic_eq_residual_norm_sq_div
    {Ω : Type*} [MeasurableSpace Ω]
    (X : Matrix n k ℝ) (β : k → ℝ) {σ2 : ℝ}
    (hdf : Fintype.card k < Fintype.card n)
    (ε : Ω → EuclideanSpace ℝ n)
    [Invertible (Xᵀ * X)] :
    scaledOlsResidualVarianceStatistic X β σ2 ε =
      fun ω => dotProduct
        (residual X (X *ᵥ β + WithLp.ofLp (ε ω)))
        (residual X (X *ᵥ β + WithLp.ofLp (ε ω))) / σ2 := by
  funext ω
  let df : ℝ := (Fintype.card n : ℝ) - Fintype.card k
  have hneq_df : df ≠ 0 := by
    dsimp [df]
    exact sub_ne_zero.mpr (by exact_mod_cast (Nat.ne_of_gt hdf))
  have hres :
      residual X (X *ᵥ β + WithLp.ofLp (ε ω)) =
        annihilatorMatrix X *ᵥ (WithLp.ofLp (ε ω)) := by
    rw [residual_linear_model]
  have hlin :
      annihilatorMatrix X *ᵥ (X *ᵥ β + WithLp.ofLp (ε ω)) =
        annihilatorMatrix X *ᵥ (WithLp.ofLp (ε ω)) := by
    have hMXβ : annihilatorMatrix X *ᵥ (X *ᵥ β) = 0 := by
      simpa [Matrix.mulVec_mulVec] using
        congrArg (fun M : Matrix n k ℝ => M *ᵥ β) (annihilator_mul_X X)
    rw [Matrix.mulVec_add, hMXβ, zero_add]
  calc
    scaledOlsResidualVarianceStatistic X β σ2 ε ω
        = (df *
            (dotProduct
              (annihilatorMatrix X *ᵥ (X *ᵥ β + WithLp.ofLp (ε ω)))
              (annihilatorMatrix X *ᵥ (X *ᵥ β + WithLp.ofLp (ε ω))) / df)) / σ2 := by
              simp [scaledOlsResidualVarianceStatistic, olsResidualVarianceEstimator, df]
    _ = dotProduct
          (annihilatorMatrix X *ᵥ (X *ᵥ β + WithLp.ofLp (ε ω)))
          (annihilatorMatrix X *ᵥ (X *ᵥ β + WithLp.ofLp (ε ω))) / σ2 := by
            field_simp [hneq_df]
    _ = dotProduct
          (residual X (X *ᵥ β + WithLp.ofLp (ε ω)))
          (residual X (X *ᵥ β + WithLp.ofLp (ε ω))) / σ2 := by
            rw [hlin, hres]

-- Hansen Theorem 5.7, independence component: in the homoskedastic normal regression model, the
-- OLS coefficient vector is independent of the scaled residual-variance statistic `((n-k)s²)/σ²`.
set_option maxHeartbeats 800000 in
-- The Gaussian independence proof expands several large `toLp` / linear-map coercions.
theorem olsBeta_indep_scaledOlsResidualVarianceStatistic
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (X : Matrix n k ℝ) (β : k → ℝ) {σ2 : ℝ}
    (hσ2 : 0 < σ2) (hdf : Fintype.card k < Fintype.card n)
    (ε : Ω → EuclideanSpace ℝ n)
    [Invertible (Xᵀ * X)]
    (hε : HasLaw ε (multivariateGaussian 0 ((σ2 : ℝ) • (1 : Matrix n n ℝ))) μ) :
    (fun ω => olsBeta X (X *ᵥ β + WithLp.ofLp (ε ω))) ⟂ᵢ[μ]
      scaledOlsResidualVarianceStatistic X β σ2 ε := by
  classical
  let A : EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ k :=
    (Matrix.toEuclideanLin (⅟ (Xᵀ * X) * Xᵀ)).toContinuousLinearMap
  let M : EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ n :=
    (Matrix.toEuclideanLin (annihilatorMatrix X)).toContinuousLinearMap
  let centeredBeta : Ω → EuclideanSpace ℝ k := fun ω => A (ε ω)
  let residualE : Ω → EuclideanSpace ℝ n := fun ω => M (ε ω)
  have hε_gauss : HasGaussianLaw ε μ := hε.hasGaussianLaw
  have hJoint : HasGaussianLaw (fun ω => (centeredBeta ω, residualE ω)) μ := by
    simpa [centeredBeta, residualE, A, M] using hε_gauss.map_fun (A.prod M)
  have hS :
      (((σ2 : ℝ) • (1 : Matrix n n ℝ)) : Matrix n n ℝ).PosSemidef := by
    simpa [smul_one_eq_diagonal] using
      (Matrix.PosSemidef.diagonal (n := n) (d := fun _ => σ2) fun _ => hσ2.le)
  have hCov :
      ∀ x y,
        cov[fun ω => inner ℝ x (centeredBeta ω),
          fun ω => inner ℝ y (residualE ω); μ] = 0 := by
    intro x y
    have hMadjointLin :
        (Matrix.toEuclideanLin (annihilatorMatrix X)).adjoint =
          Matrix.toEuclideanLin (annihilatorMatrix X) := by
      simpa [Matrix.conjTranspose_eq_transpose_of_trivial, annihilatorMatrix_transpose] using
        (Matrix.toEuclideanLin_conjTranspose_eq_adjoint (A := annihilatorMatrix X)).symm
    have hMadjoint : M.adjoint = M := by
      simpa [M, LinearMap.adjoint_toContinuousLinearMap] using
        congrArg LinearMap.toContinuousLinearMap hMadjointLin
    have hcomp : A ∘L M = 0 := by
      ext z i
      simp [A, M, Matrix.mul_assoc, regressors_transpose_mul_annihilator]
    have hcomp_apply : A (M y) = 0 := by
      simpa using congrArg (fun T : EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ k => T y) hcomp
    have hcov :=
      hε.covariance_fun_comp
        (f := fun z : EuclideanSpace ℝ n => inner ℝ x (A z))
        (g := fun z : EuclideanSpace ℝ n => inner ℝ y (M z))
        (by fun_prop) (by fun_prop)
    have hA :
        (fun z : EuclideanSpace ℝ n => inner ℝ x (A z)) =
          fun z => inner ℝ (A.adjoint x) z := by
      ext z
      simpa [A] using (A.adjoint_inner_left z x).symm
    have hM :
        (fun z : EuclideanSpace ℝ n => inner ℝ y (M z)) =
          fun z => inner ℝ (M y) z := by
      ext z
      simpa [hMadjoint] using (M.adjoint_inner_left z y).symm
    have hmem :
        MemLp id 2 (multivariateGaussian 0 ((σ2 : ℝ) • (1 : Matrix n n ℝ))) :=
      IsGaussian.memLp_two_id
    calc
      cov[fun ω => inner ℝ x (centeredBeta ω),
        fun ω => inner ℝ y (residualE ω); μ]
          = cov[fun z : EuclideanSpace ℝ n => inner ℝ (A.adjoint x) z,
              fun z : EuclideanSpace ℝ n => inner ℝ (M y) z;
                multivariateGaussian 0 ((σ2 : ℝ) • (1 : Matrix n n ℝ))] := by
              simpa [centeredBeta, residualE, hA, hM] using hcov
      _ = covarianceBilin (multivariateGaussian 0 ((σ2 : ℝ) • (1 : Matrix n n ℝ)))
            (A.adjoint x) (M y) := by
              symm
              exact covarianceBilin_apply_eq_cov hmem (A.adjoint x) (M y)
      _ = (A.adjoint x) ⬝ᵥ (((σ2 : ℝ) • (1 : Matrix n n ℝ)) *ᵥ (M y)) := by
              rw [covarianceBilin_multivariateGaussian hS]
      _ = (σ2 : ℝ) * ((A.adjoint x : EuclideanSpace ℝ n) ⬝ᵥ (M y)) := by
              simp [smul_mulVec, one_mulVec, dotProduct_smul, smul_eq_mul]
      _ = 0 := by
              have hinner :
                  inner ℝ (A.adjoint x) (M y) = 0 := by
                calc
                  inner ℝ (A.adjoint x) (M y) = inner ℝ x (A (M y)) := by
                    simpa [A] using A.adjoint_inner_left (M y) x
                  _ = 0 := by simp [hcomp_apply]
              have hdot :
                  ((A.adjoint x : EuclideanSpace ℝ n) ⬝ᵥ (M y)) = 0 := by
                have hdot' : (M y).ofLp ⬝ᵥ star (((A.adjoint x : EuclideanSpace ℝ n)).ofLp) = 0 := by
                  simpa [EuclideanSpace.inner_eq_star_dotProduct] using hinner
                simpa [dotProduct, Pi.star_apply, conj_trivial, mul_comm] using hdot'
              rw [hdot, mul_zero]
  have hIndCentered : centeredBeta ⟂ᵢ[μ] residualE :=
    hJoint.indepFun_of_covariance_inner hCov
  have hIndEuclid :
      (fun ω => WithLp.toLp 2 (olsBeta X (X *ᵥ β + WithLp.ofLp (ε ω)))) ⟂ᵢ[μ]
        (fun ω => WithLp.toLp 2 (residual X (X *ᵥ β + WithLp.ofLp (ε ω)))) := by
    let φ : EuclideanSpace ℝ k → EuclideanSpace ℝ k := fun z => WithLp.toLp 2 (β + WithLp.ofLp z)
    refine (IndepFun.comp (φ := φ) (ψ := id) hIndCentered ?_ measurable_id).congr ?_ ?_
    · change Measurable (fun z : EuclideanSpace ℝ k => WithLp.toLp 2 (β + WithLp.ofLp z))
      fun_prop
    · filter_upwards with ω
      rw [olsBeta_linear_decomposition]
      simpa [centeredBeta, A, φ, Matrix.mulVec_mulVec] using
        (Matrix.toLpLin_apply (p := 2) (q := 2) (⅟ (Xᵀ * X) * Xᵀ) (ε ω))
    · filter_upwards with ω
      rw [residual_linear_model]
      simpa [residualE, M] using
        (Matrix.toLpLin_apply (p := 2) (q := 2) (annihilatorMatrix X) (ε ω))
  have hIndActual :
      (fun ω => olsBeta X (X *ᵥ β + WithLp.ofLp (ε ω))) ⟂ᵢ[μ]
        (fun ω => residual X (X *ᵥ β + WithLp.ofLp (ε ω))) := by
    have hmeasK : Measurable (WithLp.ofLp : EuclideanSpace ℝ k → k → ℝ) :=
      WithLp.measurable_ofLp (p := 2) (X := k → ℝ)
    have hmeasN : Measurable (WithLp.ofLp : EuclideanSpace ℝ n → n → ℝ) :=
      WithLp.measurable_ofLp (p := 2) (X := n → ℝ)
    simpa using
      (IndepFun.comp (φ := (WithLp.ofLp : EuclideanSpace ℝ k → k → ℝ))
        (ψ := (WithLp.ofLp : EuclideanSpace ℝ n → n → ℝ))
        hIndEuclid hmeasK hmeasN)
  let q : (n → ℝ) → ℝ := fun r => dotProduct r r / σ2
  have hq : Measurable q := by
    simpa [q] using (Continuous.dotProduct continuous_id continuous_id).div_const σ2 |>.measurable
  have hIndStat :
      (fun ω => olsBeta X (X *ᵥ β + WithLp.ofLp (ε ω))) ⟂ᵢ[μ]
        (q ∘ fun ω => residual X (X *ᵥ β + WithLp.ofLp (ε ω))) := by
    exact IndepFun.comp (μ := μ) (φ := id) (ψ := q) hIndActual measurable_id hq
  refine IndepFun.congr hIndStat Filter.EventuallyEq.rfl ?_
  filter_upwards with ω
  simpa [q, scaledOlsResidualVarianceStatistic_eq_residual_norm_sq_div, hdf]

/-- The diagonal entry of the inverse Gram matrix appearing in the classical OLS standard error is
strictly positive. -/
theorem inv_gram_diagonal_pos
    (X : Matrix n k ℝ) [Invertible (Xᵀ * X)] (j : k) :
    0 < (⅟ (Xᵀ * X)) j j := by
  have hXinj : Function.Injective X.mulVec := by
    intro v w hvw
    have hgram :
        (Xᵀ * X) *ᵥ (v - w) = 0 := by
      calc
        (Xᵀ * X) *ᵥ (v - w) = Xᵀ *ᵥ (X *ᵥ (v - w)) := by
          rw [Matrix.mulVec_mulVec]
        _ = Xᵀ *ᵥ (X *ᵥ v - X *ᵥ w) := by
          rw [Matrix.mulVec_sub]
        _ = 0 := by
          simp [hvw]
    have hGramInj : Function.Injective (fun u : k → ℝ => (Xᵀ * X) *ᵥ u) :=
      Matrix.mulVec_injective_of_invertible (Xᵀ * X)
    have hzero : v - w = 0 := by
      apply hGramInj
      simpa using hgram
    exact sub_eq_zero.mp hzero
  have hGramPosDef : (Xᵀ * X).PosDef := by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
      (Matrix.PosDef.conjTranspose_mul_self X hXinj)
  have hInvPosDef : (⅟ (Xᵀ * X)).PosDef := by
    simpa using hGramPosDef.inv
  simpa using hInvPosDef.diag_pos (i := j)

/-- The classical homoskedastic estimated standard error for OLS coefficient `j`. -/
noncomputable def olsEstimatedStandardError
    (X : Matrix n k ℝ) (j : k) [Invertible (Xᵀ * X)] (y : n → ℝ) : ℝ :=
  Real.sqrt (olsResidualVarianceEstimator X y * (⅟ (Xᵀ * X)) j j)

/-- The classical symmetric confidence interval for OLS coefficient `j` with critical value `c`. -/
noncomputable def olsConfidenceInterval
    (X : Matrix n k ℝ) (j : k) (c : ℝ) [Invertible (Xᵀ * X)] (y : n → ℝ) : Set ℝ :=
  Set.Icc
    (olsBeta X y j - c * olsEstimatedStandardError X j y)
    (olsBeta X y j + c * olsEstimatedStandardError X j y)

/-- Deterministic bridge: membership in the classical OLS confidence interval is equivalent to the
usual absolute-value inequality for the centered coefficient scaled by its estimated standard error,
provided the standard error is positive. -/
theorem mem_olsConfidenceInterval_iff_abs_centered_div_le
    (X : Matrix n k ℝ) (j : k) (c β0 : ℝ) [Invertible (Xᵀ * X)] {y : n → ℝ}
    (hse : 0 < olsEstimatedStandardError X j y) :
    β0 ∈ olsConfidenceInterval X j c y ↔
      |(olsBeta X y j - β0) / olsEstimatedStandardError X j y| ≤ c := by
  let se := olsEstimatedStandardError X j y
  let x : ℝ := olsBeta X y j - β0
  have hse_ne : se ≠ 0 := ne_of_gt hse
  constructor
  · intro hmem
    rcases hmem with ⟨hl, hu⟩
    have habs : |x| ≤ c * se := by
      rw [abs_le]
      constructor
      · dsimp [x, se] at hl hu ⊢
        linarith
      · dsimp [x, se] at hl hu ⊢
        linarith
    rw [abs_div, abs_of_pos hse]
    exact (div_le_iff₀ hse).2 habs
  · intro ht
    have habs : |x| ≤ c * se := by
      have hdiv : |x| / se ≤ c := by
        simpa [x, se, abs_div, abs_of_pos hse] using ht
      exact (div_le_iff₀ hse).1 hdiv
    rw [abs_le] at habs
    constructor
    · dsimp [olsConfidenceInterval, x, se]
      linarith
    · dsimp [olsConfidenceInterval, x, se]
      linarith

/-- The true-variance standardized OLS coefficient error for coordinate `j`. This is the Gaussian
numerator in Hansen Theorem 5.8. -/
noncomputable def standardizedOlsBetaCoordinate
    {Ω : Type*}
    (X : Matrix n k ℝ) (β : k → ℝ) (σ2 : ℝ) (j : k) [Invertible (Xᵀ * X)]
    (ε : Ω → EuclideanSpace ℝ n) : Ω → ℝ :=
  fun ω =>
    (olsBeta X (X *ᵥ β + WithLp.ofLp (ε ω)) j - β j) /
      Real.sqrt (σ2 * (⅟ (Xᵀ * X)) j j)

/-- The Chapter 5 studentization factor built from the scaled residual variance statistic. -/
noncomputable def olsStudentizationFactor
    {Ω : Type*}
    (X : Matrix n k ℝ) (β : k → ℝ) (σ2 : ℝ) [Invertible (Xᵀ * X)]
    (ε : Ω → EuclideanSpace ℝ n) : Ω → ℝ :=
  fun ω =>
    Real.sqrt (Fintype.card n - Fintype.card k : ℝ) /
      Real.sqrt (scaledOlsResidualVarianceStatistic X β σ2 ε ω)

/-- Hansen's classical OLS t-statistic for coefficient `β_j`. -/
noncomputable def olsTStatistic
    {Ω : Type*}
    (X : Matrix n k ℝ) (β : k → ℝ) (σ2 : ℝ) (j : k) [Invertible (Xᵀ * X)]
    (ε : Ω → EuclideanSpace ℝ n) : Ω → ℝ :=
  fun ω => standardizedOlsBetaCoordinate X β σ2 j ε ω * olsStudentizationFactor X β σ2 ε ω

/-- The one-dimensional factor multiplying the Gaussian numerator in the Student-t ratio
representation. -/
noncomputable def studentTFactor (ν : ℕ) : Measure ℝ :=
  (chiSquared ν).map fun q : ℝ => Real.sqrt (ν : ℝ) / Real.sqrt q

/-- Student's t distribution, packaged through the ratio representation
`Z / √(Q/ν)` with `Z ∼ N(0,1)` and `Q ∼ χ²(ν)` independent. -/
noncomputable def studentT (ν : ℕ) : Measure ℝ :=
  gaussianReal 0 1 ∗ₘ studentTFactor ν

/-- The true-variance standardized OLS coefficient error is standard normal. -/
theorem standardizedOlsBetaCoordinate_hasLaw_standardNormal
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (X : Matrix n k ℝ) (β : k → ℝ) {σ2 : ℝ} (j : k)
    (hσ2 : 0 < σ2)
    (ε : Ω → EuclideanSpace ℝ n)
    [Invertible (Xᵀ * X)]
    (hε : HasLaw ε (multivariateGaussian 0 ((σ2 : ℝ) • (1 : Matrix n n ℝ))) μ) :
    HasLaw (standardizedOlsBetaCoordinate X β σ2 j ε) (gaussianReal 0 1) μ := by
  let A : Matrix k n ℝ := ⅟ (Xᵀ * X) * Xᵀ
  let u : EuclideanSpace ℝ n := WithLp.toLp 2 (A j)
  let L : EuclideanSpace ℝ n →L[ℝ] ℝ :=
    (EuclideanSpace.proj j).comp (Matrix.toEuclideanLin A).toContinuousLinearMap
  let S : Matrix n n ℝ := (σ2 : ℝ) • (1 : Matrix n n ℝ)
  have hdiagPos : 0 < (⅟ (Xᵀ * X)) j j := inv_gram_diagonal_pos X j
  have hvarPos : 0 < σ2 * (⅟ (Xᵀ * X)) j j := mul_pos hσ2 hdiagPos
  have hS : S.PosSemidef := by
    simpa [S, smul_one_eq_diagonal] using
      (Matrix.PosSemidef.diagonal (n := n) (d := fun _ => σ2) fun _ => hσ2.le)
  have hAA : A * Aᵀ = ⅟ (Xᵀ * X) := by
    dsimp [A]
    rw [Matrix.transpose_mul, Matrix.transpose_transpose, inv_gram_transpose]
    calc
      (⅟ (Xᵀ * X) * Xᵀ) * (X * ⅟ (Xᵀ * X))
          = ⅟ (Xᵀ * X) * (Xᵀ * (X * ⅟ (Xᵀ * X))) := by
              rw [Matrix.mul_assoc]
      _ = ⅟ (Xᵀ * X) * ((Xᵀ * X) * ⅟ (Xᵀ * X)) := by
            rw [Matrix.mul_assoc, ← Matrix.mul_assoc]
      _ = ⅟ (Xᵀ * X) := by
            rw [← Matrix.mul_assoc, invOf_mul_self, Matrix.one_mul]
  have hdotA : dotProduct (A j) (A j) = (⅟ (Xᵀ * X)) j j := by
    calc
      dotProduct (A j) (A j) = (A * Aᵀ) j j := by
        simp [Matrix.mul_apply, dotProduct]
      _ = (⅟ (Xᵀ * X)) j j := by
        rw [hAA]
  have hLMap :
      (multivariateGaussian 0 S).map L =
        gaussianReal 0 ⟨σ2 * (⅟ (Xᵀ * X)) j j, hvarPos.le⟩ := by
    have hEq := IsGaussian.map_eq_gaussianReal (μ := multivariateGaussian 0 S) L
    have hMean : (multivariateGaussian 0 S)[L] = 0 := by
      rw [ContinuousLinearMap.integral_comp_id_comm]
      · simp [L, S, integral_id_multivariateGaussian]
      · exact IsGaussian.integrable_id (μ := multivariateGaussian 0 S)
    have hVar : Var[L; multivariateGaussian 0 S] = σ2 * (⅟ (Xᵀ * X)) j j := by
      have hLfun : (⇑L : EuclideanSpace ℝ n → ℝ) = fun x => inner ℝ u x := by
        ext x
        calc
          L x = dotProduct (A j) x.ofLp := by
            simp [L, Matrix.mulVec, dotProduct]
          _ = dotProduct x.ofLp (A j) := by
            simp [dotProduct, mul_comm]
          _ = inner ℝ u x := by
            simpa [u] using (EuclideanSpace.inner_toLp_toLp (A j) x.ofLp).symm
      rw [← covariance_self (Measurable.aemeasurable <| by fun_prop), hLfun,
        ← covarianceBilin_apply_eq_cov]
      · calc
          covarianceBilin (multivariateGaussian 0 S) u u = u ⬝ᵥ (S *ᵥ u) := by
            rw [covarianceBilin_multivariateGaussian hS]
          _ = (σ2 : ℝ) * dotProduct (A j) (A j) := by
            simp [u, S, smul_mulVec, one_mulVec, dotProduct_smul, smul_eq_mul]
          _ = σ2 * (⅟ (Xᵀ * X)) j j := by
            rw [hdotA]
      · exact IsGaussian.memLp_two_id (μ := multivariateGaussian 0 S)
    rw [hMean, hVar, Real.toNNReal_of_nonneg hvarPos.le] at hEq
    simpa using hEq
  have hLawCentered :
      HasLaw
        (fun ω => olsBeta X (X *ᵥ β + WithLp.ofLp (ε ω)) j - β j)
        (gaussianReal 0 ⟨σ2 * (⅟ (Xᵀ * X)) j j, hvarPos.le⟩) μ := by
    refine (HasLaw.comp ⟨by fun_prop, hLMap⟩ hε).congr ?_
    filter_upwards with ω
    rw [olsBeta_linear_decomposition]
    simp [L, A, Matrix.mulVec_mulVec]
  have hLawStd :=
    gaussianReal_div_const hLawCentered (Real.sqrt (σ2 * (⅟ (Xᵀ * X)) j j))
  convert hLawStd using 2
  · simp
  · apply Subtype.ext
    change (1 : ℝ) = (σ2 * (⅟ (Xᵀ * X)) j j) / (Real.sqrt (σ2 * (⅟ (Xᵀ * X)) j j) ^ 2)
    rw [Real.sq_sqrt hvarPos.le]
    field_simp [hvarPos.ne']

/-- The Gaussian numerator in the t-statistic is independent of the scaled residual variance
statistic. -/
theorem standardizedOlsBetaCoordinate_indep_scaledOlsResidualVarianceStatistic
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (X : Matrix n k ℝ) (β : k → ℝ) {σ2 : ℝ} (j : k)
    (hσ2 : 0 < σ2) (hdf : Fintype.card k < Fintype.card n)
    (ε : Ω → EuclideanSpace ℝ n)
    [Invertible (Xᵀ * X)]
    (hε : HasLaw ε (multivariateGaussian 0 ((σ2 : ℝ) • (1 : Matrix n n ℝ))) μ) :
    standardizedOlsBetaCoordinate X β σ2 j ε ⟂ᵢ[μ]
      scaledOlsResidualVarianceStatistic X β σ2 ε := by
  refine IndepFun.comp
    (φ := fun b : k → ℝ => (b j - β j) / Real.sqrt (σ2 * (⅟ (Xᵀ * X)) j j))
    (ψ := id)
    (olsBeta_indep_scaledOlsResidualVarianceStatistic X β hσ2 hdf ε hε)
    ?_ measurable_id
  fun_prop

/-- The studentization factor is the inverse square-root transform of the chi-square statistic. -/
theorem olsStudentizationFactor_hasLaw
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (X : Matrix n k ℝ) (β : k → ℝ) {σ2 : ℝ}
    (hσ2 : 0 < σ2) (hdf : Fintype.card k < Fintype.card n)
    (ε : Ω → EuclideanSpace ℝ n)
    [Invertible (Xᵀ * X)]
    (hε : HasLaw ε (multivariateGaussian 0 ((σ2 : ℝ) • (1 : Matrix n n ℝ))) μ) :
    HasLaw (olsStudentizationFactor X β σ2 ε)
      (studentTFactor (Fintype.card n - Fintype.card k)) μ := by
  let ν : ℕ := Fintype.card n - Fintype.card k
  have hMap :
      HasLaw (fun q : ℝ => Real.sqrt (ν : ℝ) / Real.sqrt q)
        (studentTFactor ν) (chiSquared ν) := by
    exact ⟨by fun_prop, rfl⟩
  refine (hMap.comp (scaledOlsResidualVarianceStatistic_hasLaw_chiSquared X β hσ2 hdf ε hε)).congr ?_
  exact Filter.Eventually.of_forall fun ω => by
    simp [olsStudentizationFactor, ν, Nat.cast_sub hdf.le]

/-- Hansen Theorem 5.8: in the homoskedastic normal regression model, the classical OLS
t-statistic has a Student t distribution with `n-k` degrees of freedom. -/
theorem olsTStatistic_hasLaw_studentT
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (X : Matrix n k ℝ) (β : k → ℝ) {σ2 : ℝ} (j : k)
    (hσ2 : 0 < σ2) (hdf : Fintype.card k < Fintype.card n)
    (ε : Ω → EuclideanSpace ℝ n)
    [Invertible (Xᵀ * X)]
    (hε : HasLaw ε (multivariateGaussian 0 ((σ2 : ℝ) • (1 : Matrix n n ℝ))) μ) :
    HasLaw (olsTStatistic X β σ2 j ε)
      (studentT (Fintype.card n - Fintype.card k)) μ := by
  let ν : ℕ := Fintype.card n - Fintype.card k
  letI : Fact (0 < ν) := ⟨by
    dsimp [ν]
    exact Nat.sub_pos_of_lt hdf⟩
  letI : IsProbabilityMeasure (chiSquared ν) := isProbabilityMeasure_chiSquared (k := ν) Fact.out
  letI : IsProbabilityMeasure (studentTFactor ν) := by
    change IsProbabilityMeasure ((chiSquared ν).map fun q : ℝ => Real.sqrt (ν : ℝ) / Real.sqrt q)
    exact Measure.isProbabilityMeasure_map (by fun_prop)
  have hNum :
      HasLaw (standardizedOlsBetaCoordinate X β σ2 j ε) (gaussianReal 0 1) μ :=
    standardizedOlsBetaCoordinate_hasLaw_standardNormal X β j hσ2 ε hε
  have hFac :
      HasLaw (olsStudentizationFactor X β σ2 ε)
        (studentTFactor ν) μ :=
    olsStudentizationFactor_hasLaw X β hσ2 hdf ε hε
  have hInd :
      standardizedOlsBetaCoordinate X β σ2 j ε ⟂ᵢ[μ]
        olsStudentizationFactor X β σ2 ε := by
    refine (IndepFun.comp
      (φ := id)
      (ψ := fun q : ℝ => Real.sqrt (ν : ℝ) / Real.sqrt q)
      (standardizedOlsBetaCoordinate_indep_scaledOlsResidualVarianceStatistic
        X β j hσ2 hdf ε hε)
      measurable_id (by fun_prop)).congr ?_ ?_
    · exact Filter.Eventually.of_forall fun _ => rfl
    · exact Filter.Eventually.of_forall fun ω => by
        simp [olsStudentizationFactor, ν, Nat.cast_sub hdf.le]
  simpa [olsTStatistic, studentT, ν] using
    IndepFun.hasLaw_fun_mul hNum hFac hInd

/-- On outcomes where the scaled residual variance statistic is nonzero, Hansen's Chapter 5
`t`-statistic agrees with the classical centered coefficient divided by its estimated standard error. -/
theorem olsTStatistic_eq_centered_beta_div_estimatedSE
    {Ω : Type*} [MeasurableSpace Ω]
    (X : Matrix n k ℝ) (β : k → ℝ) {σ2 : ℝ} (j : k)
    (hσ2 : 0 < σ2) (hdf : Fintype.card k < Fintype.card n)
    (ε : Ω → EuclideanSpace ℝ n)
    [Invertible (Xᵀ * X)] {ω : Ω}
    (hstat : scaledOlsResidualVarianceStatistic X β σ2 ε ω ≠ 0) :
    olsTStatistic X β σ2 j ε ω =
      (olsBeta X (X *ᵥ β + WithLp.ofLp (ε ω)) j - β j) /
        olsEstimatedStandardError X j (X *ᵥ β + WithLp.ofLp (ε ω)) := by
  let y : n → ℝ := X *ᵥ β + WithLp.ofLp (ε ω)
  let s2 : ℝ := olsResidualVarianceEstimator X y
  let g : ℝ := (⅟ (Xᵀ * X)) j j
  let df : ℝ := (Fintype.card n - Fintype.card k : ℝ)
  let a : ℝ := olsBeta X y j - β j
  have hdf_cast : (Fintype.card k : ℝ) < Fintype.card n := by
    exact_mod_cast hdf
  have hdf_pos : 0 < df := by
    dsimp [df]
    linarith
  have hdf_ne : df ≠ 0 := ne_of_gt hdf_pos
  have hg_pos : 0 < g := inv_gram_diagonal_pos X j
  have hs2_nonneg : 0 ≤ s2 := by
    dsimp [s2, y, olsResidualVarianceEstimator]
    refine div_nonneg ?_ ?_
    · simpa using dotProduct_self_star_nonneg (annihilatorMatrix X *ᵥ y)
    · positivity
  have hs2_ne : s2 ≠ 0 := by
    intro hs2
    apply hstat
    simp [scaledOlsResidualVarianceStatistic, y, s2, df, hs2]
  have hs2_pos : 0 < s2 := lt_of_le_of_ne hs2_nonneg hs2_ne.symm
  have hsqrt_scaled :
      Real.sqrt (df * s2 / σ2) = (Real.sqrt df * Real.sqrt s2) / Real.sqrt σ2 := by
    rw [Real.sqrt_div (show 0 ≤ df * s2 by positivity), Real.sqrt_mul hdf_pos.le]
  have hsqrt_sigma_g :
      Real.sqrt (σ2 * g) = Real.sqrt σ2 * Real.sqrt g := by
    rw [Real.sqrt_mul hσ2.le]
  have hsqrt_s2_g :
      Real.sqrt (s2 * g) = Real.sqrt s2 * Real.sqrt g := by
    rw [Real.sqrt_mul hs2_nonneg]
  calc
    olsTStatistic X β σ2 j ε ω
        = (a / Real.sqrt (σ2 * g)) * (Real.sqrt df / Real.sqrt (df * s2 / σ2)) := by
            simp [olsTStatistic, standardizedOlsBetaCoordinate, olsStudentizationFactor,
              scaledOlsResidualVarianceStatistic, a, y, s2, g, df]
    _ = (a / (Real.sqrt σ2 * Real.sqrt g)) *
          (Real.sqrt df / ((Real.sqrt df * Real.sqrt s2) / Real.sqrt σ2)) := by
            rw [hsqrt_sigma_g, hsqrt_scaled]
    _ = (a / (Real.sqrt σ2 * Real.sqrt g)) * (Real.sqrt σ2 / Real.sqrt s2) := by
          field_simp [hdf_ne, Real.sqrt_ne_zero'.2 hσ2, Real.sqrt_ne_zero'.2 hs2_pos]
    _ = a / (Real.sqrt s2 * Real.sqrt g) := by
          field_simp [Real.sqrt_ne_zero'.2 hσ2, Real.sqrt_ne_zero'.2 hs2_pos,
            Real.sqrt_ne_zero'.2 hg_pos]
    _ = a / Real.sqrt (s2 * g) := by rw [hsqrt_s2_g]
    _ = (olsBeta X y j - β j) / olsEstimatedStandardError X j y := by
          simp [olsEstimatedStandardError, a, y, s2, g]

/-- The Chapter 5 scaled residual variance statistic is almost surely nonzero under the normal
regression model. This is the null-set exclusion needed to identify the classical confidence interval
event with the `|T| ≤ c` event. -/
theorem scaledOlsResidualVarianceStatistic_ne_zero_ae
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (X : Matrix n k ℝ) (β : k → ℝ) {σ2 : ℝ}
    (hσ2 : 0 < σ2) (hdf : Fintype.card k < Fintype.card n)
    (ε : Ω → EuclideanSpace ℝ n)
    [Invertible (Xᵀ * X)]
    (hε : HasLaw ε (multivariateGaussian 0 ((σ2 : ℝ) • (1 : Matrix n n ℝ))) μ) :
    ∀ᵐ ω ∂μ, scaledOlsResidualVarianceStatistic X β σ2 ε ω ≠ 0 := by
  let ν : ℕ := Fintype.card n - Fintype.card k
  letI : Fact (0 < ν) := ⟨by
    dsimp [ν]
    exact Nat.sub_pos_of_lt hdf⟩
  have hLaw :
      HasLaw (scaledOlsResidualVarianceStatistic X β σ2 ε) (chiSquared ν) μ :=
    scaledOlsResidualVarianceStatistic_hasLaw_chiSquared X β hσ2 hdf ε hε
  have hzero :
      μ {ω | scaledOlsResidualVarianceStatistic X β σ2 ε ω = 0} = 0 := by
    have hpre :
        μ {ω | scaledOlsResidualVarianceStatistic X β σ2 ε ω = 0} =
          (chiSquared ν) {0} := by
      simpa [Set.preimage, ν] using
        HasLaw.preimage_eq hLaw (s := ({0} : Set ℝ)) (measurableSet_singleton 0)
    rw [hpre, measure_singleton]
  simpa [ae_iff] using hzero

/-- The classical coefficient confidence interval event is almost surely identical to the event
`|T| ≤ c`. -/
theorem ae_mem_olsConfidenceInterval_iff_abs_t_le
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (X : Matrix n k ℝ) (β : k → ℝ) {σ2 : ℝ} (j : k) (c : ℝ)
    (hσ2 : 0 < σ2) (hdf : Fintype.card k < Fintype.card n)
    (ε : Ω → EuclideanSpace ℝ n)
    [Invertible (Xᵀ * X)]
    (hε : HasLaw ε (multivariateGaussian 0 ((σ2 : ℝ) • (1 : Matrix n n ℝ))) μ) :
    {ω | β j ∈ olsConfidenceInterval X j c (X *ᵥ β + WithLp.ofLp (ε ω))} =ᵐ[μ]
      {ω | |olsTStatistic X β σ2 j ε ω| ≤ c} := by
  filter_upwards [scaledOlsResidualVarianceStatistic_ne_zero_ae X β hσ2 hdf ε hε] with ω hω
  let y : n → ℝ := X *ᵥ β + WithLp.ofLp (ε ω)
  let s2 : ℝ := olsResidualVarianceEstimator X y
  have hdf_cast : (Fintype.card k : ℝ) < Fintype.card n := by
    exact_mod_cast hdf
  have hdf_real_pos : 0 < (Fintype.card n - Fintype.card k : ℝ) := by
    linarith
  have hs2_nonneg : 0 ≤ s2 := by
    dsimp [s2, y, olsResidualVarianceEstimator]
    refine div_nonneg ?_ ?_
    · simpa using dotProduct_self_star_nonneg (annihilatorMatrix X *ᵥ y)
    · exact hdf_real_pos.le
  have hs2_ne : s2 ≠ 0 := by
    intro hs2
    apply hω
    simp [scaledOlsResidualVarianceStatistic, y, s2, hs2]
  have hs2_pos : 0 < s2 := lt_of_le_of_ne hs2_nonneg hs2_ne.symm
  have hse_pos : 0 < olsEstimatedStandardError X j y := by
    dsimp [olsEstimatedStandardError, y, s2]
    exact Real.sqrt_pos.2 (mul_pos hs2_pos (inv_gram_diagonal_pos X j))
  have hmem :
      β j ∈ olsConfidenceInterval X j c y ↔
        |(olsBeta X y j - β j) / olsEstimatedStandardError X j y| ≤ c :=
    mem_olsConfidenceInterval_iff_abs_centered_div_le X j c (β j) (y := y) hse_pos
  have ht :
      |(olsBeta X y j - β j) / olsEstimatedStandardError X j y| ≤ c ↔
        |olsTStatistic X β σ2 j ε ω| ≤ c := by
    rw [olsTStatistic_eq_centered_beta_div_estimatedSE X β j hσ2 hdf ε hω]
  simpa [y] using hmem.trans ht

/-- Exact symmetric-interval coverage for the Chapter 5 t-statistic. This is the core probability
identity underlying Hansen Theorem 5.9 before packaging the confidence interval itself. -/
theorem olsTStatistic_abs_le_coverage_eq_studentT_interval
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (X : Matrix n k ℝ) (β : k → ℝ) {σ2 : ℝ} (j : k) (c : ℝ)
    (hσ2 : 0 < σ2) (hdf : Fintype.card k < Fintype.card n)
    (ε : Ω → EuclideanSpace ℝ n)
    [Invertible (Xᵀ * X)]
    (hε : HasLaw ε (multivariateGaussian 0 ((σ2 : ℝ) • (1 : Matrix n n ℝ))) μ) :
    μ.real {ω | |olsTStatistic X β σ2 j ε ω| ≤ c} =
      (studentT (Fintype.card n - Fintype.card k)).real (Set.Icc (-c) c) := by
  let ν : ℕ := Fintype.card n - Fintype.card k
  have hT :
      HasLaw (olsTStatistic X β σ2 j ε) (studentT ν) μ :=
    olsTStatistic_hasLaw_studentT X β j hσ2 hdf ε hε
  simpa [ν] using HasLaw.real_preimage_abs_le_eq_Icc hT c

/-- Exact coverage of the classical Chapter 5 coefficient confidence interval for an arbitrary
critical value `c`. This is the theorem-level packaging of Hansen's equation `(5.9)`. -/
theorem olsConfidenceInterval_coverage_eq_studentT_interval
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (X : Matrix n k ℝ) (β : k → ℝ) {σ2 : ℝ} (j : k) (c : ℝ)
    (hσ2 : 0 < σ2) (hdf : Fintype.card k < Fintype.card n)
    (ε : Ω → EuclideanSpace ℝ n)
    [Invertible (Xᵀ * X)]
    (hε : HasLaw ε (multivariateGaussian 0 ((σ2 : ℝ) • (1 : Matrix n n ℝ))) μ) :
    μ.real {ω | β j ∈ olsConfidenceInterval X j c (X *ᵥ β + WithLp.ofLp (ε ω))} =
      (studentT (Fintype.card n - Fintype.card k)).real (Set.Icc (-c) c) := by
  rw [measureReal_congr (ae_mem_olsConfidenceInterval_iff_abs_t_le X β j c hσ2 hdf ε hε)]
  exact olsTStatistic_abs_le_coverage_eq_studentT_interval X β j c hσ2 hdf ε hε

/-- CDF version of the symmetric-interval coverage identity for the Chapter 5 t-statistic. This is
the direct bridge from the exact Student-t law to Hansen's coverage calculations in Theorem 5.9. -/
theorem olsTStatistic_abs_le_coverage_eq_studentT_cdf
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (X : Matrix n k ℝ) (β : k → ℝ) {σ2 : ℝ} (j : k) (c : ℝ)
    (hc : 0 ≤ c)
    (hσ2 : 0 < σ2) (hdf : Fintype.card k < Fintype.card n)
    (ε : Ω → EuclideanSpace ℝ n)
    [Invertible (Xᵀ * X)]
    (hε : HasLaw ε (multivariateGaussian 0 ((σ2 : ℝ) • (1 : Matrix n n ℝ))) μ) :
    μ.real {ω | |olsTStatistic X β σ2 j ε ω| ≤ c} =
      cdf (studentT (Fintype.card n - Fintype.card k)) c -
        Function.leftLim (cdf (studentT (Fintype.card n - Fintype.card k))) (-c) := by
  let ν : ℕ := Fintype.card n - Fintype.card k
  letI : Fact (0 < ν) := ⟨by
    dsimp [ν]
    exact Nat.sub_pos_of_lt hdf⟩
  letI : IsProbabilityMeasure (chiSquared ν) := isProbabilityMeasure_chiSquared (k := ν) Fact.out
  letI : IsProbabilityMeasure (studentTFactor ν) := by
    change IsProbabilityMeasure ((chiSquared ν).map fun q : ℝ => Real.sqrt (ν : ℝ) / Real.sqrt q)
    exact Measure.isProbabilityMeasure_map (by fun_prop)
  letI : IsProbabilityMeasure (studentT ν) := ⟨by
    dsimp [studentT]
    simp⟩
  have hT :
      HasLaw (olsTStatistic X β σ2 j ε) (studentT ν) μ :=
    olsTStatistic_hasLaw_studentT X β j hσ2 hdf ε hε
  simpa [ν] using HasLaw.real_preimage_abs_le_eq_cdf_sub_leftLim hT hc

/-- CDF version of the exact coverage theorem for Hansen's Chapter 5 coefficient confidence
interval. -/
theorem olsConfidenceInterval_coverage_eq_studentT_cdf
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (X : Matrix n k ℝ) (β : k → ℝ) {σ2 : ℝ} (j : k) (c : ℝ)
    (hc : 0 ≤ c)
    (hσ2 : 0 < σ2) (hdf : Fintype.card k < Fintype.card n)
    (ε : Ω → EuclideanSpace ℝ n)
    [Invertible (Xᵀ * X)]
    (hε : HasLaw ε (multivariateGaussian 0 ((σ2 : ℝ) • (1 : Matrix n n ℝ))) μ) :
    μ.real {ω | β j ∈ olsConfidenceInterval X j c (X *ᵥ β + WithLp.ofLp (ε ω))} =
      cdf (studentT (Fintype.card n - Fintype.card k)) c -
        Function.leftLim (cdf (studentT (Fintype.card n - Fintype.card k))) (-c) := by
  rw [measureReal_congr (ae_mem_olsConfidenceInterval_iff_abs_t_le X β j c hσ2 hdf ε hε)]
  exact olsTStatistic_abs_le_coverage_eq_studentT_cdf X β j c hc hσ2 hdf ε hε

/-- Critical-value wrapper for Hansen Theorem 5.9: if the right tail and the left-limit term match
the desired `α/2` probabilities, then the symmetric `t` interval has exact coverage `1 - α`. -/
theorem olsTStatistic_abs_le_coverage_eq_one_sub
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (X : Matrix n k ℝ) (β : k → ℝ) {σ2 α : ℝ} (j : k) (c : ℝ)
    (hc : 0 ≤ c)
    (hcdf_pos : cdf (studentT (Fintype.card n - Fintype.card k)) c = 1 - α / 2)
    (hcdf_neg :
      Function.leftLim (cdf (studentT (Fintype.card n - Fintype.card k))) (-c) = α / 2)
    (hσ2 : 0 < σ2) (hdf : Fintype.card k < Fintype.card n)
    (ε : Ω → EuclideanSpace ℝ n)
    [Invertible (Xᵀ * X)]
    (hε : HasLaw ε (multivariateGaussian 0 ((σ2 : ℝ) • (1 : Matrix n n ℝ))) μ) :
    μ.real {ω | |olsTStatistic X β σ2 j ε ω| ≤ c} = 1 - α := by
  rw [olsTStatistic_abs_le_coverage_eq_studentT_cdf X β j c hc hσ2 hdf ε hε,
    hcdf_pos, hcdf_neg]
  ring

/-- Confidence-interval version of Hansen Theorem 5.9: if the critical value `c` matches the
desired tail probabilities, then the classical OLS interval has exact coverage `1 - α`. -/
theorem olsConfidenceInterval_coverage_eq_one_sub
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (X : Matrix n k ℝ) (β : k → ℝ) {σ2 α : ℝ} (j : k) (c : ℝ)
    (hc : 0 ≤ c)
    (hcdf_pos : cdf (studentT (Fintype.card n - Fintype.card k)) c = 1 - α / 2)
    (hcdf_neg :
      Function.leftLim (cdf (studentT (Fintype.card n - Fintype.card k))) (-c) = α / 2)
    (hσ2 : 0 < σ2) (hdf : Fintype.card k < Fintype.card n)
    (ε : Ω → EuclideanSpace ℝ n)
    [Invertible (Xᵀ * X)]
    (hε : HasLaw ε (multivariateGaussian 0 ((σ2 : ℝ) • (1 : Matrix n n ℝ))) μ) :
    μ.real {ω | β j ∈ olsConfidenceInterval X j c (X *ᵥ β + WithLp.ofLp (ε ω))} = 1 - α := by
  rw [measureReal_congr (ae_mem_olsConfidenceInterval_iff_abs_t_le X β j c hσ2 hdf ε hε)]
  exact olsTStatistic_abs_le_coverage_eq_one_sub X β j c hc hcdf_pos hcdf_neg hσ2 hdf ε hε

/-- Hansen's exact confidence interval for the error variance `σ²`, written as a random closed
interval on the probability space carrying the regression error. -/
noncomputable def olsVarianceConfidenceInterval
    {Ω : Type*}
    (X : Matrix n k ℝ) (β : k → ℝ) (c₁ c₂ : ℝ) [Invertible (Xᵀ * X)]
    (ε : Ω → EuclideanSpace ℝ n) : Ω → Set ℝ :=
  fun ω =>
    Set.Icc
      (((Fintype.card n - Fintype.card k : ℝ) *
          olsResidualVarianceEstimator X (X *ᵥ β + WithLp.ofLp (ε ω))) / c₂)
      (((Fintype.card n - Fintype.card k : ℝ) *
          olsResidualVarianceEstimator X (X *ᵥ β + WithLp.ofLp (ε ω))) / c₁)

/-- Membership of the true variance `σ²` in Hansen's interval (5.12) is equivalent to the scaled
variance statistic lying in `[c₁, c₂]`. -/
theorem sigma2_mem_olsVarianceConfidenceInterval_iff_scaledStatistic_mem_Icc
    {Ω : Type*}
    (X : Matrix n k ℝ) (β : k → ℝ) {σ2 : ℝ} (c₁ c₂ : ℝ)
    (hσ2 : 0 < σ2) (hc₁ : 0 < c₁) (hc₂ : c₁ ≤ c₂)
    (ε : Ω → EuclideanSpace ℝ n)
    [Invertible (Xᵀ * X)]
    (ω : Ω) :
    σ2 ∈ olsVarianceConfidenceInterval X β c₁ c₂ ε ω ↔
      scaledOlsResidualVarianceStatistic X β σ2 ε ω ∈ Set.Icc c₁ c₂ := by
  let A : ℝ :=
    (Fintype.card n - Fintype.card k : ℝ) *
      olsResidualVarianceEstimator X (X *ᵥ β + WithLp.ofLp (ε ω))
  have hc₂' : 0 < c₂ := lt_of_lt_of_le hc₁ hc₂
  change σ2 ∈ Set.Icc (A / c₂) (A / c₁) ↔ A / σ2 ∈ Set.Icc c₁ c₂
  simp only [Set.mem_Icc]
  constructor
  · intro h
    constructor
    · have hA : σ2 * c₁ ≤ A := (le_div_iff₀ hc₁).mp h.2
      exact (le_div_iff₀ hσ2).2 (by simpa [mul_comm, mul_left_comm, mul_assoc] using hA)
    · have hA : A ≤ σ2 * c₂ := (div_le_iff₀ hc₂').mp h.1
      exact (div_le_iff₀ hσ2).2 (by simpa [mul_comm, mul_left_comm, mul_assoc] using hA)
  · intro h
    constructor
    · have hA : A ≤ c₂ * σ2 := (div_le_iff₀ hσ2).mp h.2
      exact (div_le_iff₀ hc₂').2 (by simpa [mul_comm, mul_left_comm, mul_assoc] using hA)
    · have hA : c₁ * σ2 ≤ A := (le_div_iff₀ hσ2).mp h.1
      exact (le_div_iff₀ hc₁).2 (by simpa [mul_comm, mul_left_comm, mul_assoc] using hA)

/-- Exact interval-probability statement underlying Hansen Theorem 5.11. -/
theorem olsVarianceConfidenceInterval_coverage_eq_chiSquared_interval
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (X : Matrix n k ℝ) (β : k → ℝ) {σ2 : ℝ} (c₁ c₂ : ℝ)
    (hσ2 : 0 < σ2) (hdf : Fintype.card k < Fintype.card n)
    (hc₁ : 0 < c₁) (hc₂ : c₁ ≤ c₂)
    (ε : Ω → EuclideanSpace ℝ n)
    [Invertible (Xᵀ * X)]
    (hε : HasLaw ε (multivariateGaussian 0 ((σ2 : ℝ) • (1 : Matrix n n ℝ))) μ) :
    μ.real {ω | σ2 ∈ olsVarianceConfidenceInterval X β c₁ c₂ ε ω} =
      (chiSquared (Fintype.card n - Fintype.card k)).real (Set.Icc c₁ c₂) := by
  let ν : ℕ := Fintype.card n - Fintype.card k
  have hQ :
      HasLaw (scaledOlsResidualVarianceStatistic X β σ2 ε) (chiSquared ν) μ :=
    scaledOlsResidualVarianceStatistic_hasLaw_chiSquared X β hσ2 hdf ε hε
  rw [show {ω | σ2 ∈ olsVarianceConfidenceInterval X β c₁ c₂ ε ω} =
      (scaledOlsResidualVarianceStatistic X β σ2 ε) ⁻¹' Set.Icc c₁ c₂ by
        ext ω
        simpa [ν] using
          sigma2_mem_olsVarianceConfidenceInterval_iff_scaledStatistic_mem_Icc
            X β c₁ c₂ hσ2 hc₁ hc₂ ε ω]
  exact HasLaw.real_preimage_Icc_eq hQ c₁ c₂

/-- CDF version of the exact variance-interval coverage identity from Hansen Theorem 5.11. -/
theorem olsVarianceConfidenceInterval_coverage_eq_chiSquared_cdf
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (X : Matrix n k ℝ) (β : k → ℝ) {σ2 : ℝ} (c₁ c₂ : ℝ)
    (hσ2 : 0 < σ2) (hdf : Fintype.card k < Fintype.card n)
    (hc₁ : 0 < c₁) (hc₂ : c₁ ≤ c₂)
    (ε : Ω → EuclideanSpace ℝ n)
    [Invertible (Xᵀ * X)]
    (hε : HasLaw ε (multivariateGaussian 0 ((σ2 : ℝ) • (1 : Matrix n n ℝ))) μ) :
    μ.real {ω | σ2 ∈ olsVarianceConfidenceInterval X β c₁ c₂ ε ω} =
      cdf (chiSquared (Fintype.card n - Fintype.card k)) c₂ -
        cdf (chiSquared (Fintype.card n - Fintype.card k)) c₁ := by
  let ν : ℕ := Fintype.card n - Fintype.card k
  letI : Fact (0 < ν) := ⟨by
    dsimp [ν]
    exact Nat.sub_pos_of_lt hdf⟩
  have hQ :
      HasLaw (scaledOlsResidualVarianceStatistic X β σ2 ε) (chiSquared ν) μ :=
    scaledOlsResidualVarianceStatistic_hasLaw_chiSquared X β hσ2 hdf ε hε
  rw [show {ω | σ2 ∈ olsVarianceConfidenceInterval X β c₁ c₂ ε ω} =
      (scaledOlsResidualVarianceStatistic X β σ2 ε) ⁻¹' Set.Icc c₁ c₂ by
        ext ω
        simpa [ν] using
          sigma2_mem_olsVarianceConfidenceInterval_iff_scaledStatistic_mem_Icc
            X β c₁ c₂ hσ2 hc₁ hc₂ ε ω]
  simpa [ν] using
    HasLaw.real_preimage_Icc_eq_cdf_sub_of_noAtoms (μ := μ) (ν := chiSquared ν) hQ hc₂

/-- Critical-value wrapper for Hansen Theorem 5.11: if the chi-square interval endpoints match the
desired `α/2` and `1 - α/2` cdf values, then the variance interval has exact coverage `1 - α`. -/
theorem olsVarianceConfidenceInterval_coverage_eq_one_sub
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (X : Matrix n k ℝ) (β : k → ℝ) {σ2 α : ℝ} (c₁ c₂ : ℝ)
    (hcdf₁ : cdf (chiSquared (Fintype.card n - Fintype.card k)) c₁ = α / 2)
    (hcdf₂ : cdf (chiSquared (Fintype.card n - Fintype.card k)) c₂ = 1 - α / 2)
    (hσ2 : 0 < σ2) (hdf : Fintype.card k < Fintype.card n)
    (hc₁ : 0 < c₁) (hc₂ : c₁ ≤ c₂)
    (ε : Ω → EuclideanSpace ℝ n)
    [Invertible (Xᵀ * X)]
    (hε : HasLaw ε (multivariateGaussian 0 ((σ2 : ℝ) • (1 : Matrix n n ℝ))) μ) :
    μ.real {ω | σ2 ∈ olsVarianceConfidenceInterval X β c₁ c₂ ε ω} = 1 - α := by
  rw [olsVarianceConfidenceInterval_coverage_eq_chiSquared_cdf
      X β c₁ c₂ hσ2 hdf hc₁ hc₂ ε hε, hcdf₁, hcdf₂]
  ring

/-- Hansen Theorem 5.12 significance statement: if the critical value `c` is calibrated so that the
acceptance region has probability `1 - α`, then the two-sided rejection rule `c < |T|` has exact
size `α` under the null. -/
theorem olsTStatistic_rejection_probability_eq_alpha
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (X : Matrix n k ℝ) (β : k → ℝ) {σ2 α : ℝ} (j : k) (c : ℝ)
    (hc : 0 ≤ c)
    (hcdf_pos : cdf (studentT (Fintype.card n - Fintype.card k)) c = 1 - α / 2)
    (hcdf_neg :
      Function.leftLim (cdf (studentT (Fintype.card n - Fintype.card k))) (-c) = α / 2)
    (hσ2 : 0 < σ2) (hdf : Fintype.card k < Fintype.card n)
    (ε : Ω → EuclideanSpace ℝ n)
    [Invertible (Xᵀ * X)]
    (hε : HasLaw ε (multivariateGaussian 0 ((σ2 : ℝ) • (1 : Matrix n n ℝ))) μ) :
    μ.real {ω | c < |olsTStatistic X β σ2 j ε ω|} = α := by
  let ν : ℕ := Fintype.card n - Fintype.card k
  letI : Fact (0 < ν) := ⟨by
    dsimp [ν]
    exact Nat.sub_pos_of_lt hdf⟩
  letI : IsProbabilityMeasure (chiSquared ν) := isProbabilityMeasure_chiSquared (k := ν) Fact.out
  letI : IsProbabilityMeasure (studentTFactor ν) := by
    change IsProbabilityMeasure ((chiSquared ν).map fun q : ℝ => Real.sqrt (ν : ℝ) / Real.sqrt q)
    exact Measure.isProbabilityMeasure_map (by fun_prop)
  letI : IsProbabilityMeasure (studentT ν) := by
    dsimp [studentT]
    infer_instance
  have hRejectLaw :
      μ.real {ω | c < |olsTStatistic X β σ2 j ε ω|} =
        (studentT ν).real {x : ℝ | c < |x|} := by
    have hT :
        HasLaw (olsTStatistic X β σ2 j ε) (studentT ν) μ :=
      olsTStatistic_hasLaw_studentT X β j hσ2 hdf ε hε
    rw [show {ω | c < |olsTStatistic X β σ2 j ε ω|} =
        (olsTStatistic X β σ2 j ε) ⁻¹' {x : ℝ | c < |x|} by
          ext ω
          simp]
    exact HasLaw.real_preimage_eq hT (measurableSet_lt measurable_const measurable_abs)
  have hAcc :
      (studentT ν).real (Set.Icc (-c) c) = 1 - α := by
    rw [measureReal_Icc_eq_cdf_sub_leftLim (ν := studentT ν) (by linarith), hcdf_pos, hcdf_neg]
    ring
  rw [hRejectLaw, show {x : ℝ | c < |x|} = (Set.Icc (-c) c)ᶜ by
      ext x
      have hiff : c < |x| ↔ x < -c ∨ c < x := by
        constructor
        · intro hx
          rcases lt_abs.mp hx with hpos | hneg
          · right
            exact hpos
          · left
            linarith
        · intro hx
          rcases hx with hneg | hpos
          · apply lt_abs.mpr
            right
            linarith
          · apply lt_abs.mpr
            left
            exact hpos
      constructor
      · intro hx hxIcc
        rcases hiff.mp hx with hneg | hpos
        · linarith [hxIcc.1]
        · linarith [hxIcc.2]
      · intro hx
        have hx' : x < -c ∨ c < x := by
          by_contra hx'
          push_neg at hx'
          exact hx ⟨hx'.1, hx'.2⟩
        exact hiff.mpr hx']
  rw [MeasureTheory.probReal_compl_eq_one_sub measurableSet_Icc, hAcc]
  ring

section LikelihoodRatioTest

variable {k₁ k₂ : Type*}
variable [Fintype k₁] [DecidableEq k₁] [Fintype k₂] [DecidableEq k₂]

/-- The projection increment `P - P₁` that appears in Hansen's likelihood-ratio / F-test
decomposition. It extracts the fitted-value contribution of the second regressor block `X₂` after
controlling for `X₁`. -/
noncomputable def fTestProjectionMatrix
    (X₁ : Matrix n k₁ ℝ) (X₂ : Matrix n k₂ ℝ)
    [Invertible (X₁ᵀ * X₁)]
    [Invertible ((Matrix.fromCols X₁ X₂)ᵀ * Matrix.fromCols X₁ X₂)] :
    Matrix n n ℝ :=
  hatMatrix (Matrix.fromCols X₁ X₂) - hatMatrix X₁

/-- The chi-square numerator in Hansen's F statistic, scaled by the true variance `σ²`. -/
noncomputable def scaledOlsFNumeratorStatistic
    {Ω : Type*}
    (X₁ : Matrix n k₁ ℝ) (X₂ : Matrix n k₂ ℝ) (β₁ : k₁ → ℝ) (σ2 : ℝ)
    [Invertible (X₁ᵀ * X₁)]
    [Invertible ((Matrix.fromCols X₁ X₂)ᵀ * Matrix.fromCols X₁ X₂)]
    (ε : Ω → EuclideanSpace ℝ n) : Ω → ℝ :=
  fun ω =>
    (olsResidualSumSquares X₁ (X₁ *ᵥ β₁ + WithLp.ofLp (ε ω)) -
      olsResidualSumSquares (Matrix.fromCols X₁ X₂) (X₁ *ᵥ β₁ + WithLp.ofLp (ε ω))) / σ2

/-- Hansen's F statistic for testing that the right block `β₂` in the partitioned regression
`[X₁ X₂]` is zero. -/
noncomputable def olsFStatistic
    (X₁ : Matrix n k₁ ℝ) (X₂ : Matrix n k₂ ℝ) (y : n → ℝ)
    [Invertible (X₁ᵀ * X₁)]
    [Invertible ((Matrix.fromCols X₁ X₂)ᵀ * Matrix.fromCols X₁ X₂)] : ℝ :=
  ((olsResidualSumSquares X₁ y - olsResidualSumSquares (Matrix.fromCols X₁ X₂) y) /
      (Fintype.card k₂ : ℝ)) /
    (olsResidualSumSquares (Matrix.fromCols X₁ X₂) y /
      (Fintype.card n - Fintype.card (Sum k₁ k₂) : ℝ))

lemma fromCols_nullRightBlock_mulVec
    (X₁ : Matrix n k₁ ℝ) (X₂ : Matrix n k₂ ℝ) (β₁ : k₁ → ℝ) :
    Matrix.fromCols X₁ X₂ *ᵥ (Sum.elim β₁ (fun _ : k₂ => 0)) = X₁ *ᵥ β₁ := by
  rw [Matrix.fromCols_mulVec]
  change X₁ *ᵥ β₁ + X₂ *ᵥ (0 : k₂ → ℝ) = X₁ *ᵥ β₁
  rw [Matrix.mulVec_zero, add_zero]

theorem hatMatrix_fromCols_mul_left
    (X₁ : Matrix n k₁ ℝ) (X₂ : Matrix n k₂ ℝ)
    [Invertible ((Matrix.fromCols X₁ X₂)ᵀ * Matrix.fromCols X₁ X₂)] :
    hatMatrix (Matrix.fromCols X₁ X₂) * X₁ = X₁ := by
  have hPX := hat_mul_X (Matrix.fromCols X₁ X₂)
  ext i j
  simpa using congrFun (congrFun hPX i) (Sum.inl j)

theorem leftBlock_transpose_mul_fullAnnihilator
    (X₁ : Matrix n k₁ ℝ) (X₂ : Matrix n k₂ ℝ)
    [Invertible ((Matrix.fromCols X₁ X₂)ᵀ * Matrix.fromCols X₁ X₂)] :
    X₁ᵀ * annihilatorMatrix (Matrix.fromCols X₁ X₂) = 0 := by
  have h := regressors_transpose_mul_annihilator (Matrix.fromCols X₁ X₂)
  ext i j
  simpa using congrFun (congrFun h (Sum.inl i)) j

theorem fullHat_mul_leftHat
    (X₁ : Matrix n k₁ ℝ) (X₂ : Matrix n k₂ ℝ)
    [Invertible (X₁ᵀ * X₁)]
    [Invertible ((Matrix.fromCols X₁ X₂)ᵀ * Matrix.fromCols X₁ X₂)] :
    hatMatrix (Matrix.fromCols X₁ X₂) * hatMatrix X₁ = hatMatrix X₁ := by
  calc
    hatMatrix (Matrix.fromCols X₁ X₂) * hatMatrix X₁
        = hatMatrix (Matrix.fromCols X₁ X₂) * (X₁ * ⅟ (X₁ᵀ * X₁) * X₁ᵀ) := by
            rfl
    _ = (hatMatrix (Matrix.fromCols X₁ X₂) * (X₁ * ⅟ (X₁ᵀ * X₁))) * X₁ᵀ := by
          rw [← Matrix.mul_assoc]
    _ = ((hatMatrix (Matrix.fromCols X₁ X₂) * X₁) * ⅟ (X₁ᵀ * X₁)) * X₁ᵀ := by
          rw [← Matrix.mul_assoc]
    _ = X₁ * ⅟ (X₁ᵀ * X₁) * X₁ᵀ := by
          rw [hatMatrix_fromCols_mul_left]
    _ = hatMatrix X₁ := by
          rfl

theorem leftHat_mul_fullHat
    (X₁ : Matrix n k₁ ℝ) (X₂ : Matrix n k₂ ℝ)
    [Invertible (X₁ᵀ * X₁)]
    [Invertible ((Matrix.fromCols X₁ X₂)ᵀ * Matrix.fromCols X₁ X₂)] :
    hatMatrix X₁ * hatMatrix (Matrix.fromCols X₁ X₂) = hatMatrix X₁ := by
  have hT := congrArg Matrix.transpose (fullHat_mul_leftHat X₁ X₂)
  simpa [Matrix.transpose_mul, hatMatrix_transpose] using hT

theorem fTestProjectionMatrix_transpose
    (X₁ : Matrix n k₁ ℝ) (X₂ : Matrix n k₂ ℝ)
    [Invertible (X₁ᵀ * X₁)]
    [Invertible ((Matrix.fromCols X₁ X₂)ᵀ * Matrix.fromCols X₁ X₂)] :
    (fTestProjectionMatrix X₁ X₂)ᵀ = fTestProjectionMatrix X₁ X₂ := by
  simp [fTestProjectionMatrix, Matrix.transpose_sub, hatMatrix_transpose]

theorem fTestProjectionMatrix_isHermitian
    (X₁ : Matrix n k₁ ℝ) (X₂ : Matrix n k₂ ℝ)
    [Invertible (X₁ᵀ * X₁)]
    [Invertible ((Matrix.fromCols X₁ X₂)ᵀ * Matrix.fromCols X₁ X₂)] :
    (fTestProjectionMatrix X₁ X₂).IsHermitian :=
  (Matrix.conjTranspose_eq_transpose_of_trivial _).trans
    (fTestProjectionMatrix_transpose X₁ X₂)

theorem fTestProjectionMatrix_idempotent
    (X₁ : Matrix n k₁ ℝ) (X₂ : Matrix n k₂ ℝ)
    [Invertible (X₁ᵀ * X₁)]
    [Invertible ((Matrix.fromCols X₁ X₂)ᵀ * Matrix.fromCols X₁ X₂)] :
    fTestProjectionMatrix X₁ X₂ * fTestProjectionMatrix X₁ X₂ = fTestProjectionMatrix X₁ X₂ := by
  simp [fTestProjectionMatrix, Matrix.sub_mul, Matrix.mul_sub, fullHat_mul_leftHat,
    leftHat_mul_fullHat, hatMatrix_idempotent]

theorem rank_fTestProjectionMatrix
    (X₁ : Matrix n k₁ ℝ) (X₂ : Matrix n k₂ ℝ)
    [Invertible (X₁ᵀ * X₁)]
    [Invertible ((Matrix.fromCols X₁ X₂)ᵀ * Matrix.fromCols X₁ X₂)] :
    (fTestProjectionMatrix X₁ X₂).rank = Fintype.card k₂ := by
  have h :=
    rank_eq_natCast_trace_of_isHermitian_idempotent
      (fTestProjectionMatrix_isHermitian X₁ X₂)
      (fTestProjectionMatrix_idempotent X₁ X₂)
  rw [fTestProjectionMatrix, Matrix.trace_sub, hatMatrix_trace, hatMatrix_trace,
    Fintype.card_sum, Nat.cast_add] at h
  have h' : ((fTestProjectionMatrix X₁ X₂).rank : ℝ) = Fintype.card k₂ := by
    calc
      ((fTestProjectionMatrix X₁ X₂).rank : ℝ)
          = (Fintype.card k₁ : ℝ) + Fintype.card k₂ - Fintype.card k₁ := h
      _ = Fintype.card k₂ := by ring
  exact_mod_cast h'

theorem fTestProjectionMatrix_mul_fullAnnihilator
    (X₁ : Matrix n k₁ ℝ) (X₂ : Matrix n k₂ ℝ)
    [Invertible (X₁ᵀ * X₁)]
    [Invertible ((Matrix.fromCols X₁ X₂)ᵀ * Matrix.fromCols X₁ X₂)] :
    fTestProjectionMatrix X₁ X₂ * annihilatorMatrix (Matrix.fromCols X₁ X₂) = 0 := by
  have hP1M : hatMatrix X₁ * annihilatorMatrix (Matrix.fromCols X₁ X₂) = 0 := by
    unfold hatMatrix
    rw [Matrix.mul_assoc, Matrix.mul_assoc]
    rw [leftBlock_transpose_mul_fullAnnihilator X₁ X₂]
    simp
  calc
    fTestProjectionMatrix X₁ X₂ * annihilatorMatrix (Matrix.fromCols X₁ X₂)
        = hatMatrix (Matrix.fromCols X₁ X₂) * annihilatorMatrix (Matrix.fromCols X₁ X₂) -
            hatMatrix X₁ * annihilatorMatrix (Matrix.fromCols X₁ X₂) := by
              simp [fTestProjectionMatrix, Matrix.sub_mul]
    _ = 0 := by
          simp [hatMatrix_mul_annihilator, hP1M]

/-- Generic spectral rewrite for quadratic forms of symmetric idempotent matrices: the quadratic
form is a sum of squared eigenbasis coordinates over the `1`-eigenspace. -/
theorem quadratic_form_eq_sum_sq_eigenvector_coords_of_isHermitian_idempotent
    (A : Matrix n n ℝ)
    (hA : A.IsHermitian) (hI : IsIdempotentElem A) (e : n → ℝ) :
    let b : OrthonormalBasis n ℝ (EuclideanSpace ℝ n) := hA.eigenvectorBasis
    e ⬝ᵥ A *ᵥ e = ∑ i : {j : n // hA.eigenvalues j = 1}, (b.repr (WithLp.toLp 2 e) i.1)^2 := by
  classical
  let b : OrthonormalBasis n ℝ (EuclideanSpace ℝ n) := hA.eigenvectorBasis
  let z : EuclideanSpace ℝ n := WithLp.toLp 2 e
  have hAt : Aᵀ = A := by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using hA
  have hcoord : ∀ i : n, b.repr (Matrix.toEuclideanLin A z) i = hA.eigenvalues i * b.repr z i := by
    intro i
    let T : EuclideanSpace ℝ n →ₗ[ℝ] EuclideanSpace ℝ n := Matrix.toEuclideanLin A
    have hSymm : T.IsSymmetric := Matrix.isHermitian_iff_isSymmetric.mp hA
    have hEig : T (b i) = hA.eigenvalues i • b i := by
      simpa [T] using congrArg (WithLp.toLp 2) (hA.mulVec_eigenvectorBasis i)
    calc
      b.repr (T z) i = inner ℝ (b i) (T z) := by
        simpa using (OrthonormalBasis.repr_apply_apply (b := b) (v := T z) (i := i))
      _ = inner ℝ (T (b i)) z := by rw [← hSymm (b i) z]
      _ = inner ℝ (hA.eigenvalues i • b i) z := by rw [hEig]
      _ = hA.eigenvalues i * b.repr z i := by
        rw [real_inner_smul_left, OrthonormalBasis.repr_apply_apply]
  have hnorm :
      e ⬝ᵥ A *ᵥ e = ∑ i : n, (hA.eigenvalues i * b.repr z i) ^ 2 := by
    let T : EuclideanSpace ℝ n →ₗ[ℝ] EuclideanSpace ℝ n := Matrix.toEuclideanLin A
    calc
      e ⬝ᵥ A *ᵥ e = dotProduct (A *ᵥ e) (A *ᵥ e) := by
        exact quadratic_form_eq_dotProduct_of_symm_idempotent A hAt hI e
      _ = ‖T z‖ ^ 2 := by
        change dotProduct (A *ᵥ e) (A *ᵥ e) = ‖WithLp.toLp 2 (A *ᵥ e)‖ ^ 2
        simpa [pow_two] using (EuclideanSpace.real_norm_sq_eq (WithLp.toLp 2 (A *ᵥ e))).symm
      _ = ∑ i : n, ‖inner ℝ (b i) (T z)‖ ^ 2 := by
        symm
        exact OrthonormalBasis.sum_sq_norm_inner_right b (T z)
      _ = ∑ i : n, (b.repr (T z) i) ^ 2 := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        rw [OrthonormalBasis.repr_apply_apply]
        simpa [sq_abs]
      _ = ∑ i : n, (hA.eigenvalues i * b.repr z i) ^ 2 := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        rw [hcoord i]
  have heig01 := eigenvalues_zero_or_one_of_isHermitian_idempotent hA hI
  have hsum :
      ∑ i : n, (hA.eigenvalues i * b.repr z i) ^ 2
        = ∑ i : {j : n // hA.eigenvalues j = 1}, (b.repr z i.1) ^ 2 := by
    calc
      ∑ i : n, (hA.eigenvalues i * b.repr z i) ^ 2
          = ∑ i : n, if hA.eigenvalues i = 1 then (b.repr z i) ^ 2 else 0 := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              by_cases h1 : hA.eigenvalues i = 1
              · simp [h1]
              · have h0 : hA.eigenvalues i = 0 := (heig01 i).resolve_right h1
                simp [h0]
      _ = ∑ i : n with hA.eigenvalues i = 1, (b.repr z i) ^ 2 := by
            rw [Finset.sum_filter]
      _ = ∑ i : {j : n // hA.eigenvalues j = 1}, (b.repr z i.1) ^ 2 := by
            rw [Finset.sum_subtype]
            intro x
            simp
  simpa [b, z] using hnorm.trans hsum

/-- The chi-square numerator in Hansen's F statistic is the squared norm of the projection
increment `P - P₁`, divided by `σ²`. -/
theorem scaledOlsFNumeratorStatistic_eq_projection_norm_sq_div
    {Ω : Type*} [MeasurableSpace Ω]
    (X₁ : Matrix n k₁ ℝ) (X₂ : Matrix n k₂ ℝ) (β₁ : k₁ → ℝ) (σ2 : ℝ)
    (ε : Ω → EuclideanSpace ℝ n)
    [Invertible (X₁ᵀ * X₁)]
    [Invertible ((Matrix.fromCols X₁ X₂)ᵀ * Matrix.fromCols X₁ X₂)] :
    scaledOlsFNumeratorStatistic X₁ X₂ β₁ σ2 ε =
      fun ω =>
        dotProduct
          (fTestProjectionMatrix X₁ X₂ *ᵥ WithLp.ofLp (ε ω))
          (fTestProjectionMatrix X₁ X₂ *ᵥ WithLp.ofLp (ε ω)) / σ2 := by
  classical
  let fullX : Matrix n (Sum k₁ k₂) ℝ := Matrix.fromCols X₁ X₂
  let βfull : Sum k₁ k₂ → ℝ := Sum.elim β₁ (fun _ : k₂ => 0)
  let D : Matrix n n ℝ := fTestProjectionMatrix X₁ X₂
  have hβfull : fullX *ᵥ βfull = X₁ *ᵥ β₁ := by
    simpa [fullX, βfull] using fromCols_nullRightBlock_mulVec X₁ X₂ β₁
  funext ω
  let e : n → ℝ := WithLp.ofLp (ε ω)
  have hrestr :
      olsResidualSumSquares X₁ (X₁ *ᵥ β₁ + e) = e ⬝ᵥ (annihilatorMatrix X₁) *ᵥ e := by
    simpa using olsResidualSumSquares_linear_model_quadratic_form X₁ β₁ e
  have hfull :
      olsResidualSumSquares fullX (X₁ *ᵥ β₁ + e) = e ⬝ᵥ (annihilatorMatrix fullX) *ᵥ e := by
    rw [← hβfull]
    simpa [fullX, βfull] using olsResidualSumSquares_linear_model_quadratic_form fullX βfull e
  have hAnnDiff : annihilatorMatrix X₁ - annihilatorMatrix fullX = D := by
    ext i j
    simp [D, fTestProjectionMatrix, annihilatorMatrix]
    ring
  have hquad :
      dotProduct (D *ᵥ e) (D *ᵥ e) = e ⬝ᵥ D *ᵥ e := by
    exact (quadratic_form_eq_dotProduct_of_symm_idempotent D
      (fTestProjectionMatrix_transpose X₁ X₂)
      (fTestProjectionMatrix_idempotent X₁ X₂) e).symm
  calc
    scaledOlsFNumeratorStatistic X₁ X₂ β₁ σ2 ε ω
        = ((e ⬝ᵥ (annihilatorMatrix X₁) *ᵥ e) -
            (e ⬝ᵥ (annihilatorMatrix fullX) *ᵥ e)) / σ2 := by
              simp [scaledOlsFNumeratorStatistic, e, hrestr, hfull, fullX]
    _ = (e ⬝ᵥ D *ᵥ e) / σ2 := by
          rw [← dotProduct_sub, ← Matrix.sub_mulVec, hAnnDiff]
    _ = dotProduct (D *ᵥ e) (D *ᵥ e) / σ2 := by
          rw [hquad]

theorem scaledOlsFNumeratorStatistic_eq_sum_sq_eigenvector_coords
    {Ω : Type*} [MeasurableSpace Ω]
    (X₁ : Matrix n k₁ ℝ) (X₂ : Matrix n k₂ ℝ) (β₁ : k₁ → ℝ) {σ2 : ℝ}
    (hσ2 : 0 < σ2)
    (ε : Ω → EuclideanSpace ℝ n)
    [Invertible (X₁ᵀ * X₁)]
    [Invertible ((Matrix.fromCols X₁ X₂)ᵀ * Matrix.fromCols X₁ X₂)] :
    let D := fTestProjectionMatrix X₁ X₂
    let hD : D.IsHermitian := fTestProjectionMatrix_isHermitian X₁ X₂
    let b : OrthonormalBasis n ℝ (EuclideanSpace ℝ n) := hD.eigenvectorBasis
    scaledOlsFNumeratorStatistic X₁ X₂ β₁ σ2 ε =
      sumSquaresRV (restrictedStandardizedCoords b
        (fun i : {j : n // hD.eigenvalues j = 1} => i.1) σ2 ε) := by
  classical
  let D : Matrix n n ℝ := fTestProjectionMatrix X₁ X₂
  let hD : D.IsHermitian := fTestProjectionMatrix_isHermitian X₁ X₂
  let b : OrthonormalBasis n ℝ (EuclideanSpace ℝ n) := hD.eigenvectorBasis
  funext ω
  let e : n → ℝ := WithLp.ofLp (ε ω)
  have hquad :
      e ⬝ᵥ D *ᵥ e = ∑ i : {j : n // hD.eigenvalues j = 1}, (b.repr (ε ω) i.1)^2 := by
    simpa [D, hD, b, e] using
      quadratic_form_eq_sum_sq_eigenvector_coords_of_isHermitian_idempotent
        D hD (fTestProjectionMatrix_idempotent X₁ X₂) e
  have hscaled :
      scaledOlsFNumeratorStatistic X₁ X₂ β₁ σ2 ε ω = (e ⬝ᵥ D *ᵥ e) / σ2 := by
    rw [congrFun (scaledOlsFNumeratorStatistic_eq_projection_norm_sq_div X₁ X₂ β₁ σ2 ε) ω]
    exact congrArg (fun t : ℝ => t / σ2)
      ((quadratic_form_eq_dotProduct_of_symm_idempotent D
        (fTestProjectionMatrix_transpose X₁ X₂)
        (fTestProjectionMatrix_idempotent X₁ X₂) e).symm)
  calc
    scaledOlsFNumeratorStatistic X₁ X₂ β₁ σ2 ε ω
        = (e ⬝ᵥ D *ᵥ e) / σ2 := hscaled
    _ = (∑ i : {j : n // hD.eigenvalues j = 1}, (b.repr (ε ω) i.1)^2) / σ2 := by rw [hquad]
    _ = ∑ i : {j : n // hD.eigenvalues j = 1}, ((b.repr (ε ω) i.1) / Real.sqrt σ2)^2 := by
          rw [Finset.sum_div]
          refine Finset.sum_congr rfl ?_
          intro i hi
          field_simp [Real.sq_sqrt hσ2.le, hσ2.ne']
          rw [Real.sq_sqrt hσ2.le]
    _ = sumSquaresRV
          (restrictedStandardizedCoords b
            (fun i : {j : n // hD.eigenvalues j = 1} => i.1) σ2 ε) ω := by
          simp [sumSquaresRV, restrictedStandardizedCoords, standardizedCoords]

/-- Hansen Theorem 5.13, chi-square numerator component: under the null, the restricted-unrestricted
RSS gap divided by `σ²` has a `χ²(q)` law, where `q` is the number of tested restrictions. -/
theorem scaledOlsFNumeratorStatistic_hasLaw_chiSquared
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (X₁ : Matrix n k₁ ℝ) (X₂ : Matrix n k₂ ℝ) (β₁ : k₁ → ℝ) {σ2 : ℝ}
    (hσ2 : 0 < σ2) (hq : 0 < Fintype.card k₂)
    (ε : Ω → EuclideanSpace ℝ n)
    [Invertible (X₁ᵀ * X₁)]
    [Invertible ((Matrix.fromCols X₁ X₂)ᵀ * Matrix.fromCols X₁ X₂)]
    (hε : HasLaw ε (multivariateGaussian 0 ((σ2 : ℝ) • (1 : Matrix n n ℝ))) μ) :
    HasLaw (scaledOlsFNumeratorStatistic X₁ X₂ β₁ σ2 ε) (chiSquared (Fintype.card k₂)) μ := by
  classical
  let hD : (fTestProjectionMatrix X₁ X₂).IsHermitian := fTestProjectionMatrix_isHermitian X₁ X₂
  let W : {j : n // hD.eigenvalues j = 1} → Ω → ℝ :=
    restrictedStandardizedCoords hD.eigenvectorBasis
      (fun i : {j : n // hD.eigenvalues j = 1} => i.1) σ2 ε
  have hRankEqCard :
      (fTestProjectionMatrix X₁ X₂).rank = Fintype.card {j : n // hD.eigenvalues j = 1} := by
    simpa [hD] using rank_eq_card_eigenvalues_eq_one_of_isHermitian_idempotent hD
      (fTestProjectionMatrix_idempotent X₁ X₂)
  have hCardPos : 0 < Fintype.card {j : n // hD.eigenvalues j = 1} := by
    rw [← hRankEqCard, rank_fTestProjectionMatrix X₁ X₂]
    exact hq
  have hcoords := orthonormalBasis_coords_div_sqrt_iIndep_standardGaussian
    (b := hD.eigenvectorBasis) hσ2 ε hε
  have hLawW : ∀ i, HasLaw (W i) (gaussianReal 0 1) μ := by
    intro i
    simpa [W, restrictedStandardizedCoords, standardizedCoords] using hcoords.1 i.1
  have hIndepW : ProbabilityTheory.iIndepFun W μ := by
    simpa [W, restrictedStandardizedCoords, standardizedCoords] using
      hcoords.2.precomp Subtype.val_injective
  letI : MeasureSpace Ω := ⟨μ⟩
  have hLawSumSq : HasLaw (sumSquaresRV W)
      (chiSquared (Fintype.card {j : n // hD.eigenvalues j = 1})) μ := by
    simpa [W, sumSquaresRV] using hasLaw_sum_sq_chiSquared_fintype hCardPos hLawW hIndepW
  have hEq := scaledOlsFNumeratorStatistic_eq_sum_sq_eigenvector_coords X₁ X₂ β₁ hσ2 ε
  convert hLawSumSq.congr ?_ using 1
  · rw [← hRankEqCard, rank_fTestProjectionMatrix X₁ X₂]
  · simpa [hD, W] using hEq.symm

set_option maxHeartbeats 800000 in
theorem scaledOlsFNumeratorStatistic_indep_scaledOlsResidualVarianceStatistic
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (X₁ : Matrix n k₁ ℝ) (X₂ : Matrix n k₂ ℝ) (β₁ : k₁ → ℝ) {σ2 : ℝ}
    (hσ2 : 0 < σ2) (hdf : Fintype.card (Sum k₁ k₂) < Fintype.card n)
    (ε : Ω → EuclideanSpace ℝ n)
    [Invertible (X₁ᵀ * X₁)]
    [Invertible ((Matrix.fromCols X₁ X₂)ᵀ * Matrix.fromCols X₁ X₂)]
    (hε : HasLaw ε (multivariateGaussian 0 ((σ2 : ℝ) • (1 : Matrix n n ℝ))) μ) :
    scaledOlsFNumeratorStatistic X₁ X₂ β₁ σ2 ε ⟂ᵢ[μ]
      scaledOlsResidualVarianceStatistic
        (Matrix.fromCols X₁ X₂) (Sum.elim β₁ (fun _ : k₂ => 0)) σ2 ε := by
  classical
  let fullX : Matrix n (Sum k₁ k₂) ℝ := Matrix.fromCols X₁ X₂
  let βfull : Sum k₁ k₂ → ℝ := Sum.elim β₁ (fun _ : k₂ => 0)
  let D : EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ n :=
    (Matrix.toEuclideanLin (fTestProjectionMatrix X₁ X₂)).toContinuousLinearMap
  let M : EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ n :=
    (Matrix.toEuclideanLin (annihilatorMatrix fullX)).toContinuousLinearMap
  let numeratorE : Ω → EuclideanSpace ℝ n := fun ω => D (ε ω)
  let residualE : Ω → EuclideanSpace ℝ n := fun ω => M (ε ω)
  have hε_gauss : HasGaussianLaw ε μ := hε.hasGaussianLaw
  have hJoint : HasGaussianLaw (fun ω => (numeratorE ω, residualE ω)) μ := by
    simpa [numeratorE, residualE, D, M] using hε_gauss.map_fun (D.prod M)
  have hCov :
      ∀ x y,
        cov[fun ω => inner ℝ x (numeratorE ω),
          fun ω => inner ℝ y (residualE ω); μ] = 0 := by
    intro x y
    have hDadjointLin :
        (Matrix.toEuclideanLin (fTestProjectionMatrix X₁ X₂)).adjoint =
          Matrix.toEuclideanLin (fTestProjectionMatrix X₁ X₂) := by
      simpa [Matrix.conjTranspose_eq_transpose_of_trivial, fTestProjectionMatrix_transpose] using
        (Matrix.toEuclideanLin_conjTranspose_eq_adjoint
          (A := fTestProjectionMatrix X₁ X₂)).symm
    have hMadjointLin :
        (Matrix.toEuclideanLin (annihilatorMatrix fullX)).adjoint =
          Matrix.toEuclideanLin (annihilatorMatrix fullX) := by
      simpa [Matrix.conjTranspose_eq_transpose_of_trivial, annihilatorMatrix_transpose] using
        (Matrix.toEuclideanLin_conjTranspose_eq_adjoint (A := annihilatorMatrix fullX)).symm
    have hDadjoint : D.adjoint = D := by
      simpa [D, LinearMap.adjoint_toContinuousLinearMap] using
        congrArg LinearMap.toContinuousLinearMap hDadjointLin
    have hMadjoint : M.adjoint = M := by
      simpa [M, LinearMap.adjoint_toContinuousLinearMap] using
        congrArg LinearMap.toContinuousLinearMap hMadjointLin
    have hcomp : D ∘L M = 0 := by
      ext z i
      simpa [D, M, Matrix.ofLp_toEuclideanLin_apply, Matrix.mulVec_mulVec] using
        congrArg (fun A : Matrix n n ℝ => (A *ᵥ (WithLp.ofLp z)) i)
          (fTestProjectionMatrix_mul_fullAnnihilator X₁ X₂)
    have hcomp_apply : D (M y) = 0 := by
      simpa using congrArg (fun T : EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ n => T y) hcomp
    have hcov :=
      hε.covariance_fun_comp
        (f := fun z : EuclideanSpace ℝ n => inner ℝ x (D z))
        (g := fun z : EuclideanSpace ℝ n => inner ℝ y (M z))
        (by fun_prop) (by fun_prop)
    have hDfun :
        (fun z : EuclideanSpace ℝ n => inner ℝ x (D z)) =
          fun z => inner ℝ (D.adjoint x) z := by
      ext z
      simpa [D] using (D.adjoint_inner_left z x).symm
    have hMfun :
        (fun z : EuclideanSpace ℝ n => inner ℝ y (M z)) =
          fun z => inner ℝ (M y) z := by
      ext z
      simpa [hMadjoint] using (M.adjoint_inner_left z y).symm
    have hmem :
        MemLp id 2 (multivariateGaussian 0 ((σ2 : ℝ) • (1 : Matrix n n ℝ))) :=
      IsGaussian.memLp_two_id
    calc
      cov[fun ω => inner ℝ x (numeratorE ω),
        fun ω => inner ℝ y (residualE ω); μ]
          = cov[fun z : EuclideanSpace ℝ n => inner ℝ (D.adjoint x) z,
              fun z : EuclideanSpace ℝ n => inner ℝ (M y) z;
                multivariateGaussian 0 ((σ2 : ℝ) • (1 : Matrix n n ℝ))] := by
              simpa [numeratorE, residualE, hDfun, hMfun] using hcov
      _ = covarianceBilin (multivariateGaussian 0 ((σ2 : ℝ) • (1 : Matrix n n ℝ)))
            (D.adjoint x) (M y) := by
              symm
              exact covarianceBilin_apply_eq_cov hmem (D.adjoint x) (M y)
      _ = (D.adjoint x) ⬝ᵥ (((σ2 : ℝ) • (1 : Matrix n n ℝ)) *ᵥ (M y)) := by
              rw [covarianceBilin_multivariateGaussian
                (by
                  simpa [smul_one_eq_diagonal] using
                    (Matrix.PosSemidef.diagonal (n := n) (d := fun _ => σ2) fun _ => hσ2.le))]
      _ = (σ2 : ℝ) * ((D.adjoint x : EuclideanSpace ℝ n) ⬝ᵥ (M y)) := by
              simp [smul_mulVec, one_mulVec, dotProduct_smul, smul_eq_mul]
      _ = 0 := by
              have hinner :
                  inner ℝ (D.adjoint x) (M y) = 0 := by
                calc
                  inner ℝ (D.adjoint x) (M y) = inner ℝ x (D (M y)) := by
                    simpa [D] using D.adjoint_inner_left (M y) x
                  _ = 0 := by simp [hcomp_apply]
              have hdot :
                  ((D.adjoint x : EuclideanSpace ℝ n) ⬝ᵥ (M y)) = 0 := by
                have hdot' :
                    (M y).ofLp ⬝ᵥ star (((D.adjoint x : EuclideanSpace ℝ n)).ofLp) = 0 := by
                  simpa [EuclideanSpace.inner_eq_star_dotProduct] using hinner
                simpa [dotProduct, Pi.star_apply, conj_trivial, mul_comm] using hdot'
              rw [hdot, mul_zero]
  have hIndProj : numeratorE ⟂ᵢ[μ] residualE :=
    hJoint.indepFun_of_covariance_inner hCov
  have hIndFunctions :
      (fun ω => fTestProjectionMatrix X₁ X₂ *ᵥ WithLp.ofLp (ε ω)) ⟂ᵢ[μ]
        (fun ω => annihilatorMatrix fullX *ᵥ WithLp.ofLp (ε ω)) := by
    have hIndEuclid :
        (fun ω => WithLp.toLp 2 (fTestProjectionMatrix X₁ X₂ *ᵥ WithLp.ofLp (ε ω))) ⟂ᵢ[μ]
          (fun ω => WithLp.toLp 2 (annihilatorMatrix fullX *ᵥ WithLp.ofLp (ε ω))) := by
      refine (IndepFun.congr hIndProj ?_ ?_)
      · filter_upwards with ω
        simpa [numeratorE, D] using
          (Matrix.toLpLin_apply (p := 2) (q := 2) (fTestProjectionMatrix X₁ X₂) (ε ω))
      · filter_upwards with ω
        simpa [residualE, M] using
          (Matrix.toLpLin_apply (p := 2) (q := 2) (annihilatorMatrix fullX) (ε ω))
    have hmeasN : Measurable (WithLp.ofLp : EuclideanSpace ℝ n → n → ℝ) :=
      WithLp.measurable_ofLp (p := 2) (X := n → ℝ)
    simpa using
      (IndepFun.comp (φ := (WithLp.ofLp : EuclideanSpace ℝ n → n → ℝ))
        (ψ := (WithLp.ofLp : EuclideanSpace ℝ n → n → ℝ))
        hIndEuclid hmeasN hmeasN)
  let q : (n → ℝ) → ℝ := fun r => dotProduct r r / σ2
  have hq : Measurable q := by
    simpa [q] using (Continuous.dotProduct continuous_id continuous_id).div_const σ2 |>.measurable
  have hIndStat :
      (q ∘ fun ω => fTestProjectionMatrix X₁ X₂ *ᵥ WithLp.ofLp (ε ω)) ⟂ᵢ[μ]
        (q ∘ fun ω => annihilatorMatrix fullX *ᵥ WithLp.ofLp (ε ω)) := by
    exact IndepFun.comp (μ := μ) (φ := q) (ψ := q) hIndFunctions hq hq
  refine IndepFun.congr hIndStat ?_ ?_
  · filter_upwards with ω
    simp [Function.comp, q]
    exact (congrFun (scaledOlsFNumeratorStatistic_eq_projection_norm_sq_div
      X₁ X₂ β₁ σ2 ε) ω).symm
  · filter_upwards with ω
    rw [scaledOlsResidualVarianceStatistic_eq_residual_norm_sq_div fullX βfull hdf ε]
    simpa [Function.comp, q, fullX, βfull] using
      congrArg (fun r : n → ℝ => dotProduct r r / σ2)
        ((residual_linear_model fullX βfull (WithLp.ofLp (ε ω))).symm)

theorem olsFStatistic_eq_ratio_of_scaled_chiSquared_statistics
    {Ω : Type*} [MeasurableSpace Ω]
    (X₁ : Matrix n k₁ ℝ) (X₂ : Matrix n k₂ ℝ) (β₁ : k₁ → ℝ) {σ2 : ℝ}
    (hσ2 : 0 < σ2) (hdf : Fintype.card (Sum k₁ k₂) < Fintype.card n)
    (ε : Ω → EuclideanSpace ℝ n)
    [Invertible (X₁ᵀ * X₁)]
    [Invertible ((Matrix.fromCols X₁ X₂)ᵀ * Matrix.fromCols X₁ X₂)] :
    let fullX : Matrix n (Sum k₁ k₂) ℝ := Matrix.fromCols X₁ X₂
    let βfull : Sum k₁ k₂ → ℝ := Sum.elim β₁ (fun _ : k₂ => 0)
    (fun ω => olsFStatistic X₁ X₂ (X₁ *ᵥ β₁ + WithLp.ofLp (ε ω))) =
      fun ω =>
        ((scaledOlsFNumeratorStatistic X₁ X₂ β₁ σ2 ε ω) / (Fintype.card k₂ : ℝ)) /
          (scaledOlsResidualVarianceStatistic fullX βfull σ2 ε ω /
            (Fintype.card n - Fintype.card (Sum k₁ k₂) : ℝ)) := by
  classical
  let fullX : Matrix n (Sum k₁ k₂) ℝ := Matrix.fromCols X₁ X₂
  let βfull : Sum k₁ k₂ → ℝ := Sum.elim β₁ (fun _ : k₂ => 0)
  have hβfull : fullX *ᵥ βfull = X₁ *ᵥ β₁ := fromCols_nullRightBlock_mulVec X₁ X₂ β₁
  let ν : ℝ := (Fintype.card n - Fintype.card (Sum k₁ k₂) : ℝ)
  have hν_ne : ν ≠ 0 := by
    dsimp [ν]
    exact sub_ne_zero.mpr (by exact_mod_cast (Nat.ne_of_gt hdf))
  ext ω
  let e : n → ℝ := WithLp.ofLp (ε ω)
  let rssR : ℝ := olsResidualSumSquares X₁ (X₁ *ᵥ β₁ + e)
  let rssU : ℝ := olsResidualSumSquares fullX (X₁ *ᵥ β₁ + e)
  have hNum :
      scaledOlsFNumeratorStatistic X₁ X₂ β₁ σ2 ε ω = (rssR - rssU) / σ2 := by
    simp [scaledOlsFNumeratorStatistic, rssR, rssU, e, fullX]
  have hDen :
      scaledOlsResidualVarianceStatistic fullX βfull σ2 ε ω = rssU / σ2 := by
    have hν_cast : ((Fintype.card n - Fintype.card (Sum k₁ k₂) : ℕ) : ℝ) = ν := by
      rw [Nat.cast_sub hdf.le]
    calc
      scaledOlsResidualVarianceStatistic fullX βfull σ2 ε ω
          = (ν * olsResidualVarianceEstimator fullX (fullX *ᵥ βfull + e)) / σ2 := by
              simp [scaledOlsResidualVarianceStatistic, ν, e, hν_cast]
      _ = (ν * (rssU / ν)) / σ2 := by
            have hrssU : rssU = olsResidualSumSquares fullX (fullX *ᵥ βfull + e) := by
              simp [rssU, hβfull]
            rw [hrssU]
            simp [ν, e, fullX, βfull, olsResidualVarianceEstimator, olsResidualSumSquares, hν_ne]
      _ = rssU / σ2 := by
            field_simp [hν_ne]
  calc
    olsFStatistic X₁ X₂ (X₁ *ᵥ β₁ + e)
        = ((rssR - rssU) / (Fintype.card k₂ : ℝ)) / (rssU / ν) := by
            simp [olsFStatistic, rssR, rssU, ν, e, fullX]
    _ = (((rssR - rssU) / σ2) / (Fintype.card k₂ : ℝ)) / ((rssU / σ2) / ν) := by
          field_simp [hσ2.ne']
    _ = ((scaledOlsFNumeratorStatistic X₁ X₂ β₁ σ2 ε ω) / (Fintype.card k₂ : ℝ)) /
          (scaledOlsResidualVarianceStatistic fullX βfull σ2 ε ω / ν) := by
            rw [hNum, hDen]

/-- Hansen Theorem 5.13: under the null `β₂ = 0`, the classical block F statistic has the
Fisher-Snedecor law with `q` and `n-k` degrees of freedom. -/
theorem olsFStatistic_hasLaw_fDist
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (X₁ : Matrix n k₁ ℝ) (X₂ : Matrix n k₂ ℝ) (β₁ : k₁ → ℝ) {σ2 : ℝ}
    (hσ2 : 0 < σ2) (hq : 0 < Fintype.card k₂)
    (hdf : Fintype.card (Sum k₁ k₂) < Fintype.card n)
    (ε : Ω → EuclideanSpace ℝ n)
    [Invertible (X₁ᵀ * X₁)]
    [Invertible ((Matrix.fromCols X₁ X₂)ᵀ * Matrix.fromCols X₁ X₂)]
    (hε : HasLaw ε (multivariateGaussian 0 ((σ2 : ℝ) • (1 : Matrix n n ℝ))) μ) :
    HasLaw (fun ω => olsFStatistic X₁ X₂ (X₁ *ᵥ β₁ + WithLp.ofLp (ε ω)))
      (fDist (Fintype.card k₂) (Fintype.card n - Fintype.card (Sum k₁ k₂))) μ := by
  let fullX : Matrix n (Sum k₁ k₂) ℝ := Matrix.fromCols X₁ X₂
  let βfull : Sum k₁ k₂ → ℝ := Sum.elim β₁ (fun _ : k₂ => 0)
  have hNum :
      HasLaw (scaledOlsFNumeratorStatistic X₁ X₂ β₁ σ2 ε) (chiSquared (Fintype.card k₂)) μ :=
    scaledOlsFNumeratorStatistic_hasLaw_chiSquared X₁ X₂ β₁ hσ2 hq ε hε
  have hDen :
      HasLaw (scaledOlsResidualVarianceStatistic fullX βfull σ2 ε)
        (chiSquared (Fintype.card n - Fintype.card (Sum k₁ k₂))) μ :=
    scaledOlsResidualVarianceStatistic_hasLaw_chiSquared fullX βfull hσ2 hdf ε hε
  have hInd :
      scaledOlsFNumeratorStatistic X₁ X₂ β₁ σ2 ε ⟂ᵢ[μ]
        scaledOlsResidualVarianceStatistic fullX βfull σ2 ε :=
    scaledOlsFNumeratorStatistic_indep_scaledOlsResidualVarianceStatistic
      X₁ X₂ β₁ hσ2 hdf ε hε
  have hRatio :
      HasLaw
        (fun ω =>
          ((scaledOlsFNumeratorStatistic X₁ X₂ β₁ σ2 ε ω) / (Fintype.card k₂ : ℝ)) /
            (scaledOlsResidualVarianceStatistic fullX βfull σ2 ε ω /
              (Fintype.card n - Fintype.card (Sum k₁ k₂) : ℝ)))
        (fDist (Fintype.card k₂) (Fintype.card n - Fintype.card (Sum k₁ k₂))) μ :=
    by
      have hdf' : Fintype.card k₁ + Fintype.card k₂ ≤ Fintype.card n := by
        exact Nat.le_of_lt (by simpa [Fintype.card_sum] using hdf)
      simpa [Fintype.card_sum, Nat.cast_add, Nat.cast_sub hdf'] using
        (hasLaw_ratio_chiSquared_fDist hq (Nat.sub_pos_of_lt hdf) hNum hDen hInd)
  refine hRatio.congr ?_
  filter_upwards with ω
  simpa [fullX, βfull] using
    congrFun (olsFStatistic_eq_ratio_of_scaled_chiSquared_statistics
      X₁ X₂ β₁ hσ2 hdf ε) ω

/-- Hansen Theorem 5.13 rejection statement: if the upper-tail critical value `c` is calibrated to
have F-distribution tail probability `α`, then the rule `F > c` has exact size `α` under the null. -/
theorem olsFStatistic_rejection_probability_eq_alpha
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (X₁ : Matrix n k₁ ℝ) (X₂ : Matrix n k₂ ℝ) (β₁ : k₁ → ℝ) {σ2 α : ℝ}
    (c : ℝ) (hcrit :
      (fDist (Fintype.card k₂) (Fintype.card n - Fintype.card (Sum k₁ k₂))).real (Set.Ioi c) = α)
    (hσ2 : 0 < σ2) (hq : 0 < Fintype.card k₂)
    (hdf : Fintype.card (Sum k₁ k₂) < Fintype.card n)
    (ε : Ω → EuclideanSpace ℝ n)
    [Invertible (X₁ᵀ * X₁)]
    [Invertible ((Matrix.fromCols X₁ X₂)ᵀ * Matrix.fromCols X₁ X₂)]
    (hε : HasLaw ε (multivariateGaussian 0 ((σ2 : ℝ) • (1 : Matrix n n ℝ))) μ) :
    μ.real {ω | c < olsFStatistic X₁ X₂ (X₁ *ᵥ β₁ + WithLp.ofLp (ε ω))} = α := by
  have hF :
      HasLaw (fun ω => olsFStatistic X₁ X₂ (X₁ *ᵥ β₁ + WithLp.ofLp (ε ω)))
        (fDist (Fintype.card k₂) (Fintype.card n - Fintype.card (Sum k₁ k₂))) μ :=
    olsFStatistic_hasLaw_fDist X₁ X₂ β₁ hσ2 hq hdf ε hε
  have hPre :
      μ.real {ω | c < olsFStatistic X₁ X₂ (X₁ *ᵥ β₁ + WithLp.ofLp (ε ω))} =
        (fDist (Fintype.card k₂) (Fintype.card n - Fintype.card (Sum k₁ k₂))).real (Set.Ioi c) := by
    rw [show {ω | c < olsFStatistic X₁ X₂ (X₁ *ᵥ β₁ + WithLp.ofLp (ε ω))} =
        (fun ω => olsFStatistic X₁ X₂ (X₁ *ᵥ β₁ + WithLp.ofLp (ε ω))) ⁻¹' Set.Ioi c by
          ext ω
          simp [Set.mem_Ioi]]
    exact HasLaw.real_preimage_eq hF measurableSet_Ioi
  rw [hPre, hcrit]

end LikelihoodRatioTest

end HansenEconometrics
