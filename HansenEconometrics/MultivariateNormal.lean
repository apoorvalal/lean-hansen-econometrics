import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence

open MeasureTheory ProbabilityTheory
open Matrix WithLp
open scoped MatrixOrder RealInnerProductSpace

namespace HansenEconometrics

/-!
# Multivariate normal helper wrappers

This module provides Hansen-facing wrappers around Mathlib's real and multivariate Gaussian
distribution API.  The public surface is intentionally thin: standard-normal finite-moment facts,
mean/covariance facts for `multivariateGaussian`, affine-image laws, marginal laws, and the
joint-Gaussian independence/covariance equivalence.
-/

/-! ## Hansen Theorem 5.1: standard-normal moment facts -/

/-- Standard normal random variables have finite moments of every finite nonnegative order.  This is
the Mathlib-backed finite-moment face of Hansen Theorem 5.1. -/
theorem standardNormal_memLp (p : NNReal) :
    MemLp id p (gaussianReal 0 1) := by
  simpa using (memLp_id_gaussianReal (μ := 0) (v := 1) p)

/-- The standard normal has mean zero. -/
@[simp] theorem standardNormal_mean :
    ∫ z : ℝ, z ∂gaussianReal 0 1 = 0 := by
  simp [integral_id_gaussianReal]

/-- The standard normal has variance one. -/
@[simp] theorem standardNormal_variance :
    Var[id; gaussianReal 0 1] = 1 := by
  simp [variance_id_gaussianReal]

/-! ## Matrix-linear maps on Euclidean spaces -/

/-- The continuous linear map induced by a rectangular real matrix between Euclidean spaces. -/
noncomputable def matrixContinuousLinearMap
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (B : Matrix m n ℝ) : EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ m :=
  (Matrix.toEuclideanLin B).toContinuousLinearMap

@[simp] theorem matrixContinuousLinearMap_apply
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (B : Matrix m n ℝ) (x : EuclideanSpace ℝ n) :
    (matrixContinuousLinearMap B x).ofLp = B *ᵥ x.ofLp :=
  rfl

/-! ## Hansen Theorem 5.2: affine images of multivariate normals -/

/-- Covariance of a matrix-linear image of a multivariate normal. -/
theorem covarianceBilin_map_matrix_multivariateGaussian
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    {μ : EuclideanSpace ℝ n} {S : Matrix n n ℝ} (hS : S.PosSemidef)
    (B : Matrix m n ℝ) (u v : EuclideanSpace ℝ m) :
    covarianceBilin ((multivariateGaussian μ S).map (matrixContinuousLinearMap B)) u v =
      u.ofLp ⬝ᵥ (B * S * Bᴴ) *ᵥ v.ofLp := by
  classical
  let L : EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ m := matrixContinuousLinearMap B
  rw [covarianceBilin_map (μ := multivariateGaussian μ S) IsGaussian.memLp_two_id L u v]
  rw [covarianceBilin_multivariateGaussian hS]
  have hAdj : L.adjoint = matrixContinuousLinearMap Bᴴ := by
    dsimp [L, matrixContinuousLinearMap]
    have h2 :=
      congrArg LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin_conjTranspose_eq_adjoint B)
    exact (LinearMap.adjoint_toContinuousLinearMap (Matrix.toEuclideanLin B)).symm.trans h2.symm
  rw [hAdj]
  change (Bᴴ *ᵥ u.ofLp) ⬝ᵥ S *ᵥ (Bᴴ *ᵥ v.ofLp) =
      u.ofLp ⬝ᵥ (B * S * Bᴴ) *ᵥ v.ofLp
  calc
    (Bᴴ *ᵥ u.ofLp) ⬝ᵥ S *ᵥ (Bᴴ *ᵥ v.ofLp)
        = (u.ofLp ᵥ* B) ⬝ᵥ S *ᵥ (Bᴴ *ᵥ v.ofLp) := by
            simp [← Matrix.vecMul_transpose]
    _ = u.ofLp ⬝ᵥ B *ᵥ (S *ᵥ (Bᴴ *ᵥ v.ofLp)) := by
            exact (Matrix.dotProduct_mulVec u.ofLp B (S *ᵥ (Bᴴ *ᵥ v.ofLp))).symm
    _ = u.ofLp ⬝ᵥ (B * S * Bᴴ) *ᵥ v.ofLp := by
            simp [Matrix.mulVec_mulVec, Matrix.mul_assoc]

/-- A matrix-linear image of a multivariate normal is multivariate normal with covariance
`B Σ B'`. -/
theorem map_matrix_multivariateGaussian
    {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    {μ : EuclideanSpace ℝ n} {S : Matrix n n ℝ} (hS : S.PosSemidef)
    (B : Matrix m n ℝ) :
    (multivariateGaussian μ S).map (matrixContinuousLinearMap B) =
      multivariateGaussian (matrixContinuousLinearMap B μ) (B * S * Bᴴ) := by
  apply IsGaussian.ext
  · simp only [id_eq]
    rw [ContinuousLinearMap.integral_id_map IsGaussian.integrable_id,
      integral_id_multivariateGaussian, integral_id_multivariateGaussian]
  · ext u v
    rw [covarianceBilin_map_matrix_multivariateGaussian hS B u v]
    rw [covarianceBilin_multivariateGaussian (hS.mul_mul_conjTranspose_same B)]

/-- Translating a multivariate normal shifts its mean and preserves its covariance. -/
theorem map_const_add_multivariateGaussian
    {n : Type*} [Fintype n] [DecidableEq n]
    (a μ : EuclideanSpace ℝ n) (S : Matrix n n ℝ) :
    (multivariateGaussian μ S).map (fun x => a + x) =
      multivariateGaussian (a + μ) S := by
  rw [multivariateGaussian]
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  ext x i
  simp [add_assoc]

/-- **Hansen Theorem 5.2.** If `X ∼ N(μ, Σ)`, then `a + B X` has law
`N(a + B μ, B Σ B')`. -/
theorem map_affine_multivariateGaussian
    {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    {μ : EuclideanSpace ℝ n} {S : Matrix n n ℝ} (hS : S.PosSemidef)
    (a : EuclideanSpace ℝ m) (B : Matrix m n ℝ) :
    (multivariateGaussian μ S).map (fun x => a + matrixContinuousLinearMap B x) =
      multivariateGaussian (a + matrixContinuousLinearMap B μ) (B * S * Bᴴ) := by
  let L : EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ m := matrixContinuousLinearMap B
  calc
    (multivariateGaussian μ S).map (fun x => a + matrixContinuousLinearMap B x)
        = ((multivariateGaussian μ S).map L).map (fun y => a + y) := by
            rw [Measure.map_map (by fun_prop) (by fun_prop)]
            rfl
    _ = (multivariateGaussian (L μ) (B * S * Bᴴ)).map (fun y => a + y) := by
            rw [map_matrix_multivariateGaussian hS B]
    _ = multivariateGaussian (a + L μ) (B * S * Bᴴ) := by
            rw [map_const_add_multivariateGaussian]

/-- Random-variable version of Hansen Theorem 5.2. -/
theorem hasLaw_affine_multivariateGaussian
    {Ω m n : Type*} [MeasurableSpace Ω]
    [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    {P : Measure Ω} {X : Ω → EuclideanSpace ℝ n}
    {μ : EuclideanSpace ℝ n} {S : Matrix n n ℝ} (hS : S.PosSemidef)
    (hX : HasLaw X (multivariateGaussian μ S) P)
    (a : EuclideanSpace ℝ m) (B : Matrix m n ℝ) :
    HasLaw (fun ω => a + matrixContinuousLinearMap B (X ω))
      (multivariateGaussian (a + matrixContinuousLinearMap B μ) (B * S * Bᴴ)) P := by
  have hf : HasLaw (fun x : EuclideanSpace ℝ n => a + matrixContinuousLinearMap B x)
      (multivariateGaussian (a + matrixContinuousLinearMap B μ) (B * S * Bᴴ))
      (multivariateGaussian μ S) := by
    constructor
    · exact Measurable.aemeasurable (Continuous.measurable
        ((continuous_const : Continuous (fun _ : EuclideanSpace ℝ n => a)).add
          (matrixContinuousLinearMap B).continuous))
    · exact map_affine_multivariateGaussian hS a B
  simpa [Function.comp_def] using (HasLaw.comp hf hX)

/-! ## Hansen Theorem 5.3: basic multivariate-normal properties -/

/-- The mean vector of `N(μ, Σ)` is `μ`. -/
@[simp] theorem multivariateGaussian_mean
    {n : Type*} [Fintype n] [DecidableEq n]
    {μ : EuclideanSpace ℝ n} {S : Matrix n n ℝ} :
    ∫ x, x ∂multivariateGaussian μ S = μ :=
  integral_id_multivariateGaussian

/-- The covariance bilinear form of `N(μ, Σ)` is represented by `Σ`. -/
theorem multivariateGaussian_covarianceBilin
    {n : Type*} [Fintype n] [DecidableEq n]
    {μ : EuclideanSpace ℝ n} {S : Matrix n n ℝ} (hS : S.PosSemidef)
    (u v : EuclideanSpace ℝ n) :
    covarianceBilin (multivariateGaussian μ S) u v = u.ofLp ⬝ᵥ S *ᵥ v.ofLp :=
  covarianceBilin_multivariateGaussian hS u v

/-- Coordinate covariance in `N(μ, Σ)` reads off the corresponding matrix entry. -/
theorem multivariateGaussian_covariance_eval
    {n : Type*} [Fintype n] [DecidableEq n]
    {μ : EuclideanSpace ℝ n} {S : Matrix n n ℝ} (hS : S.PosSemidef)
    (i j : n) :
    cov[fun x => x.ofLp i, fun x => x.ofLp j; multivariateGaussian μ S] = S i j :=
  covariance_eval_multivariateGaussian hS i j

/-- Coordinate variance in `N(μ, Σ)` reads off the corresponding diagonal entry. -/
theorem multivariateGaussian_variance_eval
    {n : Type*} [Fintype n] [DecidableEq n]
    {μ : EuclideanSpace ℝ n} {S : Matrix n n ℝ} (hS : S.PosSemidef)
    (i : n) :
    Var[fun x => x.ofLp i; multivariateGaussian μ S] = S i i :=
  variance_eval_multivariateGaussian hS i

/-- A coordinate projection of a multivariate normal is univariate normal. -/
theorem multivariateGaussian_eval_hasLaw
    {n : Type*} [Fintype n] [DecidableEq n]
    {μ : EuclideanSpace ℝ n} {S : Matrix n n ℝ} (hS : S.PosSemidef)
    (i : n) :
    HasLaw (fun x : EuclideanSpace ℝ n => x.ofLp i)
      (gaussianReal (μ.ofLp i) (S i i).toNNReal) (multivariateGaussian μ S) :=
  (measurePreserving_eval_multivariateGaussian (μ := μ) (S := S) hS (i := i)).hasLaw

/-- A coordinate subvector of a multivariate normal is multivariate normal with the corresponding
subvector mean and covariance submatrix. -/
theorem multivariateGaussian_restrict₂_hasLaw
    {ι : Type*} [DecidableEq ι] {I J : Finset ι}
    {μ : EuclideanSpace ℝ I} {S : Matrix I I ℝ} (hS : S.PosSemidef)
    (hJI : J ⊆ I) :
    HasLaw (EuclideanSpace.restrict₂ hJI)
      (multivariateGaussian ((EuclideanSpace.restrict₂ hJI) μ)
        (S.submatrix (fun i : J => ⟨i.1, hJI i.2⟩) (fun i : J => ⟨i.1, hJI i.2⟩)))
      (multivariateGaussian μ S) :=
  (measurePreserving_restrict₂_multivariateGaussian hS hJI).hasLaw

/-- For scalar jointly Gaussian variables, independence is equivalent to zero covariance.  This is
the scalar Hansen-facing form of the uncorrelated-subvector property in Theorem 5.3. -/
theorem jointGaussian_indepFun_iff_cov_eq_zero
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X Y : Ω → ℝ}
    (hXY : HasGaussianLaw (fun ω => (X ω, Y ω)) P) :
    IndepFun X Y P ↔ cov[X, Y; P] = 0 := by
  constructor
  · intro h
    exact h.covariance_eq_zero hXY.fst.memLp_two hXY.snd.memLp_two
  · exact hXY.indepFun_of_covariance_eq_zero

end HansenEconometrics
