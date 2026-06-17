import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Chapter 11 — factor models

This module records the principal-component factor-estimation surface and the
large-dimension condition package used in Hansen's approximate-factor discussion.
It ties the factor-PCA certificate to the sample second-moment matrix and a
concrete eigenspace equation. It also proves deterministic least-squares bridges
for Hansen Theorem 11.9: the principal-component score formula is the
fixed-loading least-squares score, and the eigenspace/scaling certificate implies
the sample factor normalization and loading normal equation.
-/

open scoped Matrix

namespace HansenEconometrics

open Matrix

variable {n k r : Type*}
variable [Fintype n] [Fintype k] [Fintype r] [DecidableEq n] [DecidableEq k] [DecidableEq r]

/-- Principal-component loading estimator `H D^{1/2}`. The square-root diagonal is supplied
explicitly so downstream files can choose the spectral normalization they need. -/
noncomputable def factorLoadingEstimator
    (H : Matrix k r ℝ) (sqrtD : Matrix r r ℝ) : Matrix k r ℝ :=
  H * sqrtD

/-- Principal-component factor estimator `D^{-1/2} H' X`. -/
noncomputable def factorScoreEstimator
    (H : Matrix k r ℝ) (invSqrtD : Matrix r r ℝ) (X : k → ℝ) : r → ℝ :=
  invSqrtD *ᵥ (Hᵀ *ᵥ X)

/-- Fixed-loading least-squares factor score
`(Λ'Λ)^{-1}Λ'X`, using Mathlib's total nonsingular inverse. -/
noncomputable def factorScoreLeastSquares
    (Λ : Matrix k r ℝ) (X : k → ℝ) : r → ℝ :=
  (Λᵀ * Λ)⁻¹ *ᵥ (Λᵀ *ᵥ X)

/-- Sample second-moment matrix `n⁻¹∑ X_i X_i'` used in Hansen Theorem 11.9. -/
noncomputable def factorSampleCovariance
    (X : n → k → ℝ) : Matrix k k ℝ :=
  (Fintype.card n : ℝ)⁻¹ • ∑ i : n, Matrix.vecMulVec (X i) (X i)

/-- Sample cross moment `n⁻¹∑ X_i Fhat_i'`. Under Hansen's factor normalization,
this is the least-squares loading normal equation. -/
noncomputable def factorSampleCrossCovariance
    (X : n → k → ℝ) (Fhat : n → r → ℝ) : Matrix k r ℝ :=
  (Fintype.card n : ℝ)⁻¹ • ∑ i : n, Matrix.vecMulVec (X i) (Fhat i)

/-- Sample second-moment matrix of estimated factors. -/
noncomputable def factorScoreSampleCovariance
    (Fhat : n → r → ℝ) : Matrix r r ℝ :=
  (Fintype.card n : ℝ)⁻¹ • ∑ i : n, Matrix.vecMulVec (Fhat i) (Fhat i)

/-- Hansen Theorem 11.9 normalization `n⁻¹∑ Fhat_i Fhat_i' = I_r`. -/
def factorScoreNormalization (Fhat : n → r → ℝ) : Prop :=
  factorScoreSampleCovariance Fhat = 1

omit [Fintype k] [DecidableEq n] [DecidableEq k] in
@[simp]
theorem factorSampleCovariance_apply
    (X : n → k → ℝ) (a b : k) :
    factorSampleCovariance X a b =
      (Fintype.card n : ℝ)⁻¹ * ∑ i : n, X i a * X i b := by
  rw [factorSampleCovariance]
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.sum_apply, Matrix.vecMulVec_apply]

omit [Fintype k] [Fintype r] [DecidableEq n] [DecidableEq k] [DecidableEq r] in
@[simp]
theorem factorSampleCrossCovariance_apply
    (X : n → k → ℝ) (Fhat : n → r → ℝ) (a : k) (b : r) :
    factorSampleCrossCovariance X Fhat a b =
      (Fintype.card n : ℝ)⁻¹ * ∑ i : n, X i a * Fhat i b := by
  rw [factorSampleCrossCovariance]
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.sum_apply, Matrix.vecMulVec_apply]

omit [Fintype r] [DecidableEq n] [DecidableEq r] in
@[simp]
theorem factorScoreSampleCovariance_apply
    (Fhat : n → r → ℝ) (a b : r) :
    factorScoreSampleCovariance Fhat a b =
      (Fintype.card n : ℝ)⁻¹ * ∑ i : n, Fhat i a * Fhat i b := by
  rw [factorScoreSampleCovariance]
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.sum_apply, Matrix.vecMulVec_apply]

omit [Fintype r] [DecidableEq n] [DecidableEq k] [DecidableEq r] in
private theorem vecMulVec_mulVec_right
    (x : k → ℝ) (A : Matrix r k ℝ) :
    Matrix.vecMulVec x (A *ᵥ x) = Matrix.vecMulVec x x * Aᵀ := by
  rw [Matrix.vecMulVec_mul, Matrix.vecMul_transpose]

omit [Fintype r] [DecidableEq n] [DecidableEq k] [DecidableEq r] in
/-- Outer products commute with applying a fixed linear score map to the right. -/
private theorem vecMulVec_mulVec_both
    (x : k → ℝ) (A : Matrix r k ℝ) :
    Matrix.vecMulVec (A *ᵥ x) (A *ᵥ x) =
      A * Matrix.vecMulVec x x * Aᵀ := by
  calc
    Matrix.vecMulVec (A *ᵥ x) (A *ᵥ x)
        = A * Matrix.vecMulVec x (A *ᵥ x) := by
            rw [Matrix.mul_vecMulVec]
    _ = A * (Matrix.vecMulVec x x * Aᵀ) := by
            rw [vecMulVec_mulVec_right]
    _ = A * Matrix.vecMulVec x x * Aᵀ := by
            rw [Matrix.mul_assoc]

omit [Fintype r] [DecidableEq n] [DecidableEq k] [DecidableEq r] in
/-- Cross moments after applying a fixed linear score map. -/
theorem factorSampleCrossCovariance_linearMap
    (X : n → k → ℝ) (A : Matrix r k ℝ) :
    factorSampleCrossCovariance X (fun i => A *ᵥ X i) =
      factorSampleCovariance X * Aᵀ := by
  rw [factorSampleCrossCovariance, factorSampleCovariance]
  simp_rw [vecMulVec_mulVec_right]
  rw [← Matrix.sum_mul, Matrix.smul_mul]

omit [Fintype r] [DecidableEq n] [DecidableEq k] [DecidableEq r] in
/-- Score covariance after applying a fixed linear score map. -/
theorem factorScoreSampleCovariance_linearMap
    (X : n → k → ℝ) (A : Matrix r k ℝ) :
    factorScoreSampleCovariance (fun i => A *ᵥ X i) =
      A * factorSampleCovariance X * Aᵀ := by
  rw [factorScoreSampleCovariance, factorSampleCovariance]
  simp_rw [vecMulVec_mulVec_both]
  rw [← Matrix.sum_mul, ← Matrix.mul_sum, Matrix.mul_smul, Matrix.smul_mul]

omit [Fintype k] [DecidableEq n] [DecidableEq k] in
/-- The factor-model sample second-moment matrix is symmetric. -/
theorem factorSampleCovariance_transpose
    (X : n → k → ℝ) :
    (factorSampleCovariance X)ᵀ = factorSampleCovariance X := by
  ext a b
  rw [factorSampleCovariance]
  simp only [Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul]
  rw [Matrix.sum_apply, Matrix.sum_apply]
  congr 1
  exact Finset.sum_congr rfl (fun i _ => mul_comm (X i b) (X i a))

/-- Concrete leading-eigenspace equation behind the factor-PCA certificate:
columns of `H` diagonalize the sample covariance with eigenvalue matrix `D`. -/
def factorLeadingEigenspace
    (Shat : Matrix k k ℝ) (H : Matrix k r ℝ) (D : Matrix r r ℝ) : Prop :=
  Shat * H = H * D

/-- Hansen Theorem 11.9 concentrated spectral objective. Under the normalized
factor-score parametrization, maximizing the concentrated least-squares
criterion is equivalent to maximizing this trace over matrices with orthonormal
columns. -/
noncomputable def factorConcentratedObjective
    (Shat : Matrix k k ℝ) (H : Matrix k r ℝ) : ℝ :=
  Matrix.trace (Hᵀ * Shat * H)

/-- Global maximizer predicate for the concentrated factor-PCA spectral
objective over orthonormal loading directions. -/
structure FactorConcentratedObjectiveMaximizer
    (Shat : Matrix k k ℝ) (H : Matrix k r ℝ) : Prop where
  orthonormal : Hᵀ * H = 1
  maximizes :
    ∀ G : Matrix k r ℝ, Gᵀ * G = 1 →
      factorConcentratedObjective Shat G ≤ factorConcentratedObjective Shat H

/-- Deterministic scaling assumptions for Hansen Theorem 11.9's PCA factor
solution. `H` has orthonormal selected eigenvectors, `D` is the selected
eigenvalue matrix, and `sqrtD`/`invSqrtD` are paired so that Hansen's rotated
loadings and normalized factor scores satisfy the advertised equations. -/
structure FactorPCScaling
    (H : Matrix k r ℝ) (D sqrtD invSqrtD : Matrix r r ℝ) : Prop where
  eigenvectors_orthonormal : Hᵀ * H = 1
  score_scale_normalizes : invSqrtD * D * invSqrtDᵀ = 1
  loading_scale : D * invSqrtDᵀ = sqrtD
  leastSquares_score_scale : (sqrtDᵀ * sqrtD)⁻¹ * sqrtDᵀ = invSqrtD

omit [DecidableEq k] in
/-- Orthonormal eigenspaces convert the concentrated factor-PCA spectral
objective to the trace of the selected eigenvalue matrix. -/
theorem factorConcentratedObjective_eq_trace_eigenvalues_of_normalized
    (Shat : Matrix k k ℝ) (H : Matrix k r ℝ) (D : Matrix r r ℝ)
    (hLead : factorLeadingEigenspace Shat H D) (hOrth : Hᵀ * H = 1) :
    factorConcentratedObjective Shat H = Matrix.trace D := by
  have hmiddle : Hᵀ * Shat * H = D := by
    calc
      Hᵀ * Shat * H = Hᵀ * (Shat * H) := by rw [Matrix.mul_assoc]
      _ = Hᵀ * (H * D) := by rw [hLead]
      _ = Hᵀ * H * D := by rw [Matrix.mul_assoc]
      _ = D := by rw [hOrth, Matrix.one_mul]
  simp [factorConcentratedObjective, hmiddle]

omit [DecidableEq k] in
/-- Diagonal version of the concentrated factor-PCA objective: normalized
selected eigenvectors attain the sum of their selected eigenvalues. -/
theorem factorConcentratedObjective_eq_sum_eigenvalues_of_normalized
    (Shat : Matrix k k ℝ) (H : Matrix k r ℝ) (d : r → ℝ)
    (hLead : factorLeadingEigenspace Shat H (Matrix.diagonal d))
    (hOrth : Hᵀ * H = 1) :
    factorConcentratedObjective Shat H = ∑ j, d j := by
  rw [factorConcentratedObjective_eq_trace_eigenvalues_of_normalized
    Shat H (Matrix.diagonal d) hLead hOrth, Matrix.trace_diagonal]

omit [DecidableEq k] in
/-- Assemble the concentrated objective maximizer certificate from an
orthonormality proof and a global trace-comparison proof. The missing Ky Fan
step for Hansen Theorem 11.9 is exactly the `hmax` argument for the leading
eigenspace. -/
theorem factorConcentratedObjectiveMaximizer_of_trace_maximal
    (Shat : Matrix k k ℝ) (H : Matrix k r ℝ)
    (hOrth : Hᵀ * H = 1)
    (hmax : ∀ G : Matrix k r ℝ, Gᵀ * G = 1 →
      factorConcentratedObjective Shat G ≤ factorConcentratedObjective Shat H) :
    FactorConcentratedObjectiveMaximizer Shat H where
  orthonormal := hOrth
  maximizes := hmax

omit [DecidableEq k] in
/-- If the factor eigenspace equation is written with a diagonal eigenvalue
matrix, each column of `H` is an eigenvector. -/
theorem factorLeadingEigenspace_col_diagonal
    (Shat : Matrix k k ℝ) (H : Matrix k r ℝ) (d : r → ℝ)
    (h : factorLeadingEigenspace Shat H (Matrix.diagonal d)) (j : r) :
    Shat *ᵥ (fun a => H a j) = d j • fun a => H a j := by
  ext a
  have hij := congrFun (congrFun h a) j
  simpa [Matrix.mul_apply, Matrix.mulVec, Matrix.diagonal, mul_comm] using hij

omit [DecidableEq k] in
/-- Hansen Theorem 11.9 score formula as a fixed-loading least-squares score.
For `Λ = H D^{1/2}`, the fixed-loading least-squares score
`(Λ'Λ)^{-1}Λ'X` equals `D^{-1/2}H'X` under the deterministic PCA scaling
identities. -/
theorem factorScoreEstimator_eq_leastSquaresScore
    (H : Matrix k r ℝ) (D sqrtD invSqrtD : Matrix r r ℝ)
    (X : k → ℝ) (hscale : FactorPCScaling H D sqrtD invSqrtD) :
    factorScoreEstimator H invSqrtD X =
      factorScoreLeastSquares (factorLoadingEstimator H sqrtD) X := by
  have hgram : (H * sqrtD)ᵀ * (H * sqrtD) = sqrtDᵀ * sqrtD := by
    calc
      (H * sqrtD)ᵀ * (H * sqrtD)
          = (sqrtDᵀ * Hᵀ) * (H * sqrtD) := by rw [Matrix.transpose_mul]
      _ = sqrtDᵀ * ((Hᵀ * H) * sqrtD) := by
            rw [Matrix.mul_assoc, ← Matrix.mul_assoc Hᵀ H sqrtD]
      _ = sqrtDᵀ * (1 * sqrtD) := by rw [hscale.eigenvectors_orthonormal]
      _ = sqrtDᵀ * sqrtD := by rw [Matrix.one_mul]
  unfold factorScoreEstimator factorScoreLeastSquares factorLoadingEstimator
  rw [hgram, Matrix.transpose_mul]
  calc
    invSqrtD *ᵥ (Hᵀ *ᵥ X)
        = ((sqrtDᵀ * sqrtD)⁻¹ * sqrtDᵀ) *ᵥ (Hᵀ *ᵥ X) := by
            rw [hscale.leastSquares_score_scale]
    _ = (sqrtDᵀ * sqrtD)⁻¹ *ᵥ (sqrtDᵀ *ᵥ (Hᵀ *ᵥ X)) := by
            exact (Matrix.mulVec_mulVec (Hᵀ *ᵥ X)
              ((sqrtDᵀ * sqrtD)⁻¹) sqrtDᵀ).symm
    _ = (sqrtDᵀ * sqrtD)⁻¹ *ᵥ ((sqrtDᵀ * Hᵀ) *ᵥ X) := by
            congr 1
            exact Matrix.mulVec_mulVec X sqrtDᵀ Hᵀ

omit [DecidableEq n] [DecidableEq k] in
/-- The eigenspace/scaling certificate implies Hansen's score normalization
`n⁻¹∑ Fhat_i Fhat_i' = I_r` for the principal-component factor scores. -/
theorem factorScoreNormalization_of_eigenspace_scores
    (Shat : Matrix k k ℝ) (H : Matrix k r ℝ)
    (D sqrtD invSqrtD : Matrix r r ℝ) (X : n → k → ℝ)
    (hSample : Shat = factorSampleCovariance X)
    (hLead : factorLeadingEigenspace Shat H D)
    (hscale : FactorPCScaling H D sqrtD invSqrtD) :
    factorScoreNormalization (fun i => factorScoreEstimator H invSqrtD (X i)) := by
  unfold factorScoreNormalization factorScoreEstimator
  simp_rw [Matrix.mulVec_mulVec]
  rw [factorScoreSampleCovariance_linearMap X (invSqrtD * Hᵀ), ← hSample]
  calc
    (invSqrtD * Hᵀ) * Shat * (invSqrtD * Hᵀ)ᵀ
        = invSqrtD * (Hᵀ * Shat * H) * invSqrtDᵀ := by
            rw [Matrix.transpose_mul, Matrix.transpose_transpose]
            simp only [Matrix.mul_assoc]
    _ = invSqrtD * D * invSqrtDᵀ := by
            rw [show Hᵀ * Shat * H = D by
              calc
                Hᵀ * Shat * H = Hᵀ * (Shat * H) := by rw [Matrix.mul_assoc]
                _ = Hᵀ * (H * D) := by rw [hLead]
                _ = Hᵀ * H * D := by rw [Matrix.mul_assoc]
                _ = D := by rw [hscale.eigenvectors_orthonormal, Matrix.one_mul]]
    _ = 1 := hscale.score_scale_normalizes

omit [DecidableEq n] [DecidableEq k] in
/-- The eigenspace/scaling certificate implies Hansen's loading normal equation
under the normalized principal-component scores:
`n⁻¹∑ X_i Fhat_i' = H D^{1/2}`. -/
theorem factorSampleCrossCovariance_eq_loading_of_eigenspace_scores
    (Shat : Matrix k k ℝ) (H : Matrix k r ℝ)
    (D sqrtD invSqrtD : Matrix r r ℝ) (X : n → k → ℝ)
    (hSample : Shat = factorSampleCovariance X)
    (hLead : factorLeadingEigenspace Shat H D)
    (hscale : FactorPCScaling H D sqrtD invSqrtD) :
    factorSampleCrossCovariance X
        (fun i => factorScoreEstimator H invSqrtD (X i)) =
      factorLoadingEstimator H sqrtD := by
  unfold factorScoreEstimator factorLoadingEstimator
  simp_rw [Matrix.mulVec_mulVec]
  rw [factorSampleCrossCovariance_linearMap X (invSqrtD * Hᵀ), ← hSample]
  calc
    Shat * (invSqrtD * Hᵀ)ᵀ
        = Shat * H * invSqrtDᵀ := by
            rw [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
    _ = H * D * invSqrtDᵀ := by rw [hLead]
    _ = H * sqrtD := by rw [Matrix.mul_assoc, hscale.loading_scale]

/-- Principal-component least-squares factor solution from Hansen Theorem 11.9. -/
structure FactorPCSolution
    (Shat : Matrix k k ℝ) (H : Matrix k r ℝ) (sqrtD invSqrtD : Matrix r r ℝ)
    (Λhat : Matrix k r ℝ) (X : n → k → ℝ) (Fhat : n → r → ℝ)
    (leadingEigenspace normalization : Prop) : Prop where
  sample_covariance_eq : Shat = factorSampleCovariance X
  leading_eigenspace : leadingEigenspace
  loading_eq : Λhat = factorLoadingEstimator H sqrtD
  factor_eq : ∀ i, Fhat i = factorScoreEstimator H invSqrtD (X i)
  normalization : normalization

omit [DecidableEq n] [DecidableEq k] [DecidableEq r] in
/-- Assemble a principal-component factor-solution certificate. -/
theorem factorPCSolution_of_certificate
    (Shat : Matrix k k ℝ) (H : Matrix k r ℝ) (sqrtD invSqrtD : Matrix r r ℝ)
    (Λhat : Matrix k r ℝ) (X : n → k → ℝ) (Fhat : n → r → ℝ)
    {leadingEigenspace normalization : Prop}
    (hSample : Shat = factorSampleCovariance X)
    (hLead : leadingEigenspace)
    (hLoad : Λhat = factorLoadingEstimator H sqrtD)
    (hFactor : ∀ i, Fhat i = factorScoreEstimator H invSqrtD (X i))
    (hNorm : normalization) :
    FactorPCSolution Shat H sqrtD invSqrtD Λhat X Fhat leadingEigenspace normalization where
  sample_covariance_eq := hSample
  leading_eigenspace := hLead
  loading_eq := hLoad
  factor_eq := hFactor
  normalization := hNorm

omit [DecidableEq n] [DecidableEq k] [DecidableEq r] in
/-- Sample-covariance equality component of Hansen Theorem 11.9. -/
theorem factorPCSolution_sample_covariance_eq
    (Shat : Matrix k k ℝ) (H : Matrix k r ℝ) (sqrtD invSqrtD : Matrix r r ℝ)
    (Λhat : Matrix k r ℝ) (X : n → k → ℝ) (Fhat : n → r → ℝ)
    {leadingEigenspace normalization : Prop}
    (h : FactorPCSolution Shat H sqrtD invSqrtD Λhat X Fhat leadingEigenspace normalization) :
    Shat = factorSampleCovariance X :=
  h.sample_covariance_eq

omit [DecidableEq n] [DecidableEq k] [DecidableEq r] in
/-- Loading equality component of Hansen Theorem 11.9. -/
theorem factorPCSolution_loading_eq
    (Shat : Matrix k k ℝ) (H : Matrix k r ℝ) (sqrtD invSqrtD : Matrix r r ℝ)
    (Λhat : Matrix k r ℝ) (X : n → k → ℝ) (Fhat : n → r → ℝ)
    {leadingEigenspace normalization : Prop}
    (h : FactorPCSolution Shat H sqrtD invSqrtD Λhat X Fhat leadingEigenspace normalization) :
    Λhat = factorLoadingEstimator H sqrtD :=
  h.loading_eq

omit [DecidableEq n] [DecidableEq k] [DecidableEq r] in
/-- Factor-score equality component of Hansen Theorem 11.9. -/
theorem factorPCSolution_factor_eq
    (Shat : Matrix k k ℝ) (H : Matrix k r ℝ) (sqrtD invSqrtD : Matrix r r ℝ)
    (Λhat : Matrix k r ℝ) (X : n → k → ℝ) (Fhat : n → r → ℝ)
    {leadingEigenspace normalization : Prop}
    (h : FactorPCSolution Shat H sqrtD invSqrtD Λhat X Fhat leadingEigenspace normalization) :
    ∀ i, Fhat i = factorScoreEstimator H invSqrtD (X i) :=
  h.factor_eq

omit [DecidableEq n] [DecidableEq k] [DecidableEq r] in
/-- Factor-PCA certificate with a concrete eigenspace equation
`Shat * H = H * D`. -/
theorem factorPCSolution_of_eigenspace_certificate
    (Shat : Matrix k k ℝ) (H : Matrix k r ℝ)
    (D sqrtD invSqrtD : Matrix r r ℝ)
    (Λhat : Matrix k r ℝ) (X : n → k → ℝ) (Fhat : n → r → ℝ)
    {normalization : Prop}
    (hSample : Shat = factorSampleCovariance X)
    (hLead : factorLeadingEigenspace Shat H D)
    (hLoad : Λhat = factorLoadingEstimator H sqrtD)
    (hFactor : ∀ i, Fhat i = factorScoreEstimator H invSqrtD (X i))
    (hNorm : normalization) :
    FactorPCSolution Shat H sqrtD invSqrtD Λhat X Fhat
      (factorLeadingEigenspace Shat H D) normalization :=
  factorPCSolution_of_certificate Shat H sqrtD invSqrtD Λhat X Fhat
    hSample hLead hLoad hFactor hNorm

omit [DecidableEq n] [DecidableEq k] [DecidableEq r] in
/-- Concrete eigenspace equation extracted from a factor-PCA certificate. -/
theorem factorPCSolution_leadingEigenspace_eq
    (Shat : Matrix k k ℝ) (H : Matrix k r ℝ)
    (D sqrtD invSqrtD : Matrix r r ℝ)
    (Λhat : Matrix k r ℝ) (X : n → k → ℝ) (Fhat : n → r → ℝ)
    {normalization : Prop}
    (h : FactorPCSolution Shat H sqrtD invSqrtD Λhat X Fhat
      (factorLeadingEigenspace Shat H D) normalization) :
    Shat * H = H * D :=
  h.leading_eigenspace

omit [DecidableEq n] [DecidableEq k] in
/-- Factor-PCA certificate with Hansen's concrete score normalization. -/
theorem factorPCSolution_of_normalized_eigenspace_certificate
    (Shat : Matrix k k ℝ) (H : Matrix k r ℝ)
    (D sqrtD invSqrtD : Matrix r r ℝ)
    (Λhat : Matrix k r ℝ) (X : n → k → ℝ) (Fhat : n → r → ℝ)
    (hSample : Shat = factorSampleCovariance X)
    (hLead : factorLeadingEigenspace Shat H D)
    (hLoad : Λhat = factorLoadingEstimator H sqrtD)
    (hFactor : ∀ i, Fhat i = factorScoreEstimator H invSqrtD (X i))
    (hNorm : factorScoreNormalization Fhat) :
    FactorPCSolution Shat H sqrtD invSqrtD Λhat X Fhat
      (factorLeadingEigenspace Shat H D) (factorScoreNormalization Fhat) :=
  factorPCSolution_of_eigenspace_certificate Shat H D sqrtD invSqrtD Λhat X Fhat
    hSample hLead hLoad hFactor hNorm

omit [DecidableEq n] [DecidableEq k] in
/-- Hansen Theorem 11.9 certificate assembled directly from the eigenspace and
PCA scaling equations. Unlike `factorPCSolution_of_normalized_eigenspace_certificate`,
the score normalization is proved from the eigenspace/scaling hypotheses rather
than supplied as an input. -/
theorem factorPCSolution_of_eigenspace_scaling_certificate
    (Shat : Matrix k k ℝ) (H : Matrix k r ℝ)
    (D sqrtD invSqrtD : Matrix r r ℝ) (X : n → k → ℝ)
    (hSample : Shat = factorSampleCovariance X)
    (hLead : factorLeadingEigenspace Shat H D)
    (hscale : FactorPCScaling H D sqrtD invSqrtD) :
    FactorPCSolution Shat H sqrtD invSqrtD
      (factorLoadingEstimator H sqrtD) X
      (fun i => factorScoreEstimator H invSqrtD (X i))
      (factorLeadingEigenspace Shat H D)
      (factorScoreNormalization (fun i => factorScoreEstimator H invSqrtD (X i))) :=
  factorPCSolution_of_eigenspace_certificate Shat H D sqrtD invSqrtD
    (factorLoadingEstimator H sqrtD) X
    (fun i => factorScoreEstimator H invSqrtD (X i))
    hSample hLead rfl (fun _ => rfl)
    (factorScoreNormalization_of_eigenspace_scores Shat H D sqrtD invSqrtD X
      hSample hLead hscale)

omit [DecidableEq n] [DecidableEq k] in
/-- Hansen Theorem 11.9 certificate assembled from the global concentrated
objective optimizer, eigenspace equation, and PCA scaling equations.

This is the theorem-facing endpoint for the factor-PCA route: the remaining
spectral theorem must provide `FactorConcentratedObjectiveMaximizer` for the
leading `r` eigenspace, rather than only sequential one-column optimality. -/
theorem factorPCSolution_of_concentratedObjective_optimizer
    (Shat : Matrix k k ℝ) (H : Matrix k r ℝ)
    (D sqrtD invSqrtD : Matrix r r ℝ) (X : n → k → ℝ)
    (hSample : Shat = factorSampleCovariance X)
    (hLead : factorLeadingEigenspace Shat H D)
    (hscale : FactorPCScaling H D sqrtD invSqrtD)
    (hOpt : FactorConcentratedObjectiveMaximizer Shat H) :
    FactorPCSolution Shat H sqrtD invSqrtD
      (factorLoadingEstimator H sqrtD) X
      (fun i => factorScoreEstimator H invSqrtD (X i))
      (factorLeadingEigenspace Shat H D ∧
        FactorConcentratedObjectiveMaximizer Shat H)
      (factorScoreNormalization (fun i => factorScoreEstimator H invSqrtD (X i))) :=
  factorPCSolution_of_certificate Shat H sqrtD invSqrtD
    (factorLoadingEstimator H sqrtD) X
    (fun i => factorScoreEstimator H invSqrtD (X i))
    hSample ⟨hLead, hOpt⟩ rfl (fun _ => rfl)
    (factorScoreNormalization_of_eigenspace_scores Shat H D sqrtD invSqrtD X
      hSample hLead hscale)

omit [DecidableEq n] [DecidableEq k] in
/-- A factor-PCA certificate satisfying the scaling equations uses the
fixed-loading least-squares score `(Λhat'Λhat)^{-1}Λhat'X_i`. -/
theorem factorPCSolution_factor_eq_leastSquaresScore
    (Shat : Matrix k k ℝ) (H : Matrix k r ℝ)
    (D sqrtD invSqrtD : Matrix r r ℝ)
    (Λhat : Matrix k r ℝ) (X : n → k → ℝ) (Fhat : n → r → ℝ)
    {normalization : Prop}
    (hscale : FactorPCScaling H D sqrtD invSqrtD)
    (h : FactorPCSolution Shat H sqrtD invSqrtD Λhat X Fhat
      (factorLeadingEigenspace Shat H D) normalization) :
    ∀ i, Fhat i = factorScoreLeastSquares Λhat (X i) := by
  intro i
  rw [h.factor_eq i, h.loading_eq]
  exact factorScoreEstimator_eq_leastSquaresScore H D sqrtD invSqrtD (X i) hscale

omit [DecidableEq n] [DecidableEq k] in
/-- A factor-PCA certificate satisfying the scaling equations solves the loading
normal equation under Hansen's factor normalization:
`n⁻¹∑ X_i Fhat_i' = Λhat`. -/
theorem factorPCSolution_loading_normalEquation
    (Shat : Matrix k k ℝ) (H : Matrix k r ℝ)
    (D sqrtD invSqrtD : Matrix r r ℝ)
    (Λhat : Matrix k r ℝ) (X : n → k → ℝ) (Fhat : n → r → ℝ)
    {normalization : Prop}
    (hscale : FactorPCScaling H D sqrtD invSqrtD)
    (h : FactorPCSolution Shat H sqrtD invSqrtD Λhat X Fhat
      (factorLeadingEigenspace Shat H D) normalization) :
    factorSampleCrossCovariance X Fhat = Λhat := by
  rw [h.loading_eq]
  have hF :
      Fhat = fun i => factorScoreEstimator H invSqrtD (X i) :=
    funext h.factor_eq
  rw [hF]
  exact factorSampleCrossCovariance_eq_loading_of_eigenspace_scores Shat H
    D sqrtD invSqrtD X h.sample_covariance_eq h.leading_eigenspace hscale

/-- Hansen Assumption 11.1, in a finite-dimensional theorem-facing package. -/
structure ApproximateFactorAssumption
    (Λ : Matrix k r ℝ) (Ψ : Matrix k k ℝ) where
  bounded_idiosyncratic_covariance : ∃ B : ℝ, 0 ≤ B ∧ ∀ x : k → ℝ,
    x ⬝ᵥ (Ψ *ᵥ x) ≤ B * (x ⬝ᵥ x)
  pervasive_loadings : Prop

omit [Fintype r] [DecidableEq k] [DecidableEq r] in
/-- Variance bound for the idealized factor-score error, exposed as the reusable
consequence of Assumption 11.1 used in the chapter prose. -/
theorem approximateFactor_scoreVariance_bound
    (Λ : Matrix k r ℝ) (Ψ : Matrix k k ℝ)
    (h : ApproximateFactorAssumption Λ Ψ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x : k → ℝ, x ⬝ᵥ (Ψ *ᵥ x) ≤ B * (x ⬝ᵥ x) :=
  h.bounded_idiosyncratic_covariance

end HansenEconometrics
