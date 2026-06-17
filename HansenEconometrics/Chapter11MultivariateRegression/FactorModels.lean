import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul

/-!
# Chapter 11 — factor models

This module records the principal-component factor-estimation surface and the
large-dimension condition package used in Hansen's approximate-factor discussion.
It ties the factor-PCA certificate to the sample second-moment matrix and a
concrete eigenspace equation; the full least-squares/eigenspace optimizer behind
Hansen Theorem 11.9 remains separate.
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

/-- Sample second-moment matrix `n⁻¹∑ X_i X_i'` used in Hansen Theorem 11.9. -/
noncomputable def factorSampleCovariance
    (X : n → k → ℝ) : Matrix k k ℝ :=
  (Fintype.card n : ℝ)⁻¹ • ∑ i : n, Matrix.vecMulVec (X i) (X i)

/-- Sample second-moment matrix of estimated factors. -/
noncomputable def factorScoreSampleCovariance
    (Fhat : n → r → ℝ) : Matrix r r ℝ :=
  (Fintype.card n : ℝ)⁻¹ • ∑ i : n, Matrix.vecMulVec (Fhat i) (Fhat i)

/-- Hansen Theorem 11.9 normalization `n⁻¹∑ Fhat_i Fhat_i' = I_r`. -/
def factorScoreNormalization (Fhat : n → r → ℝ) : Prop :=
  factorScoreSampleCovariance Fhat = 1

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
