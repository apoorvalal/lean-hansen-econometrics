import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Data.Matrix.Mul

/-!
# Chapter 11 — factor models

This module records the principal-component factor-estimation surface and the
large-dimension condition package used in Hansen's approximate-factor discussion.
The factor-model MLE/PCA certificate here is a support interface, not the full
proof of Hansen Theorem 11.9 from the least-squares objective.
-/

open scoped Matrix

namespace HansenEconometrics

open Matrix

variable {k r : Type*}
variable [Fintype k] [Fintype r] [DecidableEq k] [DecidableEq r]

/-- Principal-component loading estimator `H D^{1/2}`. The square-root diagonal is supplied
explicitly so downstream files can choose the spectral normalization they need. -/
noncomputable def factorLoadingEstimator
    (H : Matrix k r ℝ) (sqrtD : Matrix r r ℝ) : Matrix k r ℝ :=
  H * sqrtD

/-- Principal-component factor estimator `D^{-1/2} H' X`. -/
noncomputable def factorScoreEstimator
    (H : Matrix k r ℝ) (invSqrtD : Matrix r r ℝ) (X : k → ℝ) : r → ℝ :=
  invSqrtD *ᵥ (Hᵀ *ᵥ X)

/-- Principal-component least-squares factor solution from Hansen Theorem 11.9. -/
structure FactorPCSolution
    (Shat : Matrix k k ℝ) (H : Matrix k r ℝ) (sqrtD invSqrtD : Matrix r r ℝ)
    (Λhat : Matrix k r ℝ) (Fhat : k → r → ℝ)
    (leadingEigenspace normalization : Prop) : Prop where
  leading_eigenspace : leadingEigenspace
  loading_eq : Λhat = factorLoadingEstimator H sqrtD
  factor_eq : ∀ i, Fhat i = factorScoreEstimator H invSqrtD (fun a => if a = i then 1 else 0)
  normalization : normalization

omit [DecidableEq r] in
/-- Assemble a principal-component factor-solution certificate. -/
theorem factorPCSolution_of_certificate
    (Shat : Matrix k k ℝ) (H : Matrix k r ℝ) (sqrtD invSqrtD : Matrix r r ℝ)
    (Λhat : Matrix k r ℝ) (Fhat : k → r → ℝ)
    {leadingEigenspace normalization : Prop}
    (hLead : leadingEigenspace)
    (hLoad : Λhat = factorLoadingEstimator H sqrtD)
    (hFactor : ∀ i, Fhat i = factorScoreEstimator H invSqrtD (fun a => if a = i then 1 else 0))
    (hNorm : normalization) :
    FactorPCSolution Shat H sqrtD invSqrtD Λhat Fhat leadingEigenspace normalization where
  leading_eigenspace := hLead
  loading_eq := hLoad
  factor_eq := hFactor
  normalization := hNorm

omit [DecidableEq r] in
/-- Loading equality component of Hansen Theorem 11.9. -/
theorem factorPCSolution_loading_eq
    (Shat : Matrix k k ℝ) (H : Matrix k r ℝ) (sqrtD invSqrtD : Matrix r r ℝ)
    (Λhat : Matrix k r ℝ) (Fhat : k → r → ℝ)
    {leadingEigenspace normalization : Prop}
    (h : FactorPCSolution Shat H sqrtD invSqrtD Λhat Fhat leadingEigenspace normalization) :
    Λhat = factorLoadingEstimator H sqrtD :=
  h.loading_eq

omit [DecidableEq r] in
/-- Factor-score equality component of Hansen Theorem 11.9. -/
theorem factorPCSolution_factor_eq
    (Shat : Matrix k k ℝ) (H : Matrix k r ℝ) (sqrtD invSqrtD : Matrix r r ℝ)
    (Λhat : Matrix k r ℝ) (Fhat : k → r → ℝ)
    {leadingEigenspace normalization : Prop}
    (h : FactorPCSolution Shat H sqrtD invSqrtD Λhat Fhat leadingEigenspace normalization) :
    ∀ i, Fhat i = factorScoreEstimator H invSqrtD (fun a => if a = i then 1 else 0) :=
  h.factor_eq

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
