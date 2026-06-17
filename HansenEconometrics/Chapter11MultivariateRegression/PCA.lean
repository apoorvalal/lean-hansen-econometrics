import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Data.Matrix.Mul
import HansenEconometrics.ProbabilityUtils

/-!
# Chapter 11 — principal components

Principal components are exposed through the covariance quadratic form. Mathlib's
Hermitian spectral theorem supplies the eigenvector basis used by Hansen Theorem
11.8; this file exposes the chapter-facing variance wrappers.
-/

open MeasureTheory ProbabilityTheory
open scoped Matrix MeasureTheory ProbabilityTheory

namespace HansenEconometrics

open Matrix

variable {Ω k : Type*}
variable [Fintype k] [DecidableEq k]

/-- Linear principal-component score `h'X`. -/
noncomputable def principalComponent
    (h : k → ℝ) (X : Ω → k → ℝ) : Ω → ℝ :=
  fun ω => h ⬝ᵥ X ω

/-- Covariance quadratic form maximized by a principal component. -/
noncomputable def principalComponentVariance
    (Sigma : Matrix k k ℝ) (h : k → ℝ) : ℝ :=
  h ⬝ᵥ (Sigma *ᵥ h)

/-- A vector satisfying the principal-component first-order and optimality conditions. -/
structure PrincipalComponentSolution
    (Sigma : Matrix k k ℝ) (h : k → ℝ) (lambda : ℝ) : Prop where
  unit_norm : h ⬝ᵥ h = 1
  eigenvector : Sigma *ᵥ h = lambda • h
  maximizes_variance :
    ∀ g : k → ℝ, g ⬝ᵥ g = 1 →
      principalComponentVariance Sigma g ≤ principalComponentVariance Sigma h

omit [DecidableEq k] in
/-- Eigenvector component of a supplied `PrincipalComponentSolution`. -/
theorem principalComponent_eigenvector_of_solution
    (Sigma : Matrix k k ℝ) (h : k → ℝ) (lambda : ℝ)
    (hh : PrincipalComponentSolution Sigma h lambda) :
    Sigma *ᵥ h = lambda • h :=
  hh.eigenvector

omit [DecidableEq k] in
/-- A principal component's variance is the eigenvalue attached to a unit eigenvector. -/
theorem principalComponentVariance_eq_eigenvalue
    (Sigma : Matrix k k ℝ) (h : k → ℝ) (lambda : ℝ)
    (hunit : h ⬝ᵥ h = 1) (heig : Sigma *ᵥ h = lambda • h) :
    principalComponentVariance Sigma h = lambda := by
  rw [principalComponentVariance, heig]
  simp [dotProduct_smul, hunit]

omit [DecidableEq k] in
/-- **Hansen Theorem 11.8, variance identity.**

The variance of the principal-component score `h'X` is the covariance quadratic
form `h'Σh`. This is the probability-facing wrapper around the reusable
finite-dimensional covariance lemma in `ProbabilityUtils`. -/
theorem principalComponent_variance_eq_covMat_quadratic
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : Ω → k → ℝ) (h : k → ℝ)
    (hX : ∀ i, MemLp (fun ω => X ω i) 2 μ) :
    Var[principalComponent h X; μ] = principalComponentVariance (covMat μ X) h := by
  simpa [principalComponent, principalComponentVariance, dotProduct_comm] using
    variance_dotProduct_eq_dotProduct_covMat_mulVec (μ := μ) X h hX

omit [DecidableEq k] in
/-- **Hansen Theorem 11.8, eigenvalue variance face.**

If `h` is a unit eigenvector of the covariance matrix with eigenvalue `λ`, then
the principal-component score `h'X` has variance `λ`. -/
theorem principalComponent_variance_eq_eigenvalue
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : Ω → k → ℝ) (h : k → ℝ) (lambda : ℝ)
    (hX : ∀ i, MemLp (fun ω => X ω i) 2 μ)
    (hunit : h ⬝ᵥ h = 1) (heig : covMat μ X *ᵥ h = lambda • h) :
    Var[principalComponent h X; μ] = lambda := by
  rw [principalComponent_variance_eq_covMat_quadratic X h hX]
  exact principalComponentVariance_eq_eigenvalue (covMat μ X) h lambda hunit heig

/-- **Hansen Theorem 11.8, spectral-theorem form.**

For a Hermitian covariance matrix, Mathlib's eigenvector basis gives the
principal-component directions, and each component variance is the corresponding
eigenvalue. -/
theorem principalComponent_variance_eq_hermitian_eigenvalue
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : Ω → k → ℝ)
    (hX : ∀ i, MemLp (fun ω => X ω i) 2 μ)
    (hSigma : (covMat μ X).IsHermitian) (j : k) :
    Var[principalComponent (⇑(hSigma.eigenvectorBasis j)) X; μ] =
      hSigma.eigenvalues j := by
  have hunit :
      (⇑(hSigma.eigenvectorBasis j) : k → ℝ) ⬝ᵥ
        (⇑(hSigma.eigenvectorBasis j) : k → ℝ) = 1 := by
    have hinner := (orthonormal_iff_ite.mp hSigma.eigenvectorBasis.orthonormal) j j
    rw [EuclideanSpace.inner_eq_star_dotProduct] at hinner
    simpa [dotProduct_comm] using hinner
  exact principalComponent_variance_eq_eigenvalue X (⇑(hSigma.eigenvectorBasis j))
    (hSigma.eigenvalues j) hX hunit (hSigma.mulVec_eigenvectorBasis j)

/-- **Hansen Theorem 11.8, covariance-eigenbasis form.**

The covariance matrix is Hermitian by `covMat_isHermitian`, so its Mathlib
eigenbasis gives principal-component directions whose score variances are the
corresponding covariance eigenvalues. -/
theorem principalComponent_variance_eq_covMat_eigenvalue
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : Ω → k → ℝ)
    (hX : ∀ i, MemLp (fun ω => X ω i) 2 μ) (j : k) :
    Var[principalComponent
        (⇑((covMat_isHermitian (μ := μ) X).eigenvectorBasis j)) X; μ] =
      (covMat_isHermitian (μ := μ) X).eigenvalues j :=
  principalComponent_variance_eq_hermitian_eigenvalue X hX
    (covMat_isHermitian (μ := μ) X) j

end HansenEconometrics
