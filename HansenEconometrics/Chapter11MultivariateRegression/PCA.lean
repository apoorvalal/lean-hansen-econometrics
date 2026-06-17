import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Data.Matrix.Mul
import HansenEconometrics.LinearAlgebraUtils
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

/-- Index in the matrix coordinate type corresponding to an ordered eigenvalue
index `Fin (card k)` from Mathlib's Hermitian spectrum API. -/
noncomputable def orderedPCEigenIndex (j : Fin (Fintype.card k)) : k :=
  (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card k))) j

/-- Ordered principal-component eigenvalue, using Mathlib's nonincreasing
Hermitian eigenvalue order. -/
noncomputable def orderedPCEigenvalue
    {Sigma : Matrix k k ℝ} (hSigma : Sigma.IsHermitian)
    (j : Fin (Fintype.card k)) : ℝ :=
  hSigma.eigenvalues₀ j

/-- Ordered principal-component eigenvector corresponding to
`orderedPCEigenvalue`. -/
noncomputable def orderedPCEigenvector
    {Sigma : Matrix k k ℝ} (hSigma : Sigma.IsHermitian)
    (j : Fin (Fintype.card k)) : k → ℝ :=
  ⇑(hSigma.eigenvectorBasis (orderedPCEigenIndex j))

/-- Hansen's sequential PCA feasible set: unit vectors orthogonal to all earlier
ordered principal-component directions. -/
def pcaFeasibleBefore
    (H : Fin (Fintype.card k) → k → ℝ)
    (j : Fin (Fintype.card k)) (h : k → ℝ) : Prop :=
  h ⬝ᵥ h = 1 ∧ ∀ i, i < j → h ⬝ᵥ H i = 0

/-- A vector satisfying the principal-component first-order and optimality conditions. -/
structure PrincipalComponentSolution
    (Sigma : Matrix k k ℝ) (h : k → ℝ) (lambda : ℝ) : Prop where
  unit_norm : h ⬝ᵥ h = 1
  eigenvector : Sigma *ᵥ h = lambda • h
  maximizes_variance :
    ∀ g : k → ℝ, g ⬝ᵥ g = 1 →
      principalComponentVariance Sigma g ≤ principalComponentVariance Sigma h

/-- Sequential PCA solution certificate for Hansen's ordered principal
components. For `j > 0`, the optimizer is only required to dominate vectors
orthogonal to the previously selected directions. -/
structure SequentialPrincipalComponentSolution
    (Sigma : Matrix k k ℝ) (H : Fin (Fintype.card k) → k → ℝ)
    (j : Fin (Fintype.card k)) (h : k → ℝ) (lambda : ℝ) : Prop where
  feasible : pcaFeasibleBefore H j h
  eigenvector : Sigma *ᵥ h = lambda • h
  maximizes_variance :
    ∀ g : k → ℝ, pcaFeasibleBefore H j g →
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

/-- Ordered PCA eigenvectors solve the ordered covariance eigenvalue equation. -/
theorem orderedPCEigenvector_eigenvector
    {Sigma : Matrix k k ℝ} (hSigma : Sigma.IsHermitian)
    (j : Fin (Fintype.card k)) :
    Sigma *ᵥ orderedPCEigenvector hSigma j =
      orderedPCEigenvalue hSigma j • orderedPCEigenvector hSigma j := by
  simpa [orderedPCEigenvector, orderedPCEigenvalue, orderedPCEigenIndex,
    Matrix.IsHermitian.eigenvalues] using
    hSigma.mulVec_eigenvectorBasis (orderedPCEigenIndex j)

/-- Ordered PCA eigenvectors have unit Euclidean norm. -/
theorem orderedPCEigenvector_unit
    {Sigma : Matrix k k ℝ} (hSigma : Sigma.IsHermitian)
    (j : Fin (Fintype.card k)) :
    orderedPCEigenvector hSigma j ⬝ᵥ orderedPCEigenvector hSigma j = 1 := by
  have hinner := (orthonormal_iff_ite.mp hSigma.eigenvectorBasis.orthonormal)
    (orderedPCEigenIndex j) (orderedPCEigenIndex j)
  rw [EuclideanSpace.inner_eq_star_dotProduct] at hinner
  simpa [orderedPCEigenvector, dotProduct_comm] using hinner

/-- Ordered PCA eigenvectors are feasible for Hansen's sequential PCA problem. -/
theorem orderedPCEigenvector_feasibleBefore
    {Sigma : Matrix k k ℝ} (hSigma : Sigma.IsHermitian)
    (j : Fin (Fintype.card k)) :
    pcaFeasibleBefore (orderedPCEigenvector hSigma) j
      (orderedPCEigenvector hSigma j) := by
  constructor
  · exact orderedPCEigenvector_unit hSigma j
  · intro i hij
    have hne : orderedPCEigenIndex j ≠ orderedPCEigenIndex i := by
      intro hidx
      have : j = i :=
        (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card k))).injective hidx
      exact (ne_of_gt hij) this
    have hinner := (orthonormal_iff_ite.mp hSigma.eigenvectorBasis.orthonormal)
      (orderedPCEigenIndex j) (orderedPCEigenIndex i)
    rw [EuclideanSpace.inner_eq_star_dotProduct] at hinner
    simpa [orderedPCEigenvector, hne, dotProduct_comm] using hinner

/-- The variance of an ordered PCA eigenvector equals the ordered eigenvalue. -/
theorem principalComponentVariance_eq_orderedPCEigenvalue
    {Sigma : Matrix k k ℝ} (hSigma : Sigma.IsHermitian)
    (j : Fin (Fintype.card k)) :
    principalComponentVariance Sigma (orderedPCEigenvector hSigma j) =
      orderedPCEigenvalue hSigma j :=
  principalComponentVariance_eq_eigenvalue Sigma (orderedPCEigenvector hSigma j)
    (orderedPCEigenvalue hSigma j) (orderedPCEigenvector_unit hSigma j)
    (orderedPCEigenvector_eigenvector hSigma j)

/-- Ordered PCA eigenvectors solve Hansen's sequential variance maximization problem.

The feasible set requires unit norm and orthogonality to the earlier ordered
principal-component directions. Mathlib's ordered Hermitian eigenvalues and the
shared spectral expansion then give the Rayleigh-quotient bound. -/
theorem orderedPCEigenvector_maximizes_variance_feasibleBefore
    {Sigma : Matrix k k ℝ} (hSigma : Sigma.IsHermitian)
    (j : Fin (Fintype.card k)) :
    ∀ g : k → ℝ, pcaFeasibleBefore (orderedPCEigenvector hSigma) j g →
      principalComponentVariance Sigma g ≤
        principalComponentVariance Sigma (orderedPCEigenvector hSigma j) := by
  classical
  intro g hg
  let z : EuclideanSpace ℝ k := WithLp.toLp 2 g
  have hzero :
      ∀ i : Fin (Fintype.card k), i < j →
        hSigma.eigenvectorBasis.repr z
          ((Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card k))) i) = 0 := by
    intro i hij
    have horth := hg.2 i hij
    have hrepr :
        hSigma.eigenvectorBasis.repr z (orderedPCEigenIndex i) =
          g ⬝ᵥ orderedPCEigenvector hSigma i := by
      rw [OrthonormalBasis.repr_apply_apply]
      rfl
    change hSigma.eigenvectorBasis.repr z (orderedPCEigenIndex i) = 0
    exact hrepr.trans horth
  have hle :=
    quadForm_le_ordered_eigenvalue_of_unit_of_zero_before
      (M := Sigma) hSigma j z (by simpa [z] using hg.1) hzero
  rw [principalComponentVariance_eq_orderedPCEigenvalue hSigma j]
  simpa [principalComponentVariance, orderedPCEigenvalue, z] using hle

/-- Ordered PCA eigenvectors packaged as sequential solution certificates. -/
theorem orderedPCEigenvector_sequentialPrincipalComponentSolution
    {Sigma : Matrix k k ℝ} (hSigma : Sigma.IsHermitian)
    (j : Fin (Fintype.card k)) :
    SequentialPrincipalComponentSolution Sigma (orderedPCEigenvector hSigma) j
      (orderedPCEigenvector hSigma j) (orderedPCEigenvalue hSigma j) where
  feasible := orderedPCEigenvector_feasibleBefore hSigma j
  eigenvector := orderedPCEigenvector_eigenvector hSigma j
  maximizes_variance := by
    exact orderedPCEigenvector_maximizes_variance_feasibleBefore hSigma j

/-- Hansen Theorem 11.8, sequential optimizer form specialized to the covariance
matrix of a random vector. -/
theorem ordered_covMat_PCEigenvector_sequentialPrincipalComponentSolution
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : Ω → k → ℝ) (j : Fin (Fintype.card k)) :
    SequentialPrincipalComponentSolution (covMat μ X)
      (orderedPCEigenvector (covMat_isHermitian (μ := μ) X)) j
      (orderedPCEigenvector (covMat_isHermitian (μ := μ) X) j)
      (orderedPCEigenvalue (covMat_isHermitian (μ := μ) X) j) :=
  orderedPCEigenvector_sequentialPrincipalComponentSolution
    (covMat_isHermitian (μ := μ) X) j

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

/-- Ordered covariance-eigenbasis form of Hansen Theorem 11.8's variance
identity. This uses Mathlib's nonincreasing `eigenvalues₀` order. -/
theorem principalComponent_variance_eq_ordered_covMat_eigenvalue
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : Ω → k → ℝ)
    (hX : ∀ i, MemLp (fun ω => X ω i) 2 μ)
    (j : Fin (Fintype.card k)) :
    Var[principalComponent
        (orderedPCEigenvector (covMat_isHermitian (μ := μ) X) j) X; μ] =
      orderedPCEigenvalue (covMat_isHermitian (μ := μ) X) j := by
  rw [principalComponent_variance_eq_covMat_quadratic X
    (orderedPCEigenvector (covMat_isHermitian (μ := μ) X) j) hX]
  exact principalComponentVariance_eq_orderedPCEigenvalue
    (covMat_isHermitian (μ := μ) X) j

end HansenEconometrics
