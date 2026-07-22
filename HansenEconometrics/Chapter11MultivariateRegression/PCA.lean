import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Data.Matrix.Mul
import HansenEconometrics.LinearAlgebraUtils
import HansenEconometrics.ProbabilityUtils

/-!
# Chapter 11 — principal components

Principal components are exposed through the covariance quadratic form. Mathlib's
Hermitian spectral theorem supplies the eigenvector basis used by Hansen Theorem
11.8. The optimizer-first public surface characterizes every sequential variance
optimizer relative to the earlier ordered directions by membership in the
corresponding ordered eigenspace, while the canonical ordered eigenbasis remains
available as a construction.
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

/-- Vector of principal-component scores with loading rows `H`. -/
noncomputable def principalComponentScores
    {j : Type*} (H : j → k → ℝ) (X : Ω → k → ℝ) : Ω → j → ℝ :=
  fun ω a => principalComponent (H a) X ω

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

private theorem eigenvectorBasis_repr_toLp_ordered_eq_dotProduct
    {Sigma : Matrix k k ℝ} (hSigma : Sigma.IsHermitian)
    (j : Fin (Fintype.card k)) (h : k → ℝ) :
    hSigma.eigenvectorBasis.repr (WithLp.toLp 2 h) (orderedPCEigenIndex j) =
      h ⬝ᵥ orderedPCEigenvector hSigma j := by
  rw [OrthonormalBasis.repr_apply_apply]
  rfl

/-- Matrix whose rows are the ordered principal-component eigenvectors. -/
noncomputable def orderedPCEigenvectorMatrix
    {Sigma : Matrix k k ℝ} (hSigma : Sigma.IsHermitian) :
    Matrix (Fin (Fintype.card k)) k ℝ :=
  fun j => orderedPCEigenvector hSigma j

/-- Hansen's loading matrix `H = [h₁, ..., hₖ]`, whose columns are the ordered
principal-component eigenvectors. -/
noncomputable def orderedPCLoadingMatrix
    {Sigma : Matrix k k ℝ} (hSigma : Sigma.IsHermitian) :
    Matrix k (Fin (Fintype.card k)) ℝ :=
  (orderedPCEigenvectorMatrix hSigma)ᵀ

/-- Hansen's ordered principal-component vector `U = H'X`. -/
noncomputable def orderedPrincipalComponents
    {Sigma : Matrix k k ℝ} (hSigma : Sigma.IsHermitian)
    (X : Ω → k → ℝ) : Ω → Fin (Fintype.card k) → ℝ :=
  principalComponentScores (orderedPCLoadingMatrix hSigma)ᵀ X

/-- Hansen's sequential PCA feasible set: unit vectors orthogonal to all earlier
ordered principal-component directions. -/
def pcaFeasibleBefore
    (H : Fin (Fintype.card k) → k → ℝ)
    (j : Fin (Fintype.card k)) (h : k → ℝ) : Prop :=
  h ⬝ᵥ h = 1 ∧ ∀ i, i < j → h ⬝ᵥ H i = 0

/-- Optimizer-only certificate for Hansen's sequential principal-component
problem. Unlike `SequentialPrincipalComponentSolution`, this does not assume
the eigenvector equation that Theorem 11.8 is meant to derive. -/
structure SequentialPrincipalComponentOptimizer
    (Sigma : Matrix k k ℝ) (H : Fin (Fintype.card k) → k → ℝ)
    (j : Fin (Fintype.card k)) (h : k → ℝ) : Prop where
  feasible : pcaFeasibleBefore H j h
  maximizes_variance :
    ∀ g : k → ℝ, pcaFeasibleBefore H j g →
      principalComponentVariance Sigma g ≤ principalComponentVariance Sigma h

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
/-- A sequential solution with no earlier feasible directions is Hansen's
single-component solution. In particular, this is the bridge from the `j = 0`
sequential problem to the first principal-component problem. -/
theorem SequentialPrincipalComponentSolution.toPrincipalComponentSolution_of_noEarlier
    {Sigma : Matrix k k ℝ} {H : Fin (Fintype.card k) → k → ℝ}
    {j : Fin (Fintype.card k)} {h : k → ℝ} {lambda : ℝ}
    (hsol : SequentialPrincipalComponentSolution Sigma H j h lambda)
    (hfirst : ∀ i, ¬ i < j) :
    PrincipalComponentSolution Sigma h lambda where
  unit_norm := hsol.feasible.1
  eigenvector := hsol.eigenvector
  maximizes_variance := by
    intro g hg
    exact hsol.maximizes_variance g ⟨hg, fun i hi => (hfirst i hi).elim⟩

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
  simpa [orderedPCEigenvector, dotProduct_comm, Pi.star_apply, conj_trivial]
    using hinner

/-- Ordered PCA eigenvectors are orthonormal in matrix-coordinate notation. -/
@[simp]
theorem orderedPCEigenvector_dotProduct
    {Sigma : Matrix k k ℝ} (hSigma : Sigma.IsHermitian)
    (i j : Fin (Fintype.card k)) :
    orderedPCEigenvector hSigma i ⬝ᵥ orderedPCEigenvector hSigma j =
      if i = j then 1 else 0 := by
  classical
  by_cases hij : i = j
  · subst j
    simpa using orderedPCEigenvector_unit hSigma i
  · have hidx : orderedPCEigenIndex i ≠ orderedPCEigenIndex j := by
      intro h
      exact hij
        ((Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card k))).injective h)
    have hinner := (orthonormal_iff_ite.mp hSigma.eigenvectorBasis.orthonormal)
      (orderedPCEigenIndex i) (orderedPCEigenIndex j)
    rw [EuclideanSpace.inner_eq_star_dotProduct] at hinner
    simpa [orderedPCEigenvector, hidx, hij, dotProduct_comm, Pi.star_apply, conj_trivial]
      using hinner

/-- The ordered PCA loading matrix has orthonormal rows. -/
theorem orderedPCEigenvectorMatrix_mul_transpose
    {Sigma : Matrix k k ℝ} (hSigma : Sigma.IsHermitian) :
    orderedPCEigenvectorMatrix hSigma * (orderedPCEigenvectorMatrix hSigma)ᵀ = 1 := by
  classical
  ext i j
  rw [Matrix.mul_apply]
  simpa [orderedPCEigenvectorMatrix, Matrix.transpose_apply, dotProduct]
    using orderedPCEigenvector_dotProduct hSigma i j

/-- Hansen's loading matrix has orthonormal columns. -/
theorem orderedPCLoadingMatrix_transpose_mul_self
    {Sigma : Matrix k k ℝ} (hSigma : Sigma.IsHermitian) :
    (orderedPCLoadingMatrix hSigma)ᵀ * orderedPCLoadingMatrix hSigma = 1 := by
  simpa [orderedPCLoadingMatrix] using
    orderedPCEigenvectorMatrix_mul_transpose hSigma

/-- Hansen's loading matrix is orthogonal. This is the complementary identity to
`orderedPCLoadingMatrix_transpose_mul_self`, using completeness of Mathlib's
orthonormal eigenbasis. -/
theorem orderedPCLoadingMatrix_mul_transpose
    {Sigma : Matrix k k ℝ} (hSigma : Sigma.IsHermitian) :
    orderedPCLoadingMatrix hSigma * (orderedPCLoadingMatrix hSigma)ᵀ = 1 := by
  simpa [orderedPCLoadingMatrix] using
    (Matrix.mul_eq_one_comm_of_equiv
      (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card k)))).mp
        (orderedPCEigenvectorMatrix_mul_transpose hSigma)

/-- The ordered PCA eigenvalues are in Mathlib's nonincreasing order. -/
theorem orderedPCEigenvalue_antitone
    {Sigma : Matrix k k ℝ} (hSigma : Sigma.IsHermitian) :
    Antitone (orderedPCEigenvalue hSigma) :=
  hSigma.eigenvalues₀_antitone

/-- Hansen's loading matrix columns solve the diagonal covariance eigenspace
equation `Σ H = H D`. -/
theorem orderedPCLoadingMatrix_eigenspace
    {Sigma : Matrix k k ℝ} (hSigma : Sigma.IsHermitian) :
    Sigma * orderedPCLoadingMatrix hSigma =
      orderedPCLoadingMatrix hSigma *
        Matrix.diagonal (orderedPCEigenvalue hSigma) := by
  classical
  ext a j
  have heig := orderedPCEigenvector_eigenvector hSigma j
  have haj := congrFun heig a
  simpa [orderedPCLoadingMatrix, orderedPCEigenvectorMatrix, orderedPCEigenvector,
    orderedPCEigenvalue, Matrix.mul_apply, Matrix.mulVec, Matrix.diagonal, mul_comm]
    using haj

/-- Hansen's spectral-decomposition display for the ordered PCA loading matrix:
`Σ = H D H'`. -/
theorem orderedPCLoadingMatrix_mul_diagonal_mul_transpose
    {Sigma : Matrix k k ℝ} (hSigma : Sigma.IsHermitian) :
    orderedPCLoadingMatrix hSigma *
        Matrix.diagonal (orderedPCEigenvalue hSigma) *
        (orderedPCLoadingMatrix hSigma)ᵀ = Sigma := by
  calc
    orderedPCLoadingMatrix hSigma *
        Matrix.diagonal (orderedPCEigenvalue hSigma) *
        (orderedPCLoadingMatrix hSigma)ᵀ
        = (Sigma * orderedPCLoadingMatrix hSigma) *
            (orderedPCLoadingMatrix hSigma)ᵀ := by
            rw [← orderedPCLoadingMatrix_eigenspace hSigma]
    _ = Sigma * (orderedPCLoadingMatrix hSigma *
            (orderedPCLoadingMatrix hSigma)ᵀ) := by
            rw [Matrix.mul_assoc]
    _ = Sigma := by
            rw [orderedPCLoadingMatrix_mul_transpose hSigma, Matrix.mul_one]

/-- The `j`th component of Hansen's `U = H'X` is `hⱼ'X`. -/
theorem orderedPrincipalComponents_apply
    {Sigma : Matrix k k ℝ} (hSigma : Sigma.IsHermitian)
    (X : Ω → k → ℝ) (ω : Ω) (j : Fin (Fintype.card k)) :
    orderedPrincipalComponents hSigma X ω j =
      principalComponent (orderedPCEigenvector hSigma j) X ω := by
  simp [orderedPrincipalComponents, orderedPCLoadingMatrix, principalComponentScores,
    orderedPCEigenvectorMatrix]

/-- Ordered PCA eigenvectors are feasible for Hansen's sequential PCA problem. -/
theorem orderedPCEigenvector_feasibleBefore
    {Sigma : Matrix k k ℝ} (hSigma : Sigma.IsHermitian)
    (j : Fin (Fintype.card k)) :
    pcaFeasibleBefore (orderedPCEigenvector hSigma) j
      (orderedPCEigenvector hSigma j) := by
  constructor
  · exact orderedPCEigenvector_unit hSigma j
  · intro i hij
    simp [ne_of_gt hij]

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
        hSigma.eigenvectorBasis.repr (WithLp.toLp 2 g) (orderedPCEigenIndex i) =
          g ⬝ᵥ orderedPCEigenvector hSigma i :=
      eigenvectorBasis_repr_toLp_ordered_eq_dotProduct hSigma i g
    have hrepr_z :
        hSigma.eigenvectorBasis.repr z (orderedPCEigenIndex i) =
          g ⬝ᵥ orderedPCEigenvector hSigma i := by
      simpa [z] using hrepr
    change hSigma.eigenvectorBasis.repr z (orderedPCEigenIndex i) = 0
    exact hrepr_z.trans horth
  have hle :=
    quadForm_le_ordered_eigenvalue_of_unit_of_zero_before
      (M := Sigma) hSigma j z (by simpa [z] using hg.1) hzero
  rw [principalComponentVariance_eq_orderedPCEigenvalue hSigma j]
  simpa [principalComponentVariance, orderedPCEigenvalue, z] using hle

/-- Ordered PCA eigenvectors attain Hansen's sequential maximum value, the
corresponding ordered eigenvalue. -/
theorem orderedPCEigenvector_maximizes_variance_feasibleBefore_eigenvalue
    {Sigma : Matrix k k ℝ} (hSigma : Sigma.IsHermitian)
    (j : Fin (Fintype.card k)) :
    ∀ g : k → ℝ, pcaFeasibleBefore (orderedPCEigenvector hSigma) j g →
      principalComponentVariance Sigma g ≤ orderedPCEigenvalue hSigma j :=
  fun g hg =>
  (orderedPCEigenvector_maximizes_variance_feasibleBefore hSigma j g hg).trans_eq
    (principalComponentVariance_eq_orderedPCEigenvalue hSigma j)

private theorem pcaFeasibleBefore_eigenvector_of_variance_eq_orderedPCEigenvalue
    {Sigma : Matrix k k ℝ} (hSigma : Sigma.IsHermitian)
    (j : Fin (Fintype.card k)) (h : k → ℝ)
    (hfeasible : pcaFeasibleBefore (orderedPCEigenvector hSigma) j h)
    (hvariance :
      principalComponentVariance Sigma h = orderedPCEigenvalue hSigma j) :
    Sigma *ᵥ h = orderedPCEigenvalue hSigma j • h := by
  classical
  let e : Fin (Fintype.card k) ≃ k :=
    Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card k))
  let z : EuclideanSpace ℝ k := WithLp.toLp 2 h
  let c : Fin (Fintype.card k) → ℝ := fun i =>
    hSigma.eigenvectorBasis.repr z (e i)
  have hc_before : ∀ i : Fin (Fintype.card k), i < j → c i = 0 := by
    intro i hij
    have horth := hfeasible.2 i hij
    have hrepr :
        hSigma.eigenvectorBasis.repr (WithLp.toLp 2 h) (orderedPCEigenIndex i) =
          h ⬝ᵥ orderedPCEigenvector hSigma i :=
      eigenvectorBasis_repr_toLp_ordered_eq_dotProduct hSigma i h
    simpa [c, e, z, orderedPCEigenIndex] using hrepr.trans horth
  have hcoords_sum_k :
      ∑ i : k, (hSigma.eigenvectorBasis.repr z i) ^ 2 = 1 := by
    have hnorm : ‖z‖ ^ 2 = 1 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      simpa [z, dotProduct, pow_two] using hfeasible.1
    calc
      ∑ i : k, (hSigma.eigenvectorBasis.repr z i) ^ 2 =
          ∑ i : k, ‖inner ℝ (hSigma.eigenvectorBasis i) z‖ ^ 2 := by
            refine Finset.sum_congr rfl ?_
            intro i _
            rw [OrthonormalBasis.repr_apply_apply]
            simp [sq_abs]
            rfl
      _ = ‖z‖ ^ 2 :=
        OrthonormalBasis.sum_sq_norm_inner_right hSigma.eigenvectorBasis z
      _ = 1 := hnorm
  have hcoords_sum :
      ∑ i : Fin (Fintype.card k), (c i) ^ 2 = 1 := by
    calc
      ∑ i : Fin (Fintype.card k), (c i) ^ 2 =
          ∑ i : k, (hSigma.eigenvectorBasis.repr z i) ^ 2 := by
            simpa [c, e] using
              (Equiv.sum_comp e
                (fun i : k => (hSigma.eigenvectorBasis.repr z i) ^ 2))
      _ = 1 := hcoords_sum_k
  have hquad := quadForm_eq_sum_eigenvalues (M := Sigma) hSigma z
  have hquad_ordered :
      ∑ i : Fin (Fintype.card k),
          hSigma.eigenvalues (e i) * (c i) ^ 2 =
        orderedPCEigenvalue hSigma j := by
    calc
      ∑ i : Fin (Fintype.card k),
          hSigma.eigenvalues (e i) * (c i) ^ 2 =
          ∑ i : k,
            hSigma.eigenvalues i *
              (hSigma.eigenvectorBasis.repr z i) ^ 2 := by
            simpa [c, e] using
              (Equiv.sum_comp e
                (fun i : k =>
                  hSigma.eigenvalues i *
                    (hSigma.eigenvectorBasis.repr z i) ^ 2))
      _ = principalComponentVariance Sigma h := by
            simpa [principalComponentVariance, z] using hquad.symm
      _ = orderedPCEigenvalue hSigma j := hvariance
  have hgap_sum :
      ∑ i : Fin (Fintype.card k),
          (orderedPCEigenvalue hSigma j - hSigma.eigenvalues (e i)) *
            (c i) ^ 2 = 0 := by
    calc
      ∑ i : Fin (Fintype.card k),
          (orderedPCEigenvalue hSigma j - hSigma.eigenvalues (e i)) *
            (c i) ^ 2 =
          ∑ i : Fin (Fintype.card k),
              orderedPCEigenvalue hSigma j * (c i) ^ 2 -
            ∑ i : Fin (Fintype.card k),
              hSigma.eigenvalues (e i) * (c i) ^ 2 := by
                rw [← Finset.sum_sub_distrib]
                refine Finset.sum_congr rfl ?_
                intro i _
                ring
      _ = orderedPCEigenvalue hSigma j *
            (∑ i : Fin (Fintype.card k), (c i) ^ 2) -
          ∑ i : Fin (Fintype.card k),
            hSigma.eigenvalues (e i) * (c i) ^ 2 := by
              rw [Finset.mul_sum]
      _ = 0 := by rw [hcoords_sum, hquad_ordered]; ring
  have hgap_nonneg : ∀ i : Fin (Fintype.card k),
      0 ≤ (orderedPCEigenvalue hSigma j - hSigma.eigenvalues (e i)) *
        (c i) ^ 2 := by
    intro i
    by_cases hij : i < j
    · rw [hc_before i hij]
      simp
    · have heig_le :
          hSigma.eigenvalues (e i) ≤ orderedPCEigenvalue hSigma j := by
        simpa [orderedPCEigenvalue, Matrix.IsHermitian.eigenvalues, e] using
          hSigma.eigenvalues₀_antitone (le_of_not_gt hij)
      exact mul_nonneg (sub_nonneg.mpr heig_le) (sq_nonneg (c i))
  have hgap_zero_fun :
      (fun i : Fin (Fintype.card k) =>
        (orderedPCEigenvalue hSigma j - hSigma.eigenvalues (e i)) *
          (c i) ^ 2) = 0 :=
    (Fintype.sum_eq_zero_iff_of_nonneg hgap_nonneg).mp hgap_sum
  have hgap_zero : ∀ i : Fin (Fintype.card k),
      (orderedPCEigenvalue hSigma j - hSigma.eigenvalues (e i)) *
        (c i) ^ 2 = 0 := by
    intro i
    exact congrFun hgap_zero_fun i
  have hcoordinate_eigen : ∀ i : Fin (Fintype.card k),
      (hSigma.eigenvalues (e i) - orderedPCEigenvalue hSigma j) * c i = 0 := by
    intro i
    rcases mul_eq_zero.mp (hgap_zero i) with hdiff | hcoord
    · have : hSigma.eigenvalues (e i) - orderedPCEigenvalue hSigma j = 0 := by
        linarith
      simp [this]
    · have hc : c i = 0 := sq_eq_zero_iff.mp hcoord
      simp [hc]
  have hz_coord :
      h = ∑ i : k,
        hSigma.eigenvectorBasis.repr z i •
          (hSigma.eigenvectorBasis i : k → ℝ) := by
    have hsum : z = ∑ i : k,
        hSigma.eigenvectorBasis.repr z i • hSigma.eigenvectorBasis i :=
      (hSigma.eigenvectorBasis.sum_repr z).symm
    have hz := congrArg
      (fun x : EuclideanSpace ℝ k => (x : k → ℝ)) hsum
    simpa [z, WithLp.ofLp_sum] using hz
  have hSigma_h_coord :
      Sigma *ᵥ h = ∑ i : k,
        (hSigma.eigenvectorBasis.repr z i * hSigma.eigenvalues i) •
          (hSigma.eigenvectorBasis i : k → ℝ) := by
    rw [hz_coord, Matrix.mulVec_sum]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [Matrix.mulVec_smul, hSigma.mulVec_eigenvectorBasis, smul_smul]
  rw [hSigma_h_coord, hz_coord, Finset.smul_sum]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [smul_smul]
  congr 1
  have hi := hcoordinate_eigen (e.symm i)
  simp only [Equiv.apply_symm_apply, c] at hi
  nlinarith

/-- Every optimizer relative to the earlier ordered eigenvectors has the `j`th
ordered eigenvalue and lies in its full eigenspace. In particular, tied
eigenvalues do not identify the optimizer with Mathlib's chosen
`orderedPCEigenvector`. -/
theorem SequentialPrincipalComponentOptimizer.eigenvector
    {Sigma : Matrix k k ℝ} (hSigma : Sigma.IsHermitian)
    (j : Fin (Fintype.card k)) (h : k → ℝ)
    (hOpt : SequentialPrincipalComponentOptimizer Sigma
      (orderedPCEigenvector hSigma) j h) :
    Sigma *ᵥ h = orderedPCEigenvalue hSigma j • h := by
  apply pcaFeasibleBefore_eigenvector_of_variance_eq_orderedPCEigenvalue
    hSigma j h hOpt.feasible
  apply le_antisymm
  · exact orderedPCEigenvector_maximizes_variance_feasibleBefore_eigenvalue
      hSigma j h hOpt.feasible
  · rw [← principalComponentVariance_eq_orderedPCEigenvalue hSigma j]
    exact hOpt.maximizes_variance (orderedPCEigenvector hSigma j)
      (orderedPCEigenvector_feasibleBefore hSigma j)

/-- A feasible vector in the `j`th ordered eigenspace solves Hansen's
sequential variance-maximization problem. -/
theorem sequentialPrincipalComponentOptimizer_of_eigenvector
    {Sigma : Matrix k k ℝ} (hSigma : Sigma.IsHermitian)
    (j : Fin (Fintype.card k)) (h : k → ℝ)
    (hfeasible : pcaFeasibleBefore (orderedPCEigenvector hSigma) j h)
    (heigen : Sigma *ᵥ h = orderedPCEigenvalue hSigma j • h) :
    SequentialPrincipalComponentOptimizer Sigma
      (orderedPCEigenvector hSigma) j h where
  feasible := hfeasible
  maximizes_variance := by
    intro g hg
    calc
      principalComponentVariance Sigma g ≤ orderedPCEigenvalue hSigma j :=
        orderedPCEigenvector_maximizes_variance_feasibleBefore_eigenvalue
          hSigma j g hg
      _ = principalComponentVariance Sigma h :=
        (principalComponentVariance_eq_eigenvalue Sigma h
          (orderedPCEigenvalue hSigma j) hfeasible.1 heigen).symm

/-- Hansen's sequential optimizer condition is equivalent to membership in
the `j`th ordered eigenspace, subject to the same feasibility constraints. -/
theorem sequentialPrincipalComponentOptimizer_iff_eigenvector
    {Sigma : Matrix k k ℝ} (hSigma : Sigma.IsHermitian)
    (j : Fin (Fintype.card k)) (h : k → ℝ) :
    SequentialPrincipalComponentOptimizer Sigma
        (orderedPCEigenvector hSigma) j h ↔
      pcaFeasibleBefore (orderedPCEigenvector hSigma) j h ∧
        Sigma *ᵥ h = orderedPCEigenvalue hSigma j • h := by
  constructor
  · intro hOpt
    exact ⟨hOpt.feasible, hOpt.eigenvector hSigma j h⟩
  · rintro ⟨hfeasible, heigen⟩
    exact sequentialPrincipalComponentOptimizer_of_eigenvector
      hSigma j h hfeasible heigen

/-- Mathlib's canonical ordered eigenvector is an optimizer witness for the
optimizer-first characterization of Hansen Theorem 11.8. -/
theorem orderedPCEigenvector_sequentialPrincipalComponentOptimizer
    {Sigma : Matrix k k ℝ} (hSigma : Sigma.IsHermitian)
    (j : Fin (Fintype.card k)) :
    SequentialPrincipalComponentOptimizer Sigma
      (orderedPCEigenvector hSigma) j (orderedPCEigenvector hSigma j) where
  feasible := orderedPCEigenvector_feasibleBefore hSigma j
  maximizes_variance :=
    orderedPCEigenvector_maximizes_variance_feasibleBefore hSigma j

/-- Ordered PCA eigenvectors packaged as sequential solution certificates. -/
theorem orderedPCEigenvector_sequentialPrincipalComponentSolution
    {Sigma : Matrix k k ℝ} (hSigma : Sigma.IsHermitian)
    (j : Fin (Fintype.card k)) :
    SequentialPrincipalComponentSolution Sigma (orderedPCEigenvector hSigma) j
      (orderedPCEigenvector hSigma j) (orderedPCEigenvalue hSigma j) where
  feasible := orderedPCEigenvector_feasibleBefore hSigma j
  eigenvector := orderedPCEigenvector_eigenvector hSigma j
  maximizes_variance :=
    orderedPCEigenvector_maximizes_variance_feasibleBefore hSigma j

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

/-- **Hansen Theorem 11.8, optimizer-first direction.**

Any loading `h` that is feasible for the `j`th sequential problem and
maximizes the actual score variance lies in the eigenspace for the `j`th
ordered covariance eigenvalue. No equality with Mathlib's chosen ordered
eigenvector is asserted when that eigenvalue is repeated. -/
theorem ordered_covMat_eigenvector_of_maximizes_variance_feasibleBefore
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : Ω → k → ℝ)
    (hX : ∀ i, MemLp (fun ω => X ω i) 2 μ)
    (j : Fin (Fintype.card k)) (h : k → ℝ)
    (hfeasible : pcaFeasibleBefore
      (orderedPCEigenvector (covMat_isHermitian (μ := μ) X)) j h)
    (hmax : ∀ g : k → ℝ,
      pcaFeasibleBefore
          (orderedPCEigenvector (covMat_isHermitian (μ := μ) X)) j g →
        Var[principalComponent g X; μ] ≤ Var[principalComponent h X; μ]) :
    covMat μ X *ᵥ h =
      orderedPCEigenvalue (covMat_isHermitian (μ := μ) X) j • h := by
  apply SequentialPrincipalComponentOptimizer.eigenvector
    (covMat_isHermitian (μ := μ) X) j h
  refine ⟨hfeasible, ?_⟩
  intro g hg
  calc
    principalComponentVariance (covMat μ X) g =
        Var[principalComponent g X; μ] :=
      (principalComponent_variance_eq_covMat_quadratic X g hX).symm
    _ ≤ Var[principalComponent h X; μ] := hmax g hg
    _ = principalComponentVariance (covMat μ X) h :=
      principalComponent_variance_eq_covMat_quadratic X h hX

/-- **Hansen Theorem 11.8, optimizer/eigenspace characterization.**

For the sequential feasible set, maximizing `Var[h'X]` is equivalent to lying
in the eigenspace of the `j`th ordered covariance eigenvalue. The eigenspace
form is the correct statement in the presence of repeated eigenvalues. -/
theorem ordered_covMat_maximizes_variance_feasibleBefore_iff_eigenvector
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : Ω → k → ℝ)
    (hX : ∀ i, MemLp (fun ω => X ω i) 2 μ)
    (j : Fin (Fintype.card k)) (h : k → ℝ) :
    (pcaFeasibleBefore
          (orderedPCEigenvector (covMat_isHermitian (μ := μ) X)) j h ∧
        ∀ g : k → ℝ,
          pcaFeasibleBefore
              (orderedPCEigenvector (covMat_isHermitian (μ := μ) X)) j g →
            Var[principalComponent g X; μ] ≤ Var[principalComponent h X; μ]) ↔
      (pcaFeasibleBefore
          (orderedPCEigenvector (covMat_isHermitian (μ := μ) X)) j h ∧
        covMat μ X *ᵥ h =
          orderedPCEigenvalue (covMat_isHermitian (μ := μ) X) j • h) := by
  constructor
  · rintro ⟨hfeasible, hmax⟩
    exact ⟨hfeasible,
      ordered_covMat_eigenvector_of_maximizes_variance_feasibleBefore
        X hX j h hfeasible hmax⟩
  · rintro ⟨hfeasible, heigen⟩
    have hOpt := sequentialPrincipalComponentOptimizer_of_eigenvector
      (covMat_isHermitian (μ := μ) X) j h hfeasible heigen
    refine ⟨hfeasible, ?_⟩
    intro g hg
    calc
      Var[principalComponent g X; μ] =
          principalComponentVariance (covMat μ X) g :=
        principalComponent_variance_eq_covMat_quadratic X g hX
      _ ≤ principalComponentVariance (covMat μ X) h :=
        hOpt.maximizes_variance g hg
      _ = Var[principalComponent h X; μ] :=
        (principalComponent_variance_eq_covMat_quadratic X h hX).symm

omit [DecidableEq k] in
/-- Covariance matrix of a vector of fixed principal-component scores.

This is the matrix form of the scalar covariance identity used in Hansen
Theorem 11.8: fixed score loadings transform `Σ` into `HΣH'`. -/
theorem covMat_principalComponentScores_eq
    {Ω j : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : Ω → k → ℝ) (H : Matrix j k ℝ)
    (hX : ∀ i, MemLp (fun ω => X ω i) 2 μ) :
    covMat μ (principalComponentScores H X) = H * covMat μ X * Hᵀ := by
  classical
  ext a b
  have hlinb : MemLp (fun ω => dotProduct (X ω) (H b)) 2 μ := by
    convert (memLp_finset_sum' (s := Finset.univ)
      (f := fun i ω => X ω i * H b i)
      (fun i _ => (hX i).mul_const (H b i))) using 1
    ext ω
    simp [dotProduct]
  calc
    cov[fun ω => principalComponentScores H X ω a,
        fun ω => principalComponentScores H X ω b; μ]
        = cov[fun ω => ∑ i, X ω i * H a i,
            fun ω => dotProduct (X ω) (H b); μ] := by
          congr 1 <;> ext ω <;> simp [principalComponentScores, principalComponent,
            dotProduct, mul_comm]
    _ = ∑ i, cov[fun ω => X ω i * H a i,
            fun ω => dotProduct (X ω) (H b); μ] := by
          rw [ProbabilityTheory.covariance_fun_sum_left]
          · intro i
            exact (hX i).mul_const (H a i)
          · exact hlinb
    _ = ∑ i, (H a i) * (covMat μ X *ᵥ H b) i := by
          refine Finset.sum_congr rfl ?_
          intro i _
          rw [ProbabilityTheory.covariance_mul_const_left]
          have hcov := congrFun
            (covVec_dotProduct_eq_covMat_mulVec (μ := μ) X (H b) hX) i
          simpa [covVec, mul_comm] using congrArg (fun x => (H a i) * x) hcov
    _ = H a ⬝ᵥ (covMat μ X *ᵥ H b) := by
          simp [dotProduct, Matrix.mulVec, mul_comm]
    _ = (H * covMat μ X * Hᵀ) a b := by
          rw [Matrix.dotProduct_mulVec]
          simp [Matrix.mul_apply, Matrix.vecMul, Matrix.transpose_apply,
            dotProduct, mul_comm]

/-- Ordered covariance eigenvectors diagonalize the covariance matrix in
principal-component coordinates. -/
theorem orderedPCEigenvector_mul_covMat_mul_transpose_eq_diagonal
    {Sigma : Matrix k k ℝ} (hSigma : Sigma.IsHermitian) :
    orderedPCEigenvectorMatrix hSigma * Sigma * (orderedPCEigenvectorMatrix hSigma)ᵀ =
      Matrix.diagonal (orderedPCEigenvalue hSigma) := by
  classical
  ext i j
  calc
    ((orderedPCEigenvectorMatrix hSigma * Sigma * (orderedPCEigenvectorMatrix hSigma)ᵀ)
        i j)
        =
          orderedPCEigenvector hSigma i ⬝ᵥ
            (Sigma *ᵥ orderedPCEigenvector hSigma j) := by
          rw [Matrix.dotProduct_mulVec]
          simp [orderedPCEigenvectorMatrix, Matrix.mul_apply, Matrix.vecMul,
            Matrix.transpose_apply, dotProduct, mul_comm]
    _ = orderedPCEigenvector hSigma i ⬝ᵥ
          (orderedPCEigenvalue hSigma j • orderedPCEigenvector hSigma j) := by
          rw [orderedPCEigenvector_eigenvector hSigma j]
    _ = (Matrix.diagonal (orderedPCEigenvalue hSigma)) i j := by
          by_cases hij : i = j
          · subst hij
            simp [Matrix.diagonal, orderedPCEigenvector_dotProduct]
          · simp [Matrix.diagonal, hij, orderedPCEigenvector_dotProduct,
              dotProduct_smul]

/-- Hansen-column form of the ordered PCA diagonalization: `H'ΣH = D`. -/
theorem orderedPCLoadingMatrix_transpose_mul_covMat_mul_eq_diagonal
    {Sigma : Matrix k k ℝ} (hSigma : Sigma.IsHermitian) :
    (orderedPCLoadingMatrix hSigma)ᵀ * Sigma * orderedPCLoadingMatrix hSigma =
      Matrix.diagonal (orderedPCEigenvalue hSigma) := by
  simpa [orderedPCLoadingMatrix] using
    orderedPCEigenvector_mul_covMat_mul_transpose_eq_diagonal hSigma

/-- **Hansen Theorem 11.8, vector covariance face.**

For the ordered principal-component score vector `U = H'X`, the covariance
matrix is diagonal and its diagonal entries are the ordered covariance
eigenvalues. -/
theorem ordered_covMat_principalComponentScores_covMat_eq_diagonal
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : Ω → k → ℝ)
    (hX : ∀ i, MemLp (fun ω => X ω i) 2 μ) :
    covMat μ
        (principalComponentScores
          (orderedPCEigenvectorMatrix (covMat_isHermitian (μ := μ) X)) X) =
      Matrix.diagonal (orderedPCEigenvalue (covMat_isHermitian (μ := μ) X)) := by
  rw [covMat_principalComponentScores_eq (X := X)
    (H := orderedPCEigenvectorMatrix (covMat_isHermitian (μ := μ) X)) hX]
  exact orderedPCEigenvector_mul_covMat_mul_transpose_eq_diagonal
    (covMat_isHermitian (μ := μ) X)

/-- **Hansen Theorem 11.8, vector covariance face in Hansen notation.**

For `H = [h₁, ..., hₖ]` and `U = H'X`, the covariance matrix of `U` is
`D = diag(λ₁, ..., λₖ)`. -/
theorem ordered_covMat_orderedPrincipalComponents_covMat_eq_diagonal
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : Ω → k → ℝ)
    (hX : ∀ i, MemLp (fun ω => X ω i) 2 μ) :
    covMat μ
        (orderedPrincipalComponents (covMat_isHermitian (μ := μ) X) X) =
      Matrix.diagonal (orderedPCEigenvalue (covMat_isHermitian (μ := μ) X)) := by
  simpa [orderedPrincipalComponents, orderedPCLoadingMatrix] using
    ordered_covMat_principalComponentScores_covMat_eq_diagonal X hX

/-- **Hansen Theorem 11.8, probability-facing sequential optimizer form.**

The ordered covariance eigenvector maximizes the actual variance
`Var[h'X]` over Hansen's sequential feasible set, not just the deterministic
quadratic form `h'Σh`. -/
theorem ordered_covMat_principalComponent_maximizes_variance
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : Ω → k → ℝ)
    (hX : ∀ i, MemLp (fun ω => X ω i) 2 μ)
    (j : Fin (Fintype.card k)) :
    ∀ g : k → ℝ,
      pcaFeasibleBefore (orderedPCEigenvector (covMat_isHermitian (μ := μ) X)) j g →
        Var[principalComponent g X; μ] ≤
          Var[principalComponent
            (orderedPCEigenvector (covMat_isHermitian (μ := μ) X) j) X; μ] := by
  intro g hg
  rw [principalComponent_variance_eq_covMat_quadratic X g hX,
    principalComponent_variance_eq_covMat_quadratic X
      (orderedPCEigenvector (covMat_isHermitian (μ := μ) X) j) hX]
  exact orderedPCEigenvector_maximizes_variance_feasibleBefore
    (covMat_isHermitian (μ := μ) X) j g hg

/-- **Hansen Theorem 11.8, probability-facing maximum value.**

The maximum attainable variance in Hansen's `j`th sequential PCA problem is
the `j`th ordered covariance eigenvalue. -/
theorem ordered_covMat_principalComponent_variance_le_ordered_eigenvalue
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : Ω → k → ℝ)
    (hX : ∀ i, MemLp (fun ω => X ω i) 2 μ)
    (j : Fin (Fintype.card k)) :
    ∀ g : k → ℝ,
      pcaFeasibleBefore (orderedPCEigenvector (covMat_isHermitian (μ := μ) X)) j g →
        Var[principalComponent g X; μ] ≤
          orderedPCEigenvalue (covMat_isHermitian (μ := μ) X) j := by
  intro g hg
  rw [principalComponent_variance_eq_covMat_quadratic X g hX]
  exact orderedPCEigenvector_maximizes_variance_feasibleBefore_eigenvalue
    (covMat_isHermitian (μ := μ) X) j g hg

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

/-- Ordered covariance eigenvalues are nonnegative because they are variances
of the corresponding principal components. -/
theorem ordered_covMat_PCEigenvalue_nonneg
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : Ω → k → ℝ)
    (hX : ∀ i, MemLp (fun ω => X ω i) 2 μ)
    (j : Fin (Fintype.card k)) :
    0 ≤ orderedPCEigenvalue (covMat_isHermitian (μ := μ) X) j := by
  rw [← principalComponent_variance_eq_ordered_covMat_eigenvalue X hX j]
  exact ProbabilityTheory.variance_nonneg
    (principalComponent (orderedPCEigenvector (covMat_isHermitian (μ := μ) X) j) X) μ

/-- Ordered covariance eigenvalues are nonincreasing in Hansen's PCA order. -/
theorem ordered_covMat_PCEigenvalue_antitone
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : Ω → k → ℝ) :
    Antitone (orderedPCEigenvalue (covMat_isHermitian (μ := μ) X)) :=
  orderedPCEigenvalue_antitone (covMat_isHermitian (μ := μ) X)

/-- Hansen Theorem 11.8, single-component theorem-facing package. -/
structure OrderedPrincipalComponentTheorem11_8
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → k → ℝ) (j : Fin (Fintype.card k)) : Prop where
  component_eq :
    ∀ ω, orderedPrincipalComponents (covMat_isHermitian (μ := μ) X) X ω j =
      principalComponent
        (orderedPCEigenvector (covMat_isHermitian (μ := μ) X) j) X ω
  eigenvector :
    covMat μ X *ᵥ orderedPCEigenvector (covMat_isHermitian (μ := μ) X) j =
      orderedPCEigenvalue (covMat_isHermitian (μ := μ) X) j •
        orderedPCEigenvector (covMat_isHermitian (μ := μ) X) j
  sequential_solution :
    SequentialPrincipalComponentSolution (covMat μ X)
      (orderedPCEigenvector (covMat_isHermitian (μ := μ) X)) j
      (orderedPCEigenvector (covMat_isHermitian (μ := μ) X) j)
      (orderedPCEigenvalue (covMat_isHermitian (μ := μ) X) j)
  variance_maximizes :
    ∀ g : k → ℝ,
      pcaFeasibleBefore (orderedPCEigenvector (covMat_isHermitian (μ := μ) X)) j g →
        Var[principalComponent g X; μ] ≤
          Var[principalComponent
            (orderedPCEigenvector (covMat_isHermitian (μ := μ) X) j) X; μ]
  variance_eq_eigenvalue :
    Var[principalComponent
        (orderedPCEigenvector (covMat_isHermitian (μ := μ) X) j) X; μ] =
      orderedPCEigenvalue (covMat_isHermitian (μ := μ) X) j

/-- Hansen Theorem 11.8, exact single-component endpoint:
`Uⱼ = hⱼ'X`, `Σhⱼ = λⱼhⱼ`, and `hⱼ` solves the sequential variance problem. -/
theorem orderedPrincipalComponent_theorem11_8
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : Ω → k → ℝ)
    (hX : ∀ i, MemLp (fun ω => X ω i) 2 μ)
    (j : Fin (Fintype.card k)) :
    OrderedPrincipalComponentTheorem11_8 μ X j where
  component_eq := fun ω =>
    orderedPrincipalComponents_apply (covMat_isHermitian (μ := μ) X) X ω j
  eigenvector :=
    orderedPCEigenvector_eigenvector (covMat_isHermitian (μ := μ) X) j
  sequential_solution :=
    ordered_covMat_PCEigenvector_sequentialPrincipalComponentSolution μ X j
  variance_maximizes :=
    ordered_covMat_principalComponent_maximizes_variance X hX j
  variance_eq_eigenvalue :=
    principalComponent_variance_eq_ordered_covMat_eigenvalue X hX j

/-- Bundled Hansen Theorem 11.8 surface for all ordered principal components.

This packages the sequential optimizer statement, the maximum-value statement,
the scalar variance/eigenvalue identity, and the Hansen matrix identity
`U = H'X`, `Var(U) = D`. -/
structure OrderedCovMatPrincipalComponentsTheorem11_8
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → k → ℝ) : Prop where
  sequential_solution :
    ∀ j : Fin (Fintype.card k),
      SequentialPrincipalComponentSolution (covMat μ X)
        (orderedPCEigenvector (covMat_isHermitian (μ := μ) X)) j
        (orderedPCEigenvector (covMat_isHermitian (μ := μ) X) j)
        (orderedPCEigenvalue (covMat_isHermitian (μ := μ) X) j)
  quadratic_maximum_value :
    ∀ j : Fin (Fintype.card k), ∀ g : k → ℝ,
      pcaFeasibleBefore (orderedPCEigenvector (covMat_isHermitian (μ := μ) X)) j g →
        principalComponentVariance (covMat μ X) g ≤
          orderedPCEigenvalue (covMat_isHermitian (μ := μ) X) j
  variance_maximum_value :
    ∀ j : Fin (Fintype.card k), ∀ g : k → ℝ,
      pcaFeasibleBefore (orderedPCEigenvector (covMat_isHermitian (μ := μ) X)) j g →
        Var[principalComponent g X; μ] ≤
          orderedPCEigenvalue (covMat_isHermitian (μ := μ) X) j
  variance_eq_eigenvalue :
    ∀ j : Fin (Fintype.card k),
      Var[principalComponent
          (orderedPCEigenvector (covMat_isHermitian (μ := μ) X) j) X; μ] =
        orderedPCEigenvalue (covMat_isHermitian (μ := μ) X) j
  eigenvalue_nonneg :
    ∀ j : Fin (Fintype.card k),
      0 ≤ orderedPCEigenvalue (covMat_isHermitian (μ := μ) X) j
  eigenvalue_antitone :
    Antitone (orderedPCEigenvalue (covMat_isHermitian (μ := μ) X))
  component_eq :
    ∀ (ω : Ω) (j : Fin (Fintype.card k)),
      orderedPrincipalComponents (covMat_isHermitian (μ := μ) X) X ω j =
        principalComponent
          (orderedPCEigenvector (covMat_isHermitian (μ := μ) X) j) X ω
  loading_spectral_decomposition :
    orderedPCLoadingMatrix (covMat_isHermitian (μ := μ) X) *
        Matrix.diagonal (orderedPCEigenvalue (covMat_isHermitian (μ := μ) X)) *
        (orderedPCLoadingMatrix (covMat_isHermitian (μ := μ) X))ᵀ =
      covMat μ X
  scores_covMat_eq_diagonal :
    covMat μ (orderedPrincipalComponents (covMat_isHermitian (μ := μ) X) X) =
      Matrix.diagonal (orderedPCEigenvalue (covMat_isHermitian (μ := μ) X))

/-- **Hansen Theorem 11.8**, bundled ordered-covariance endpoint for the full
principal-component vector `U = H'X`. -/
theorem ordered_covMat_principalComponents_theorem11_8
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : Ω → k → ℝ)
    (hX : ∀ i, MemLp (fun ω => X ω i) 2 μ) :
    OrderedCovMatPrincipalComponentsTheorem11_8 μ X where
  sequential_solution := fun j =>
    ordered_covMat_PCEigenvector_sequentialPrincipalComponentSolution μ X j
  quadratic_maximum_value := fun j g hg =>
    orderedPCEigenvector_maximizes_variance_feasibleBefore_eigenvalue
      (covMat_isHermitian (μ := μ) X) j g hg
  variance_maximum_value := fun j g hg =>
    ordered_covMat_principalComponent_variance_le_ordered_eigenvalue X hX j g hg
  variance_eq_eigenvalue := fun j =>
    principalComponent_variance_eq_ordered_covMat_eigenvalue X hX j
  eigenvalue_nonneg := fun j =>
    ordered_covMat_PCEigenvalue_nonneg X hX j
  eigenvalue_antitone :=
    ordered_covMat_PCEigenvalue_antitone μ X
  component_eq := fun ω j =>
    orderedPrincipalComponents_apply (covMat_isHermitian (μ := μ) X) X ω j
  loading_spectral_decomposition :=
    orderedPCLoadingMatrix_mul_diagonal_mul_transpose
      (covMat_isHermitian (μ := μ) X)
  scores_covMat_eq_diagonal :=
    ordered_covMat_orderedPrincipalComponents_covMat_eq_diagonal X hX

end HansenEconometrics
