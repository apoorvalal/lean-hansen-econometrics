import Mathlib.Data.Real.StarOrdered
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Order.Fin.Tuple
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Topology.Instances.Matrix

/-!
# Shared finite-dimensional linear algebra

This module provides the repository's reusable real-matrix support layer. Its
public surface includes finite-matrix Borel measurability, total inverse and
Gram identities, Hermitian idempotent projection formulas, rectangular-Gram
spectrum transfer, Hermitian eigenvalue expansions, compression/interlacing
bounds, and Ky Fan-style leading-eigenvalue inequalities.

Chapter files should reuse these declarations before introducing local matrix
algebra. Proof scaffolding for list sorting, determinant expansions, and column
orthogonality remains private; the public theorem families are intended for
cross-chapter use.
-/

open scoped Matrix
open scoped MatrixOrder

namespace HansenEconometrics

open Matrix

/-- Product measurable space used for finite real matrix coordinates.

This is intentionally not a global instance; downstream files can install it
locally when they need matrix-valued Borel measurability. -/
@[reducible]
noncomputable def matrixBorelMeasurableSpace (m n : Type*) [Fintype m] [Fintype n] :
    MeasurableSpace (Matrix m n ℝ) :=
  borel _

/-- Borel-space certificate for `matrixBorelMeasurableSpace`. -/
lemma matrixBorelSpace (m n : Type*) [Fintype m] [Fintype n] :
    @BorelSpace (Matrix m n ℝ) inferInstance (matrixBorelMeasurableSpace m n) := by
  letI : MeasurableSpace (Matrix m n ℝ) := matrixBorelMeasurableSpace m n
  exact ⟨rfl⟩

private theorem measurable_continuous_matrix_comp_of_entries
    {α κ : Type*} [MeasurableSpace α] [Finite κ]
    {A : α → Matrix κ κ ℝ} (hA : ∀ i j, Measurable fun x => A x i j)
    {f : Matrix κ κ ℝ → ℝ} (hf : Continuous f) :
    Measurable fun x => f (A x) := by
  letI : MeasurableSpace (Matrix κ κ ℝ) :=
    (inferInstance : MeasurableSpace (κ → κ → ℝ))
  letI : BorelSpace (Matrix κ κ ℝ) := by
    change BorelSpace (κ → κ → ℝ)
    infer_instance
  have hA' : Measurable A :=
    measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j => hA i j
  exact hf.measurable.comp hA'

/-- A finite determinant is measurable when all matrix entries are measurable. -/
theorem det_measurable_of_entries
    {α κ : Type*} [MeasurableSpace α] [Fintype κ] [DecidableEq κ]
    {A : α → Matrix κ κ ℝ} (hA : ∀ i j, Measurable fun x => A x i j) :
    Measurable fun x => (A x).det := by
  exact measurable_continuous_matrix_comp_of_entries
    hA continuous_id.matrix_det

/-- Every adjugate entry is measurable when all source entries are measurable. -/
theorem adjugate_apply_measurable_of_entries
    {α κ : Type*} [MeasurableSpace α] [Fintype κ] [DecidableEq κ]
    {A : α → Matrix κ κ ℝ} (hA : ∀ i j, Measurable fun x => A x i j) (i j : κ) :
    Measurable fun x => (A x).adjugate i j := by
  exact measurable_continuous_matrix_comp_of_entries
    hA (continuous_id.matrix_adjugate.matrix_elem i j)

/-- Every entry of the totalized matrix inverse is measurable when all source
entries are measurable. -/
theorem matrix_inv_apply_measurable_of_entries
    {α κ : Type*} [MeasurableSpace α] [Fintype κ] [DecidableEq κ]
    {A : α → Matrix κ κ ℝ} (hA : ∀ i j, Measurable fun x => A x i j) (i j : κ) :
    Measurable fun x => (A x)⁻¹ i j := by
  classical
  have hdet : Measurable fun x => (A x).det := det_measurable_of_entries hA
  have hadj : Measurable fun x => (A x).adjugate i j :=
    adjugate_apply_measurable_of_entries hA i j
  have hrinv : Measurable fun x => Ring.inverse ((A x).det) := by
    rw [show (fun x => Ring.inverse ((A x).det)) = fun x => ((A x).det)⁻¹ by
      funext x
      exact Ring.inverse_eq_inv _]
    exact measurable_inv.comp hdet
  rw [show (fun x => (A x)⁻¹ i j) =
      (fun x => Ring.inverse ((A x).det) * (A x).adjugate i j) by
        funext x
        rw [Matrix.inv_def]
        rfl]
  exact hrinv.mul hadj

/-- A totalized finite matrix inverse is Borel measurable when all source
entries are measurable. -/
theorem matrix_inv_measurable_of_entries
    {α κ : Type*} [MeasurableSpace α] [Fintype κ] [DecidableEq κ]
    {A : α → Matrix κ κ ℝ} (hA : ∀ i j, Measurable fun x => A x i j) :
    @Measurable α (Matrix κ κ ℝ) inferInstance (borel (Matrix κ κ ℝ))
      (fun x => (A x)⁻¹) := by
  letI mMatrix : MeasurableSpace (Matrix κ κ ℝ) :=
    (inferInstance : MeasurableSpace (κ → κ → ℝ))
  letI : BorelSpace (Matrix κ κ ℝ) := by
    change BorelSpace (κ → κ → ℝ)
    infer_instance
  have hInv : Measurable fun x => (A x)⁻¹ :=
    measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j =>
      matrix_inv_apply_measurable_of_entries hA i j
  have hm : mMatrix = borel (Matrix κ κ ℝ) := BorelSpace.measurable_eq
  rw [hm] at hInv
  exact hInv

/-- Every entry of a finite Gram matrix is measurable when all source entries
are measurable. -/
theorem gram_apply_measurable_of_entries
    {α n κ : Type*} [MeasurableSpace α] [Fintype n]
    {X : α → Matrix n κ ℝ} (hX : ∀ i j, Measurable fun x => X x i j) (a b : κ) :
    Measurable fun x => ((X x)ᵀ * X x) a b := by
  classical
  simp only [Matrix.mul_apply, Matrix.transpose_apply]
  exact Finset.measurable_sum Finset.univ (fun r _ => (hX r a).mul (hX r b))

/-- **Scalar-scaled matrix inverse (unconditional).** For `c : ℝ` and any square
matrix `M` over `ℝ`, the total inverse `Matrix.nonsingInv` satisfies
`(c • M)⁻¹ = c⁻¹ • M⁻¹`. Mathlib's `Matrix.inv_smul` requires `Invertible c`
and `IsUnit M.det`; we dispatch the singular cases by hand so the identity
holds for all scalar/matrix pairs. -/
theorem nonsingInv_smul {k : Type*} [Fintype k] [DecidableEq k]
    (c : ℝ) (M : Matrix k k ℝ) :
    (c • M)⁻¹ = c⁻¹ • M⁻¹ := by
  by_cases hc : c = 0
  · subst hc
    simp [Matrix.inv_zero]
  by_cases hM : IsUnit M.det
  · have : Invertible c := invertibleOfNonzero hc
    rw [Matrix.inv_smul _ _ hM, invOf_eq_inv]
  · have hM' : M.det = 0 := by
      rwa [isUnit_iff_ne_zero, ne_eq, not_not] at hM
    have hcMdet : ¬ IsUnit (c • M).det := by
      rw [Matrix.det_smul, hM', mul_zero]
      simp
    rw [Matrix.nonsing_inv_apply_not_isUnit _ hcMdet,
        Matrix.nonsing_inv_apply_not_isUnit _ hM, smul_zero]

/-- Total inverse of a congruent Gram matrix under explicit two-sided inverse
column transforms.

This shared helper is used by later asymptotic covariance transforms and by
the Chapter 11 inverse-Wishart coordinate-alignment layer. -/
theorem nonsingInv_conjugate_of_inverse {k q : Type*}
    [Fintype k] [Fintype q] [DecidableEq k] [DecidableEq q]
    (G : Matrix k k ℝ) (T : Matrix k q ℝ) (S : Matrix q k ℝ)
    (hST : S * T = 1) (hTS : T * S = 1) (hG : IsUnit G.det) :
    (Tᵀ * G * T)⁻¹ = S * G⁻¹ * Sᵀ := by
  have htr : Sᵀ * Tᵀ = 1 := by
    rw [← Matrix.transpose_mul, hTS, Matrix.transpose_one]
  refine Matrix.inv_eq_left_inv ?_
  calc
    (S * G⁻¹ * Sᵀ) * (Tᵀ * G * T)
        = S * (G⁻¹ * ((Sᵀ * Tᵀ) * (G * T))) := by
          rw [Matrix.mul_assoc Tᵀ G T]
          simp [Matrix.mul_assoc]
    _ = S * (G⁻¹ * (G * T)) := by rw [htr, Matrix.one_mul]
    _ = S * ((G⁻¹ * G) * T) := by rw [Matrix.mul_assoc]
    _ = S * ((1 : Matrix k k ℝ) * T) := by rw [Matrix.nonsing_inv_mul G hG]
    _ = S * T := by simp
    _ = 1 := hST

/-- Hansen Theorem 3.3.1 helper: the Gram matrix `Xᵀ * X` is symmetric. Relocated here from
`Chapter3Projections.lean` so that earlier files (e.g., `Chapter3LeastSquaresAlgebra.lean`)
can use it without creating a circular import. -/
@[simp]
theorem gram_transpose {n k : Type*} [Fintype n]
    (X : Matrix n k ℝ) :
    (Xᵀ * X)ᵀ = Xᵀ * X := by
  rw [Matrix.transpose_mul, Matrix.transpose_transpose]

/-- Hansen Theorem 3.3.1 helper: the inverse of the symmetric Gram matrix is symmetric.
Relocated here from `Chapter3Projections.lean` so that downstream chapters can cite it
directly from the shared linear-algebra helper layer. -/
@[simp]
theorem inv_gram_transpose {n k : Type*} [Fintype n] [Fintype k] [DecidableEq k]
    (X : Matrix n k ℝ) [Invertible (Xᵀ * X)] :
    (⅟ (Xᵀ * X))ᵀ = ⅟ (Xᵀ * X) := by
  simpa using
    (Matrix.transpose_invOf (A := Xᵀ * X))

/-- Left-multiplication by a row vector is right-multiplication by the transpose. -/
@[simp]
lemma vecMul_eq_mulVec_transpose {m n : Type*} [Fintype m]
    (M : Matrix m n ℝ) (x : m → ℝ) :
    Matrix.vecMul x M = Mᵀ *ᵥ x := by
  simpa using (Matrix.vecMul_transpose Mᵀ x)

/-- For a symmetric matrix, left-multiplication as a row vector agrees with right-multiplication
as a column vector. -/
lemma vecMul_eq_mulVec_of_transpose_eq_self {n : Type*} [Fintype n]
    (M : Matrix n n ℝ) (hM : Mᵀ = M) (x : n → ℝ) :
    Matrix.vecMul x M = M *ᵥ x := by
  conv_rhs => rw [← hM]
  exact vecMul_eq_mulVec_transpose M x

/-- For a symmetric idempotent matrix, the associated quadratic form equals the squared norm of
the projected vector. This is the linear-algebra identity behind projection-based chi-square
arguments. -/
lemma quadratic_form_eq_dotProduct_of_symm_idempotent {n : Type*} [Fintype n]
    (M : Matrix n n ℝ) (hMt : Mᵀ = M) (hMid : M * M = M) (x : n → ℝ) :
    x ⬝ᵥ M *ᵥ x = dotProduct (M *ᵥ x) (M *ᵥ x) := by
  have hvec : Matrix.vecMul x M = M *ᵥ x :=
    vecMul_eq_mulVec_of_transpose_eq_self M hMt x
  have h := Matrix.dotProduct_mulVec x M (M *ᵥ x)
  rw [hvec, Matrix.mulVec_mulVec, hMid] at h
  exact h

/-- A real symmetric idempotent matrix has nonnegative diagonal entries. -/
lemma diag_nonneg_of_symm_idempotent {n : Type*} [Fintype n]
    (M : Matrix n n ℝ) (hMt : Mᵀ = M) (hMid : M * M = M) (i : n) :
    0 ≤ M i i := by
  classical
  let e : n → ℝ := Pi.single i 1
  have hquad := quadratic_form_eq_dotProduct_of_symm_idempotent M hMt hMid e
  have hdiag : e ⬝ᵥ M *ᵥ e = M i i := by
    simp [e]
  have hnonneg : 0 ≤ dotProduct (M *ᵥ e) (M *ᵥ e) := by
    simpa using dotProduct_star_self_nonneg (M *ᵥ e)
  rw [← hquad, hdiag] at hnonneg
  exact hnonneg

/-- The Gram matrix `Xᵀ * X` generates a nonneg quadratic form. This is the
finite-sample counterpart of positive semidefiniteness: for every vector `v`,
`v ⬝ᵥ ((Xᵀ * X) *ᵥ v) ≥ 0`. -/
lemma gram_quadratic_nonneg {n k : Type*} [Fintype n] [Fintype k]
    (X : Matrix n k ℝ) (v : k → ℝ) :
    0 ≤ v ⬝ᵥ ((Xᵀ * X) *ᵥ v) := by
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
      vecMul_eq_mulVec_transpose, Matrix.transpose_transpose]
  exact dotProduct_star_self_nonneg (X *ᵥ v)

/-- Strict positive-definiteness of the Gram matrix under invertibility: for any
`v ≠ 0`, `0 < v ⬝ᵥ ((Xᵀ * X) *ᵥ v)`. Strengthens `gram_quadratic_nonneg` whenever
`Xᵀ * X` is invertible. Used to discharge the strict-positivity hypothesis of Chapter 2's
`linearProjectionBeta_eq_of_MSE_eq` when specialized to sample moments. -/
lemma gram_quadratic_pos {n k : Type*} [Fintype n] [Fintype k] [DecidableEq k]
    (X : Matrix n k ℝ) [Invertible (Xᵀ * X)] {v : k → ℝ} (hv : v ≠ 0) :
    0 < v ⬝ᵥ ((Xᵀ * X) *ᵥ v) := by
  rcases (gram_quadratic_nonneg X v).lt_or_eq with h | h
  · exact h
  · exfalso
    have hquad : v ⬝ᵥ ((Xᵀ * X) *ᵥ v) = (X *ᵥ v) ⬝ᵥ (X *ᵥ v) := by
      rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
          vecMul_eq_mulVec_transpose, Matrix.transpose_transpose]
    rw [hquad] at h
    have hXv : X *ᵥ v = 0 := dotProduct_self_eq_zero.mp h.symm
    have hXtXv : (Xᵀ * X) *ᵥ v = 0 := by
      rw [← Matrix.mulVec_mulVec, hXv, Matrix.mulVec_zero]
    have hv0 : v = 0 := by
      have h1 : ⅟ (Xᵀ * X) *ᵥ ((Xᵀ * X) *ᵥ v) = 0 := by
        rw [hXtXv, Matrix.mulVec_zero]
      rwa [Matrix.mulVec_mulVec, invOf_mul_self, Matrix.one_mulVec] at h1
    exact hv hv0

/-- The row-space Gram matrix of a rectangular real matrix is Hermitian. -/
theorem mul_transpose_isHermitian {k m : Type*} [Fintype m]
    (D : Matrix k m ℝ) :
    (D * Dᵀ).IsHermitian := by
  simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
    Matrix.isHermitian_mul_conjTranspose_self D

/-- The column-space Gram matrix of a rectangular real matrix is Hermitian. -/
theorem transpose_mul_isHermitian {k m : Type*} [Fintype k]
    (D : Matrix k m ℝ) :
    (Dᵀ * D).IsHermitian := by
  simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
    Matrix.isHermitian_conjTranspose_mul_self D

/-- Rectangular Sylvester identity for the two real Gram matrices of `D`.

The powers of `X` account for the zero eigenvalues added when passing between
row space and column space. -/
private theorem mul_transpose_charpoly_mul_X {k m : Type*}
    [Fintype k] [Fintype m] [DecidableEq k] [DecidableEq m]
    (D : Matrix k m ℝ) :
    Polynomial.X ^ Fintype.card m * (D * Dᵀ).charpoly =
      Polynomial.X ^ Fintype.card k * (Dᵀ * D).charpoly := by
  simpa using Matrix.charpoly_mul_comm' D Dᵀ

/-- Root-multiset form of `mul_transpose_charpoly_mul_X`.

It states that the spectra of `D * Dᵀ` and `Dᵀ * D` agree after padding
each side with the zero roots contributed by the other index type. -/
private theorem mul_transpose_roots_with_zero_padding {k m : Type*}
    [Fintype k] [Fintype m] [DecidableEq k] [DecidableEq m]
    (D : Matrix k m ℝ) :
    Fintype.card m • ({0} : Multiset ℝ) + (D * Dᵀ).charpoly.roots =
      Fintype.card k • ({0} : Multiset ℝ) + (Dᵀ * D).charpoly.roots := by
  classical
  have hroot := congrArg Polynomial.roots (mul_transpose_charpoly_mul_X D)
  have hleft_ne :
      Polynomial.X ^ Fintype.card m * (D * Dᵀ).charpoly ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ Polynomial.X_ne_zero)
      (Matrix.charpoly_monic (D * Dᵀ)).ne_zero
  have hright_ne :
      Polynomial.X ^ Fintype.card k * (Dᵀ * D).charpoly ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ Polynomial.X_ne_zero)
      (Matrix.charpoly_monic (Dᵀ * D)).ne_zero
  rw [Polynomial.roots_mul hleft_ne, Polynomial.roots_mul hright_ne,
    Polynomial.roots_X_pow, Polynomial.roots_X_pow] at hroot
  exact hroot

private lemma sortedGE_append_replicate_of_le
    {α : Type*} [LinearOrder α] {l : List α} {z : α}
    (hs : l.SortedGE) (hz : ∀ x ∈ l, z ≤ x) (n : ℕ) :
    (l ++ List.replicate n z).SortedGE := by
  rw [List.sortedGE_iff_pairwise] at hs ⊢
  simp only [List.pairwise_append, hs, List.pairwise_replicate_of_refl, true_and]
  intro a ha b hb
  rw [List.eq_of_mem_replicate hb]
  exact hz a ha

private lemma padded_sorted_lists_eq_of_multiset_eq
    {α : Type*} [LinearOrder α] {l₁ l₂ : List α} {z : α} {a b : ℕ}
    (hs₁ : l₁.SortedGE) (hs₂ : l₂.SortedGE)
    (hz₁ : ∀ x ∈ l₁, z ≤ x) (hz₂ : ∀ x ∈ l₂, z ≤ x)
    (hpad : a • ({z} : Multiset α) + (l₁ : Multiset α) =
      b • ({z} : Multiset α) + (l₂ : Multiset α)) :
    l₁ ++ List.replicate a z = l₂ ++ List.replicate b z := by
  have hrep_a : (List.replicate a z : Multiset α) =
      a • ({z} : Multiset α) := by
    rw [Multiset.coe_replicate, ← Multiset.nsmul_singleton]
  have hrep_b : (List.replicate b z : Multiset α) =
      b • ({z} : Multiset α) := by
    rw [Multiset.coe_replicate, ← Multiset.nsmul_singleton]
  have hcoe :
      ((l₁ ++ List.replicate a z : List α) : Multiset α) =
        ((l₂ ++ List.replicate b z : List α) : Multiset α) := by
    calc
      ((l₁ ++ List.replicate a z : List α) : Multiset α)
          = (l₁ : Multiset α) + a • ({z} : Multiset α) := by
              rw [← Multiset.coe_add, hrep_a]
      _ = a • ({z} : Multiset α) + (l₁ : Multiset α) := by rw [add_comm]
      _ = b • ({z} : Multiset α) + (l₂ : Multiset α) := hpad
      _ = (l₂ : Multiset α) + b • ({z} : Multiset α) := by rw [add_comm]
      _ = ((l₂ ++ List.replicate b z : List α) : Multiset α) := by
              rw [← Multiset.coe_add, hrep_b]
  exact List.Perm.eq_of_sortedGE
    (sortedGE_append_replicate_of_le hs₁ hz₁ a)
    (sortedGE_append_replicate_of_le hs₂ hz₂ b)
    (Multiset.coe_eq_coe.mp hcoe)

/-- Canonical bridge from Mathlib's ambient-index eigenvalues to the ordered
`Fin (card)` indexing used by this repository's spectral theorems. -/
@[simp]
lemma hermitian_eigenvalues_equivOfCardEq
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M : Matrix ι ι ℝ} (hM : M.IsHermitian)
    (i : Fin (Fintype.card ι)) :
    hM.eigenvalues
        ((Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card ι))) i) =
      hM.eigenvalues₀ i := by
  simp [Matrix.IsHermitian.eigenvalues]

/-- Sorted nonnegative eigenvalue-list form of the rectangular Gram bridge.

Because both Gram matrices are positive semidefinite, the zero padding appears
after their decreasingly ordered `eigenvalues₀` lists. -/
private theorem mul_transpose_padded_eigenvalues₀_eq {k m : Type*}
    [Fintype k] [Fintype m] [DecidableEq k] [DecidableEq m]
    (D : Matrix k m ℝ) :
    List.ofFn (mul_transpose_isHermitian D).eigenvalues₀ ++
        List.replicate (Fintype.card m) (0 : ℝ) =
      List.ofFn (transpose_mul_isHermitian D).eigenvalues₀ ++
        List.replicate (Fintype.card k) (0 : ℝ) := by
  let lrow := List.ofFn (mul_transpose_isHermitian D).eigenvalues₀
  let lcol := List.ofFn (transpose_mul_isHermitian D).eigenvalues₀
  have hrowRoots : (D * Dᵀ).charpoly.roots = (lrow : Multiset ℝ) := by
    simpa [lrow, Function.comp_def] using
      (mul_transpose_isHermitian D).roots_charpoly_eq_eigenvalues₀
  have hcolRoots : (Dᵀ * D).charpoly.roots = (lcol : Multiset ℝ) := by
    simpa [lcol, Function.comp_def] using
      (transpose_mul_isHermitian D).roots_charpoly_eq_eigenvalues₀
  have hpad : Fintype.card m • ({0} : Multiset ℝ) + (lrow : Multiset ℝ) =
      Fintype.card k • ({0} : Multiset ℝ) + (lcol : Multiset ℝ) := by
    simpa [hrowRoots, hcolRoots] using mul_transpose_roots_with_zero_padding D
  have hsRow : lrow.SortedGE := by
    exact (mul_transpose_isHermitian D).eigenvalues₀_antitone.sortedGE_ofFn
  have hsCol : lcol.SortedGE := by
    exact (transpose_mul_isHermitian D).eigenvalues₀_antitone.sortedGE_ofFn
  have hrowPSD : (D * Dᵀ).PosSemidef := by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.posSemidef_self_mul_conjTranspose D
  have hcolPSD : (Dᵀ * D).PosSemidef := by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.posSemidef_conjTranspose_mul_self D
  have h0Row : ∀ x ∈ lrow, 0 ≤ x := by
    intro x hx
    dsimp [lrow] at hx
    rw [List.mem_ofFn] at hx
    rcases hx with ⟨i, rfl⟩
    have hproof : hrowPSD.1 = mul_transpose_isHermitian D := Subsingleton.elim _ _
    rw [← hproof]
    have hnonneg := hrowPSD.eigenvalues_nonneg
      ((Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card k))) i)
    rw [hermitian_eigenvalues_equivOfCardEq hrowPSD.1 i] at hnonneg
    exact hnonneg
  have h0Col : ∀ x ∈ lcol, 0 ≤ x := by
    intro x hx
    dsimp [lcol] at hx
    rw [List.mem_ofFn] at hx
    rcases hx with ⟨i, rfl⟩
    have hproof : hcolPSD.1 = transpose_mul_isHermitian D := Subsingleton.elim _ _
    rw [← hproof]
    have hnonneg := hcolPSD.eigenvalues_nonneg
      ((Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card m))) i)
    rw [hermitian_eigenvalues_equivOfCardEq hcolPSD.1 i] at hnonneg
    exact hnonneg
  exact padded_sorted_lists_eq_of_multiset_eq hsRow hsCol h0Row h0Col hpad

/-- The leading ordered eigenvalues of the two rectangular Gram matrices agree
at every index present on both sides. -/
theorem mul_transpose_eigenvalues₀_eq_of_lt {k m : Type*}
    [Fintype k] [Fintype m] [DecidableEq k] [DecidableEq m]
    (D : Matrix k m ℝ) (i : ℕ)
    (hik : i < Fintype.card k) (him : i < Fintype.card m) :
    (mul_transpose_isHermitian D).eigenvalues₀ ⟨i, hik⟩ =
      (transpose_mul_isHermitian D).eigenvalues₀ ⟨i, him⟩ := by
  have hpadded := mul_transpose_padded_eigenvalues₀_eq D
  have hget := congrArg (fun l : List ℝ => l[i]?) hpadded
  dsimp only at hget
  rw [List.getElem?_append_left (by simpa using hik),
    List.getElem?_append_left (by simpa using him)] at hget
  simpa [List.getElem?_ofFn, hik, him] using hget

/-- A positive semidefinite real matrix of rank at least `r` has strictly
positive ordered eigenvalues at each of its first `r` indices. -/
theorem leading_eigenvalues₀_pos_of_posSemidef_rank_ge
    {k r : Type*} [Fintype k] [Fintype r] [DecidableEq k]
    {M : Matrix k k ℝ} (hM : M.PosSemidef)
    (hcard : Fintype.card r ≤ Fintype.card k)
    (hrank : Fintype.card r ≤ M.rank) :
    ∀ j : r, 0 < hM.1.eigenvalues₀
      (Fin.castLE hcard ((Fintype.equivFin r) j)) := by
  classical
  let e : Fin (Fintype.card k) ≃ k :=
    Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card k))
  have hnonneg : ∀ i : Fin (Fintype.card k), 0 ≤ hM.1.eigenvalues₀ i := by
    intro i
    simpa [e] using hM.eigenvalues_nonneg (e i)
  have hrank_eq :
      M.rank = Fintype.card
        {i : Fin (Fintype.card k) // hM.1.eigenvalues₀ i ≠ 0} := by
    let nonzeroEquiv :
        {i : Fin (Fintype.card k) // hM.1.eigenvalues₀ i ≠ 0} ≃
          {a : k // hM.1.eigenvalues a ≠ 0} := {
      toFun i := ⟨e i.1, by
        simpa [e] using i.2⟩
      invFun a := ⟨e.symm a.1, by
        simpa [e] using a.2⟩
      left_inv i := by
        ext
        simp [e]
      right_inv a := by
        ext
        simp [e] }
    rw [hM.1.rank_eq_card_non_zero_eigs]
    exact (Fintype.card_congr nonzeroEquiv).symm
  intro j
  let idx : Fin (Fintype.card k) :=
    Fin.castLE hcard ((Fintype.equivFin r) j)
  have hdown :
      ∀ i j : Fin (Fintype.card k), j ≤ i →
        hM.1.eigenvalues₀ i ≠ 0 → hM.1.eigenvalues₀ j ≠ 0 := by
    intro i j hji hi hzero
    have hle : hM.1.eigenvalues₀ i ≤ hM.1.eigenvalues₀ j :=
      hM.1.eigenvalues₀_antitone hji
    have hzero_i : hM.1.eigenvalues₀ i = 0 :=
      le_antisymm (by simpa [hzero] using hle) (hnonneg i)
    exact hi hzero_i
  have hidx_lt_r : (idx : ℕ) < Fintype.card r := by
    simp [idx]
  have hidx_lt_count :
      idx < Fintype.card
        {i : Fin (Fintype.card k) // hM.1.eigenvalues₀ i ≠ 0} :=
    lt_of_lt_of_le hidx_lt_r (hrank.trans_eq hrank_eq)
  have hidx_nonzero : hM.1.eigenvalues₀ idx ≠ 0 :=
    (Fin.lt_card_filter_univ_iff_apply_of_imp
      (fun i : Fin (Fintype.card k) => hM.1.eigenvalues₀ i ≠ 0)
      hdown).mp (by simpa [Fintype.card_subtype] using hidx_lt_count)
  exact lt_of_le_of_ne (hnonneg idx) hidx_nonzero.symm

/-- The ordered eigenvalues of `I - A` are the reversed complements of the
ordered eigenvalues of a real Hermitian matrix `A`.

The reversal is essential: Mathlib orders `eigenvalues₀` nonincreasingly,
while `x ↦ 1 - x` reverses inequalities. -/
private theorem one_sub_ordered_eigenvalues₀_eq_reverse_map
    {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA : A.IsHermitian) :
    List.ofFn (isHermitian_one.sub hA).eigenvalues₀ =
      (List.ofFn hA.eigenvalues₀).reverse.map (fun x => 1 - x) := by
  let hIA : (1 - A).IsHermitian := isHermitian_one.sub hA
  let f : ℝ → ℝ := fun x => 1 - x
  have hdiag :
      1 - A =
        Unitary.conjStarAlgAut ℝ (Matrix n n ℝ) hA.eigenvectorUnitary
          (Matrix.diagonal (f ∘ hA.eigenvalues)) := by
    calc
      1 - A = 1 -
          Unitary.conjStarAlgAut ℝ (Matrix n n ℝ) hA.eigenvectorUnitary
            (Matrix.diagonal (fun i => hA.eigenvalues i)) :=
        congrArg (fun M : Matrix n n ℝ => 1 - M) hA.spectral_theorem
      _ = Unitary.conjStarAlgAut ℝ (Matrix n n ℝ) hA.eigenvectorUnitary
          (1 - Matrix.diagonal (fun i => hA.eigenvalues i)) := by
        rw [map_sub, map_one]
      _ = Unitary.conjStarAlgAut ℝ (Matrix n n ℝ) hA.eigenvectorUnitary
          (Matrix.diagonal (f ∘ hA.eigenvalues)) := by
        congr 1
        ext i j
        by_cases hij : i = j
        · subst j
          simp [f, Function.comp_def]
        · simp [Matrix.diagonal, hij]
  have hchar :
      (1 - A).charpoly =
        ∏ i, (Polynomial.X - Polynomial.C (f (hA.eigenvalues i))) := by
    rw [hdiag, Unitary.conjStarAlgAut_apply, Matrix.charpoly_mul_comm, ← mul_assoc]
    simp [Matrix.charpoly_diagonal, f, Function.comp_def]
  have hroots :
      (1 - A).charpoly.roots =
        Multiset.map f A.charpoly.roots := by
    rw [hchar, Polynomial.roots_prod]
    · rw [hA.roots_charpoly_eq_eigenvalues]
      simp only [Polynomial.roots_X_sub_C, Multiset.bind_singleton,
        Multiset.map_map, Function.comp_apply, RCLike.ofReal_real_eq_id, id_eq]
    · exact Finset.prod_ne_zero_iff.mpr
        (fun i _ => Polynomial.X_sub_C_ne_zero _)
  have hrootsIA :
      (1 - A).charpoly.roots =
        ((List.ofFn hIA.eigenvalues₀ : List ℝ) : Multiset ℝ) := by
    simpa [hIA, Function.comp_def] using hIA.roots_charpoly_eq_eigenvalues₀
  have hrootsA :
      A.charpoly.roots =
        ((List.ofFn hA.eigenvalues₀ : List ℝ) : Multiset ℝ) := by
    simpa [Function.comp_def] using hA.roots_charpoly_eq_eigenvalues₀
  have hperm :
      List.Perm (List.ofFn hIA.eigenvalues₀)
        ((List.ofFn hA.eigenvalues₀).reverse.map f) := by
    apply Multiset.coe_eq_coe.mp
    calc
      ((List.ofFn hIA.eigenvalues₀ : List ℝ) : Multiset ℝ) =
          (1 - A).charpoly.roots := hrootsIA.symm
      _ = Multiset.map f A.charpoly.roots := hroots
      _ = Multiset.map f
          ((List.ofFn hA.eigenvalues₀ : List ℝ) : Multiset ℝ) := by rw [hrootsA]
      _ = (((List.ofFn hA.eigenvalues₀).reverse.map f : List ℝ) : Multiset ℝ) := by
        simp
  have hleft : (List.ofFn hIA.eigenvalues₀).SortedGE :=
    hIA.eigenvalues₀_antitone.sortedGE_ofFn
  have hf : StrictAnti f := by
    intro a b hab
    exact sub_lt_sub_left hab 1
  have hright : ((List.ofFn hA.eigenvalues₀).reverse.map f).SortedGE := by
    rw [hf.sortedGE_listMap, List.sortedLE_reverse]
    exact hA.eigenvalues₀_antitone.sortedGE_ofFn
  change List.ofFn hIA.eigenvalues₀ =
    (List.ofFn hA.eigenvalues₀).reverse.map f
  exact hperm.eq_of_sortedGE hleft hright

/-- Pointwise form of `one_sub_ordered_eigenvalues₀_eq_reverse_map`.

The `i`-th largest eigenvalue of `I - A` is one minus the `i`-th smallest
eigenvalue of `A`. -/
theorem one_sub_ordered_eigenvalues₀_apply
    {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA : A.IsHermitian)
    (i : Fin (Fintype.card n)) :
    (isHermitian_one.sub hA).eigenvalues₀ i =
      1 - hA.eigenvalues₀ (Fin.rev i) := by
  have hlist := one_sub_ordered_eigenvalues₀_eq_reverse_map hA
  have hget := congrArg (fun l : List ℝ => l[i.val]?) hlist
  simpa [List.getElem?_ofFn, List.getElem?_map, List.getElem?_reverse,
    Fin.rev, i.isLt, Nat.sub_sub, Nat.add_comm] using hget
/-- A one-row restriction has full row rank exactly when one displayed
coefficient is nonzero.

This is the finite-dimensional bridge from Hansen's usual one-row
nonzero-restriction condition to the linear-map injectivity premise used by
the studentization helpers. -/
theorem oneRow_transpose_mulVec_injective_iff_exists_ne_zero {k : Type*}
    (R : Matrix Unit k ℝ) :
    Function.Injective Rᵀ.mulVec ↔ ∃ j : k, R () j ≠ 0 := by
  constructor
  · intro hR
    by_contra hnone
    have hnone' : ∀ j : k, R () j = 0 := by
      intro j
      by_contra hj
      exact hnone ⟨j, hj⟩
    have hmap :
        Rᵀ.mulVec (fun _ : Unit => (1 : ℝ)) =
          Rᵀ.mulVec (fun _ : Unit => (0 : ℝ)) := by
      funext j
      simp [Matrix.mulVec, hnone' j]
    have hscalar := congrFun (hR hmap) ()
    norm_num at hscalar
  · rintro ⟨j, hj⟩ x y hxy
    funext u
    cases u
    have hcoord : R () j * x () = R () j * y () := by
      simpa [Matrix.mulVec] using congrFun hxy j
    exact mul_left_cancel₀ hj hcoord

/-- One nonzero coefficient in a one-row restriction gives full row rank. -/
theorem oneRow_transpose_mulVec_injective_of_exists_ne_zero {k : Type*}
    {R : Matrix Unit k ℝ} (hR : ∃ j : k, R () j ≠ 0) :
    Function.Injective Rᵀ.mulVec :=
  (oneRow_transpose_mulVec_injective_iff_exists_ne_zero R).2 hR
/-- Eigenvalues of a real Hermitian idempotent matrix are `0` or `1`. -/
theorem eigenvalues_zero_or_one_of_isHermitian_idempotent {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ}
    (hH : A.IsHermitian)
    (hI : IsIdempotentElem A) :
    ∀ i : n, hH.eigenvalues i = 0 ∨ hH.eigenvalues i = 1 := by
  intro i
  have hmem := hI.spectrum_subset ℝ (hH.eigenvalues_mem_spectrum_real i)
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
  exact hmem

/-- For a real Hermitian idempotent matrix, rank equals the trace. This packages the spectral
argument that the eigenvalues are all `0` or `1`, so the rank counts the same terms that the trace
sums. -/
theorem rank_eq_natCast_trace_of_isHermitian_idempotent {n : Type*} [Fintype n]
    {A : Matrix n n ℝ}
    (hH : A.IsHermitian)
    (hI : IsIdempotentElem A) :
    (A.rank : ℝ) = A.trace := by
  classical
  have heig := eigenvalues_zero_or_one_of_isHermitian_idempotent hH hI
  rw [hH.rank_eq_card_non_zero_eigs, hH.trace_eq_sum_eigenvalues]
  -- ↑(card {i // eigenvalues i ≠ 0}) = ∑ i, (eigenvalues i : ℝ)
  simp only [RCLike.ofReal_real_eq_id, id]
  -- Each nonzero eigenvalue is 1.
  have heig1 : ∀ i : n, hH.eigenvalues i ≠ 0 → hH.eigenvalues i = 1 :=
    fun i hi => (heig i).resolve_left hi
  symm
  calc ∑ i : n, hH.eigenvalues i
      = ∑ i : n, if hH.eigenvalues i ≠ 0 then (1 : ℝ) else 0 :=
          Finset.sum_congr rfl (fun i _ => by rcases heig i with h | h <;> simp [h])
    _ = ↑(Finset.univ.filter (fun i : n => hH.eigenvalues i ≠ 0)).card :=
          Finset.sum_boole _ _
    _ = ↑(Fintype.card {i : n // hH.eigenvalues i ≠ 0}) := by
          congr 1
          exact (Fintype.card_of_subtype _ (fun x => by
            simp only [Finset.mem_filter, Finset.mem_univ, true_and])).symm

/-- For a Hermitian idempotent real matrix, rank is the number of `1`-eigenvalues. -/
theorem rank_eq_card_eigenvalues_eq_one_of_isHermitian_idempotent {n : Type*}
    [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ}
    (hH : A.IsHermitian)
    (hI : IsIdempotentElem A) :
    A.rank = Fintype.card {i : n // hH.eigenvalues i = 1} := by
  classical
  have heig := eigenvalues_zero_or_one_of_isHermitian_idempotent hH hI
  rw [hH.rank_eq_card_non_zero_eigs]
  refine Fintype.card_congr ?_
  exact
    { toFun := fun i => ⟨i.1, (heig i.1).resolve_left i.2⟩
      invFun := fun i => ⟨i.1, by rw [i.2]; norm_num⟩
      left_inv := by
        intro i
        cases i
        rfl
      right_inv := by
        intro i
        cases i
        rfl }

/-- A real Hermitian idempotent matrix is the orthogonal projection onto its
`1`-eigenspace, written as the sum of outer products of Mathlib's eigenbasis
vectors. -/
theorem isHermitian_idempotent_eq_sum_one_eigenvectorBasis_outer
    {n : Type*} [Fintype n] [DecidableEq n]
    {P : Matrix n n ℝ} (hP : P.IsHermitian) (hI : IsIdempotentElem P) :
    (fun j k : n => ∑ r : {i : n // hP.eigenvalues i = 1},
      (hP.eigenvectorBasis r.1 : EuclideanSpace ℝ n) j *
        (hP.eigenvectorBasis r.1 : EuclideanSpace ℝ n) k) = P := by
  classical
  ext j k
  have heig := eigenvalues_zero_or_one_of_isHermitian_idempotent hP hI
  let f : n → ℝ := fun x =>
    (hP.eigenvectorBasis x : EuclideanSpace ℝ n) j *
      (hP.eigenvectorBasis x : EuclideanSpace ℝ n) k
  have hsub :
      (∑ r : {i : n // hP.eigenvalues i = 1}, f r.1) =
        ∑ x ∈ (Finset.univ.filter (fun i : n => hP.eigenvalues i = 1)), f x := by
    rw [← Finset.sum_subtype
      (s := Finset.univ.filter (fun i : n => hP.eigenvalues i = 1))]
    intro x
    simp
  have hfilter :
      (∑ x ∈ (Finset.univ.filter (fun i : n => hP.eigenvalues i = 1)), f x) =
        ∑ x : n, f x * hP.eigenvalues x := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl ?_
    intro x _
    by_cases h1 : hP.eigenvalues x = 1
    · simp [h1]
    · have h0 : hP.eigenvalues x = 0 := (heig x).resolve_right h1
      simp [h0]
  have hsum :
      (∑ r : {i : n // hP.eigenvalues i = 1},
        (hP.eigenvectorBasis r.1 : EuclideanSpace ℝ n) j *
          (hP.eigenvectorBasis r.1 : EuclideanSpace ℝ n) k) =
        ∑ x : n, (hP.eigenvectorBasis x : EuclideanSpace ℝ n) j *
          hP.eigenvalues x * (hP.eigenvectorBasis x : EuclideanSpace ℝ n) k := by
    calc
      (∑ r : {i : n // hP.eigenvalues i = 1},
        (hP.eigenvectorBasis r.1 : EuclideanSpace ℝ n) j *
          (hP.eigenvectorBasis r.1 : EuclideanSpace ℝ n) k)
          = ∑ r : {i : n // hP.eigenvalues i = 1}, f r.1 := by rfl
      _ = ∑ x ∈ (Finset.univ.filter (fun i : n => hP.eigenvalues i = 1)), f x :=
        hsub
      _ = ∑ x : n, f x * hP.eigenvalues x := hfilter
      _ = ∑ x : n, (hP.eigenvectorBasis x : EuclideanSpace ℝ n) j *
          hP.eigenvalues x * (hP.eigenvectorBasis x : EuclideanSpace ℝ n) k := by
          refine Finset.sum_congr rfl ?_
          intro x _
          dsimp [f]
          ring
  rw [hsum]
  conv_rhs => rw [hP.spectral_theorem]
  simp [Unitary.conjStarAlgAut_apply, Matrix.mul_apply, Matrix.diagonal]

/-- A Hermitian idempotent real matrix has quadratic form equal to the sum of squared
coordinates on its `1`-eigenspace. This is the reusable deterministic bridge behind finite-sample
chi-square arguments for projection residuals. -/
theorem isHermitian_idempotent_quadratic_form_eq_sum_sq_eigenvector_coords
    {n : Type*} [Fintype n] [DecidableEq n]
    {P : Matrix n n ℝ} (hP : P.IsHermitian) (hI : IsIdempotentElem P) (e : n → ℝ) :
    e ⬝ᵥ P *ᵥ e =
      ∑ i : {j : n // hP.eigenvalues j = 1},
        (hP.eigenvectorBasis.repr (WithLp.toLp 2 e) i.1) ^ 2 := by
  classical
  let b : OrthonormalBasis n ℝ (EuclideanSpace ℝ n) := hP.eigenvectorBasis
  let z : EuclideanSpace ℝ n := WithLp.toLp 2 e
  have hcoord : ∀ i : n,
      b.repr (Matrix.toEuclideanLin P z) i = hP.eigenvalues i * b.repr z i := by
    intro i
    let T : EuclideanSpace ℝ n →ₗ[ℝ] EuclideanSpace ℝ n := Matrix.toEuclideanLin P
    have hSymm : T.IsSymmetric := Matrix.isHermitian_iff_isSymmetric.mp hP
    have hEig : T (b i) = hP.eigenvalues i • b i := by
      simpa [T] using congrArg (WithLp.toLp 2) (hP.mulVec_eigenvectorBasis i)
    calc
      b.repr (T z) i = inner ℝ (b i) (T z) := by
        simpa using (OrthonormalBasis.repr_apply_apply (b := b) (v := T z) (i := i))
      _ = inner ℝ (T (b i)) z := by rw [← hSymm (b i) z]
      _ = inner ℝ (hP.eigenvalues i • b i) z := by rw [hEig]
      _ = hP.eigenvalues i * b.repr z i := by
        rw [real_inner_smul_left, OrthonormalBasis.repr_apply_apply]
  have hnorm :
      dotProduct (P *ᵥ e) (P *ᵥ e)
        = ∑ i : n, (hP.eigenvalues i * b.repr z i) ^ 2 := by
    let T : EuclideanSpace ℝ n →ₗ[ℝ] EuclideanSpace ℝ n := Matrix.toEuclideanLin P
    calc
      dotProduct (P *ᵥ e) (P *ᵥ e) = ‖T z‖ ^ 2 := by
        change dotProduct (P *ᵥ e) (P *ᵥ e) = ‖WithLp.toLp 2 (P *ᵥ e)‖ ^ 2
        simpa [pow_two] using
          (EuclideanSpace.real_norm_sq_eq (WithLp.toLp 2 (P *ᵥ e))).symm
      _ = ∑ i : n, ‖inner ℝ (b i) (T z)‖ ^ 2 := by
        symm
        exact OrthonormalBasis.sum_sq_norm_inner_right b (T z)
      _ = ∑ i : n, (b.repr (T z) i) ^ 2 := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        rw [OrthonormalBasis.repr_apply_apply]
        simp [sq_abs]
      _ = ∑ i : n, (hP.eigenvalues i * b.repr z i) ^ 2 := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        rw [hcoord i]
  have heig01 := eigenvalues_zero_or_one_of_isHermitian_idempotent hP hI
  have hsum :
      ∑ i : n, (hP.eigenvalues i * b.repr z i) ^ 2
        = ∑ i : {j : n // hP.eigenvalues j = 1}, (b.repr z i.1) ^ 2 := by
    calc
      ∑ i : n, (hP.eigenvalues i * b.repr z i) ^ 2
          = ∑ i : n, if hP.eigenvalues i = 1 then (b.repr z i) ^ 2 else 0 := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              by_cases h1 : hP.eigenvalues i = 1
              · simp [h1]
              · have h0 : hP.eigenvalues i = 0 := (heig01 i).resolve_right h1
                simp [h0]
      _ = ∑ i : n with hP.eigenvalues i = 1, (b.repr z i) ^ 2 := by
            rw [Finset.sum_filter]
      _ = ∑ i : {j : n // hP.eigenvalues j = 1}, (b.repr z i.1) ^ 2 := by
            rw [Finset.sum_subtype]
            intro x
            simp
  have hPt : Pᵀ = P := by
    exact (Matrix.conjTranspose_eq_transpose_of_trivial P).symm.trans hP
  have hquad : e ⬝ᵥ P *ᵥ e = dotProduct (P *ᵥ e) (P *ᵥ e) :=
    quadratic_form_eq_dotProduct_of_symm_idempotent P hPt hI e
  simpa [b, z] using hquad.trans (hnorm.trans hsum)

/-- Pull a quadratic form through a fixed rectangular matrix map. -/
lemma quadraticForm_mulVec_eq_pullback_rect
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (B : Matrix κ ι ℝ) (A : Matrix κ κ ℝ) (x : ι → ℝ) :
    (B *ᵥ x) ⬝ᵥ (A *ᵥ (B *ᵥ x)) =
      x ⬝ᵥ ((Bᵀ * A * B) *ᵥ x) := by
  calc
    (B *ᵥ x) ⬝ᵥ (A *ᵥ (B *ᵥ x))
        = ((B *ᵥ x) ᵥ* A) ⬝ᵥ (B *ᵥ x) := by
      rw [Matrix.dotProduct_mulVec]
    _ = (((x ᵥ* Bᵀ) ᵥ* A) ⬝ᵥ (B *ᵥ x)) := by
      rw [Matrix.vecMul_transpose]
    _ = ((x ᵥ* (Bᵀ * A)) ⬝ᵥ (B *ᵥ x)) := by
      rw [Matrix.vecMul_vecMul]
    _ = (((x ᵥ* (Bᵀ * A)) ᵥ* B) ⬝ᵥ x) := by
      rw [Matrix.dotProduct_mulVec]
    _ = ((x ᵥ* ((Bᵀ * A) * B)) ⬝ᵥ x) := by
      rw [Matrix.vecMul_vecMul]
    _ = x ⬝ᵥ ((Bᵀ * A * B) *ᵥ x) := by
      rw [← Matrix.dotProduct_mulVec]

/-- Pointwise domination of squared norms after two matrix maps implies the
corresponding Loewner order on their Gram matrices. -/
private theorem gram_le_gram_of_mulVec_norm_sq_le
    {m n : Type*} [Fintype m] [Fintype n]
    (A B : Matrix m n ℝ)
    (h : ∀ x : n → ℝ,
      dotProduct (A *ᵥ x) (A *ᵥ x) ≤ dotProduct (B *ᵥ x) (B *ᵥ x)) :
    Aᵀ * A ≤ Bᵀ * B := by
  classical
  rw [Matrix.le_iff]
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · simpa [Matrix.conjTranspose, Matrix.star_apply] using
      (Matrix.isHermitian_conjTranspose_mul_self B).sub
        (Matrix.isHermitian_conjTranspose_mul_self A)
  · intro x
    have hA :
        dotProduct (A *ᵥ x) (A *ᵥ x) =
          dotProduct x ((Aᵀ * A) *ᵥ x) := by
      simpa using
        (quadraticForm_mulVec_eq_pullback_rect A (1 : Matrix m m ℝ) x)
    have hB :
        dotProduct (B *ᵥ x) (B *ᵥ x) =
          dotProduct x ((Bᵀ * B) *ᵥ x) := by
      simpa using
        (quadraticForm_mulVec_eq_pullback_rect B (1 : Matrix m m ℝ) x)
    simpa [Matrix.sub_mulVec, hA, hB] using sub_nonneg.mpr (h x)

/-- Left multiplication by a positive-semidefinite weight preserves trace
inequalities in the Loewner order. -/
theorem trace_mul_le_trace_mul_of_le_of_posSemidef
    {n : Type*} [Fintype n]
    {A B W : Matrix n n ℝ}
    (hAB : A ≤ B) (hW : W.PosSemidef) :
    Matrix.trace (W * A) ≤ Matrix.trace (W * B) := by
  classical
  let S : Matrix n n ℝ := CFC.sqrt W
  have hD : (B - A).PosSemidef := Matrix.le_iff.mp hAB
  have hS : Sᴴ = S := by
    simpa [S] using (CFC.sqrt_nonneg W).isSelfAdjoint
  have hSsq : S * S = W := by
    simpa [S] using CFC.sqrt_mul_sqrt_self W hW.nonneg
  have hcongr : (Sᴴ * (B - A) * S).PosSemidef :=
    hD.conjTranspose_mul_mul_same S
  rw [← sub_nonneg, ← Matrix.trace_sub, ← Matrix.mul_sub]
  calc
    0 ≤ Matrix.trace (Sᴴ * (B - A) * S) := hcongr.trace_nonneg
    _ = Matrix.trace (S * Sᴴ * (B - A)) :=
      Matrix.trace_mul_cycle Sᴴ (B - A) S
    _ = Matrix.trace (W * (B - A)) := by rw [hS, hSsq]

private lemma quadForm_eq_sum_eigenvalues_core
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M : Matrix ι ι ℝ} (hH : M.IsHermitian)
    (z : EuclideanSpace ℝ ι) :
    (z : ι → ℝ) ⬝ᵥ (M *ᵥ (z : ι → ℝ))
      = ∑ i, hH.eigenvalues i * (hH.eigenvectorBasis.repr z i) ^ 2 := by
  set b := hH.eigenvectorBasis with hb_def
  -- Write `z` as a sum in the eigenbasis.
  have hz_coord : (z : ι → ℝ) = ∑ i, b.repr z i • ((b i : ι → ℝ)) := by
    have hsum : z = ∑ i, b.repr z i • b i := (b.sum_repr z).symm
    have : ((z : EuclideanSpace ℝ ι) : ι → ℝ)
        = (((∑ i, b.repr z i • b i) : EuclideanSpace ℝ ι) : ι → ℝ) :=
      congrArg _ hsum
    rw [this, WithLp.ofLp_sum]
    rfl
  -- Apply M to that sum; linearity + eigenvector identity.
  have hMz_coord : M *ᵥ (z : ι → ℝ)
      = ∑ i, (b.repr z i * hH.eigenvalues i) • ((b i : ι → ℝ)) := by
    rw [hz_coord, Matrix.mulVec_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Matrix.mulVec_smul, hH.mulVec_eigenvectorBasis, smul_smul]
  -- Orthonormality of the eigenbasis as `ι → ℝ` vectors. For real scalars the inner
  -- product coincides with the flipped dot product: `⟪x, y⟫_ℝ = y ⬝ᵥ x`.
  have hinner_eq_dot : ∀ x y : EuclideanSpace ℝ ι,
      @inner ℝ (EuclideanSpace ℝ ι) _ x y = ((y : ι → ℝ)) ⬝ᵥ ((x : ι → ℝ)) :=
    fun _ _ => rfl
  have horth : ∀ i j : ι,
      ((b i : ι → ℝ)) ⬝ᵥ ((b j : ι → ℝ)) = if i = j then (1 : ℝ) else 0 := by
    intro i j
    rw [dotProduct_comm, ← hinner_eq_dot]
    have := (orthonormal_iff_ite.mp b.orthonormal) i j
    simpa using this
  -- Expand the dot product step by step.
  rw [hMz_coord, hz_coord, sum_dotProduct]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [smul_dotProduct, dotProduct_sum, smul_eq_mul]
  have step : ∀ j, (b i : ι → ℝ) ⬝ᵥ ((b.repr z j * hH.eigenvalues j) • (b j : ι → ℝ))
      = (b.repr z j * hH.eigenvalues j) * (if i = j then (1 : ℝ) else 0) := by
    intro j; rw [dotProduct_smul, horth, smul_eq_mul]
  simp_rw [step]
  rw [Finset.sum_congr rfl (fun j _ => show
    (b.repr z j * hH.eigenvalues j) * (if i = j then (1 : ℝ) else 0)
      = if i = j then b.repr z i * hH.eigenvalues i else 0 by
    split_ifs with hij
    · rw [hij]; ring
    · ring)]
  rw [Finset.sum_ite_eq Finset.univ i]
  simp
  ring

/-- Spectral expansion of the quadratic form `z ⬝ᵥ M *ᵥ z` in the eigenbasis of a
Hermitian real matrix: it equals the sum of eigenvalues times squared basis coordinates. -/
lemma quadForm_eq_sum_eigenvalues
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M : Matrix ι ι ℝ} (hH : M.IsHermitian)
    (z : EuclideanSpace ℝ ι) :
    (z : ι → ℝ) ⬝ᵥ (M *ᵥ (z : ι → ℝ))
      = ∑ i, hH.eigenvalues i * (hH.eigenvectorBasis.repr z i) ^ 2 := by
  exact quadForm_eq_sum_eigenvalues_core hH z

private lemma sum_sq_eigenbasis_repr_eq_one
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M : Matrix ι ι ℝ} (hH : M.IsHermitian)
    (z : EuclideanSpace ℝ ι)
    (hunit : (z : ι → ℝ) ⬝ᵥ (z : ι → ℝ) = 1) :
    ∑ i : ι, (hH.eigenvectorBasis.repr z i) ^ 2 = 1 := by
  have hnorm : ‖z‖ ^ 2 = 1 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simpa [dotProduct, pow_two] using hunit
  calc
    ∑ i : ι, (hH.eigenvectorBasis.repr z i) ^ 2
        = ∑ i : ι, ‖inner ℝ (hH.eigenvectorBasis i) z‖ ^ 2 := by
            refine Finset.sum_congr rfl ?_
            intro i _
            rw [OrthonormalBasis.repr_apply_apply]
            simp [sq_abs]
            rfl
    _ = ‖z‖ ^ 2 := OrthonormalBasis.sum_sq_norm_inner_right hH.eigenvectorBasis z
    _ = 1 := hnorm

private lemma sum_sq_eigenbasis_repr_equiv_eq_one
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M : Matrix ι ι ℝ} (hH : M.IsHermitian)
    (z : EuclideanSpace ℝ ι)
    (hunit : (z : ι → ℝ) ⬝ᵥ (z : ι → ℝ) = 1) :
    ∑ i : Fin (Fintype.card ι),
        (hH.eigenvectorBasis.repr z
          ((Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card ι))) i)) ^ 2 = 1 := by
  calc
    _ = ∑ i : ι, (hH.eigenvectorBasis.repr z i) ^ 2 := by
      simpa using
        (Equiv.sum_comp
          (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card ι)))
          (fun i : ι => (hH.eigenvectorBasis.repr z i) ^ 2))
    _ = 1 := sum_sq_eigenbasis_repr_eq_one hH z hunit

/-- Rayleigh-quotient upper bound from a Hermitian spectral expansion.

If the coordinates before `j` in the ordered Hermitian eigenbasis are zero,
then a unit vector's quadratic form is bounded by the `j`th ordered eigenvalue.
This is the deterministic core of the sequential PCA optimizer argument. -/
lemma quadForm_le_ordered_eigenvalue_of_unit_of_zero_before
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M : Matrix ι ι ℝ} (hH : M.IsHermitian)
    (j : Fin (Fintype.card ι)) (z : EuclideanSpace ℝ ι)
    (hunit : (z : ι → ℝ) ⬝ᵥ (z : ι → ℝ) = 1)
    (hzero : ∀ i : Fin (Fintype.card ι), i < j →
      hH.eigenvectorBasis.repr z
        ((Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card ι))) i) = 0) :
    (z : ι → ℝ) ⬝ᵥ (M *ᵥ (z : ι → ℝ)) ≤ hH.eigenvalues₀ j := by
  classical
  let e : Fin (Fintype.card ι) ≃ ι :=
    Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card ι))
  let c : Fin (Fintype.card ι) → ℝ := fun i =>
    (hH.eigenvectorBasis.repr z (e i)) ^ 2
  have hcoords_sum : ∑ i : Fin (Fintype.card ι), c i = 1 := by
    simpa [c, e] using sum_sq_eigenbasis_repr_equiv_eq_one hH z hunit
  have hquad :=
    quadForm_eq_sum_eigenvalues (M := M) hH z
  rw [hquad]
  calc
    ∑ i : ι, hH.eigenvalues i * (hH.eigenvectorBasis.repr z i) ^ 2
        = ∑ i : Fin (Fintype.card ι), hH.eigenvalues (e i) * c i := by
            simpa [c, e] using
              (Equiv.sum_comp
                (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card ι)))
                (fun i : ι =>
                  hH.eigenvalues i * (hH.eigenvectorBasis.repr z i) ^ 2)).symm
    _ ≤ ∑ i : Fin (Fintype.card ι), hH.eigenvalues₀ j * c i := by
          refine Finset.sum_le_sum ?_
          intro i _
          by_cases hij : i < j
          · have hc0 : c i = 0 := by
              have hz : hH.eigenvectorBasis.repr z (e i) = 0 := by
                simpa [e] using hzero i hij
              simp [c, hz]
            rw [hc0, mul_zero, mul_zero]
          · have hji : j ≤ i := le_of_not_gt hij
            have heig :
                hH.eigenvalues (e i) ≤ hH.eigenvalues₀ j := by
              simpa [e] using
                hH.eigenvalues₀_antitone hji
            exact mul_le_mul_of_nonneg_right heig (sq_nonneg _)
    _ = hH.eigenvalues₀ j := by
          rw [← Finset.mul_sum, hcoords_sum, mul_one]

/-- Rayleigh-quotient lower bound from a Hermitian spectral expansion.

If the coordinates after `j` in the ordered Hermitian eigenbasis are zero,
then the `j`th ordered eigenvalue bounds a unit vector's quadratic form from
below. This is the lower-bound counterpart used in Ritz interlacing. -/
private lemma ordered_eigenvalue_le_quadForm_of_unit_of_zero_after
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M : Matrix ι ι ℝ} (hH : M.IsHermitian)
    (j : Fin (Fintype.card ι)) (z : EuclideanSpace ℝ ι)
    (hunit : (z : ι → ℝ) ⬝ᵥ (z : ι → ℝ) = 1)
    (hzero : ∀ i : Fin (Fintype.card ι), j < i →
      hH.eigenvectorBasis.repr z
        ((Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card ι))) i) = 0) :
    hH.eigenvalues₀ j ≤ (z : ι → ℝ) ⬝ᵥ (M *ᵥ (z : ι → ℝ)) := by
  classical
  let e : Fin (Fintype.card ι) ≃ ι :=
    Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card ι))
  let c : Fin (Fintype.card ι) → ℝ := fun i =>
    (hH.eigenvectorBasis.repr z (e i)) ^ 2
  have hcoords_sum : ∑ i : Fin (Fintype.card ι), c i = 1 := by
    simpa [c, e] using sum_sq_eigenbasis_repr_equiv_eq_one hH z hunit
  have hquad :=
    quadForm_eq_sum_eigenvalues (M := M) hH z
  rw [hquad]
  calc
    hH.eigenvalues₀ j =
        ∑ i : Fin (Fintype.card ι), hH.eigenvalues₀ j * c i := by
          rw [← Finset.mul_sum, hcoords_sum, mul_one]
    _ ≤ ∑ i : Fin (Fintype.card ι), hH.eigenvalues (e i) * c i := by
          refine Finset.sum_le_sum ?_
          intro i _
          by_cases hij : j < i
          · have hc0 : c i = 0 := by
              have hz : hH.eigenvectorBasis.repr z (e i) = 0 := by
                simpa [e] using hzero i hij
              simp [c, hz]
            rw [hc0, mul_zero, mul_zero]
          · have hij' : i ≤ j := le_of_not_gt hij
            have heig :
                hH.eigenvalues₀ j ≤ hH.eigenvalues (e i) := by
              simpa [e] using
                hH.eigenvalues₀_antitone hij'
            exact mul_le_mul_of_nonneg_right heig (sq_nonneg _)
    _ = ∑ i : ι, hH.eigenvalues i *
        (hH.eigenvectorBasis.repr z i) ^ 2 := by
          simpa [c, e] using
            (Equiv.sum_comp
              (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card ι)))
              (fun i : ι =>
                hH.eigenvalues i * (hH.eigenvectorBasis.repr z i) ^ 2))

/-- Ritz upper interlacing for an orthonormal-column compression of a real
Hermitian matrix.

For `Hᵀ H = I` and every ordered compression eigenvalue, the corresponding
ordered eigenvalue of `Hᵀ M H` is at most the same leading ordered eigenvalue
of `M`. The proof uses rank-nullity to intersect the image under `H` of the
first `j + 1` compression eigendirections with the subspace orthogonal to the
first `j` eigendirections of `M`. -/
theorem hermitian_compression_ordered_eigenvalue_le
    {q r : Type*} [Fintype q] [Fintype r] [DecidableEq q] [DecidableEq r]
    {M : Matrix q q ℝ} (hM : M.IsHermitian)
    (H : Matrix q r ℝ) (hH : Hᵀ * H = 1)
    (hcard : Fintype.card r ≤ Fintype.card q)
    (j : Fin (Fintype.card r)) :
    let hC : (Hᵀ * M * H).IsHermitian := by
      simpa [Matrix.conjTranspose, Matrix.star_apply] using
        Matrix.isHermitian_conjTranspose_mul_mul H hM
    hC.eigenvalues₀ j ≤ hM.eigenvalues₀ (Fin.castLE hcard j) := by
  classical
  let C : Matrix r r ℝ := Hᵀ * M * H
  have hC : C.IsHermitian := by
    simpa [C, Matrix.conjTranspose, Matrix.star_apply] using
      Matrix.isHermitian_conjTranspose_mul_mul H hM
  let eC : Fin (Fintype.card r) ≃ r :=
    Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card r))
  let eM : Fin (Fintype.card q) ≃ q :=
    Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card q))
  have hjr : j.val + 1 ≤ Fintype.card r := Nat.succ_le_iff.mpr j.isLt
  have hjq : j.val ≤ Fintype.card q :=
    (Nat.le_of_lt j.isLt).trans hcard
  let vC : Fin (j.val + 1) → EuclideanSpace ℝ r := fun k =>
    hC.eigenvectorBasis (eC (Fin.castLE hjr k))
  let HvC : Fin (j.val + 1) → EuclideanSpace ℝ q := fun k =>
    Matrix.toEuclideanLin H (vC k)
  let A : Matrix (Fin j.val) (Fin (j.val + 1)) ℝ := fun i k =>
    hM.eigenvectorBasis.repr (HvC k) (eM (Fin.castLE hjq i))
  have hdim :
      Module.finrank ℝ (Fin j.val → ℝ) <
        Module.finrank ℝ (Fin (j.val + 1) → ℝ) := by
    simpa only [Module.finrank_pi, Fintype.card_fin] using Nat.lt_succ_self j.val
  have hker : LinearMap.ker A.mulVecLin ≠ ⊥ :=
    LinearMap.ker_ne_bot_of_finrank_lt hdim
  obtain ⟨a, haKer, ha0⟩ := (Submodule.ne_bot_iff _).mp hker
  have haMul : A *ᵥ a = 0 := by
    simpa only [LinearMap.mem_ker, Matrix.mulVecLin_apply] using haKer
  let x : EuclideanSpace ℝ r := (Fintype.linearCombination ℝ vC) a
  have hvorth : Orthonormal ℝ vC := by
    exact hC.eigenvectorBasis.orthonormal.comp
      (fun k : Fin (j.val + 1) => eC (Fin.castLE hjr k))
      (eC.injective.comp (Fin.castLE_injective hjr))
  have hx0 : x ≠ 0 := by
    intro hx
    apply ha0
    apply hvorth.linearIndependent.fintypeLinearCombination_injective
    simpa [x] using hx
  let u : EuclideanSpace ℝ r := ‖x‖⁻¹ • x
  have hunorm : ‖u‖ = 1 := by
    simpa [u] using norm_smul_inv_norm hx0
  have huunit : (u : r → ℝ) ⬝ᵥ (u : r → ℝ) = 1 := by
    have hnormsq := EuclideanSpace.real_norm_sq_eq u
    rw [hunorm] at hnormsq
    simpa [dotProduct, pow_two] using hnormsq.symm
  have huzeroAfter : ∀ i : Fin (Fintype.card r), j < i →
      hC.eigenvectorBasis.repr u (eC i) = 0 := by
    intro i hij
    rw [OrthonormalBasis.repr_apply_apply]
    have hinnerx : inner ℝ (hC.eigenvectorBasis (eC i)) x = 0 := by
      change inner ℝ (hC.eigenvectorBasis (eC i))
        ((Fintype.linearCombination ℝ vC) a) = 0
      rw [Fintype.linearCombination_apply, inner_sum]
      refine Finset.sum_eq_zero (fun k _ => ?_)
      have hne : eC i ≠ eC (Fin.castLE hjr k) := by
        apply eC.injective.ne
        intro hieq
        have hik : i = Fin.castLE hjr k := Fin.ext (Fin.ext_iff.mp hieq)
        have hle : (i : ℕ) ≤ j := by
          rw [hik]
          exact Nat.le_of_lt_succ k.isLt
        exact (not_le_of_gt hij) hle
      rw [real_inner_smul_right]
      have hinner : inner ℝ (hC.eigenvectorBasis (eC i)) (vC k) = 0 := by
        change inner ℝ (hC.eigenvectorBasis (eC i))
          (hC.eigenvectorBasis (eC (Fin.castLE hjr k))) = 0
        exact hC.eigenvectorBasis.orthonormal.inner_eq_zero hne
      rw [hinner, mul_zero]
    change inner ℝ (hC.eigenvectorBasis (eC i)) (‖x‖⁻¹ • x) = 0
    rw [real_inner_smul_right, hinnerx, mul_zero]
  have hHx : Matrix.toEuclideanLin H x = ∑ k, a k • HvC k := by
    change Matrix.toEuclideanLin H ((Fintype.linearCombination ℝ vC) a) = _
    rw [Fintype.linearCombination_apply, map_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [map_smul]
  have hHxzeroBefore : ∀ i : Fin j.val,
      hM.eigenvectorBasis.repr (Matrix.toEuclideanLin H x)
        (eM (Fin.castLE hjq i)) = 0 := by
    intro i
    have hrow := congrFun haMul i
    change ∑ k, A i k * a k = 0 at hrow
    have hrepr :
        hM.eigenvectorBasis.repr (Matrix.toEuclideanLin H x) =
          ∑ k, a k • hM.eigenvectorBasis.repr (HvC k) := by
      rw [hHx, map_sum]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [map_smul]
    have hcoord := congrArg
      (fun y : EuclideanSpace ℝ q => (y : q → ℝ) (eM (Fin.castLE hjq i))) hrepr
    calc
      hM.eigenvectorBasis.repr (Matrix.toEuclideanLin H x)
          (eM (Fin.castLE hjq i)) =
          ∑ k, a k * hM.eigenvectorBasis.repr (HvC k)
            (eM (Fin.castLE hjq i)) := by
              simpa only [WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply,
                Pi.smul_apply, smul_eq_mul] using hcoord
      _ = ∑ k, A i k * a k := by
              refine Finset.sum_congr rfl (fun k _ => ?_)
              change a k * A i k = A i k * a k
              ring
      _ = 0 := hrow
  let z : EuclideanSpace ℝ q := Matrix.toEuclideanLin H u
  have hzunit : (z : q → ℝ) ⬝ᵥ (z : q → ℝ) = 1 := by
    change (H *ᵥ (u : r → ℝ)) ⬝ᵥ (H *ᵥ (u : r → ℝ)) = 1
    calc
      (H *ᵥ (u : r → ℝ)) ⬝ᵥ (H *ᵥ (u : r → ℝ)) =
          (H *ᵥ (u : r → ℝ)) ⬝ᵥ
            ((1 : Matrix q q ℝ) *ᵥ (H *ᵥ (u : r → ℝ))) := by simp
      _ = (u : r → ℝ) ⬝ᵥ
          ((Hᵀ * (1 : Matrix q q ℝ) * H) *ᵥ (u : r → ℝ)) := by
            exact quadraticForm_mulVec_eq_pullback_rect
              H (1 : Matrix q q ℝ) (u : r → ℝ)
      _ = (u : r → ℝ) ⬝ᵥ (u : r → ℝ) := by
            simp [hH]
      _ = 1 := huunit
  have hzscale : z = ‖x‖⁻¹ • Matrix.toEuclideanLin H x := by
    change Matrix.toEuclideanLin H (‖x‖⁻¹ • x) = _
    rw [map_smul]
  have hzzeroBefore : ∀ i : Fin (Fintype.card q), i < Fin.castLE hcard j →
      hM.eigenvectorBasis.repr z (eM i) = 0 := by
    intro i hij
    let i' : Fin j.val := ⟨i.val, by simpa using hij⟩
    have hiCast : Fin.castLE hjq i' = i := by
      ext
      rfl
    have hxzero : hM.eigenvectorBasis.repr (Matrix.toEuclideanLin H x) (eM i) = 0 := by
      simpa [hiCast] using hHxzeroBefore i'
    rw [hzscale, map_smul]
    change ‖x‖⁻¹ *
      hM.eigenvectorBasis.repr (Matrix.toEuclideanLin H x) (eM i) = 0
    rw [hxzero, mul_zero]
  have hlower := ordered_eigenvalue_le_quadForm_of_unit_of_zero_after
    (M := C) hC j u huunit huzeroAfter
  have hupper := quadForm_le_ordered_eigenvalue_of_unit_of_zero_before
    (M := M) hM (Fin.castLE hcard j) z hzunit hzzeroBefore
  calc
    hC.eigenvalues₀ j ≤ (u : r → ℝ) ⬝ᵥ (C *ᵥ (u : r → ℝ)) := hlower
    _ = (z : q → ℝ) ⬝ᵥ (M *ᵥ (z : q → ℝ)) := by
      symm
      simpa [C, z] using
        quadraticForm_mulVec_eq_pullback_rect H M (u : r → ℝ)
    _ ≤ hM.eigenvalues₀ (Fin.castLE hcard j) := hupper

private lemma det_one_sub_eq_prod_one_sub_ordered_eigenvalues
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} (hA : A.IsHermitian) :
    (1 - A).det =
      ∏ j : Fin (Fintype.card ι), (1 - hA.eigenvalues₀ j) := by
  classical
  let e : Fin (Fintype.card ι) ≃ ι :=
    Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card ι))
  calc
    (1 - A).det = A.charpoly.eval 1 := by
      rw [Matrix.eval_charpoly]
      simp
    _ = (∏ i : ι,
        (Polynomial.X - Polynomial.C (hA.eigenvalues i))).eval 1 := by
      rw [hA.charpoly_eq]
      simp only [RCLike.ofReal_real_eq_id, id]
    _ = ∏ i : ι, (1 - hA.eigenvalues i) := by
      rw [Polynomial.eval_prod]
      simp
    _ = ∏ j : Fin (Fintype.card ι),
        (1 - hA.eigenvalues (e j)) := by
      exact (Equiv.prod_comp e (fun i : ι => 1 - hA.eigenvalues i)).symm
    _ = ∏ j : Fin (Fintype.card ι),
        (1 - hA.eigenvalues₀ j) := by
      apply Finset.prod_congr rfl
      intro j _
      simp [e]

private lemma one_sub_ordered_eigenvalue_nonneg_of_one_sub_posSemidef
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} (hA : A.IsHermitian)
    (hIA : (1 - A).PosSemidef)
    (j : Fin (Fintype.card ι)) :
    0 ≤ 1 - hA.eigenvalues₀ j := by
  classical
  let e : Fin (Fintype.card ι) ≃ ι :=
    Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card ι))
  let v : ι → ℝ := hA.eigenvectorBasis (e j)
  have hvunit : v ⬝ᵥ v = 1 := by
    have hv :=
      (orthonormal_iff_ite.mp hA.eigenvectorBasis.orthonormal) (e j) (e j)
    simpa [v] using hv
  have heig : A *ᵥ v = hA.eigenvalues (e j) • v := by
    simpa [v] using hA.mulVec_eigenvectorBasis (e j)
  have hnonneg : 0 ≤ v ⬝ᵥ ((1 - A) *ᵥ v) := by
    simpa using hIA.dotProduct_mulVec_nonneg v
  calc
    0 ≤ v ⬝ᵥ ((1 - A) *ᵥ v) := hnonneg
    _ = v ⬝ᵥ (v - A *ᵥ v) := by rw [Matrix.sub_mulVec, Matrix.one_mulVec]
    _ = v ⬝ᵥ v - v ⬝ᵥ (A *ᵥ v) := dotProduct_sub v v (A *ᵥ v)
    _ = 1 - v ⬝ᵥ (hA.eigenvalues (e j) • v) := by rw [hvunit, heig]
    _ = 1 - hA.eigenvalues (e j) := by simp [dotProduct_smul, hvunit]
    _ = 1 - hA.eigenvalues₀ j := by
      simp [e]

/-- Complement-determinant lower bound for an orthonormal-column Hermitian
compression.

If both `M` and `I - M` are positive semidefinite, then the product of the
complements of the leading `card r` ordered eigenvalues of `M` is at most
`det (I - Hᵀ M H)` for every `H` with orthonormal columns. Mathlib's
`eigenvalues₀` are nonincreasing, so Ritz upper interlacing reverses after
subtracting from one. -/
theorem prod_one_sub_ordered_eigenvalues_le_det_one_sub_compression
    {q r : Type*} [Fintype q] [Fintype r] [DecidableEq q] [DecidableEq r]
    {M : Matrix q q ℝ} (hM : M.PosSemidef)
    (hIM : (1 - M).PosSemidef)
    (H : Matrix q r ℝ) (hH : Hᵀ * H = 1)
    (hcard : Fintype.card r ≤ Fintype.card q) :
    ∏ j : Fin (Fintype.card r),
        (1 - hM.1.eigenvalues₀ (Fin.castLE hcard j)) ≤
      (1 - Hᵀ * M * H).det := by
  classical
  let C : Matrix r r ℝ := Hᵀ * M * H
  have hC : C.PosSemidef := by
    have hcomp := hM.conjTranspose_mul_mul_same H
    simpa [C, Matrix.conjTranspose, Matrix.star_apply] using hcomp
  have hEigLe : ∀ j : Fin (Fintype.card r),
      hC.1.eigenvalues₀ j ≤
        hM.1.eigenvalues₀ (Fin.castLE hcard j) := by
    intro j
    simpa [C] using
      (hermitian_compression_ordered_eigenvalue_le hM.1 H hH hcard j)
  have hFactorNonneg : ∀ j : Fin (Fintype.card r),
      0 ≤ 1 - hM.1.eigenvalues₀ (Fin.castLE hcard j) := by
    intro j
    exact one_sub_ordered_eigenvalue_nonneg_of_one_sub_posSemidef
      hM.1 hIM (Fin.castLE hcard j)
  have hprod :
      ∏ j : Fin (Fintype.card r),
          (1 - hM.1.eigenvalues₀ (Fin.castLE hcard j)) ≤
        ∏ j : Fin (Fintype.card r),
          (1 - hC.1.eigenvalues₀ j) :=
    Finset.prod_le_prod
      (fun j _ => hFactorNonneg j)
      (fun j _ => sub_le_sub_left (hEigLe j) 1)
  rw [← det_one_sub_eq_prod_one_sub_ordered_eigenvalues hC.1] at hprod
  exact hprod

/-- Reindexed form of
`prod_one_sub_ordered_eigenvalues_le_det_one_sub_compression` for APIs whose
selected eigenvalues are indexed by the compression column type itself. -/
theorem prod_one_sub_ordered_eigenvalues_le_det_one_sub_compression_reindex
    {q r : Type*} [Fintype q] [Fintype r] [DecidableEq q] [DecidableEq r]
    {M : Matrix q q ℝ} (hM : M.PosSemidef)
    (hIM : (1 - M).PosSemidef)
    (H : Matrix q r ℝ) (hH : Hᵀ * H = 1)
    (hcard : Fintype.card r ≤ Fintype.card q) :
    ∏ j : r,
        (1 - hM.1.eigenvalues₀
          (Fin.castLE hcard ((Fintype.equivFin r) j))) ≤
      (1 - Hᵀ * M * H).det := by
  have hbound :=
    prod_one_sub_ordered_eigenvalues_le_det_one_sub_compression
      hM hIM H hH hcard
  rw [← Equiv.prod_comp (Fintype.equivFin r)
    (fun j : Fin (Fintype.card r) =>
      1 - hM.1.eigenvalues₀ (Fin.castLE hcard j))] at hbound
  exact hbound

private lemma sum_fin_filter_lt_eq_sum_castLE
    {n m : ℕ} (hmn : m ≤ n) (f : Fin n → ℝ) :
    (Finset.univ.filter (fun i : Fin n => (i : ℕ) < m)).sum f =
      ∑ j : Fin m, f (Fin.castLE hmn j) := by
  classical
  have hfilter :
      Finset.univ.filter (fun i : Fin n => (i : ℕ) < m) =
        Finset.univ.map (Fin.castLEEmb hmn) := by
    ext i
    constructor
    · intro hi
      have hi' : (i : ℕ) < m := by simpa using (Finset.mem_filter.mp hi).2
      refine Finset.mem_map.mpr ?_
      refine ⟨⟨i, hi'⟩, Finset.mem_univ _, ?_⟩
      ext
      simp
    · intro hi
      rcases Finset.mem_map.mp hi with ⟨j, _hj, rfl⟩
      simp
  rw [hfilter]
  exact Finset.sum_map Finset.univ (Fin.castLEEmb hmn) f

private lemma antitone_weighted_sum_le_sum_largest
    {n m : ℕ} (hmn : m ≤ n) (a w : Fin n → ℝ)
    (ha : Antitone a)
    (hw0 : ∀ i, 0 ≤ w i)
    (hw1 : ∀ i, w i ≤ 1)
    (hsum : ∑ i : Fin n, w i = (m : ℝ)) :
    ∑ i : Fin n, a i * w i ≤
      ∑ j : Fin m, a (Fin.castLE hmn j) := by
  classical
  by_cases hm0 : m = 0
  · subst m
    have hw_zero : ∀ i : Fin n, w i = 0 := by
      intro i
      have hle_sum : w i ≤ ∑ x : Fin n, w x :=
        Finset.single_le_sum (fun x _ => hw0 x) (Finset.mem_univ i)
      rw [hsum] at hle_sum
      have hle0 : w i ≤ 0 := by simpa using hle_sum
      exact le_antisymm hle0 (hw0 i)
    simp [hw_zero]
  · have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
    have hnpos : 0 < n := hmpos.trans_le hmn
    let t : Fin n := ⟨m - 1, by omega⟩
    let p : Fin n → Prop := fun i => (i : ℕ) < m
    have hhead_one :
        (Finset.univ.filter p).sum (fun _ : Fin n => (1 : ℝ)) = (m : ℝ) := by
      rw [show (Finset.univ.filter p).sum (fun _ : Fin n => (1 : ℝ)) =
          (Finset.univ.filter (fun i : Fin n => (i : ℕ) < m)).sum
            (fun _ : Fin n => (1 : ℝ)) by rfl]
      rw [sum_fin_filter_lt_eq_sum_castLE hmn (fun _ : Fin n => (1 : ℝ))]
      simp
    have hsplit_w :
        (Finset.univ.filter p).sum w +
          (Finset.univ.filter (fun i : Fin n => ¬ p i)).sum w = (m : ℝ) := by
      rw [Finset.sum_filter_add_sum_filter_not Finset.univ p w, hsum]
    have hhead_bound :
        ∀ i : Fin n, p i →
          a i * w i ≤ a i + a t * (w i - 1) := by
      intro i hi
      have hit : i ≤ t := by
        simp only [p] at hi
        exact Fin.le_def.mpr (by change (i : ℕ) ≤ m - 1; omega)
      have hat : a t ≤ a i := ha hit
      have hwneg : w i - 1 ≤ 0 := sub_nonpos.mpr (hw1 i)
      have hmul : a i * (w i - 1) ≤ a t * (w i - 1) :=
        mul_le_mul_of_nonpos_right hat hwneg
      calc
        a i * w i = a i + a i * (w i - 1) := by ring
        _ ≤ a i + a t * (w i - 1) := by
              simpa [add_comm, add_left_comm, add_assoc] using
                add_le_add_left hmul (a i)
    have htail_bound :
        ∀ i : Fin n, ¬ p i → a i * w i ≤ a t * w i := by
      intro i hi
      have hti : t ≤ i := by
        simp only [p] at hi
        exact Fin.le_def.mpr (by change m - 1 ≤ (i : ℕ); omega)
      exact mul_le_mul_of_nonneg_right (ha hti) (hw0 i)
    calc
      ∑ i : Fin n, a i * w i
          = (Finset.univ.filter p).sum (fun i => a i * w i) +
              (Finset.univ.filter (fun i : Fin n => ¬ p i)).sum
                (fun i => a i * w i) := by
                rw [Finset.sum_filter_add_sum_filter_not Finset.univ p
                  (fun i => a i * w i)]
      _ ≤ (Finset.univ.filter p).sum (fun i => a i + a t * (w i - 1)) +
              (Finset.univ.filter (fun i : Fin n => ¬ p i)).sum (fun i => a t * w i) := by
                exact add_le_add
                  (Finset.sum_le_sum (fun i hi => hhead_bound i
                    (by simpa using (Finset.mem_filter.mp hi).2)))
                  (Finset.sum_le_sum (fun i hi => htail_bound i
                    (by simpa using (Finset.mem_filter.mp hi).2)))
      _ = (Finset.univ.filter p).sum a := by
        rw [Finset.sum_add_distrib]
        have htail :
            (Finset.univ.filter (fun x : Fin n => ¬ p x)).sum w =
              (m : ℝ) - (Finset.univ.filter p).sum w := by
          linarith
        calc
          (Finset.univ.filter p).sum a +
              (Finset.univ.filter p).sum (fun i => a t * (w i - 1)) +
              (Finset.univ.filter (fun i : Fin n => ¬ p i)).sum (fun i => a t * w i)
              = (Finset.univ.filter p).sum a +
                  a t * (((Finset.univ.filter p).sum w - (m : ℝ)) +
                    (Finset.univ.filter (fun i : Fin n => ¬ p i)).sum w) := by
                  rw [← Finset.mul_sum, ← Finset.mul_sum]
                  rw [Finset.sum_sub_distrib]
                  rw [show (Finset.univ.filter p).sum (fun _ : Fin n => (1 : ℝ)) = (m : ℝ)
                    from hhead_one]
                  ring
          _ = (Finset.univ.filter p).sum a := by
                  rw [htail]
                  ring
      _ = ∑ j : Fin m, a (Fin.castLE hmn j) := by
        rw [show (Finset.univ.filter p).sum a =
          (Finset.univ.filter (fun i : Fin n => (i : ℕ) < m)).sum a by rfl]
        exact sum_fin_filter_lt_eq_sum_castLE hmn a

private lemma matrix_columns_orthonormal_of_transpose_mul_eq_one
    {ι κ : Type*} [Fintype ι] [DecidableEq κ]
    (G : Matrix ι κ ℝ) (hG : Gᵀ * G = 1) :
    Orthonormal ℝ
      (fun j : κ => (WithLp.toLp 2 (fun i : ι => G i j) : EuclideanSpace ℝ ι)) := by
  classical
  rw [orthonormal_iff_ite]
  intro i j
  have hij := congrFun (congrFun hG i) j
  rw [Matrix.mul_apply] at hij
  calc
    inner ℝ
        (WithLp.toLp 2 (fun a : ι => G a i) : EuclideanSpace ℝ ι)
        (WithLp.toLp 2 (fun a : ι => G a j) : EuclideanSpace ℝ ι)
        = ∑ a : ι, G a i * G a j := by
          change (fun a : ι => G a j) ⬝ᵥ (fun a : ι => G a i) =
            ∑ a : ι, G a i * G a j
          rw [dotProduct_comm]
          rfl
    _ = if i = j then 1 else 0 := by
          simpa [Matrix.transpose_apply] using hij

/-- Ky Fan trace inequality for real Hermitian matrices, in finite-dimensional
matrix-coordinate form.

For any matrix `G` with orthonormal columns, the sum of Hermitian quadratic
forms along those columns is bounded by the sum of the leading ordered
eigenvalues. This is the reusable deterministic spectral result behind Hansen
Theorem 11.9's factor-PCA optimizer. -/
theorem hermitian_sum_column_quadratic_le_sum_largest_eigenvalues
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    {M : Matrix ι ι ℝ} (hM : M.IsHermitian)
    (hcard : Fintype.card κ ≤ Fintype.card ι)
    (G : Matrix ι κ ℝ) (hG : Gᵀ * G = 1) :
    ∑ j : κ, (fun a => G a j) ⬝ᵥ (M *ᵥ fun a => G a j) ≤
      ∑ j : κ, hM.eigenvalues₀
        (Fin.castLE hcard ((Fintype.equivFin κ) j)) := by
  classical
  let n := Fintype.card ι
  let m := Fintype.card κ
  let e : Fin n ≃ ι := Fintype.equivOfCardEq (Fintype.card_fin n)
  let col : κ → EuclideanSpace ℝ ι := fun j =>
    WithLp.toLp 2 (fun a : ι => G a j)
  let w : Fin n → ℝ := fun i =>
    ∑ j : κ, (hM.eigenvectorBasis.repr (col j) (e i)) ^ 2
  have horth := matrix_columns_orthonormal_of_transpose_mul_eq_one G hG
  have hw0 : ∀ i : Fin n, 0 ≤ w i := by
    intro i
    exact Finset.sum_nonneg (fun j _ => sq_nonneg _)
  have hw1 : ∀ i : Fin n, w i ≤ 1 := by
    intro i
    have hbessel := horth.sum_inner_products_le
      (s := Finset.univ) (x := hM.eigenvectorBasis (e i))
    have hnorm : ‖hM.eigenvectorBasis (e i)‖ ^ 2 = (1 : ℝ) := by
      have hnorm1 := hM.eigenvectorBasis.orthonormal.norm_eq_one (e i)
      rw [hnorm1]
      norm_num
    rw [hnorm] at hbessel
    have hbessel' :
        ∑ j : κ, inner ℝ (hM.eigenvectorBasis (e i)) (col j) ^ 2 ≤ 1 := by
      calc
        ∑ j : κ, inner ℝ (hM.eigenvectorBasis (e i)) (col j) ^ 2
            = ∑ j : κ, ‖inner ℝ (col j) (hM.eigenvectorBasis (e i))‖ ^ 2 := by
                refine Finset.sum_congr rfl ?_
                intro j _
                rw [real_inner_comm (col j) (hM.eigenvectorBasis (e i))]
                simp [Real.norm_eq_abs, sq_abs]
        _ ≤ ‖hM.eigenvectorBasis (e i)‖ ^ 2 := by
                simpa using hbessel
        _ = 1 := hnorm
    simpa [w, col, OrthonormalBasis.repr_apply_apply] using hbessel'
  have hsum_w : ∑ i : Fin n, w i = (m : ℝ) := by
    calc
      ∑ i : Fin n, w i
          = ∑ j : κ, ∑ i : Fin n,
              (hM.eigenvectorBasis.repr (col j) (e i)) ^ 2 := by
              rw [Finset.sum_comm]
      _ = ∑ j : κ, ∑ a : ι,
              (hM.eigenvectorBasis.repr (col j) a) ^ 2 := by
              refine Finset.sum_congr rfl ?_
              intro j _
              simpa [e] using
                (Equiv.sum_comp e
                  (fun a : ι => (hM.eigenvectorBasis.repr (col j) a) ^ 2))
      _ = ∑ j : κ, ‖col j‖ ^ 2 := by
              refine Finset.sum_congr rfl ?_
              intro j _
              simpa [OrthonormalBasis.repr_apply_apply] using
                (OrthonormalBasis.sum_sq_inner_right hM.eigenvectorBasis (col j))
      _ = ∑ _j : κ, (1 : ℝ) := by
              refine Finset.sum_congr rfl ?_
              intro j _
              have hnorm1 := horth.norm_eq_one j
              rw [hnorm1]
              norm_num
      _ = (m : ℝ) := by
              simp [m]
  have hleft_eq :
      ∑ j : κ, (fun a => G a j) ⬝ᵥ (M *ᵥ fun a => G a j) =
        ∑ i : Fin n, hM.eigenvalues₀ i * w i := by
    calc
      ∑ j : κ, (fun a => G a j) ⬝ᵥ (M *ᵥ fun a => G a j)
          = ∑ j : κ, ∑ a : ι,
              hM.eigenvalues a * (hM.eigenvectorBasis.repr (col j) a) ^ 2 := by
              refine Finset.sum_congr rfl ?_
              intro j _
              simpa [col] using
                quadForm_eq_sum_eigenvalues (M := M) hM (col j)
      _ = ∑ j : κ, ∑ i : Fin n,
              hM.eigenvalues (e i) *
                (hM.eigenvectorBasis.repr (col j) (e i)) ^ 2 := by
              refine Finset.sum_congr rfl ?_
              intro j _
              simpa [e] using
                (Equiv.sum_comp e
                  (fun a : ι =>
                    hM.eigenvalues a * (hM.eigenvectorBasis.repr (col j) a) ^ 2)).symm
      _ = ∑ j : κ, ∑ i : Fin n,
              hM.eigenvalues₀ i *
                (hM.eigenvectorBasis.repr (col j) (e i)) ^ 2 := by
              refine Finset.sum_congr rfl ?_
              intro j _
              refine Finset.sum_congr rfl ?_
              intro i _
              change hM.eigenvalues
                  ((Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card ι))) i) * _ = _
              rw [hermitian_eigenvalues_equivOfCardEq hM i]
      _ = ∑ i : Fin n, hM.eigenvalues₀ i * w i := by
              rw [Finset.sum_comm]
              refine Finset.sum_congr rfl ?_
              intro i _
              simp [w, Finset.mul_sum]
  rw [hleft_eq]
  have hscalar := antitone_weighted_sum_le_sum_largest
    (n := n) (m := m) hcard hM.eigenvalues₀ w
    hM.eigenvalues₀_antitone hw0 hw1 hsum_w
  refine hscalar.trans_eq ?_
  simpa [m] using
    (Equiv.sum_comp (Fintype.equivFin κ)
      (fun j : Fin m => hM.eigenvalues₀ (Fin.castLE hcard j))).symm

/-- For a Hermitian idempotent real matrix, the number of indices whose eigenvalue is `1`
equals the rank of the matrix. -/
lemma card_eigenvalue_one_eq_rank_of_isHermitian_idempotent
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M : Matrix ι ι ℝ}
    (hH : M.IsHermitian) (hI : IsIdempotentElem M) :
    (Finset.univ.filter (fun i : ι => hH.eigenvalues i = 1)).card = M.rank := by
  rw [← Fintype.card_subtype]
  exact (rank_eq_card_eigenvalues_eq_one_of_isHermitian_idempotent hH hI).symm

/-- If the square Gram-type matrix `A' Q A` is positive definite, then the
rectangular population moment map `Q A` has full column rank. -/
theorem matrix_mul_mulVec_injective_of_transpose_mul_mul_posDef
    {l k : Type*} [Fintype l] [Fintype k]
    (Q : Matrix l l ℝ) (A : Matrix l k ℝ)
    (h : (Aᵀ * Q * A).PosDef) :
    Function.Injective (Q * A).mulVec := by
  classical
  have hGram : Function.Injective (Aᵀ * Q * A).mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr h.isUnit
  intro x y hxy
  apply hGram
  have hleft := congrArg (fun z : l → ℝ => Aᵀ *ᵥ z) hxy
  simpa [Matrix.mul_assoc, Matrix.mulVec_mulVec] using hleft

end HansenEconometrics
