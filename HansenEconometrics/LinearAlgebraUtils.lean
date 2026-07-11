import Mathlib.Data.Real.StarOrdered
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Order.Fin.Tuple
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

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
  simpa [gram_transpose (X := X)] using
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

/-- Pull a quadratic form through a fixed matrix map. -/
lemma quadraticForm_mulVec_eq_pullback
    {ι : Type*} [Fintype ι]
    (B A : Matrix ι ι ℝ) (x : ι → ℝ) :
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
theorem gram_le_gram_of_mulVec_norm_sq_le
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

/-- Spectral expansion of the quadratic form `z ⬝ᵥ M *ᵥ z` in the eigenbasis of a
Hermitian real matrix: it equals the sum of eigenvalues times squared basis coordinates. -/
lemma quadForm_eq_sum_eigenvalues
    {n : ℕ} {M : Matrix (Fin n) (Fin n) ℝ} (hH : M.IsHermitian)
    (z : EuclideanSpace ℝ (Fin n)) :
    (z : Fin n → ℝ) ⬝ᵥ (M *ᵥ (z : Fin n → ℝ))
      = ∑ i, hH.eigenvalues i * (hH.eigenvectorBasis.repr z i) ^ 2 := by
  set b := hH.eigenvectorBasis with hb_def
  -- Write (z : Fin n → ℝ) as a sum in the eigenbasis.
  have hz_coord : (z : Fin n → ℝ) = ∑ i, b.repr z i • ((b i : Fin n → ℝ)) := by
    have hsum : z = ∑ i, b.repr z i • b i := (b.sum_repr z).symm
    have : ((z : EuclideanSpace ℝ (Fin n)) : Fin n → ℝ)
        = (((∑ i, b.repr z i • b i) : EuclideanSpace ℝ (Fin n)) : Fin n → ℝ) :=
      congrArg _ hsum
    rw [this, WithLp.ofLp_sum]
    rfl
  -- Apply M to that sum; linearity + eigenvector identity.
  have hMz_coord : M *ᵥ (z : Fin n → ℝ)
      = ∑ i, (b.repr z i * hH.eigenvalues i) • ((b i : Fin n → ℝ)) := by
    rw [hz_coord, Matrix.mulVec_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Matrix.mulVec_smul, hH.mulVec_eigenvectorBasis, smul_smul]
  -- Orthonormality of the eigenbasis as `Fin n → ℝ` vectors. For real scalars the inner
  -- product coincides with the flipped dot product: `⟪x, y⟫_ℝ = y ⬝ᵥ x`.
  have hinner_eq_dot : ∀ x y : EuclideanSpace ℝ (Fin n),
      @inner ℝ (EuclideanSpace ℝ (Fin n)) _ x y = ((y : Fin n → ℝ)) ⬝ᵥ ((x : Fin n → ℝ)) :=
    fun _ _ => rfl
  have horth : ∀ i j : Fin n,
      ((b i : Fin n → ℝ)) ⬝ᵥ ((b j : Fin n → ℝ)) = if i = j then (1 : ℝ) else 0 := by
    intro i j
    rw [dotProduct_comm, ← hinner_eq_dot]
    have := (orthonormal_iff_ite.mp b.orthonormal) i j
    simpa using this
  -- Expand the dot product step by step.
  rw [hMz_coord, hz_coord, sum_dotProduct]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [smul_dotProduct, dotProduct_sum, smul_eq_mul]
  have step : ∀ j, (b i : Fin n → ℝ) ⬝ᵥ ((b.repr z j * hH.eigenvalues j) • (b j : Fin n → ℝ))
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

/-- Finite-index version of `quadForm_eq_sum_eigenvalues`. -/
lemma quadForm_eq_sum_eigenvalues_fintype
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M : Matrix ι ι ℝ} (hH : M.IsHermitian)
    (z : EuclideanSpace ℝ ι) :
    (z : ι → ℝ) ⬝ᵥ (M *ᵥ (z : ι → ℝ))
      = ∑ i, hH.eigenvalues i * (hH.eigenvectorBasis.repr z i) ^ 2 := by
  set b := hH.eigenvectorBasis with hb_def
  have hz_coord : (z : ι → ℝ) = ∑ i, b.repr z i • ((b i : ι → ℝ)) := by
    have hsum : z = ∑ i, b.repr z i • b i := (b.sum_repr z).symm
    have : ((z : EuclideanSpace ℝ ι) : ι → ℝ)
        = (((∑ i, b.repr z i • b i) : EuclideanSpace ℝ ι) : ι → ℝ) :=
      congrArg _ hsum
    rw [this, WithLp.ofLp_sum]
    rfl
  have hMz_coord : M *ᵥ (z : ι → ℝ)
      = ∑ i, (b.repr z i * hH.eigenvalues i) • ((b i : ι → ℝ)) := by
    rw [hz_coord, Matrix.mulVec_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Matrix.mulVec_smul, hH.mulVec_eigenvectorBasis, smul_smul]
  have hinner_eq_dot : ∀ x y : EuclideanSpace ℝ ι,
      @inner ℝ (EuclideanSpace ℝ ι) _ x y = ((y : ι → ℝ)) ⬝ᵥ ((x : ι → ℝ)) :=
    fun _ _ => rfl
  have horth : ∀ i j : ι,
      ((b i : ι → ℝ)) ⬝ᵥ ((b j : ι → ℝ)) = if i = j then (1 : ℝ) else 0 := by
    intro i j
    rw [dotProduct_comm, ← hinner_eq_dot]
    have := (orthonormal_iff_ite.mp b.orthonormal) i j
    simpa using this
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
  have hcoords_sum_k :
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
  have hcoords_sum : ∑ i : Fin (Fintype.card ι), c i = 1 := by
    calc
      ∑ i : Fin (Fintype.card ι), c i
          = ∑ i : ι, (hH.eigenvectorBasis.repr z i) ^ 2 := by
              simpa [c, e] using
                (Equiv.sum_comp
                  (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card ι)))
                  (fun i : ι => (hH.eigenvectorBasis.repr z i) ^ 2))
      _ = 1 := hcoords_sum_k
  have hquad :=
    quadForm_eq_sum_eigenvalues_fintype (M := M) hH z
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
              simpa [Matrix.IsHermitian.eigenvalues, e] using
                hH.eigenvalues₀_antitone hji
            exact mul_le_mul_of_nonneg_right heig (sq_nonneg _)
    _ = hH.eigenvalues₀ j := by
          rw [← Finset.mul_sum, hcoords_sum, mul_one]

/-- Rayleigh-quotient lower bound from a Hermitian spectral expansion.

If the coordinates after `j` in the ordered Hermitian eigenbasis are zero,
then the `j`th ordered eigenvalue bounds a unit vector's quadratic form from
below. This is the lower-bound counterpart used in Ritz interlacing. -/
lemma ordered_eigenvalue_le_quadForm_of_unit_of_zero_after
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
  have hcoords_sum_k :
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
  have hcoords_sum : ∑ i : Fin (Fintype.card ι), c i = 1 := by
    calc
      ∑ i : Fin (Fintype.card ι), c i
          = ∑ i : ι, (hH.eigenvectorBasis.repr z i) ^ 2 := by
              simpa [c, e] using
                (Equiv.sum_comp
                  (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card ι)))
                  (fun i : ι => (hH.eigenvectorBasis.repr z i) ^ 2))
      _ = 1 := hcoords_sum_k
  have hquad :=
    quadForm_eq_sum_eigenvalues_fintype (M := M) hH z
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
              simpa [Matrix.IsHermitian.eigenvalues, e] using
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
      simp [Matrix.IsHermitian.eigenvalues, e]

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
      simp [Matrix.IsHermitian.eigenvalues, e]

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
                quadForm_eq_sum_eigenvalues_fintype (M := M) hM (col j)
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
              simp [Matrix.IsHermitian.eigenvalues, e]
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
    {n : ℕ} {M : Matrix (Fin n) (Fin n) ℝ}
    (hH : M.IsHermitian) (hI : IsIdempotentElem M) :
    (Finset.univ.filter (fun i : Fin n => hH.eigenvalues i = 1)).card = M.rank := by
  -- Eigenvalues of a Hermitian idempotent real matrix are 0 or 1.
  have heig : ∀ i : Fin n, hH.eigenvalues i = 0 ∨ hH.eigenvalues i = 1 := fun i => by
    have hmem := hI.spectrum_subset ℝ (hH.eigenvalues_mem_spectrum_real i)
    simpa using hmem
  -- So the "= 1" predicate coincides with the "≠ 0" predicate.
  have hfilter_eq : Finset.univ.filter (fun i : Fin n => hH.eigenvalues i = 1)
      = Finset.univ.filter (fun i : Fin n => hH.eigenvalues i ≠ 0) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h; rw [h]; norm_num
    · exact (heig i).resolve_left
  rw [hfilter_eq, hH.rank_eq_card_non_zero_eigs, Fintype.card_subtype]

/-- Finite-index version of `card_eigenvalue_one_eq_rank_of_isHermitian_idempotent`. -/
lemma card_eigenvalue_one_eq_rank_of_isHermitian_idempotent_fintype
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M : Matrix ι ι ℝ}
    (hH : M.IsHermitian) (hI : IsIdempotentElem M) :
    (Finset.univ.filter (fun i : ι => hH.eigenvalues i = 1)).card = M.rank := by
  have heig : ∀ i : ι, hH.eigenvalues i = 0 ∨ hH.eigenvalues i = 1 := fun i => by
    have hmem := hI.spectrum_subset ℝ (hH.eigenvalues_mem_spectrum_real i)
    simpa using hmem
  have hfilter_eq : Finset.univ.filter (fun i : ι => hH.eigenvalues i = 1)
      = Finset.univ.filter (fun i : ι => hH.eigenvalues i ≠ 0) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h; rw [h]; norm_num
    · exact (heig i).resolve_left
  rw [hfilter_eq, hH.rank_eq_card_non_zero_eigs, Fintype.card_subtype]

end HansenEconometrics
