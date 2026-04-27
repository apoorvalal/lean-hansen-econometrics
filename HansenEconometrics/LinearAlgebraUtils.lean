import Mathlib

open scoped Matrix

namespace HansenEconometrics

open Matrix

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

/-- Hansen Theorem 3.3.1 helper: the Gram matrix `Xᵀ * X` is symmetric. Relocated here from
`Chapter3Projections.lean` so that earlier files (e.g., `Chapter3LeastSquaresAlgebra.lean`)
can use it without creating a circular import. -/
theorem gram_transpose {n k : Type*} [Fintype n] [Fintype k]
    (X : Matrix n k ℝ) :
    (Xᵀ * X)ᵀ = Xᵀ * X := by
  rw [Matrix.transpose_mul, Matrix.transpose_transpose]

/-- Left-multiplication by a row vector is right-multiplication by the transpose. -/
lemma vecMul_eq_mulVec_transpose {m n : Type*} [Fintype m]
    (M : Matrix m n ℝ) (x : m → ℝ) :
    Matrix.vecMul x M = Mᵀ *ᵥ x := by
  simpa using (Matrix.vecMul_transpose Mᵀ x)

/-- For a symmetric matrix, left-multiplication as a row vector agrees with right-multiplication
as a column vector. -/
lemma vecMul_eq_mulVec_of_transpose_eq_self {n : Type*} [Fintype n]
    (M : Matrix n n ℝ) (hM : Mᵀ = M) (x : n → ℝ) :
    Matrix.vecMul x M = M *ᵥ x := by
  simpa [hM] using vecMul_eq_mulVec_transpose M x

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

/-- For a real symmetric idempotent matrix, rank equals the natural-number value of the trace.
Eigenvalues of such a matrix are 0 or 1, so
rank = #{nonzero eigenvalues} = ∑ eigenvalues = trace. -/
theorem rank_eq_natCast_trace_of_isHermitian_idempotent {n : Type*} [Fintype n]
    {A : Matrix n n ℝ}
    (hH : A.IsHermitian)
    (hI : IsIdempotentElem A) :
    (A.rank : ℝ) = A.trace := by
  classical
  -- Eigenvalues of a Hermitian idempotent are 0 or 1.
  have heig : ∀ i : n, hH.eigenvalues i = 0 ∨ hH.eigenvalues i = 1 := by
    intro i
    have hmem := hI.spectrum_subset ℝ (hH.eigenvalues_mem_spectrum_real i)
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
    exact hmem
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

end HansenEconometrics
