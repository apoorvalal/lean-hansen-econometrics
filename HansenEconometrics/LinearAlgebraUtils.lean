import Mathlib

open scoped Matrix

namespace HansenEconometrics

open Matrix

variable {m n : Type*}
variable [Fintype m] [Fintype n]

/-- Left-multiplication by a row vector is right-multiplication by the transpose. -/
lemma vecMul_eq_mulVec_transpose (M : Matrix m n ℝ) (x : m → ℝ) :
    Matrix.vecMul x M = Mᵀ *ᵥ x := by
  simpa using (Matrix.vecMul_transpose Mᵀ x)

/-- For a symmetric matrix, left-multiplication as a row vector agrees with right-multiplication as a
column vector. -/
lemma vecMul_eq_mulVec_of_transpose_eq_self
    (M : Matrix n n ℝ) (hM : Mᵀ = M) (x : n → ℝ) :
    Matrix.vecMul x M = M *ᵥ x := by
  simpa [hM] using vecMul_eq_mulVec_transpose M x

/-- For a symmetric idempotent matrix, the associated quadratic form equals the squared norm of the
projected vector. This is the linear-algebra identity behind projection-based chi-square arguments. -/
lemma quadratic_form_eq_dotProduct_of_symm_idempotent
    (M : Matrix n n ℝ) (hMt : Mᵀ = M) (hMid : M * M = M) (x : n → ℝ) :
    x ⬝ᵥ M *ᵥ x = dotProduct (M *ᵥ x) (M *ᵥ x) := by
  have hvec : Matrix.vecMul x M = M *ᵥ x :=
    vecMul_eq_mulVec_of_transpose_eq_self M hMt x
  have h := Matrix.dotProduct_mulVec x M (M *ᵥ x)
  rw [hvec, Matrix.mulVec_mulVec, hMid] at h
  exact h

end HansenEconometrics
