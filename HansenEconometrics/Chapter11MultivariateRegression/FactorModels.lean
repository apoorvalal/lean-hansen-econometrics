import Mathlib.Algebra.Order.Group.Multiset
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Data.Fin.Tuple.Take
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import HansenEconometrics.Chapter3LeastSquaresAlgebra
import HansenEconometrics.Chapter11MultivariateRegression.PCA

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

omit [Fintype n] [Fintype k] [DecidableEq n] [DecidableEq k] in
/-- Coordinate form of Hansen's canonical loading formula
`Λhat = H D^{1/2}` for diagonal `D`. -/
@[simp]
theorem factorLoadingEstimator_diagonal_apply
    (H : Matrix k r ℝ) (d : r → ℝ) (a : k) (j : r) :
    factorLoadingEstimator H (Matrix.diagonal d) a j = H a j * d j := by
  simp [factorLoadingEstimator, Matrix.mul_apply, Matrix.diagonal]

/-- Principal-component factor estimator `D^{-1/2} H' X`. -/
noncomputable def factorScoreEstimator
    (H : Matrix k r ℝ) (invSqrtD : Matrix r r ℝ) (X : k → ℝ) : r → ℝ :=
  invSqrtD *ᵥ (Hᵀ *ᵥ X)

omit [Fintype n] [DecidableEq n] [DecidableEq k] in
/-- Coordinate form of Hansen's diagonal score formula
`Fhat_{ij} = d_j^{-1/2} h_j' X_i`. -/
@[simp]
theorem factorScoreEstimator_diagonal_apply
    (H : Matrix k r ℝ) (d : r → ℝ) (X : k → ℝ) (j : r) :
    factorScoreEstimator H (Matrix.diagonal d) X j =
      d j * ((fun a => H a j) ⬝ᵥ X) := by
  rw [factorScoreEstimator, Matrix.mulVec_diagonal]
  simp [Matrix.mulVec, Matrix.transpose_apply, dotProduct]

/-- Fixed-loading least-squares factor score
`(Λ'Λ)^{-1}Λ'X`, using Mathlib's total nonsingular inverse. -/
noncomputable def factorScoreLeastSquares
    (Λ : Matrix k r ℝ) (X : k → ℝ) : r → ℝ :=
  olsBetaStar Λ X

/-- Sample second-moment matrix `n⁻¹∑ X_i X_i'` used in Hansen Theorem 11.9. -/
noncomputable def factorSampleCovariance
    (X : n → k → ℝ) : Matrix k k ℝ :=
  (Fintype.card n : ℝ)⁻¹ • ∑ i : n, Matrix.vecMulVec (X i) (X i)

/-- The raw observation-by-variable data matrix for the factor-model sample. -/
def factorDataMatrix (X : n → k → ℝ) : Matrix n k ℝ :=
  fun i a => X i a

/-- Observation-space sample Gram matrix `n⁻¹ XX'`. It has the same nonzero
spectral content as the variable-space sample covariance `n⁻¹ X'X`, and is the
natural matrix for arbitrary normalized score arrays in Hansen Theorem 11.9. -/
noncomputable def factorObservationGram
    (X : n → k → ℝ) : Matrix n n ℝ :=
  (Fintype.card n : ℝ)⁻¹ • (factorDataMatrix X * (factorDataMatrix X)ᵀ)

/-- The raw observation-by-factor score matrix for a finite sample of factors. -/
def factorScoreDataMatrix (F : n → r → ℝ) : Matrix n r ℝ :=
  fun i j => F i j

/-- The observation-space orthonormal frame associated with Hansen-normalized
scores: `(√n)⁻¹ F`. -/
noncomputable def factorNormalizedScoreFrame
    (F : n → r → ℝ) : Matrix n r ℝ :=
  (Real.sqrt (Fintype.card n : ℝ))⁻¹ • factorScoreDataMatrix F

/-- The exact finite-sample common component `F Λ'` in Hansen's factor-model notation. -/
def factorCommonComponentDataMatrix
    (Λ : Matrix k r ℝ) (F : n → r → ℝ) : Matrix n k ℝ :=
  factorScoreDataMatrix F * Λᵀ

/-- Exact finite-sample factor-model restriction `X = F Λ'` at the data-matrix level. -/
def factorExactSampleFactorModel
    (X : n → k → ℝ) (Λ : Matrix k r ℝ) (F : n → r → ℝ) : Prop :=
  factorDataMatrix X = factorCommonComponentDataMatrix Λ F

/-- Additive finite-sample approximate factor-model restriction `X = F Λ' + U`
at the data-matrix level. The matrix `U` records the observed idiosyncratic
sample component rather than a population covariance condition. -/
def factorApproxSampleFactorModel
    (X : n → k → ℝ) (Λ : Matrix k r ℝ) (F : n → r → ℝ)
    (U : Matrix n k ℝ) : Prop :=
  factorDataMatrix X = factorCommonComponentDataMatrix Λ F + U

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

omit [Fintype k] [DecidableEq n] [DecidableEq k] [DecidableEq r] in
@[simp]
theorem factorSampleCovariance_apply
    (X : n → k → ℝ) (a b : k) :
    factorSampleCovariance X a b =
      (Fintype.card n : ℝ)⁻¹ * ∑ i : n, X i a * X i b := by
  rw [factorSampleCovariance]
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.sum_apply, Matrix.vecMulVec_apply]

omit [Fintype n] [Fintype k] [DecidableEq n] [DecidableEq k] in
@[simp]
theorem factorDataMatrix_apply
    (X : n → k → ℝ) (i : n) (a : k) :
    factorDataMatrix X i a = X i a := rfl

omit [Fintype r] [DecidableEq n] [DecidableEq k] [DecidableEq r] in
@[simp]
theorem factorObservationGram_apply
    (X : n → k → ℝ) (i j : n) :
    factorObservationGram X i j =
      (Fintype.card n : ℝ)⁻¹ * ∑ a : k, X i a * X j a := by
  simp [factorObservationGram, factorDataMatrix, Matrix.mul_apply,
    Matrix.transpose_apply, smul_eq_mul]

omit [Fintype n] [Fintype k] [Fintype r] [DecidableEq n] [DecidableEq k] [DecidableEq r] in
@[simp]
theorem factorScoreDataMatrix_apply
    (F : n → r → ℝ) (i : n) (j : r) :
    factorScoreDataMatrix F i j = F i j := rfl

omit [Fintype k] [Fintype r] [DecidableEq n] [DecidableEq k] [DecidableEq r] in
@[simp]
theorem factorNormalizedScoreFrame_apply
    (F : n → r → ℝ) (i : n) (j : r) :
    factorNormalizedScoreFrame F i j =
      (Real.sqrt (Fintype.card n : ℝ))⁻¹ * F i j := by
  simp [factorNormalizedScoreFrame, smul_eq_mul]

omit [Fintype n] [Fintype k] [DecidableEq n] [DecidableEq k] [DecidableEq r] in
@[simp]
theorem factorCommonComponentDataMatrix_apply
    (Λ : Matrix k r ℝ) (F : n → r → ℝ) (i : n) (a : k) :
    factorCommonComponentDataMatrix Λ F i a =
      ∑ j : r, F i j * Λ a j := by
  simp [factorCommonComponentDataMatrix, Matrix.mul_apply, Matrix.transpose_apply]

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

omit [Fintype k] [Fintype r] [DecidableEq n] [DecidableEq k] [DecidableEq r] in
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

omit [Fintype k] [Fintype r] [DecidableEq n] [DecidableEq k] [DecidableEq r] in
/-- The factor-model sample second-moment matrix is Hermitian, so Hansen's
Theorem 11.9 leading-eigenspace endpoint does not need symmetry as a separate
premise when `Ŝ` is the sample covariance itself. -/
theorem factorSampleCovariance_isHermitian
    (X : n → k → ℝ) :
    (factorSampleCovariance X).IsHermitian := by
  rw [Matrix.IsHermitian]
  simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
    factorSampleCovariance_transpose X

omit [Fintype k] [Fintype r] [DecidableEq n] [DecidableEq k] [DecidableEq r] in
/-- The factor-model sample second-moment matrix is positive semidefinite. This
is the deterministic rank/signal support behind the positivity side condition
for Hansen Theorem 11.9's canonical square-root scaling. -/
theorem factorSampleCovariance_posSemidef
    [Finite k]
    (X : n → k → ℝ) :
    (factorSampleCovariance X).PosSemidef := by
  classical
  letI := Fintype.ofFinite k
  have hsum : (∑ i : n, Matrix.vecMulVec (X i) (X i)).PosSemidef := by
    refine Matrix.posSemidef_sum (s := Finset.univ)
      (x := fun i : n => Matrix.vecMulVec (X i) (X i)) ?_
    intro i _
    simpa using Matrix.posSemidef_vecMulVec_self_star (X i)
  have hscale : 0 ≤ ((Fintype.card n : ℝ)⁻¹) :=
    inv_nonneg.mpr (Nat.cast_nonneg _)
  simpa [factorSampleCovariance] using Matrix.PosSemidef.smul hsum hscale

omit [Fintype r] [DecidableEq n] [DecidableEq k] [DecidableEq r] in
/-- The observation-space Gram matrix `n⁻¹XX'` is positive semidefinite. -/
theorem factorObservationGram_posSemidef
    (X : n → k → ℝ) :
    (factorObservationGram X).PosSemidef := by
  have hgram : (factorDataMatrix X * (factorDataMatrix X)ᵀ).PosSemidef := by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.posSemidef_self_mul_conjTranspose (factorDataMatrix X)
  have hscale : 0 ≤ ((Fintype.card n : ℝ)⁻¹) :=
    inv_nonneg.mpr (Nat.cast_nonneg _)
  simpa [factorObservationGram] using
    Matrix.PosSemidef.smul hgram hscale

omit [Fintype k] [Fintype r] [DecidableEq n] [DecidableEq k] [DecidableEq r] in
/-- Matrix form of the sample covariance: `Ŝ = n⁻¹ X'X`, where `X` is the raw
observation-by-variable data matrix. -/
theorem factorSampleCovariance_eq_card_inv_smul_transpose_mul
    (X : n → k → ℝ) :
    factorSampleCovariance X =
      (Fintype.card n : ℝ)⁻¹ • ((factorDataMatrix X)ᵀ * factorDataMatrix X) := by
  ext a b
  rw [factorSampleCovariance_apply]
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply, Matrix.transpose_apply,
    factorDataMatrix_apply]

omit [Fintype r] [DecidableEq n] [DecidableEq k] [DecidableEq r] in
/-- Matrix form of the observation-space sample Gram matrix:
`G_X = n⁻¹XX'`. -/
theorem factorObservationGram_eq_card_inv_smul_mul_transpose
    (X : n → k → ℝ) :
    factorObservationGram X =
      (Fintype.card n : ℝ)⁻¹ • (factorDataMatrix X * (factorDataMatrix X)ᵀ) := rfl

omit [Fintype r] [DecidableEq r] in
/-- Rectangular Sylvester characteristic-polynomial bridge for Hansen's two
sample Gram matrices. The extra powers of `X` account exactly for the zero
eigenvalues introduced by moving between observation space and variable space;
the nonzero spectral content is therefore the same finite-dimensional boundary
needed for Theorem 11.9's arbitrary-score trace transfer. -/
theorem factorObservationGram_sampleCovariance_charpoly_mul_X
    (X : n → k → ℝ) :
    Polynomial.X ^ Fintype.card k * (factorObservationGram X).charpoly =
      Polynomial.X ^ Fintype.card n * (factorSampleCovariance X).charpoly := by
  let Xmat : Matrix n k ℝ := factorDataMatrix X
  let c : ℝ := (Fintype.card n : ℝ)⁻¹
  have hleft : (c • Xmat) * Xmatᵀ = factorObservationGram X := by
    rw [factorObservationGram_eq_card_inv_smul_mul_transpose]
    simp [c, Xmat, Matrix.smul_mul]
  have hright : Xmatᵀ * (c • Xmat) = factorSampleCovariance X := by
    rw [factorSampleCovariance_eq_card_inv_smul_transpose_mul]
    simp [c, Xmat, Matrix.mul_smul]
  simpa [hleft, hright] using
    (Matrix.charpoly_mul_comm' (A := c • Xmat) (B := Xmatᵀ))

omit [Fintype r] [DecidableEq r] in
/-- Root-multiset form of
`factorObservationGram_sampleCovariance_charpoly_mul_X`.

This expands the rectangular Sylvester characteristic-polynomial bridge into
the exact zero-padding statement for the two Gram spectra. The later sorted
eigenvalue bridge removes the padded zero roots and compares the leading `r`
entries. -/
theorem factorObservationGram_sampleCovariance_roots_with_zero_padding
    (X : n → k → ℝ) :
    Fintype.card k • ({0} : Multiset ℝ) +
        (factorObservationGram X).charpoly.roots =
      Fintype.card n • ({0} : Multiset ℝ) +
        (factorSampleCovariance X).charpoly.roots := by
  classical
  have hroot :=
    congrArg Polynomial.roots
      (factorObservationGram_sampleCovariance_charpoly_mul_X (n := n) (k := k) X)
  have hleft_ne :
      Polynomial.X ^ Fintype.card k * (factorObservationGram X).charpoly ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ Polynomial.X_ne_zero)
      (Matrix.charpoly_monic (factorObservationGram X)).ne_zero
  have hright_ne :
      Polynomial.X ^ Fintype.card n * (factorSampleCovariance X).charpoly ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ Polynomial.X_ne_zero)
      (Matrix.charpoly_monic (factorSampleCovariance X)).ne_zero
  rw [Polynomial.roots_mul hleft_ne, Polynomial.roots_mul hright_ne,
    Polynomial.roots_X_pow, Polynomial.roots_X_pow] at hroot
  exact hroot

omit [Fintype n] [Fintype k] [Fintype r] [DecidableEq n] [DecidableEq k]
  [DecidableEq r] in
private lemma factorList_sum_ofFn_eq_finset_sum {m : ℕ} (f : Fin m → ℝ) :
    (List.ofFn f).sum = ∑ i : Fin m, f i := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [List.ofFn_succ, Fin.sum_univ_succ]
      simp [ih]

omit [Fintype n] [Fintype k] [Fintype r] [DecidableEq n] [DecidableEq k]
  [DecidableEq r] in
private lemma factorList_sum_take_ofFn_eq_finset_sum_castLE
    {m n : ℕ} (h : m ≤ n) (f : Fin n → ℝ) :
    ((List.ofFn f).take m).sum = ∑ i : Fin m, f (Fin.castLE h i) := by
  rw [← Fin.ofFn_take_eq_take_ofFn h f]
  exact factorList_sum_ofFn_eq_finset_sum (Fin.take m h f)

omit [Fintype n] [Fintype k] [Fintype r] [DecidableEq n] [DecidableEq k]
  [DecidableEq r] in
private lemma factorSortedGE_append_replicate_zero_of_nonneg {l : List ℝ}
    (hs : l.SortedGE) (h0 : ∀ x ∈ l, 0 ≤ x) (m : ℕ) :
    (l ++ List.replicate m (0 : ℝ)).SortedGE := by
  rw [List.sortedGE_iff_pairwise] at hs ⊢
  simp only [List.pairwise_append, hs, List.pairwise_replicate_of_refl, true_and]
  intro a ha b hb
  rw [List.eq_of_mem_replicate hb]
  exact h0 a ha

omit [Fintype n] [Fintype k] [Fintype r] [DecidableEq n] [DecidableEq k]
  [DecidableEq r] in
private lemma factorPadded_sorted_nonneg_lists_eq_of_multiset_eq
    {l₁ l₂ : List ℝ} {a b : ℕ}
    (hs₁ : l₁.SortedGE) (hs₂ : l₂.SortedGE)
    (h0₁ : ∀ x ∈ l₁, 0 ≤ x) (h0₂ : ∀ x ∈ l₂, 0 ≤ x)
    (hpad : a • ({0} : Multiset ℝ) + (l₁ : Multiset ℝ) =
      b • ({0} : Multiset ℝ) + (l₂ : Multiset ℝ)) :
    l₁ ++ List.replicate a (0 : ℝ) =
      l₂ ++ List.replicate b (0 : ℝ) := by
  have hrep_a : (List.replicate a (0 : ℝ) : Multiset ℝ) =
      a • ({0} : Multiset ℝ) := by
    rw [Multiset.coe_replicate, ← Multiset.nsmul_singleton]
  have hrep_b : (List.replicate b (0 : ℝ) : Multiset ℝ) =
      b • ({0} : Multiset ℝ) := by
    rw [Multiset.coe_replicate, ← Multiset.nsmul_singleton]
  have hcoe :
      ((l₁ ++ List.replicate a (0 : ℝ) : List ℝ) : Multiset ℝ) =
        ((l₂ ++ List.replicate b (0 : ℝ) : List ℝ) : Multiset ℝ) := by
    calc
      ((l₁ ++ List.replicate a (0 : ℝ) : List ℝ) : Multiset ℝ)
          = (l₁ : Multiset ℝ) + a • ({0} : Multiset ℝ) := by
              rw [← Multiset.coe_add, hrep_a]
      _ = a • ({0} : Multiset ℝ) + (l₁ : Multiset ℝ) := by rw [add_comm]
      _ = b • ({0} : Multiset ℝ) + (l₂ : Multiset ℝ) := hpad
      _ = (l₂ : Multiset ℝ) + b • ({0} : Multiset ℝ) := by rw [add_comm]
      _ = ((l₂ ++ List.replicate b (0 : ℝ) : List ℝ) : Multiset ℝ) := by
              rw [← Multiset.coe_add, hrep_b]
  have hperm : List.Perm (l₁ ++ List.replicate a (0 : ℝ))
      (l₂ ++ List.replicate b (0 : ℝ)) :=
    Multiset.coe_eq_coe.mp hcoe
  exact List.Perm.eq_of_sortedGE
    (factorSortedGE_append_replicate_zero_of_nonneg hs₁ h0₁ a)
    (factorSortedGE_append_replicate_zero_of_nonneg hs₂ h0₂ b)
    hperm

omit [Fintype k] [Fintype r] [DecidableEq n] [DecidableEq k] [DecidableEq r] in
/-- Matrix form of the sample score covariance: `n⁻¹ F'F`. -/
theorem factorScoreSampleCovariance_eq_card_inv_smul_transpose_mul
    (F : n → r → ℝ) :
    factorScoreSampleCovariance F =
      (Fintype.card n : ℝ)⁻¹ • ((factorScoreDataMatrix F)ᵀ *
        factorScoreDataMatrix F) := by
  ext a b
  rw [factorScoreSampleCovariance_apply]
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply, Matrix.transpose_apply,
    factorScoreDataMatrix_apply]

omit [Fintype k] [DecidableEq n] [DecidableEq k] in
/-- Hansen sample factor normalization implies full selected rank of the raw
factor score matrix. This is the finite-sample bridge from the textbook
normalization `n⁻¹F'F = I_r` to the rank premise used by the PCA endpoint. -/
theorem factorScoreDataMatrix_rank_eq_card_of_scoreNormalization
    (F : n → r → ℝ) (hF : factorScoreNormalization F) :
    (factorScoreDataMatrix F).rank = Fintype.card r := by
  classical
  let Fmat : Matrix n r ℝ := factorScoreDataMatrix F
  let L : Matrix r n ℝ := (Fintype.card n : ℝ)⁻¹ • Fmatᵀ
  have hleft : L * Fmat = 1 := by
    change ((Fintype.card n : ℝ)⁻¹ • (factorScoreDataMatrix F)ᵀ) *
        factorScoreDataMatrix F = 1
    rw [Matrix.smul_mul]
    rw [← factorScoreSampleCovariance_eq_card_inv_smul_transpose_mul F]
    exact hF
  have hle : (1 : Matrix r r ℝ).rank ≤ Fmat.rank := by
    simpa [hleft] using Matrix.rank_mul_le_right L Fmat
  exact le_antisymm (Matrix.rank_le_card_width Fmat)
    (by simpa [Fmat, Matrix.rank_one] using hle)

omit [Fintype k] [Fintype r] [DecidableEq n] [DecidableEq k] [DecidableEq r] in
/-- Matrix form of the sample cross moment: `n⁻¹ X'F`. -/
theorem factorSampleCrossCovariance_eq_card_inv_smul_transpose_mul_score
    (X : n → k → ℝ) (F : n → r → ℝ) :
    factorSampleCrossCovariance X F =
      (Fintype.card n : ℝ)⁻¹ • ((factorDataMatrix X)ᵀ *
        factorScoreDataMatrix F) := by
  ext a b
  rw [factorSampleCrossCovariance_apply]
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply, Matrix.transpose_apply,
    factorDataMatrix_apply, factorScoreDataMatrix_apply]

omit [Fintype r] [DecidableEq n] [DecidableEq k] [DecidableEq r] in
/-- The observation-space sample Gram matrix is symmetric. -/
theorem factorObservationGram_transpose
    (X : n → k → ℝ) :
    (factorObservationGram X)ᵀ = factorObservationGram X := by
  rw [factorObservationGram, transpose_smul, Matrix.transpose_mul,
    Matrix.transpose_transpose]

omit [Fintype r] [DecidableEq n] [DecidableEq k] [DecidableEq r] in
/-- The observation-space sample Gram matrix is Hermitian. -/
theorem factorObservationGram_isHermitian
    (X : n → k → ℝ) :
    (factorObservationGram X).IsHermitian := by
  rw [Matrix.IsHermitian]
  simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
    factorObservationGram_transpose X

omit [Fintype k] [Fintype r] [DecidableEq n] [DecidableEq k] [DecidableEq r] in
private theorem inv_sqrt_card_mul_self
    [Nonempty n] :
    (Real.sqrt (Fintype.card n : ℝ))⁻¹ *
        (Real.sqrt (Fintype.card n : ℝ))⁻¹ =
      (Fintype.card n : ℝ)⁻¹ := by
  have hpos : 0 < (Fintype.card n : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hsqrt_ne : Real.sqrt (Fintype.card n : ℝ) ≠ 0 :=
    (Real.sqrt_pos_of_pos hpos).ne'
  have hsqrt_sq :
      Real.sqrt (Fintype.card n : ℝ) *
          Real.sqrt (Fintype.card n : ℝ) =
        (Fintype.card n : ℝ) :=
    Real.mul_self_sqrt hpos.le
  calc
    (Real.sqrt (Fintype.card n : ℝ))⁻¹ *
        (Real.sqrt (Fintype.card n : ℝ))⁻¹ =
        ((Real.sqrt (Fintype.card n : ℝ)) *
          (Real.sqrt (Fintype.card n : ℝ)))⁻¹ := by
          exact
            (show (((Real.sqrt (Fintype.card n : ℝ)) *
                (Real.sqrt (Fintype.card n : ℝ)))⁻¹ : ℝ) =
              (Real.sqrt (Fintype.card n : ℝ))⁻¹ *
                (Real.sqrt (Fintype.card n : ℝ))⁻¹ from
              _root_.mul_inv_rev
                (Real.sqrt (Fintype.card n : ℝ))
                (Real.sqrt (Fintype.card n : ℝ))).symm
    _ = (Fintype.card n : ℝ)⁻¹ := by
          rw [hsqrt_sq]

omit [Fintype k] [Fintype r] [DecidableEq n] [DecidableEq k] in
/-- Hansen-normalized scores become an orthonormal observation-space frame
after scaling by `√n`. -/
theorem factorNormalizedScoreFrame_orthonormal
    [Nonempty n] (F : n → r → ℝ)
    (hF : factorScoreNormalization F) :
    (factorNormalizedScoreFrame F)ᵀ * factorNormalizedScoreFrame F = 1 := by
  rw [factorNormalizedScoreFrame]
  rw [transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [inv_sqrt_card_mul_self]
  rw [← factorScoreSampleCovariance_eq_card_inv_smul_transpose_mul F]
  exact hF

omit [Fintype r] [DecidableEq n] [DecidableEq k] [DecidableEq r] in
/-- The cross-covariance Gram matrix for arbitrary scores is the observation
Gram matrix compressed to the normalized score frame. -/
theorem factorSampleCrossCovariance_gram_eq_normalizedScoreFrame_observationGram
    [Nonempty n] (X : n → k → ℝ) (F : n → r → ℝ) :
    (factorSampleCrossCovariance X F)ᵀ * factorSampleCrossCovariance X F =
      (factorNormalizedScoreFrame F)ᵀ * factorObservationGram X *
        factorNormalizedScoreFrame F := by
  let N : ℝ := Fintype.card n
  let c : ℝ := (Real.sqrt N)⁻¹
  let Xmat : Matrix n k ℝ := factorDataMatrix X
  let Fmat : Matrix n r ℝ := factorScoreDataMatrix F
  have hc : c * c = N⁻¹ := by
    simpa [c, N] using inv_sqrt_card_mul_self (n := n)
  have hscalar : N⁻¹ * N⁻¹ = c * N⁻¹ * c := by
    rw [← hc]
    ring
  have hinner :
      (Fmatᵀ * Xmat) * (Xmatᵀ * Fmat) =
        (Fmatᵀ * (Xmat * Xmatᵀ)) * Fmat := by
    simp [Matrix.mul_assoc]
  have hright :
      (c • Fmatᵀ) * (N⁻¹ • (Xmat * Xmatᵀ)) * (c • Fmat) =
        (c * N⁻¹ * c) • ((Fmatᵀ * (Xmat * Xmatᵀ)) * Fmat) := by
    simp [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc, smul_smul,
      mul_comm, mul_left_comm]
  calc
    (factorSampleCrossCovariance X F)ᵀ * factorSampleCrossCovariance X F =
        (N⁻¹ • (Xmatᵀ * Fmat))ᵀ * (N⁻¹ • (Xmatᵀ * Fmat)) := by
          simp [N, Xmat, Fmat,
            factorSampleCrossCovariance_eq_card_inv_smul_transpose_mul_score]
    _ = (N⁻¹ • (Fmatᵀ * Xmat)) * (N⁻¹ • (Xmatᵀ * Fmat)) := by
          rw [transpose_smul, Matrix.transpose_mul, Matrix.transpose_transpose]
    _ = (N⁻¹ * N⁻¹) • ((Fmatᵀ * Xmat) * (Xmatᵀ * Fmat)) := by
          rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    _ = (c * N⁻¹ * c) • ((Fmatᵀ * (Xmat * Xmatᵀ)) * Fmat) := by
          rw [hscalar, hinner]
    _ = (c • Fmatᵀ) * (N⁻¹ • (Xmat * Xmatᵀ)) * (c • Fmat) := by
          rw [hright]
    _ = (factorNormalizedScoreFrame F)ᵀ * factorObservationGram X *
        factorNormalizedScoreFrame F := by
          simp [factorObservationGram, factorNormalizedScoreFrame, N, c, Xmat, Fmat,
            transpose_smul]

omit [DecidableEq n] [DecidableEq k] [DecidableEq r] in
/-- The profiled cross-covariance trace for arbitrary Hansen-normalized scores
is exactly the observation-space trace objective for the normalized score frame. -/
theorem factorSampleCrossCovariance_trace_eq_observationGram_trace
    [Nonempty n] (X : n → k → ℝ) (F : n → r → ℝ) :
    Matrix.trace
        ((factorSampleCrossCovariance X F)ᵀ *
          factorSampleCrossCovariance X F) =
      Matrix.trace
        ((factorNormalizedScoreFrame F)ᵀ * factorObservationGram X *
          factorNormalizedScoreFrame F) := by
  rw [factorSampleCrossCovariance_gram_eq_normalizedScoreFrame_observationGram]

omit [Fintype n] [Fintype r] [DecidableEq n] [DecidableEq k] [DecidableEq r] in
private theorem matrix_rank_smul_eq_of_ne_zero
    {c : ℝ} (hc : c ≠ 0) (M : Matrix k k ℝ) :
    (c • M).rank = M.rank := by
  classical
  let D : Matrix k k ℝ := Matrix.diagonal (fun _ : k => c)
  have hDmul : D * M = c • M := by
    ext i j
    simp [D, Matrix.mul_apply, Matrix.diagonal]
  have hDunit : IsUnit D.det := by
    refine isUnit_iff_ne_zero.mpr ?_
    simp [D, hc]
  rw [← hDmul]
  exact Matrix.rank_mul_eq_right_of_isUnit_det D M hDunit

omit [Fintype r] [DecidableEq n] [DecidableEq k] [DecidableEq r] in
/-- For a nonempty sample, Hansen's sample covariance has the same rank as the
raw data matrix. This turns full-rank or selected-rank data conditions into the
selected-eigenvalue positivity condition used by Theorem 11.9. -/
theorem factorSampleCovariance_rank_eq_dataMatrix_rank
    [Nonempty n] (X : n → k → ℝ) :
    (factorSampleCovariance X).rank = (factorDataMatrix X).rank := by
  have hncard : (Fintype.card n : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  calc
    (factorSampleCovariance X).rank
        = (((Fintype.card n : ℝ)⁻¹) •
            ((factorDataMatrix X)ᵀ * factorDataMatrix X)).rank := by
            rw [factorSampleCovariance_eq_card_inv_smul_transpose_mul]
    _ = ((factorDataMatrix X)ᵀ * factorDataMatrix X).rank :=
            matrix_rank_smul_eq_of_ne_zero (inv_ne_zero hncard) _
    _ = (factorDataMatrix X).rank :=
            Matrix.rank_transpose_mul_self (factorDataMatrix X)

omit [Fintype r] [DecidableEq n] [DecidableEq k] [DecidableEq r] in
/-- For a nonempty sample, the observation-space Gram matrix has the same rank
as the raw data matrix. This is the rank-level part of the same nonzero-spectrum
transfer as `factorObservationGram_sampleCovariance_charpoly_mul_X`. -/
theorem factorObservationGram_rank_eq_dataMatrix_rank
    [Nonempty n] (X : n → k → ℝ) :
    (factorObservationGram X).rank = (factorDataMatrix X).rank := by
  have hncard : (Fintype.card n : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  calc
    (factorObservationGram X).rank
        = (((Fintype.card n : ℝ)⁻¹) •
            (factorDataMatrix X * (factorDataMatrix X)ᵀ)).rank := by
            rw [factorObservationGram_eq_card_inv_smul_mul_transpose]
    _ = (factorDataMatrix X * (factorDataMatrix X)ᵀ).rank :=
            matrix_rank_smul_eq_of_ne_zero (inv_ne_zero hncard) _
    _ = (factorDataMatrix X).rank :=
            Matrix.rank_self_mul_transpose (factorDataMatrix X)

omit [Fintype r] [DecidableEq n] [DecidableEq k] [DecidableEq r] in
/-- The two sample Gram matrices in Hansen Theorem 11.9 have the same rank.
The stronger characteristic-polynomial bridge above records equality of their
nonzero spectral content with zero-padding. -/
theorem factorObservationGram_rank_eq_sampleCovariance_rank
    [Nonempty n] (X : n → k → ℝ) :
    (factorObservationGram X).rank = (factorSampleCovariance X).rank := by
  rw [factorObservationGram_rank_eq_dataMatrix_rank,
    factorSampleCovariance_rank_eq_dataMatrix_rank]

omit [DecidableEq n] [DecidableEq k] [DecidableEq r] in
/-- A raw data-matrix selected-rank certificate gives the sample-covariance
selected-rank condition needed by Hansen Theorem 11.9. -/
theorem factorSampleCovariance_rank_ge_of_dataMatrix_rank_ge
    [Nonempty n] (X : n → k → ℝ)
    (hrank : Fintype.card r ≤ (factorDataMatrix X).rank) :
    Fintype.card r ≤ (factorSampleCovariance X).rank := by
  simpa [factorSampleCovariance_rank_eq_dataMatrix_rank (X := X)] using hrank

omit [Fintype n] [Fintype r] [DecidableEq n] [DecidableEq k] [DecidableEq r] in
/-- Linear independence of the sample columns is a concrete raw full-rank route
to the data-matrix rank condition. -/
theorem factorDataMatrix_rank_eq_card_k_of_columns_linearIndependent
    (X : n → k → ℝ)
    (hlin : LinearIndependent ℝ (factorDataMatrix X).col) :
    (factorDataMatrix X).rank = Fintype.card k := by
  rw [Matrix.rank_eq_finrank_span_cols,
    linearIndependent_iff_card_eq_finrank_span.mp hlin, Set.finrank]

omit [DecidableEq n] [DecidableEq k] [DecidableEq r] in
/-- Column-linear independence of the raw data matrix gives the
sample-covariance selected-rank condition whenever `r ≤ k`. -/
theorem factorSampleCovariance_rank_ge_of_dataMatrix_columns_linearIndependent
    [Nonempty n] (hcard : Fintype.card r ≤ Fintype.card k) (X : n → k → ℝ)
    (hlin : LinearIndependent ℝ (factorDataMatrix X).col) :
    Fintype.card r ≤ (factorSampleCovariance X).rank := by
  exact factorSampleCovariance_rank_ge_of_dataMatrix_rank_ge
    (r := r) X
    (by simpa [factorDataMatrix_rank_eq_card_k_of_columns_linearIndependent X hlin] using hcard)

/-- Raw finite-sample factor-model rank package. It states Hansen-facing inputs:
the observed data matrix equals the exact common component `F Λ'`, the loading
matrix has a left inverse, and the sample factor matrix has full selected rank.
It does not include any PCA/eigenspace conclusion. -/
structure ExactSampleFactorRankCondition
    (X : n → k → ℝ) (Λ : Matrix k r ℝ) (F : n → r → ℝ) : Prop where
  exact_factor : factorExactSampleFactorModel X Λ F
  loading_left_inverse : ∃ L : Matrix r k ℝ, L * Λ = 1
  sample_factor_rank : (factorScoreDataMatrix F).rank = Fintype.card r

/-- Additive finite-sample approximate-factor rank package.

It allows an idiosyncratic data component `U`, but requires a Hansen-shaped
pervasiveness/recoverability condition: some left inverse of the loading matrix
annihilates the idiosyncratic component in sample, so multiplying `X` by that
recovering direction still returns the raw factor-score matrix. This is a
deterministic noisy boundary condition between the exact-factor bridge and a
future asymptotic pervasiveness theorem. -/
structure ApproximateSampleFactorRankCondition
    (X : n → k → ℝ) (Λ : Matrix k r ℝ) (F : n → r → ℝ)
    (U : Matrix n k ℝ) : Prop where
  approximate_factor : factorApproxSampleFactorModel X Λ F U
  recoverable_loadings : ∃ L : Matrix r k ℝ, L * Λ = 1 ∧ U * Lᵀ = 0
  sample_factor_rank : (factorScoreDataMatrix F).rank = Fintype.card r

omit [Fintype n] [DecidableEq n] in
/-- Quantitative finite-sample loading pervasiveness: the loading Gram matrix
dominates a strictly positive multiple of the Euclidean norm. This is the
finite-dimensional theorem-facing analogue of Hansen's nondegenerate loading
signal condition. -/
def factorLoadingPervasiveness (Λ : Matrix k r ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ x : r → ℝ,
    c * (x ⬝ᵥ x) ≤ x ⬝ᵥ ((Λᵀ * Λ) *ᵥ x)

omit [Fintype n] [DecidableEq n] [DecidableEq k] [DecidableEq r] in
/-- A quantitative loading-pervasiveness lower bound makes the loading Gram
matrix positive definite. -/
theorem factorLoadingGram_posDef_of_pervasiveness
    (Λ : Matrix k r ℝ) (hΛ : factorLoadingPervasiveness Λ) :
    (Λᵀ * Λ).PosDef := by
  rcases hΛ with ⟨c, hc, hbound⟩
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ ?_
  · simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.isHermitian_conjTranspose_mul_self Λ
  · intro x hx
    have hx_nonneg : 0 ≤ x ⬝ᵥ x := by
      simpa using dotProduct_star_self_nonneg x
    have hx_ne : x ⬝ᵥ x ≠ 0 := by
      intro hzero
      exact hx (dotProduct_self_eq_zero.mp hzero)
    have hx_pos : 0 < x ⬝ᵥ x := lt_of_le_of_ne hx_nonneg hx_ne.symm
    have hcx_pos : 0 < c * (x ⬝ᵥ x) := mul_pos hc hx_pos
    have hreal : 0 < x ⬝ᵥ ((Λᵀ * Λ) *ᵥ x) :=
      lt_of_lt_of_le hcx_pos (hbound x)
    simpa using hreal

omit [Fintype n] [DecidableEq n] [DecidableEq k] in
/-- Quantitative loading pervasiveness implies the nonsingular loading-Gram
condition used by the existing finite-sample recoverability bridge. -/
theorem factorLoadingGram_nonsingular_of_pervasiveness
    (Λ : Matrix k r ℝ) (hΛ : factorLoadingPervasiveness Λ) :
    IsUnit (Λᵀ * Λ).det :=
  (Matrix.isUnit_iff_isUnit_det _).mp
    (factorLoadingGram_posDef_of_pervasiveness Λ hΛ).isUnit

omit [Fintype n] [Fintype r] [DecidableEq n] [DecidableEq k] [DecidableEq r] in
/-- Row-wise idiosyncratic orthogonality to the loading columns. This scalar
form is the primitive condition behind the matrix equation `UΛ = 0`. -/
def factorIdiosyncraticLoadingOrthogonality
    (U : Matrix n k ℝ) (Λ : Matrix k r ℝ) : Prop :=
  ∀ i j, (fun a => U i a) ⬝ᵥ (fun a => Λ a j) = 0

omit [Fintype n] [Fintype r] [DecidableEq n] [DecidableEq k] [DecidableEq r] in
/-- Row-wise idiosyncratic orthogonality is exactly the matrix equation
`UΛ = 0` used by the recoverability bridge. -/
theorem factorIdiosyncraticLoadingOrthogonality_matrix_eq_zero
    (U : Matrix n k ℝ) (Λ : Matrix k r ℝ)
    (hU : factorIdiosyncraticLoadingOrthogonality U Λ) :
    U * Λ = 0 := by
  ext i j
  simpa [factorIdiosyncraticLoadingOrthogonality, Matrix.mul_apply, dotProduct]
    using hU i j

omit [Fintype n] [DecidableEq n] [DecidableEq k] in
/-- Concrete recoverer for pervasive finite-sample loadings:
`(Λ'Λ)^{-1}Λ'`. It is a left inverse when the loading Gram matrix is
nonsingular. -/
noncomputable def factorLoadingGramRecoverer
    (Λ : Matrix k r ℝ) : Matrix r k ℝ :=
  (Λᵀ * Λ)⁻¹ * Λᵀ

omit [Fintype n] [DecidableEq n] [DecidableEq k] in
/-- Entrywise deterministic bound for the loading-Gram recoverer
`(Λ'Λ)^{-1}Λ'`.

If every entry of `(Λ'Λ)^{-1}` is bounded by `ρInv` and every loading entry is
bounded by `ρΛ`, then each recoverer entry is bounded by
`(# factors) ρInv ρΛ`. This is the finite-dimensional algebraic bridge behind
the Hansen Assumption 11.1 proof route where `Λ'Λ` diverges and the loadings
remain uniformly controlled. -/
theorem factorLoadingGramRecoverer_entry_abs_le_of_inverse_loading_entry_bounds
    (Λ : Matrix k r ℝ) {ρInv ρΛ : ℝ}
    (hInv : ∀ a c, |((Λᵀ * Λ)⁻¹) a c| ≤ ρInv)
    (hΛ : ∀ b c, |Λ b c| ≤ ρΛ)
    (hρInv : 0 ≤ ρInv) (a : r) (b : k) :
    |factorLoadingGramRecoverer Λ a b| ≤
      (Fintype.card r : ℝ) * ρInv * ρΛ := by
  rw [factorLoadingGramRecoverer, Matrix.mul_apply]
  calc
    |∑ c, ((Λᵀ * Λ)⁻¹) a c * (Λᵀ) c b|
        ≤ ∑ c, |((Λᵀ * Λ)⁻¹) a c * (Λᵀ) c b| :=
            Finset.abs_sum_le_sum_abs _ _
    _ = ∑ c : r, |((Λᵀ * Λ)⁻¹) a c| * |Λ b c| := by
            simp [abs_mul, Matrix.transpose_apply]
    _ ≤ ∑ _c : r, ρInv * ρΛ := by
            refine Finset.sum_le_sum ?_
            intro c _hc
            exact mul_le_mul (hInv a c) (hΛ b c) (abs_nonneg _) hρInv
    _ = (Fintype.card r : ℝ) * ρInv * ρΛ := by
            simp [Finset.sum_const, nsmul_eq_mul, mul_assoc]

omit [Fintype n] [DecidableEq n] [DecidableEq k] in
/-- Eventual version of
`factorLoadingGramRecoverer_entry_abs_le_of_inverse_loading_entry_bounds`.
It turns uniform entry envelopes for `(Λ'Λ)^{-1}` and `Λ` into the loading
recoverer envelope consumed by the approximate-factor WLLN bridges. -/
theorem factorLoadingGramRecoverer_entry_abs_bound_eventually_of_inverse_loading_entry_bounds
    {ι : Type*} {l : Filter ι}
    {Λ : ι → Matrix k r ℝ} {ρInv ρΛ ρL : ι → ℝ}
    (hInv : Filter.Eventually
      (fun i => ∀ a c, |(((Λ i)ᵀ * Λ i)⁻¹) a c| ≤ ρInv i) l)
    (hΛ : Filter.Eventually
      (fun i => ∀ b c, |Λ i b c| ≤ ρΛ i) l)
    (hρInv : Filter.Eventually (fun i => 0 ≤ ρInv i) l)
    (hρL : Filter.Eventually
      (fun i => (Fintype.card r : ℝ) * ρInv i * ρΛ i ≤ ρL i) l) :
    ∀ a b, Filter.Eventually
      (fun i => |factorLoadingGramRecoverer (Λ i) a b| ≤ ρL i) l := by
  intro a b
  filter_upwards [hInv, hΛ, hρInv, hρL] with
    i hInv_i hΛ_i hρInv_i hρL_i
  exact
    (factorLoadingGramRecoverer_entry_abs_le_of_inverse_loading_entry_bounds
      (Λ i) hInv_i hΛ_i hρInv_i a b).trans hρL_i

omit [Fintype n] [DecidableEq n] [DecidableEq k] in
/-- Nonsingularity of the loading Gram matrix makes the concrete loading-Gram
recoverer a left inverse of the loading matrix. This is the finite-dimensional
pervasiveness bridge used by the approximate-factor rank route. -/
theorem factorLoadingGramRecoverer_leftInverse
    (Λ : Matrix k r ℝ) (hΛ : IsUnit (Λᵀ * Λ).det) :
    factorLoadingGramRecoverer Λ * Λ = 1 := by
  calc
    factorLoadingGramRecoverer Λ * Λ
        = (Λᵀ * Λ)⁻¹ * (Λᵀ * Λ) := by
            rw [factorLoadingGramRecoverer, Matrix.mul_assoc]
    _ = 1 := by
            rw [Matrix.nonsing_inv_mul _ hΛ]

omit [Fintype n] [DecidableEq n] [DecidableEq k] in
/-- If the sample idiosyncratic component is orthogonal to the loading columns,
then the loading-Gram recoverer removes it. -/
theorem factorLoadingGramRecoverer_annihilates_idiosyncratic
    (Λ : Matrix k r ℝ) (U : Matrix n k ℝ) (hUΛ : U * Λ = 0) :
    U * (factorLoadingGramRecoverer Λ)ᵀ = 0 := by
  calc
    U * (factorLoadingGramRecoverer Λ)ᵀ
        = U * (Λ * ((Λᵀ * Λ)⁻¹)ᵀ) := by
            simp [factorLoadingGramRecoverer, Matrix.transpose_mul,
              Matrix.transpose_transpose]
    _ = (U * Λ) * ((Λᵀ * Λ)⁻¹)ᵀ := by
            rw [Matrix.mul_assoc]
    _ = 0 := by
            rw [hUΛ, Matrix.zero_mul]

/-- Idiosyncratic score component recovered by the loading-Gram left inverse
`(Λ'Λ)^{-1}Λ'`. This is the finite-sample perturbation that remains after
applying the factor recoverer to `X = FΛ' + U`. -/
noncomputable def factorRecoveredIdiosyncraticScoreMatrix
    (Λ : Matrix k r ℝ) (U : Matrix n k ℝ) : Matrix n r ℝ :=
  U * (factorLoadingGramRecoverer Λ)ᵀ

/-- Gram perturbation generated by the recovered idiosyncratic scores.

For `E = U ((Λ'Λ)^{-1}Λ')'`, this is
`F'E + E'F + E'E`, the cross/noise part of `(F + E)'(F + E)`. -/
noncomputable def factorRecoveredIdiosyncraticGramPerturbation
    (Λ : Matrix k r ℝ) (F : n → r → ℝ) (U : Matrix n k ℝ) :
    Matrix r r ℝ :=
  let Fmat : Matrix n r ℝ := factorScoreDataMatrix F
  let E : Matrix n r ℝ := factorRecoveredIdiosyncraticScoreMatrix Λ U
  Fmatᵀ * E + Eᵀ * Fmat + Eᵀ * E

omit [Fintype n] [DecidableEq n] [DecidableEq k] in
/-- Recovered factor scores after applying the loading-Gram left inverse to an
additive factor model. The idiosyncratic term need not vanish. -/
theorem factorRecoveredScoreDataMatrix_eq_factorScore_add_idiosyncratic
    (X : n → k → ℝ) (Λ : Matrix k r ℝ) (F : n → r → ℝ)
    (U : Matrix n k ℝ)
    (hApprox : factorApproxSampleFactorModel X Λ F U)
    (hΛ : IsUnit (Λᵀ * Λ).det) :
    factorDataMatrix X * (factorLoadingGramRecoverer Λ)ᵀ =
      factorScoreDataMatrix F + factorRecoveredIdiosyncraticScoreMatrix Λ U := by
  calc
    factorDataMatrix X * (factorLoadingGramRecoverer Λ)ᵀ
        = (factorScoreDataMatrix F * Λᵀ + U) *
            (factorLoadingGramRecoverer Λ)ᵀ := by
            rw [hApprox]
            rfl
      _ = (factorScoreDataMatrix F * Λᵀ) *
            (factorLoadingGramRecoverer Λ)ᵀ +
              U * (factorLoadingGramRecoverer Λ)ᵀ := by
            rw [Matrix.add_mul]
      _ = factorScoreDataMatrix F *
            (Λᵀ * (factorLoadingGramRecoverer Λ)ᵀ) +
              U * (factorLoadingGramRecoverer Λ)ᵀ := by
            rw [Matrix.mul_assoc]
      _ = factorScoreDataMatrix F *
            (factorLoadingGramRecoverer Λ * Λ)ᵀ +
              U * (factorLoadingGramRecoverer Λ)ᵀ := by
            rw [Matrix.transpose_mul]
      _ = factorScoreDataMatrix F + U * (factorLoadingGramRecoverer Λ)ᵀ := by
            rw [factorLoadingGramRecoverer_leftInverse Λ hΛ,
              Matrix.transpose_one, Matrix.mul_one]
      _ = factorScoreDataMatrix F +
            factorRecoveredIdiosyncraticScoreMatrix Λ U := rfl

omit [DecidableEq n] [DecidableEq k] in
/-- Gram expansion for recovered scores: the exact factor score Gram plus the
cross/noise perturbation generated by the recovered idiosyncratic scores. -/
theorem factorScore_add_recoveredIdiosyncratic_gram_eq_signal_add_perturbation
    (Λ : Matrix k r ℝ) (F : n → r → ℝ) (U : Matrix n k ℝ) :
    ((factorScoreDataMatrix F + factorRecoveredIdiosyncraticScoreMatrix Λ U)ᵀ *
        (factorScoreDataMatrix F + factorRecoveredIdiosyncraticScoreMatrix Λ U)) =
      (factorScoreDataMatrix F)ᵀ * factorScoreDataMatrix F +
        factorRecoveredIdiosyncraticGramPerturbation Λ F U := by
  simp [factorRecoveredIdiosyncraticGramPerturbation, Matrix.transpose_add,
    Matrix.add_mul, Matrix.mul_add, add_assoc]
  abel

omit [DecidableEq n] [DecidableEq k] in
/-- The recovered idiosyncratic cross/noise Gram is dominated by the factor
signal Gram. This permits nonzero idiosyncratic components and cross terms, but
requires them not to erase the selected factor signal after applying the
loading-Gram recoverer. -/
def factorRecoveredIdiosyncraticGramDominated
    (Λ : Matrix k r ℝ) (F : n → r → ℝ) (U : Matrix n k ℝ) : Prop :=
  ∀ x : r → ℝ, x ≠ 0 →
    - (x ⬝ᵥ (((factorScoreDataMatrix F)ᵀ * factorScoreDataMatrix F) *ᵥ x)) <
      x ⬝ᵥ ((factorRecoveredIdiosyncraticGramPerturbation Λ F U) *ᵥ x)

omit [DecidableEq n] [DecidableEq k] in
/-- Hansen-normalized version of the recovered-idiosyncratic perturbation
bound. Since `n⁻¹F'F = I`, the signal quadratic form is `n‖x‖²`; the bound
therefore says the recovered cross/noise Gram is strictly larger than
`-n‖x‖²` in every nonzero direction. -/
def factorRecoveredIdiosyncraticGramSmall
    (Λ : Matrix k r ℝ) (F : n → r → ℝ) (U : Matrix n k ℝ) : Prop :=
  ∀ x : r → ℝ, x ≠ 0 →
    - ((Fintype.card n : ℝ) * (x ⬝ᵥ x)) <
      x ⬝ᵥ ((factorRecoveredIdiosyncraticGramPerturbation Λ F U) *ᵥ x)

omit [DecidableEq n] [DecidableEq k] in
/-- Uniform Rayleigh quotient bound for the recovered-idiosyncratic Gram
perturbation. A sequence of these bounds with every positive tolerance is the
concrete matrix-convergence primitive used by the asymptotic bridge for Hansen
Theorem 11.9. -/
def factorRecoveredIdiosyncraticGramRayleighLE
    (Λ : Matrix k r ℝ) (F : n → r → ℝ) (U : Matrix n k ℝ)
    (δ : ℝ) : Prop :=
  ∀ x : r → ℝ, x ≠ 0 →
    |x ⬝ᵥ ((factorRecoveredIdiosyncraticGramPerturbation Λ F U) *ᵥ x)| ≤
      δ * ((Fintype.card n : ℝ) * (x ⬝ᵥ x))

omit [DecidableEq n] [DecidableEq k] in
/-- Uniform Rayleigh smallness with any tolerance below one is enough to keep
the recovered idiosyncratic perturbation from erasing Hansen's normalized
factor signal. -/
theorem factorRecoveredIdiosyncraticGramSmall_of_rayleighLE
    [Nonempty n] (Λ : Matrix k r ℝ) (F : n → r → ℝ)
    (U : Matrix n k ℝ) {δ : ℝ}
    (hδ : δ < 1)
    (h : factorRecoveredIdiosyncraticGramRayleighLE Λ F U δ) :
    factorRecoveredIdiosyncraticGramSmall Λ F U := by
  intro x hx
  have hx_nonneg : 0 ≤ x ⬝ᵥ x := by
    simpa using dotProduct_star_self_nonneg x
  have hx_ne_zero : x ⬝ᵥ x ≠ 0 := by
    intro hzero
    exact hx (dotProduct_self_eq_zero.mp hzero)
  have hx_pos : 0 < x ⬝ᵥ x :=
    lt_of_le_of_ne hx_nonneg hx_ne_zero.symm
  have hn_pos : 0 < (Fintype.card n : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hsignal_pos : 0 < (Fintype.card n : ℝ) * (x ⬝ᵥ x) :=
    mul_pos hn_pos hx_pos
  let q : ℝ :=
    x ⬝ᵥ ((factorRecoveredIdiosyncraticGramPerturbation Λ F U) *ᵥ x)
  have hq_lower :
      - (δ * ((Fintype.card n : ℝ) * (x ⬝ᵥ x))) ≤ q := by
    simpa [q] using (abs_le.mp (h x hx)).1
  have hstrict :
      - ((Fintype.card n : ℝ) * (x ⬝ᵥ x)) <
        - (δ * ((Fintype.card n : ℝ) * (x ⬝ᵥ x))) := by
    have hδ_signal :
        δ * ((Fintype.card n : ℝ) * (x ⬝ᵥ x)) <
          1 * ((Fintype.card n : ℝ) * (x ⬝ᵥ x)) :=
      mul_lt_mul_of_pos_right hδ hsignal_pos
    linarith
  exact lt_of_lt_of_le hstrict hq_lower

omit [DecidableEq n] [DecidableEq k] in
/-- Filter version of the recovered-idiosyncratic uniform Rayleigh
`o(1)` condition. For `l = atTop`, this states that the normalized recovered
cross/noise quadratic form is eventually below every positive tolerance,
uniformly over selected directions. -/
def factorRecoveredIdiosyncraticGramRayleighTendstoZero
    {ι : Type*} (l : Filter ι)
    (Λ : ι → Matrix k r ℝ) (F : ι → n → r → ℝ)
    (U : ι → Matrix n k ℝ) : Prop :=
  ∀ δ : ℝ, 0 < δ →
    Filter.Eventually
      (fun i => factorRecoveredIdiosyncraticGramRayleighLE
        (Λ i) (F i) (U i) δ) l

/-- Normalized recovered-idiosyncratic Gram perturbation.

This is the object to target with standard matrix WLLN or operator-norm
arguments: it is `n⁻¹(F'E + E'F + E'E)` after applying the loading-Gram
recoverer to the idiosyncratic component. -/
noncomputable def factorRecoveredIdiosyncraticGramNormalizedPerturbation
    (Λ : Matrix k r ℝ) (F : n → r → ℝ) (U : Matrix n k ℝ) :
    Matrix r r ℝ :=
  (Fintype.card n : ℝ)⁻¹ • factorRecoveredIdiosyncraticGramPerturbation Λ F U

/-- Normalized recovered factor/idiosyncratic cross term `n⁻¹F'E`. -/
noncomputable def factorRecoveredIdiosyncraticCrossLeftNormalized
    (Λ : Matrix k r ℝ) (F : n → r → ℝ) (U : Matrix n k ℝ) :
    Matrix r r ℝ :=
  (Fintype.card n : ℝ)⁻¹ •
    ((factorScoreDataMatrix F)ᵀ * factorRecoveredIdiosyncraticScoreMatrix Λ U)

/-- Normalized recovered idiosyncratic/factor cross term `n⁻¹E'F`. -/
noncomputable def factorRecoveredIdiosyncraticCrossRightNormalized
    (Λ : Matrix k r ℝ) (F : n → r → ℝ) (U : Matrix n k ℝ) :
    Matrix r r ℝ :=
  (Fintype.card n : ℝ)⁻¹ •
    ((factorRecoveredIdiosyncraticScoreMatrix Λ U)ᵀ * factorScoreDataMatrix F)

/-- Normalized recovered idiosyncratic Gram term `n⁻¹E'E`. -/
noncomputable def factorRecoveredIdiosyncraticNoiseGramNormalized
    (Λ : Matrix k r ℝ) (U : Matrix n k ℝ) : Matrix r r ℝ :=
  (Fintype.card n : ℝ)⁻¹ •
    ((factorRecoveredIdiosyncraticScoreMatrix Λ U)ᵀ *
      factorRecoveredIdiosyncraticScoreMatrix Λ U)

/-- Raw normalized factor/idiosyncratic cross moment `n⁻¹F'U`, before applying
the loading-Gram recoverer. -/
noncomputable def factorRawFactorIdiosyncraticCrossNormalized
    (F : n → r → ℝ) (U : Matrix n k ℝ) : Matrix r k ℝ :=
  (Fintype.card n : ℝ)⁻¹ • ((factorScoreDataMatrix F)ᵀ * U)

/-- Raw normalized idiosyncratic/factor cross moment `n⁻¹U'F`, before applying
the loading-Gram recoverer. -/
noncomputable def factorRawIdiosyncraticFactorCrossNormalized
    (F : n → r → ℝ) (U : Matrix n k ℝ) : Matrix k r ℝ :=
  (Fintype.card n : ℝ)⁻¹ • (Uᵀ * factorScoreDataMatrix F)

/-- Raw normalized idiosyncratic Gram moment `n⁻¹U'U`, before applying the
loading-Gram recoverer. -/
noncomputable def factorRawIdiosyncraticGramNormalized
    (U : Matrix n k ℝ) : Matrix k k ℝ :=
  (Fintype.card n : ℝ)⁻¹ • (Uᵀ * U)

omit [DecidableEq n] [DecidableEq k] in
/-- The recovered left cross term is the raw cross moment post-multiplied by
the loading-Gram recoverer. -/
theorem factorRecoveredIdiosyncraticCrossLeftNormalized_eq_raw_mul_recoverer
    (Λ : Matrix k r ℝ) (F : n → r → ℝ) (U : Matrix n k ℝ) :
    factorRecoveredIdiosyncraticCrossLeftNormalized Λ F U =
      factorRawFactorIdiosyncraticCrossNormalized F U *
        (factorLoadingGramRecoverer Λ)ᵀ := by
  simp [factorRecoveredIdiosyncraticCrossLeftNormalized,
    factorRecoveredIdiosyncraticScoreMatrix,
    factorRawFactorIdiosyncraticCrossNormalized, Matrix.mul_assoc,
    Matrix.smul_mul]

omit [DecidableEq n] [DecidableEq k] in
/-- The recovered right cross term is the raw cross moment pre-multiplied by
the loading-Gram recoverer. -/
theorem factorRecoveredIdiosyncraticCrossRightNormalized_eq_recoverer_mul_raw
    (Λ : Matrix k r ℝ) (F : n → r → ℝ) (U : Matrix n k ℝ) :
    factorRecoveredIdiosyncraticCrossRightNormalized Λ F U =
      factorLoadingGramRecoverer Λ *
        factorRawIdiosyncraticFactorCrossNormalized F U := by
  simp [factorRecoveredIdiosyncraticCrossRightNormalized,
    factorRecoveredIdiosyncraticScoreMatrix,
    factorRawIdiosyncraticFactorCrossNormalized, Matrix.transpose_mul,
    Matrix.transpose_transpose, Matrix.mul_assoc, Matrix.mul_smul]

omit [DecidableEq n] [DecidableEq k] in
/-- The recovered noise Gram is the raw idiosyncratic Gram sandwiched by the
loading-Gram recoverer. -/
theorem factorRecoveredIdiosyncraticNoiseGramNormalized_eq_recoverer_mul_raw_mul
    (Λ : Matrix k r ℝ) (U : Matrix n k ℝ) :
    factorRecoveredIdiosyncraticNoiseGramNormalized Λ U =
      factorLoadingGramRecoverer Λ *
        factorRawIdiosyncraticGramNormalized U *
          (factorLoadingGramRecoverer Λ)ᵀ := by
  simp [factorRecoveredIdiosyncraticNoiseGramNormalized,
    factorRecoveredIdiosyncraticScoreMatrix,
    factorRawIdiosyncraticGramNormalized, Matrix.transpose_mul,
    Matrix.transpose_transpose, Matrix.mul_assoc, Matrix.smul_mul,
    Matrix.mul_smul]

omit [DecidableEq n] [DecidableEq k] in
@[simp]
theorem factorRecoveredIdiosyncraticCrossLeftNormalized_apply
    (Λ : Matrix k r ℝ) (F : n → r → ℝ) (U : Matrix n k ℝ)
    (a b : r) :
    factorRecoveredIdiosyncraticCrossLeftNormalized Λ F U a b =
      (Fintype.card n : ℝ)⁻¹ *
        ∑ i : n, F i a * factorRecoveredIdiosyncraticScoreMatrix Λ U i b := by
  simp [factorRecoveredIdiosyncraticCrossLeftNormalized, Matrix.mul_apply,
    Matrix.transpose_apply, smul_eq_mul]

omit [DecidableEq n] [DecidableEq k] in
@[simp]
theorem factorRecoveredIdiosyncraticCrossRightNormalized_apply
    (Λ : Matrix k r ℝ) (F : n → r → ℝ) (U : Matrix n k ℝ)
    (a b : r) :
    factorRecoveredIdiosyncraticCrossRightNormalized Λ F U a b =
      (Fintype.card n : ℝ)⁻¹ *
        ∑ i : n, factorRecoveredIdiosyncraticScoreMatrix Λ U i a * F i b := by
  simp [factorRecoveredIdiosyncraticCrossRightNormalized, Matrix.mul_apply,
    Matrix.transpose_apply, smul_eq_mul]

omit [DecidableEq n] [DecidableEq k] in
@[simp]
theorem factorRecoveredIdiosyncraticNoiseGramNormalized_apply
    (Λ : Matrix k r ℝ) (U : Matrix n k ℝ) (a b : r) :
    factorRecoveredIdiosyncraticNoiseGramNormalized Λ U a b =
      (Fintype.card n : ℝ)⁻¹ *
        ∑ i : n,
          factorRecoveredIdiosyncraticScoreMatrix Λ U i a *
            factorRecoveredIdiosyncraticScoreMatrix Λ U i b := by
  simp [factorRecoveredIdiosyncraticNoiseGramNormalized, Matrix.mul_apply,
    Matrix.transpose_apply, smul_eq_mul]

omit [DecidableEq n] [DecidableEq k] in
/-- The normalized recovered perturbation is exactly Hansen's three
cross/noise terms `n⁻¹F'E + n⁻¹E'F + n⁻¹E'E`. -/
theorem factorRecoveredIdiosyncraticGramNormalizedPerturbation_eq_cross_add_noise
    (Λ : Matrix k r ℝ) (F : n → r → ℝ) (U : Matrix n k ℝ) :
    factorRecoveredIdiosyncraticGramNormalizedPerturbation Λ F U =
      factorRecoveredIdiosyncraticCrossLeftNormalized Λ F U +
        factorRecoveredIdiosyncraticCrossRightNormalized Λ F U +
          factorRecoveredIdiosyncraticNoiseGramNormalized Λ U := by
  simp [factorRecoveredIdiosyncraticGramNormalizedPerturbation,
    factorRecoveredIdiosyncraticGramPerturbation,
    factorRecoveredIdiosyncraticCrossLeftNormalized,
    factorRecoveredIdiosyncraticCrossRightNormalized,
    factorRecoveredIdiosyncraticNoiseGramNormalized, smul_add,
    add_assoc]

omit [DecidableEq n] [DecidableEq k] in
/-- Coordinate version of the normalized recovered perturbation decomposition. -/
theorem factorRecoveredIdiosyncraticGramNormalizedPerturbation_apply_eq_cross_add_noise
    (Λ : Matrix k r ℝ) (F : n → r → ℝ) (U : Matrix n k ℝ)
    (a b : r) :
    (factorRecoveredIdiosyncraticGramNormalizedPerturbation Λ F U) a b =
      factorRecoveredIdiosyncraticCrossLeftNormalized Λ F U a b +
        factorRecoveredIdiosyncraticCrossRightNormalized Λ F U a b +
          factorRecoveredIdiosyncraticNoiseGramNormalized Λ U a b := by
  rw [factorRecoveredIdiosyncraticGramNormalizedPerturbation_eq_cross_add_noise]
  rfl

omit [DecidableEq n] [DecidableEq k] in
/-- Rayleigh bound for the normalized recovered-idiosyncratic Gram
perturbation. This is the smaller stochastic primitive expected from a
matrix-WLLN/operator-norm proof. -/
def factorRecoveredIdiosyncraticGramNormalizedRayleighLE
    (Λ : Matrix k r ℝ) (F : n → r → ℝ) (U : Matrix n k ℝ)
    (δ : ℝ) : Prop :=
  ∀ x : r → ℝ, x ≠ 0 →
    |x ⬝ᵥ
        ((factorRecoveredIdiosyncraticGramNormalizedPerturbation Λ F U) *ᵥ x)| ≤
      δ * (x ⬝ᵥ x)

omit [DecidableEq n] [DecidableEq k] in
/-- A normalized Rayleigh bound is exactly the scale needed by the existing
unnormalized Theorem 11.9 perturbation bridge. -/
theorem factorRecoveredIdiosyncraticGramRayleighLE_of_normalizedRayleighLE
    [Nonempty n] (Λ : Matrix k r ℝ) (F : n → r → ℝ)
    (U : Matrix n k ℝ) {δ : ℝ}
    (h : factorRecoveredIdiosyncraticGramNormalizedRayleighLE Λ F U δ) :
    factorRecoveredIdiosyncraticGramRayleighLE Λ F U δ := by
  intro x hx
  have hn_pos : 0 < (Fintype.card n : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hn_nonneg : 0 ≤ (Fintype.card n : ℝ) := le_of_lt hn_pos
  have hnorm := h x hx
  have hscale :
      x ⬝ᵥ ((factorRecoveredIdiosyncraticGramPerturbation Λ F U) *ᵥ x) =
        (Fintype.card n : ℝ) *
          (x ⬝ᵥ
            ((factorRecoveredIdiosyncraticGramNormalizedPerturbation Λ F U) *ᵥ x)) := by
    simp [factorRecoveredIdiosyncraticGramNormalizedPerturbation,
      Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, hn_pos.ne']
  calc
    |x ⬝ᵥ ((factorRecoveredIdiosyncraticGramPerturbation Λ F U) *ᵥ x)|
        = (Fintype.card n : ℝ) *
            |x ⬝ᵥ
              ((factorRecoveredIdiosyncraticGramNormalizedPerturbation Λ F U) *ᵥ x)| := by
          rw [hscale, abs_mul, abs_of_nonneg hn_nonneg]
    _ ≤ (Fintype.card n : ℝ) * (δ * (x ⬝ᵥ x)) :=
          mul_le_mul_of_nonneg_left hnorm hn_nonneg
    _ = δ * ((Fintype.card n : ℝ) * (x ⬝ᵥ x)) := by ring

omit [DecidableEq n] [DecidableEq k] in
/-- Filter version of
`factorRecoveredIdiosyncraticGramNormalizedRayleighLE`. Proving this statement
by a standard WLLN/operator-norm argument closes the stochastic primitive used
by `ApproximateFactorAsymptoticPerturbationBridge`. -/
def factorRecoveredIdiosyncraticGramNormalizedRayleighTendstoZero
    {ι : Type*} (l : Filter ι)
    (Λ : ι → Matrix k r ℝ) (F : ι → n → r → ℝ)
    (U : ι → Matrix n k ℝ) : Prop :=
  ∀ δ : ℝ, 0 < δ →
    Filter.Eventually
      (fun i => factorRecoveredIdiosyncraticGramNormalizedRayleighLE
        (Λ i) (F i) (U i) δ) l

omit [DecidableEq n] [DecidableEq k] in
/-- Normalized recovered-Gram Rayleigh `o(1)` implies the unnormalized
Rayleigh `o(1)` condition currently consumed by the Hansen Theorem 11.9
asymptotic bridge. -/
theorem factorRecoveredIdiosyncraticGramRayleighTendstoZero_of_normalized
    [Nonempty n] {ι : Type*} {l : Filter ι}
    {Λ : ι → Matrix k r ℝ} {F : ι → n → r → ℝ}
    {U : ι → Matrix n k ℝ}
    (h :
      factorRecoveredIdiosyncraticGramNormalizedRayleighTendstoZero
        l Λ F U) :
    factorRecoveredIdiosyncraticGramRayleighTendstoZero l Λ F U := by
  intro δ hδ
  exact (h δ hδ).mono fun i hi =>
    factorRecoveredIdiosyncraticGramRayleighLE_of_normalizedRayleighLE
      (Λ i) (F i) (U i) hi

omit [DecidableEq n] [DecidableEq k] in
/-- Deterministic envelope for the normalized recovered-Gram Rayleigh quotient.

This is useful when the stochastic argument first proves an explicit scalar
operator-norm envelope `ρᵢ = o(1)`. -/
def factorRecoveredIdiosyncraticGramNormalizedRayleighEnvelopeLE
    (Λ : Matrix k r ℝ) (F : n → r → ℝ) (U : Matrix n k ℝ)
    (ρ : ℝ) : Prop :=
  ∀ x : r → ℝ, x ≠ 0 →
    |x ⬝ᵥ
        ((factorRecoveredIdiosyncraticGramNormalizedPerturbation Λ F U) *ᵥ x)| ≤
      ρ * (x ⬝ᵥ x)

omit [Fintype n] [Fintype k] [DecidableEq n] [DecidableEq k] in
/-- Entrywise envelope for the normalized recovered-idiosyncratic perturbation.

This is the deterministic handoff expected from a coordinatewise matrix WLLN:
each entry of `n⁻¹(F'E + E'F + E'E)` is bounded by the same scalar envelope. -/
def factorRecoveredIdiosyncraticGramNormalizedEntrywiseEnvelopeLE
    (Λ : Matrix k r ℝ) (F : n → r → ℝ) (U : Matrix n k ℝ)
    (η : ℝ) : Prop :=
  ∀ a b : r,
    |(factorRecoveredIdiosyncraticGramNormalizedPerturbation Λ F U) a b| ≤ η

/-- Canonical scalar envelope for coordinatewise control of the normalized
recovered-idiosyncratic perturbation: the sum of absolute values of all
matrix entries. -/
noncomputable def factorRecoveredIdiosyncraticGramNormalizedEntrywiseAbsSum
    (Λ : Matrix k r ℝ) (F : n → r → ℝ) (U : Matrix n k ℝ) : ℝ :=
  ∑ a : r, ∑ b : r,
    |(factorRecoveredIdiosyncraticGramNormalizedPerturbation Λ F U) a b|

omit [DecidableEq n] [DecidableEq k] in
/-- The canonical entrywise absolute-sum envelope is nonnegative. -/
theorem factorRecoveredIdiosyncraticGramNormalizedEntrywiseAbsSum_nonneg
    (Λ : Matrix k r ℝ) (F : n → r → ℝ) (U : Matrix n k ℝ) :
    0 ≤ factorRecoveredIdiosyncraticGramNormalizedEntrywiseAbsSum Λ F U := by
  exact Finset.sum_nonneg fun a _ =>
    Finset.sum_nonneg fun b _ => abs_nonneg _

omit [DecidableEq n] [DecidableEq k] in
/-- The canonical absolute-sum envelope dominates every entry of the normalized
recovered-idiosyncratic perturbation. -/
theorem factorRecoveredIdiosyncraticGramNormalizedEntrywiseEnvelopeLE_absSum
    (Λ : Matrix k r ℝ) (F : n → r → ℝ) (U : Matrix n k ℝ) :
    factorRecoveredIdiosyncraticGramNormalizedEntrywiseEnvelopeLE Λ F U
      (factorRecoveredIdiosyncraticGramNormalizedEntrywiseAbsSum Λ F U) := by
  intro a b
  have hrow :
      |(factorRecoveredIdiosyncraticGramNormalizedPerturbation Λ F U) a b| ≤
        ∑ b' : r,
          |(factorRecoveredIdiosyncraticGramNormalizedPerturbation Λ F U) a b'| := by
    exact Finset.single_le_sum
      (s := Finset.univ)
      (f := fun b' : r =>
        |(factorRecoveredIdiosyncraticGramNormalizedPerturbation Λ F U) a b'|)
      (fun b' _ => abs_nonneg _) (by simp)
  have hrows :
      (∑ b' : r,
          |(factorRecoveredIdiosyncraticGramNormalizedPerturbation Λ F U) a b'|) ≤
        ∑ a' : r, ∑ b' : r,
          |(factorRecoveredIdiosyncraticGramNormalizedPerturbation Λ F U) a' b'| := by
    exact Finset.single_le_sum
      (s := Finset.univ)
      (f := fun a' : r =>
        ∑ b' : r,
          |(factorRecoveredIdiosyncraticGramNormalizedPerturbation Λ F U) a' b'|)
      (fun a' _ => Finset.sum_nonneg fun b' _ => abs_nonneg _) (by simp)
  exact hrow.trans hrows

omit [DecidableEq n] [DecidableEq k] in
/-- Coordinate convergence of every normalized recovered-perturbation entry
implies convergence of the canonical absolute-sum envelope to zero.

This is the finite-dimensional glue between scalar coordinate WLLNs and the
entrywise-envelope bridge used by the factor-PCA perturbation theorem. -/
theorem factorRecoveredIdiosyncraticGramNormalizedEntrywiseAbsSum_tendsto_zero
    {ι : Type*} {l : Filter ι}
    {Λ : ι → Matrix k r ℝ} {F : ι → n → r → ℝ}
    {U : ι → Matrix n k ℝ}
    (hentry : ∀ a b : r,
      Filter.Tendsto
        (fun i =>
          (factorRecoveredIdiosyncraticGramNormalizedPerturbation
            (Λ i) (F i) (U i)) a b) l (nhds 0)) :
    Filter.Tendsto
      (fun i =>
        factorRecoveredIdiosyncraticGramNormalizedEntrywiseAbsSum
          (Λ i) (F i) (U i)) l (nhds 0) := by
  have habs : ∀ a b : r,
      Filter.Tendsto
        (fun i =>
          |(factorRecoveredIdiosyncraticGramNormalizedPerturbation
            (Λ i) (F i) (U i)) a b|) l (nhds 0) := by
    intro a b
    simpa using (continuous_abs.tendsto 0).comp (hentry a b)
  simpa [factorRecoveredIdiosyncraticGramNormalizedEntrywiseAbsSum] using
    (tendsto_finset_sum (Finset.univ : Finset r) (fun a _ =>
      tendsto_finset_sum (Finset.univ : Finset r) (fun b _ =>
        habs a b)))

omit [DecidableEq n] [DecidableEq k] in
/-- Coordinatewise control of the normalized recovered-idiosyncratic
perturbation supplies the Rayleigh envelope used by the PCA perturbation
bridge.

The proof is the finite-dimensional bound
`|x' M x| ≤ 2 r η x'x`, obtained from triangle inequality and
`2 |x_a x_b| ≤ x_a² + x_b²`. -/
theorem factorRecoveredIdiosyncraticGramNormalizedRayleighEnvelopeLE_of_entrywise
    (Λ : Matrix k r ℝ) (F : n → r → ℝ) (U : Matrix n k ℝ) {η : ℝ}
    (hη : 0 ≤ η)
    (hentry :
      factorRecoveredIdiosyncraticGramNormalizedEntrywiseEnvelopeLE Λ F U η) :
    factorRecoveredIdiosyncraticGramNormalizedRayleighEnvelopeLE Λ F U
      ((2 * (Fintype.card r : ℝ)) * η) := by
  intro x hx
  let M : Matrix r r ℝ := factorRecoveredIdiosyncraticGramNormalizedPerturbation Λ F U
  have hterm : ∀ a b : r,
      |x a * (M a b * x b)| ≤ η * (x a ^ 2 + x b ^ 2) := by
    intro a b
    have hxprod_nonneg : 0 ≤ |x a| * |x b| :=
      mul_nonneg (abs_nonneg _) (abs_nonneg _)
    have hxprod_le : |x a| * |x b| ≤ x a ^ 2 + x b ^ 2 := by
      have h2 := two_mul_le_add_sq |x a| |x b|
      have hprod_le_two : |x a| * |x b| ≤ 2 * |x a| * |x b| := by
        nlinarith [hxprod_nonneg]
      exact le_trans hprod_le_two (by simpa [sq_abs] using h2)
    calc
      |x a * (M a b * x b)| = |M a b| * (|x a| * |x b|) := by
        rw [abs_mul, abs_mul]
        ring
      _ ≤ η * (|x a| * |x b|) :=
        mul_le_mul_of_nonneg_right (hentry a b) hxprod_nonneg
      _ ≤ η * (x a ^ 2 + x b ^ 2) :=
        mul_le_mul_of_nonneg_left hxprod_le hη
  have hquad_abs :
      |x ⬝ᵥ (M *ᵥ x)| ≤ ∑ a : r, ∑ b : r, |x a * (M a b * x b)| := by
    calc
      |x ⬝ᵥ (M *ᵥ x)| =
          |∑ a : r, ∑ b : r, x a * (M a b * x b)| := by
            simp [dotProduct, Matrix.mulVec, Finset.mul_sum]
      _ ≤ ∑ a : r, |∑ b : r, x a * (M a b * x b)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ a : r, ∑ b : r, |x a * (M a b * x b)| := by
        exact Finset.sum_le_sum fun a _ => Finset.abs_sum_le_sum_abs _ _
  have hsum_bound :
      (∑ a : r, ∑ b : r, |x a * (M a b * x b)|) ≤
        ∑ a : r, ∑ b : r, η * (x a ^ 2 + x b ^ 2) := by
    exact Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => hterm a b
  have hsum_eq :
      (∑ a : r, ∑ b : r, η * (x a ^ 2 + x b ^ 2)) =
        ((2 * (Fintype.card r : ℝ)) * η) * (x ⬝ᵥ x) := by
    simp [dotProduct, Finset.sum_add_distrib, Finset.mul_sum,
      mul_add, mul_assoc, mul_left_comm, mul_comm]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro a _
    ring
  exact le_trans hquad_abs (le_trans hsum_bound (le_of_eq hsum_eq))

omit [DecidableEq n] [DecidableEq k] in
/-- A scalar envelope that converges to zero supplies the normalized Rayleigh
`o(1)` condition. This is the standard handoff point from a matrix
WLLN/operator-norm estimate to the factor-PCA perturbation bridge. -/
theorem factorRecoveredIdiosyncraticGramNormalizedRayleighTendstoZero_of_envelope
    {ι : Type*} {l : Filter ι}
    {Λ : ι → Matrix k r ℝ} {F : ι → n → r → ℝ}
    {U : ι → Matrix n k ℝ} {ρ : ι → ℝ}
    (hbound :
      Filter.Eventually
        (fun i =>
          factorRecoveredIdiosyncraticGramNormalizedRayleighEnvelopeLE
            (Λ i) (F i) (U i) (ρ i)) l)
    (hρ : Filter.Tendsto ρ l (nhds 0)) :
    factorRecoveredIdiosyncraticGramNormalizedRayleighTendstoZero l Λ F U := by
  intro δ hδ
  have hρδ : Filter.Eventually (fun i => ρ i < δ) l :=
    hρ.eventually_lt_const hδ
  filter_upwards [hbound, hρδ] with i hbi hρi
  intro x hx
  have hx_nonneg : 0 ≤ x ⬝ᵥ x := by
    simpa using dotProduct_star_self_nonneg x
  exact le_trans (hbi x hx)
    (mul_le_mul_of_nonneg_right (le_of_lt hρi) hx_nonneg)

omit [DecidableEq n] [DecidableEq k] in
/-- Combined envelope-to-bridge theorem: an `o(1)` scalar envelope for the
normalized recovered-Gram operator/Rayleigh quotient gives the existing
unnormalized uniform Rayleigh primitive. -/
theorem factorRecoveredIdiosyncraticGramRayleighTendstoZero_of_normalized_envelope
    [Nonempty n] {ι : Type*} {l : Filter ι}
    {Λ : ι → Matrix k r ℝ} {F : ι → n → r → ℝ}
    {U : ι → Matrix n k ℝ} {ρ : ι → ℝ}
    (hbound :
      Filter.Eventually
        (fun i =>
          factorRecoveredIdiosyncraticGramNormalizedRayleighEnvelopeLE
            (Λ i) (F i) (U i) (ρ i)) l)
    (hρ : Filter.Tendsto ρ l (nhds 0)) :
    factorRecoveredIdiosyncraticGramRayleighTendstoZero l Λ F U :=
  factorRecoveredIdiosyncraticGramRayleighTendstoZero_of_normalized
    (factorRecoveredIdiosyncraticGramNormalizedRayleighTendstoZero_of_envelope
      hbound hρ)

omit [DecidableEq n] [DecidableEq k] in
/-- Entrywise `o(1)` control of the normalized recovered perturbation supplies
the normalized Rayleigh `o(1)` primitive. -/
theorem factorRecoveredIdiosyncraticGramNormalizedRayleighTendstoZero_of_entrywise_envelope
    {ι : Type*} {l : Filter ι}
    {Λ : ι → Matrix k r ℝ} {F : ι → n → r → ℝ}
    {U : ι → Matrix n k ℝ} {η : ι → ℝ}
    (hη_nonneg : Filter.Eventually (fun i => 0 ≤ η i) l)
    (hentry :
      Filter.Eventually
        (fun i =>
          factorRecoveredIdiosyncraticGramNormalizedEntrywiseEnvelopeLE
            (Λ i) (F i) (U i) (η i)) l)
    (hη : Filter.Tendsto η l (nhds 0)) :
    factorRecoveredIdiosyncraticGramNormalizedRayleighTendstoZero l Λ F U :=
  factorRecoveredIdiosyncraticGramNormalizedRayleighTendstoZero_of_envelope
    (ρ := fun i => (2 * (Fintype.card r : ℝ)) * η i)
    (by
      filter_upwards [hη_nonneg, hentry] with i hηi hentryi
      exact
        factorRecoveredIdiosyncraticGramNormalizedRayleighEnvelopeLE_of_entrywise
          (Λ i) (F i) (U i) hηi hentryi)
    (by
      simpa using
        (hη.const_mul (2 * (Fintype.card r : ℝ))))

omit [DecidableEq n] [DecidableEq k] in
/-- Entrywise `o(1)` control of the normalized recovered perturbation supplies
the older unnormalized Rayleigh primitive. -/
theorem factorRecoveredIdiosyncraticGramRayleighTendstoZero_of_entrywise_envelope
    [Nonempty n] {ι : Type*} {l : Filter ι}
    {Λ : ι → Matrix k r ℝ} {F : ι → n → r → ℝ}
    {U : ι → Matrix n k ℝ} {η : ι → ℝ}
    (hη_nonneg : Filter.Eventually (fun i => 0 ≤ η i) l)
    (hentry :
      Filter.Eventually
        (fun i =>
          factorRecoveredIdiosyncraticGramNormalizedEntrywiseEnvelopeLE
            (Λ i) (F i) (U i) (η i)) l)
    (hη : Filter.Tendsto η l (nhds 0)) :
    factorRecoveredIdiosyncraticGramRayleighTendstoZero l Λ F U :=
  factorRecoveredIdiosyncraticGramRayleighTendstoZero_of_normalized
    (factorRecoveredIdiosyncraticGramNormalizedRayleighTendstoZero_of_entrywise_envelope
      hη_nonneg hentry hη)

omit [Fintype k] [DecidableEq n] [DecidableEq k] in
/-- Under Hansen's score normalization, the raw factor-score Gram quadratic
form is `n‖x‖²`. -/
theorem factorScoreDataMatrix_gram_quadratic_eq_card_mul_of_scoreNormalization
    [Nonempty n] (F : n → r → ℝ) (hF : factorScoreNormalization F)
    (x : r → ℝ) :
    x ⬝ᵥ (((factorScoreDataMatrix F)ᵀ * factorScoreDataMatrix F) *ᵥ x) =
      (Fintype.card n : ℝ) * (x ⬝ᵥ x) := by
  have hncard : (Fintype.card n : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hgram :
      (factorScoreDataMatrix F)ᵀ * factorScoreDataMatrix F =
        (Fintype.card n : ℝ) • (1 : Matrix r r ℝ) := by
    calc
      (factorScoreDataMatrix F)ᵀ * factorScoreDataMatrix F =
          (Fintype.card n : ℝ) •
            ((Fintype.card n : ℝ)⁻¹ •
              ((factorScoreDataMatrix F)ᵀ * factorScoreDataMatrix F)) := by
            rw [smul_smul, mul_inv_cancel₀ hncard, one_smul]
      _ = (Fintype.card n : ℝ) • factorScoreSampleCovariance F := by
            rw [factorScoreSampleCovariance_eq_card_inv_smul_transpose_mul]
      _ = (Fintype.card n : ℝ) • (1 : Matrix r r ℝ) := by
            rw [hF]
  simp [hgram, Matrix.smul_mulVec, dotProduct_smul]

omit [DecidableEq n] [DecidableEq k] in
/-- Hansen's normalized perturbation bound implies domination by the raw
factor-score signal Gram. -/
theorem factorRecoveredIdiosyncraticGramDominated_of_scoreNormalization
    [Nonempty n] (Λ : Matrix k r ℝ) (F : n → r → ℝ) (U : Matrix n k ℝ)
    (hF : factorScoreNormalization F)
    (hsmall : factorRecoveredIdiosyncraticGramSmall Λ F U) :
    factorRecoveredIdiosyncraticGramDominated Λ F U := by
  intro x hx
  simpa [factorScoreDataMatrix_gram_quadratic_eq_card_mul_of_scoreNormalization
    F hF x] using hsmall x hx

omit [DecidableEq n] [DecidableEq k] in
/-- If the recovered idiosyncratic Gram perturbation is dominated by the factor
signal Gram, the recovered score matrix `F + E` has positive definite Gram. -/
theorem factorRecoveredScoreGram_posDef_of_idiosyncraticGramDominated
    (Λ : Matrix k r ℝ) (F : n → r → ℝ) (U : Matrix n k ℝ)
    (hdom : factorRecoveredIdiosyncraticGramDominated Λ F U) :
    ((factorScoreDataMatrix F + factorRecoveredIdiosyncraticScoreMatrix Λ U)ᵀ *
        (factorScoreDataMatrix F +
          factorRecoveredIdiosyncraticScoreMatrix Λ U)).PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ ?_
  · simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.isHermitian_conjTranspose_mul_self
        (factorScoreDataMatrix F + factorRecoveredIdiosyncraticScoreMatrix Λ U)
  · intro x hx
    have hdomx := hdom x hx
    have hquad :
        x ⬝ᵥ
            ((((factorScoreDataMatrix F +
                    factorRecoveredIdiosyncraticScoreMatrix Λ U)ᵀ *
                  (factorScoreDataMatrix F +
                    factorRecoveredIdiosyncraticScoreMatrix Λ U)) *ᵥ x)) =
          x ⬝ᵥ (((factorScoreDataMatrix F)ᵀ *
              factorScoreDataMatrix F) *ᵥ x) +
            x ⬝ᵥ
              ((factorRecoveredIdiosyncraticGramPerturbation Λ F U) *ᵥ x) := by
      rw [factorScore_add_recoveredIdiosyncratic_gram_eq_signal_add_perturbation]
      rw [Matrix.add_mulVec, dotProduct_add]
    have hquad_star :
        star x ⬝ᵥ
            ((((factorScoreDataMatrix F +
                    factorRecoveredIdiosyncraticScoreMatrix Λ U)ᵀ *
                  (factorScoreDataMatrix F +
                    factorRecoveredIdiosyncraticScoreMatrix Λ U)) *ᵥ x)) =
          x ⬝ᵥ (((factorScoreDataMatrix F)ᵀ *
              factorScoreDataMatrix F) *ᵥ x) +
            x ⬝ᵥ
              ((factorRecoveredIdiosyncraticGramPerturbation Λ F U) *ᵥ x) := by
      simpa using hquad
    rw [hquad_star]
    linarith

omit [DecidableEq n] [DecidableEq k] in
/-- Dominated recovered idiosyncratic cross/noise terms preserve full selected
rank of the recovered score matrix. -/
theorem factorRecoveredScoreDataMatrix_rank_eq_card_of_idiosyncraticGramDominated
    (Λ : Matrix k r ℝ) (F : n → r → ℝ) (U : Matrix n k ℝ)
    (hdom : factorRecoveredIdiosyncraticGramDominated Λ F U) :
    (factorScoreDataMatrix F +
        factorRecoveredIdiosyncraticScoreMatrix Λ U).rank = Fintype.card r := by
  let Z : Matrix n r ℝ :=
    factorScoreDataMatrix F + factorRecoveredIdiosyncraticScoreMatrix Λ U
  have hpos : (Zᵀ * Z).PosDef := by
    simpa [Z] using
      factorRecoveredScoreGram_posDef_of_idiosyncraticGramDominated Λ F U hdom
  have hunit : IsUnit (Zᵀ * Z) := hpos.isUnit
  have hrankGram : (Zᵀ * Z).rank = Fintype.card r :=
    Matrix.rank_of_isUnit (Zᵀ * Z) hunit
  rw [Matrix.rank_transpose_mul_self Z] at hrankGram
  simpa [Z] using hrankGram

omit [DecidableEq n] [DecidableEq k] in
/-- Additive approximate-factor rank bridge with nonzero recovered
idiosyncratic terms.

The idiosyncratic component may survive multiplication by the loading-Gram
recoverer. It is enough that its recovered cross/noise Gram perturbation be
strictly dominated by the factor signal Gram, so `XL' = F + E` remains full
rank. -/
theorem factorDataMatrix_rank_ge_of_approx_factor_recovered_perturbation
    (X : n → k → ℝ) (Λ : Matrix k r ℝ) (F : n → r → ℝ)
    (U : Matrix n k ℝ)
    (hApprox : factorApproxSampleFactorModel X Λ F U)
    (hΛ : IsUnit (Λᵀ * Λ).det)
    (hdom : factorRecoveredIdiosyncraticGramDominated Λ F U) :
    Fintype.card r ≤ (factorDataMatrix X).rank := by
  have hrecover :=
    factorRecoveredScoreDataMatrix_eq_factorScore_add_idiosyncratic
      X Λ F U hApprox hΛ
  have hrankZ :=
    factorRecoveredScoreDataMatrix_rank_eq_card_of_idiosyncraticGramDominated
      Λ F U hdom
  have hrank_le :
      (factorScoreDataMatrix F +
          factorRecoveredIdiosyncraticScoreMatrix Λ U).rank ≤
        (factorDataMatrix X).rank := by
    rw [← hrecover]
    exact Matrix.rank_mul_le_left (factorDataMatrix X)
      (factorLoadingGramRecoverer Λ)ᵀ
  simpa [hrankZ] using hrank_le

/-- Hansen-shaped finite-sample pervasiveness/idiosyncratic package for the
approximate-factor rank bridge.

The loading Gram matrix is nonsingular, so `(Λ'Λ)^{-1}Λ'` is a concrete
recoverer; the idiosyncratic component is sample-orthogonal to the loading
columns, so this recoverer removes `U`; and the true factor-score sample has
selected rank `r`. -/
structure ApproximateSampleFactorPervasiveCondition
    (X : n → k → ℝ) (Λ : Matrix k r ℝ) (F : n → r → ℝ)
    (U : Matrix n k ℝ) : Prop where
  approximate_factor : factorApproxSampleFactorModel X Λ F U
  loading_gram_nonsingular : IsUnit (Λᵀ * Λ).det
  idiosyncratic_loading_orthogonal : U * Λ = 0
  sample_factor_rank : (factorScoreDataMatrix F).rank = Fintype.card r

namespace ApproximateSampleFactorPervasiveCondition

omit [Fintype n] [DecidableEq n] [DecidableEq k] in
/-- Convert the Hansen-shaped finite-sample pervasiveness and idiosyncratic
orthogonality package into the existing recoverability/rank package. -/
theorem toApproximateSampleFactorRankCondition
    {X : n → k → ℝ} {Λ : Matrix k r ℝ} {F : n → r → ℝ}
    {U : Matrix n k ℝ}
    (h : ApproximateSampleFactorPervasiveCondition X Λ F U) :
    ApproximateSampleFactorRankCondition X Λ F U where
  approximate_factor := h.approximate_factor
  recoverable_loadings :=
    ⟨factorLoadingGramRecoverer Λ,
      factorLoadingGramRecoverer_leftInverse Λ h.loading_gram_nonsingular,
      factorLoadingGramRecoverer_annihilates_idiosyncratic Λ U
        h.idiosyncratic_loading_orthogonal⟩
  sample_factor_rank := h.sample_factor_rank

end ApproximateSampleFactorPervasiveCondition

/-- Primitive finite-sample Hansen-style approximate-factor package.

Compared with `ApproximateSampleFactorPervasiveCondition`, this package does
not assume determinant nonsingularity or raw factor-score rank directly. It
uses a quantitative loading-pervasiveness lower bound, row-wise idiosyncratic
orthogonality to the loading columns, and Hansen's sample factor normalization
`n⁻¹F'F = I_r`; the conversion theorem below derives the older finite-sample
recoverability facade. -/
structure ApproximateSampleFactorPrimitiveCondition
    (X : n → k → ℝ) (Λ : Matrix k r ℝ) (F : n → r → ℝ)
    (U : Matrix n k ℝ) : Prop where
  approximate_factor : factorApproxSampleFactorModel X Λ F U
  loading_pervasiveness : factorLoadingPervasiveness Λ
  idiosyncratic_loading_orthogonality :
    factorIdiosyncraticLoadingOrthogonality U Λ
  sample_factor_normalization : factorScoreNormalization F

namespace ApproximateSampleFactorPrimitiveCondition

omit [DecidableEq n] [DecidableEq k] in
/-- Convert the primitive sample-factor/pervasiveness/idiosyncratic package
into the existing finite-sample pervasiveness facade. -/
theorem toApproximateSampleFactorPervasiveCondition
    {X : n → k → ℝ} {Λ : Matrix k r ℝ} {F : n → r → ℝ}
    {U : Matrix n k ℝ}
    (h : ApproximateSampleFactorPrimitiveCondition X Λ F U) :
    ApproximateSampleFactorPervasiveCondition X Λ F U where
  approximate_factor := h.approximate_factor
  loading_gram_nonsingular :=
    factorLoadingGram_nonsingular_of_pervasiveness Λ h.loading_pervasiveness
  idiosyncratic_loading_orthogonal :=
    factorIdiosyncraticLoadingOrthogonality_matrix_eq_zero U Λ
      h.idiosyncratic_loading_orthogonality
  sample_factor_rank :=
    factorScoreDataMatrix_rank_eq_card_of_scoreNormalization F
      h.sample_factor_normalization

omit [DecidableEq n] [DecidableEq k] in
/-- Convert the primitive Hansen-style package directly into the additive
recoverability/rank package. -/
theorem toApproximateSampleFactorRankCondition
    {X : n → k → ℝ} {Λ : Matrix k r ℝ} {F : n → r → ℝ}
    {U : Matrix n k ℝ}
    (h : ApproximateSampleFactorPrimitiveCondition X Λ F U) :
    ApproximateSampleFactorRankCondition X Λ F U :=
  ApproximateSampleFactorPervasiveCondition.toApproximateSampleFactorRankCondition
    (ApproximateSampleFactorPrimitiveCondition.toApproximateSampleFactorPervasiveCondition h)

end ApproximateSampleFactorPrimitiveCondition

/-- Primitive finite-sample approximate-factor perturbation package.

This is weaker than the exact idiosyncratic-orthogonality route: it does not
require `UΛ = 0` or `U ((Λ'Λ)^{-1}Λ')' = 0`. Instead, after applying the
loading-Gram recoverer, the realized idiosyncratic cross/noise Gram
`F'E + E'F + E'E` must be strictly too small to erase the normalized factor
signal in any selected direction. -/
structure ApproximateSampleFactorPerturbationCondition
    (X : n → k → ℝ) (Λ : Matrix k r ℝ) (F : n → r → ℝ)
    (U : Matrix n k ℝ) : Prop where
  approximate_factor : factorApproxSampleFactorModel X Λ F U
  loading_pervasiveness : factorLoadingPervasiveness Λ
  sample_factor_normalization : factorScoreNormalization F
  recovered_idiosyncratic_gram_small :
    factorRecoveredIdiosyncraticGramSmall Λ F U

namespace ApproximateSampleFactorPerturbationCondition

omit [DecidableEq n] [DecidableEq k] in
/-- The normalized perturbation package gives the raw domination condition
needed by the recovered-score rank bridge. -/
theorem recovered_idiosyncratic_gram_dominated
    [Nonempty n] {X : n → k → ℝ} {Λ : Matrix k r ℝ} {F : n → r → ℝ}
    {U : Matrix n k ℝ}
    (h : ApproximateSampleFactorPerturbationCondition X Λ F U) :
    factorRecoveredIdiosyncraticGramDominated Λ F U :=
  factorRecoveredIdiosyncraticGramDominated_of_scoreNormalization Λ F U
    h.sample_factor_normalization h.recovered_idiosyncratic_gram_small

end ApproximateSampleFactorPerturbationCondition

/-- Hansen-style asymptotic perturbation bridge for approximate factor models.

This is the theorem-facing boundary left after the deterministic PCA proof is
closed. It packages eventual exact sample model algebra, loading
pervasiveness, factor-score normalization, and a concrete uniform Rayleigh
`o(1)` bound for the recovered idiosyncratic cross/noise Gram. The last field is
the stochastic spectral-perturbation primitive that future probability work can
derive from Hansen's bounded idiosyncratic covariance and cross-term
assumptions. -/
structure ApproximateFactorAsymptoticPerturbationBridge
    {ι : Type*} (l : Filter ι)
    (X : ι → n → k → ℝ) (Λ : ι → Matrix k r ℝ)
    (F : ι → n → r → ℝ) (U : ι → Matrix n k ℝ) : Prop where
  eventually_approximate_factor :
    Filter.Eventually
      (fun i => factorApproxSampleFactorModel (X i) (Λ i) (F i) (U i)) l
  eventually_loading_pervasiveness :
    Filter.Eventually (fun i => factorLoadingPervasiveness (Λ i)) l
  eventually_score_normalization :
    Filter.Eventually (fun i => factorScoreNormalization (F i)) l
  recovered_rayleigh_tendsto_zero :
    factorRecoveredIdiosyncraticGramRayleighTendstoZero l Λ F U

namespace ApproximateFactorAsymptoticPerturbationBridge

omit [DecidableEq n] [DecidableEq k] in
/-- The asymptotic perturbation bridge eventually supplies the finite-sample
perturbation package already consumed by the deterministic Theorem 11.9 route. -/
theorem eventually_perturbationCondition
    [Nonempty n] {ι : Type*} {l : Filter ι}
    {X : ι → n → k → ℝ} {Λ : ι → Matrix k r ℝ}
    {F : ι → n → r → ℝ} {U : ι → Matrix n k ℝ}
    (h : ApproximateFactorAsymptoticPerturbationBridge l X Λ F U) :
    Filter.Eventually
      (fun i => ApproximateSampleFactorPerturbationCondition
        (X i) (Λ i) (F i) (U i)) l := by
  refine
    (h.eventually_approximate_factor.and
      (h.eventually_loading_pervasiveness.and
        (h.eventually_score_normalization.and
          (h.recovered_rayleigh_tendsto_zero (1 / 2) (by norm_num))))).mono ?_
  intro i hi
  rcases hi with ⟨hApprox, hLoad, hNorm, hRayleigh⟩
  exact
    { approximate_factor := hApprox
      loading_pervasiveness := hLoad
      sample_factor_normalization := hNorm
      recovered_idiosyncratic_gram_small :=
        factorRecoveredIdiosyncraticGramSmall_of_rayleighLE
          (Λ i) (F i) (U i) (by norm_num) hRayleigh }

end ApproximateFactorAsymptoticPerturbationBridge

/-- Hansen-style asymptotic bridge using the normalized recovered
idiosyncratic Gram perturbation.

This is the natural stochastic target for Theorem 11.9: prove uniform
Rayleigh `o(1)` for `n⁻¹(F'E + E'F + E'E)` after applying the loading-Gram
recoverer, then reuse the deterministic PCA proof. -/
structure ApproximateFactorAsymptoticNormalizedRayleighBridge
    {ι : Type*} (l : Filter ι)
    (X : ι → n → k → ℝ) (Λ : ι → Matrix k r ℝ)
    (F : ι → n → r → ℝ) (U : ι → Matrix n k ℝ) : Prop where
  eventually_approximate_factor :
    Filter.Eventually
      (fun i => factorApproxSampleFactorModel (X i) (Λ i) (F i) (U i)) l
  eventually_loading_pervasiveness :
    Filter.Eventually (fun i => factorLoadingPervasiveness (Λ i)) l
  eventually_score_normalization :
    Filter.Eventually (fun i => factorScoreNormalization (F i)) l
  normalized_rayleigh_tendsto_zero :
    factorRecoveredIdiosyncraticGramNormalizedRayleighTendstoZero l Λ F U

namespace ApproximateFactorAsymptoticNormalizedRayleighBridge

omit [DecidableEq n] [DecidableEq k] in
/-- The normalized-Rayleigh bridge supplies the older unnormalized perturbation
bridge consumed by the existing finite-sample Theorem 11.9 route. -/
theorem toPerturbationBridge
    [Nonempty n] {ι : Type*} {l : Filter ι}
    {X : ι → n → k → ℝ} {Λ : ι → Matrix k r ℝ}
    {F : ι → n → r → ℝ} {U : ι → Matrix n k ℝ}
    (h : ApproximateFactorAsymptoticNormalizedRayleighBridge l X Λ F U) :
    ApproximateFactorAsymptoticPerturbationBridge l X Λ F U where
  eventually_approximate_factor := h.eventually_approximate_factor
  eventually_loading_pervasiveness := h.eventually_loading_pervasiveness
  eventually_score_normalization := h.eventually_score_normalization
  recovered_rayleigh_tendsto_zero :=
    factorRecoveredIdiosyncraticGramRayleighTendstoZero_of_normalized
      h.normalized_rayleigh_tendsto_zero

end ApproximateFactorAsymptoticNormalizedRayleighBridge

/-- Hansen-style asymptotic bridge using a scalar envelope for the normalized
recovered idiosyncratic Gram Rayleigh quotient.

This is the handoff point for an operator-norm or matrix-WLLN proof: a scalar
envelope `ρᵢ = o(1)` implies the normalized Rayleigh bridge and hence the
Theorem 11.9 PCA conclusion. -/
structure ApproximateFactorAsymptoticNormalizedEnvelopeBridge
    {ι : Type*} (l : Filter ι)
    (X : ι → n → k → ℝ) (Λ : ι → Matrix k r ℝ)
    (F : ι → n → r → ℝ) (U : ι → Matrix n k ℝ)
    (ρ : ι → ℝ) : Prop where
  eventually_approximate_factor :
    Filter.Eventually
      (fun i => factorApproxSampleFactorModel (X i) (Λ i) (F i) (U i)) l
  eventually_loading_pervasiveness :
    Filter.Eventually (fun i => factorLoadingPervasiveness (Λ i)) l
  eventually_score_normalization :
    Filter.Eventually (fun i => factorScoreNormalization (F i)) l
  eventually_normalized_envelope :
    Filter.Eventually
      (fun i =>
        factorRecoveredIdiosyncraticGramNormalizedRayleighEnvelopeLE
          (Λ i) (F i) (U i) (ρ i)) l
  envelope_tendsto_zero : Filter.Tendsto ρ l (nhds 0)

namespace ApproximateFactorAsymptoticNormalizedEnvelopeBridge

omit [DecidableEq n] [DecidableEq k] in
/-- A normalized scalar-envelope bridge supplies the normalized-Rayleigh
bridge used by the theorem-facing PCA route. -/
theorem toNormalizedRayleighBridge
    {ι : Type*} {l : Filter ι}
    {X : ι → n → k → ℝ} {Λ : ι → Matrix k r ℝ}
    {F : ι → n → r → ℝ} {U : ι → Matrix n k ℝ}
    {ρ : ι → ℝ}
    (h : ApproximateFactorAsymptoticNormalizedEnvelopeBridge l X Λ F U ρ) :
    ApproximateFactorAsymptoticNormalizedRayleighBridge l X Λ F U where
  eventually_approximate_factor := h.eventually_approximate_factor
  eventually_loading_pervasiveness := h.eventually_loading_pervasiveness
  eventually_score_normalization := h.eventually_score_normalization
  normalized_rayleigh_tendsto_zero :=
    factorRecoveredIdiosyncraticGramNormalizedRayleighTendstoZero_of_envelope
      h.eventually_normalized_envelope h.envelope_tendsto_zero

omit [DecidableEq n] [DecidableEq k] in
/-- A normalized scalar-envelope bridge supplies the older unnormalized
perturbation bridge consumed by the existing deterministic proof. -/
theorem toPerturbationBridge
    [Nonempty n] {ι : Type*} {l : Filter ι}
    {X : ι → n → k → ℝ} {Λ : ι → Matrix k r ℝ}
    {F : ι → n → r → ℝ} {U : ι → Matrix n k ℝ}
    {ρ : ι → ℝ}
    (h : ApproximateFactorAsymptoticNormalizedEnvelopeBridge l X Λ F U ρ) :
    ApproximateFactorAsymptoticPerturbationBridge l X Λ F U :=
  ApproximateFactorAsymptoticNormalizedRayleighBridge.toPerturbationBridge
    (ApproximateFactorAsymptoticNormalizedEnvelopeBridge.toNormalizedRayleighBridge h)

end ApproximateFactorAsymptoticNormalizedEnvelopeBridge

/-- Hansen-style asymptotic bridge using an entrywise scalar envelope for the
normalized recovered idiosyncratic Gram perturbation.

This is the coordinatewise-WLLN-facing version of the normalized envelope
bridge: if every recovered perturbation entry is bounded by `ηᵢ = o(1)`, then
finite dimensionality turns that into the uniform Rayleigh condition consumed
by the deterministic PCA proof. -/
structure ApproximateFactorAsymptoticEntrywiseEnvelopeBridge
    {ι : Type*} (l : Filter ι)
    (X : ι → n → k → ℝ) (Λ : ι → Matrix k r ℝ)
    (F : ι → n → r → ℝ) (U : ι → Matrix n k ℝ)
    (η : ι → ℝ) : Prop where
  eventually_approximate_factor :
    Filter.Eventually
      (fun i => factorApproxSampleFactorModel (X i) (Λ i) (F i) (U i)) l
  eventually_loading_pervasiveness :
    Filter.Eventually (fun i => factorLoadingPervasiveness (Λ i)) l
  eventually_score_normalization :
    Filter.Eventually (fun i => factorScoreNormalization (F i)) l
  eventually_entrywise_envelope_nonneg :
    Filter.Eventually (fun i => 0 ≤ η i) l
  eventually_entrywise_envelope :
    Filter.Eventually
      (fun i =>
        factorRecoveredIdiosyncraticGramNormalizedEntrywiseEnvelopeLE
          (Λ i) (F i) (U i) (η i)) l
  entrywise_envelope_tendsto_zero : Filter.Tendsto η l (nhds 0)

namespace ApproximateFactorAsymptoticEntrywiseEnvelopeBridge

omit [DecidableEq n] [DecidableEq k] in
/-- An entrywise normalized perturbation envelope supplies the
normalized-Rayleigh bridge used by the theorem-facing PCA route. -/
theorem toNormalizedRayleighBridge
    {ι : Type*} {l : Filter ι}
    {X : ι → n → k → ℝ} {Λ : ι → Matrix k r ℝ}
    {F : ι → n → r → ℝ} {U : ι → Matrix n k ℝ}
    {η : ι → ℝ}
    (h : ApproximateFactorAsymptoticEntrywiseEnvelopeBridge l X Λ F U η) :
    ApproximateFactorAsymptoticNormalizedRayleighBridge l X Λ F U where
  eventually_approximate_factor := h.eventually_approximate_factor
  eventually_loading_pervasiveness := h.eventually_loading_pervasiveness
  eventually_score_normalization := h.eventually_score_normalization
  normalized_rayleigh_tendsto_zero :=
    factorRecoveredIdiosyncraticGramNormalizedRayleighTendstoZero_of_entrywise_envelope
      h.eventually_entrywise_envelope_nonneg h.eventually_entrywise_envelope
      h.entrywise_envelope_tendsto_zero

omit [DecidableEq n] [DecidableEq k] in
/-- An entrywise normalized perturbation envelope supplies the older
unnormalized perturbation bridge consumed by the deterministic proof. -/
theorem toPerturbationBridge
    [Nonempty n] {ι : Type*} {l : Filter ι}
    {X : ι → n → k → ℝ} {Λ : ι → Matrix k r ℝ}
    {F : ι → n → r → ℝ} {U : ι → Matrix n k ℝ}
    {η : ι → ℝ}
    (h : ApproximateFactorAsymptoticEntrywiseEnvelopeBridge l X Λ F U η) :
    ApproximateFactorAsymptoticPerturbationBridge l X Λ F U :=
  ApproximateFactorAsymptoticNormalizedRayleighBridge.toPerturbationBridge
    (ApproximateFactorAsymptoticEntrywiseEnvelopeBridge.toNormalizedRayleighBridge h)

end ApproximateFactorAsymptoticEntrywiseEnvelopeBridge

/-- Hansen-style asymptotic bridge whose stochastic input is coordinate
convergence of the normalized recovered-idiosyncratic perturbation.

This is the direct handoff from scalar coordinate WLLNs for the entries of
`n⁻¹(F'E + E'F + E'E)` after loading-Gram recovery. Finite dimensionality turns
those coordinate limits into the existing entrywise-envelope bridge. -/
structure ApproximateFactorAsymptoticCoordinateWLLNBridge
    {ι : Type*} (l : Filter ι)
    (X : ι → n → k → ℝ) (Λ : ι → Matrix k r ℝ)
    (F : ι → n → r → ℝ) (U : ι → Matrix n k ℝ) : Prop where
  eventually_approximate_factor :
    Filter.Eventually
      (fun i => factorApproxSampleFactorModel (X i) (Λ i) (F i) (U i)) l
  eventually_loading_pervasiveness :
    Filter.Eventually (fun i => factorLoadingPervasiveness (Λ i)) l
  eventually_score_normalization :
    Filter.Eventually (fun i => factorScoreNormalization (F i)) l
  normalized_entry_tendsto_zero : ∀ a b : r,
    Filter.Tendsto
      (fun i =>
        (factorRecoveredIdiosyncraticGramNormalizedPerturbation
          (Λ i) (F i) (U i)) a b) l (nhds 0)

namespace ApproximateFactorAsymptoticCoordinateWLLNBridge

omit [DecidableEq n] [DecidableEq k] in
/-- Coordinate WLLNs supply the existing entrywise-envelope bridge with the
canonical absolute-sum envelope. -/
theorem toEntrywiseEnvelopeBridge
    {ι : Type*} {l : Filter ι}
    {X : ι → n → k → ℝ} {Λ : ι → Matrix k r ℝ}
    {F : ι → n → r → ℝ} {U : ι → Matrix n k ℝ}
    (h : ApproximateFactorAsymptoticCoordinateWLLNBridge l X Λ F U) :
    ApproximateFactorAsymptoticEntrywiseEnvelopeBridge l X Λ F U
      (fun i =>
        factorRecoveredIdiosyncraticGramNormalizedEntrywiseAbsSum
          (Λ i) (F i) (U i)) where
  eventually_approximate_factor := h.eventually_approximate_factor
  eventually_loading_pervasiveness := h.eventually_loading_pervasiveness
  eventually_score_normalization := h.eventually_score_normalization
  eventually_entrywise_envelope_nonneg :=
    Filter.Eventually.of_forall fun i =>
      factorRecoveredIdiosyncraticGramNormalizedEntrywiseAbsSum_nonneg
        (Λ i) (F i) (U i)
  eventually_entrywise_envelope :=
    Filter.Eventually.of_forall fun i =>
      factorRecoveredIdiosyncraticGramNormalizedEntrywiseEnvelopeLE_absSum
        (Λ i) (F i) (U i)
  entrywise_envelope_tendsto_zero :=
    factorRecoveredIdiosyncraticGramNormalizedEntrywiseAbsSum_tendsto_zero
      h.normalized_entry_tendsto_zero

omit [DecidableEq n] [DecidableEq k] in
/-- Coordinate WLLNs supply the normalized-Rayleigh bridge used by the
theorem-facing PCA route. -/
theorem toNormalizedRayleighBridge
    {ι : Type*} {l : Filter ι}
    {X : ι → n → k → ℝ} {Λ : ι → Matrix k r ℝ}
    {F : ι → n → r → ℝ} {U : ι → Matrix n k ℝ}
    (h : ApproximateFactorAsymptoticCoordinateWLLNBridge l X Λ F U) :
    ApproximateFactorAsymptoticNormalizedRayleighBridge l X Λ F U :=
  ApproximateFactorAsymptoticEntrywiseEnvelopeBridge.toNormalizedRayleighBridge
    (ApproximateFactorAsymptoticCoordinateWLLNBridge.toEntrywiseEnvelopeBridge h)

omit [DecidableEq n] [DecidableEq k] in
/-- Coordinate WLLNs supply the older unnormalized perturbation bridge consumed
by the deterministic finite-sample proof. -/
theorem toPerturbationBridge
    [Nonempty n] {ι : Type*} {l : Filter ι}
    {X : ι → n → k → ℝ} {Λ : ι → Matrix k r ℝ}
    {F : ι → n → r → ℝ} {U : ι → Matrix n k ℝ}
    (h : ApproximateFactorAsymptoticCoordinateWLLNBridge l X Λ F U) :
    ApproximateFactorAsymptoticPerturbationBridge l X Λ F U :=
  ApproximateFactorAsymptoticNormalizedRayleighBridge.toPerturbationBridge
    (ApproximateFactorAsymptoticCoordinateWLLNBridge.toNormalizedRayleighBridge h)

end ApproximateFactorAsymptoticCoordinateWLLNBridge

/-- Hansen-style asymptotic bridge whose stochastic input is a matrix/operator
WLLN for the whole normalized recovered-idiosyncratic perturbation
`n⁻¹(F'E + E'F + E'E)`.

Finite-dimensional coordinate projection converts this operator target into
the existing coordinate-WLLN bridge. -/
structure ApproximateFactorAsymptoticMatrixWLLNBridge
    {ι : Type*} (l : Filter ι)
    (X : ι → n → k → ℝ) (Λ : ι → Matrix k r ℝ)
    (F : ι → n → r → ℝ) (U : ι → Matrix n k ℝ) : Prop where
  eventually_approximate_factor :
    Filter.Eventually
      (fun i => factorApproxSampleFactorModel (X i) (Λ i) (F i) (U i)) l
  eventually_loading_pervasiveness :
    Filter.Eventually (fun i => factorLoadingPervasiveness (Λ i)) l
  eventually_score_normalization :
    Filter.Eventually (fun i => factorScoreNormalization (F i)) l
  normalized_perturbation_tendsto_zero :
    Filter.Tendsto
      (fun i =>
        factorRecoveredIdiosyncraticGramNormalizedPerturbation
          (Λ i) (F i) (U i)) l (nhds 0)

namespace ApproximateFactorAsymptoticMatrixWLLNBridge

omit [DecidableEq n] [DecidableEq k] in
/-- A matrix/operator WLLN supplies the coordinate-WLLN bridge used by the
factor-PCA theorem route. -/
theorem toCoordinateWLLNBridge
    {ι : Type*} {l : Filter ι}
    {X : ι → n → k → ℝ} {Λ : ι → Matrix k r ℝ}
    {F : ι → n → r → ℝ} {U : ι → Matrix n k ℝ}
    (h : ApproximateFactorAsymptoticMatrixWLLNBridge l X Λ F U) :
    ApproximateFactorAsymptoticCoordinateWLLNBridge l X Λ F U where
  eventually_approximate_factor := h.eventually_approximate_factor
  eventually_loading_pervasiveness := h.eventually_loading_pervasiveness
  eventually_score_normalization := h.eventually_score_normalization
  normalized_entry_tendsto_zero := by
    intro a b
    exact
      (tendsto_pi_nhds.mp
        ((tendsto_pi_nhds.mp h.normalized_perturbation_tendsto_zero) a)) b

omit [DecidableEq n] [DecidableEq k] in
/-- A matrix/operator WLLN supplies the normalized-Rayleigh bridge. -/
theorem toNormalizedRayleighBridge
    {ι : Type*} {l : Filter ι}
    {X : ι → n → k → ℝ} {Λ : ι → Matrix k r ℝ}
    {F : ι → n → r → ℝ} {U : ι → Matrix n k ℝ}
    (h : ApproximateFactorAsymptoticMatrixWLLNBridge l X Λ F U) :
    ApproximateFactorAsymptoticNormalizedRayleighBridge l X Λ F U :=
  ApproximateFactorAsymptoticCoordinateWLLNBridge.toNormalizedRayleighBridge
    (ApproximateFactorAsymptoticMatrixWLLNBridge.toCoordinateWLLNBridge h)

omit [DecidableEq n] [DecidableEq k] in
/-- A matrix/operator WLLN supplies the older unnormalized perturbation bridge. -/
theorem toPerturbationBridge
    [Nonempty n] {ι : Type*} {l : Filter ι}
    {X : ι → n → k → ℝ} {Λ : ι → Matrix k r ℝ}
    {F : ι → n → r → ℝ} {U : ι → Matrix n k ℝ}
    (h : ApproximateFactorAsymptoticMatrixWLLNBridge l X Λ F U) :
    ApproximateFactorAsymptoticPerturbationBridge l X Λ F U :=
  ApproximateFactorAsymptoticCoordinateWLLNBridge.toPerturbationBridge
    (ApproximateFactorAsymptoticMatrixWLLNBridge.toCoordinateWLLNBridge h)

end ApproximateFactorAsymptoticMatrixWLLNBridge

set_option maxHeartbeats 800000 in
-- Heartbeat bump: product-topology synthesis for a generic rectangular
-- matrix multiplication continuity helper is expensive.
private theorem tendsto_matrix_mul
    {ι : Type*} {l : Filter ι}
    {m q p : Type*} [Fintype q]
    {A : ι → Matrix m q ℝ} {B : ι → Matrix q p ℝ}
    {A₀ : Matrix m q ℝ} {B₀ : Matrix q p ℝ}
    (hA : Filter.Tendsto A l (nhds A₀))
    (hB : Filter.Tendsto B l (nhds B₀)) :
    Filter.Tendsto (fun i => A i * B i) l (nhds (A₀ * B₀)) := by
  exact
    ((Continuous.matrix_mul continuous_fst continuous_snd).tendsto
      (A₀, B₀)).comp (hA.prodMk_nhds hB)

private theorem tendsto_matrix_transpose
    {ι : Type*} {l : Filter ι}
    {m q : Type*}
    {A : ι → Matrix m q ℝ} {A₀ : Matrix m q ℝ}
    (hA : Filter.Tendsto A l (nhds A₀)) :
    Filter.Tendsto (fun i => (A i)ᵀ) l (nhds A₀ᵀ) := by
  exact (continuous_id.matrix_transpose.tendsto A₀).comp hA

private theorem tendsto_matrix_of_entries
    {ι : Type*} {l : Filter ι}
    {m q : Type*}
    {A : ι → Matrix m q ℝ} {A₀ : Matrix m q ℝ}
    (hA : ∀ a b, Filter.Tendsto (fun i => A i a b) l (nhds (A₀ a b))) :
    Filter.Tendsto A l (nhds A₀) := by
  exact tendsto_pi_nhds.mpr fun a =>
    tendsto_pi_nhds.mpr fun b => hA a b

private theorem tendsto_zero_of_eventually_abs_le
    {ι : Type*} {l : Filter ι}
    {f ρ : ι → ℝ}
    (hbound : Filter.Eventually (fun i => |f i| ≤ ρ i) l)
    (hρ : Filter.Tendsto ρ l (nhds 0)) :
    Filter.Tendsto f l (nhds 0) := by
  rw [tendsto_zero_iff_abs_tendsto_zero]
  exact squeeze_zero'
    (Filter.Eventually.of_forall fun i => abs_nonneg (f i)) hbound hρ

omit [Fintype n] [DecidableEq n] [DecidableEq k] in
/-- Uniform inverse-Gram and loading-entry envelopes imply entrywise
convergence of the loading-Gram recoverer to zero. This is the deterministic
shrinking-recoverer bridge used by Hansen Theorem 11.9's approximate-factor
WLLN route. -/
theorem factorLoadingGramRecoverer_entry_tendsto_zero_of_inverse_loading_entry_bounds
    {ι : Type*} {l : Filter ι}
    {Λ : ι → Matrix k r ℝ} {ρInv ρΛ : ι → ℝ}
    (hInv : Filter.Eventually
      (fun i => ∀ a c, |(((Λ i)ᵀ * Λ i)⁻¹) a c| ≤ ρInv i) l)
    (hΛ : Filter.Eventually
      (fun i => ∀ b c, |Λ i b c| ≤ ρΛ i) l)
    (hρInv : Filter.Eventually (fun i => 0 ≤ ρInv i) l)
    (hprod : Filter.Tendsto
      (fun i => (Fintype.card r : ℝ) * ρInv i * ρΛ i) l (nhds 0)) :
    ∀ a b, Filter.Tendsto
      (fun i => factorLoadingGramRecoverer (Λ i) a b) l (nhds 0) := by
  intro a b
  exact
    tendsto_zero_of_eventually_abs_le
      (factorLoadingGramRecoverer_entry_abs_bound_eventually_of_inverse_loading_entry_bounds
        hInv hΛ hρInv (Filter.Eventually.of_forall fun _ => le_rfl) a b)
      hprod

private theorem tendsto_of_eventually_abs_sub_le
    {ι : Type*} {l : Filter ι}
    {f ρ : ι → ℝ} {a : ℝ}
    (hbound : Filter.Eventually (fun i => |f i - a| ≤ ρ i) l)
    (hρ : Filter.Tendsto ρ l (nhds 0)) :
    Filter.Tendsto f l (nhds a) := by
  have hsub :
      Filter.Tendsto (fun i => f i - a) l (nhds 0) :=
    tendsto_zero_of_eventually_abs_le hbound hρ
  have hconst : Filter.Tendsto (fun _ : ι => a) l (nhds a) :=
    tendsto_const_nhds
  have hsum := hsub.add hconst
  simpa [sub_eq_add_neg, add_assoc] using hsum

/-- Hansen-style asymptotic bridge whose stochastic inputs are raw
idiosyncratic moment WLLNs before combining the recovered perturbation.

The three fields are exactly Hansen's raw cross/noise moments after the
deterministic loading-Gram recovery map is applied:
`(n⁻¹F'U)L'`, `L(n⁻¹U'F)`, and `L(n⁻¹U'U)L'`. Their sum is the whole normalized
recovered perturbation `n⁻¹(F'E + E'F + E'E)`. -/
structure ApproximateFactorAsymptoticRawMomentMatrixWLLNBridge
    {ι : Type*} (l : Filter ι)
    (X : ι → n → k → ℝ) (Λ : ι → Matrix k r ℝ)
    (F : ι → n → r → ℝ) (U : ι → Matrix n k ℝ) : Prop where
  eventually_approximate_factor :
    Filter.Eventually
      (fun i => factorApproxSampleFactorModel (X i) (Λ i) (F i) (U i)) l
  eventually_loading_pervasiveness :
    Filter.Eventually (fun i => factorLoadingPervasiveness (Λ i)) l
  eventually_score_normalization :
    Filter.Eventually (fun i => factorScoreNormalization (F i)) l
  raw_cross_left_recovered_tendsto_zero :
    Filter.Tendsto
      (fun i =>
        factorRawFactorIdiosyncraticCrossNormalized (F i) (U i) *
          (factorLoadingGramRecoverer (Λ i))ᵀ) l (nhds 0)
  raw_cross_right_recovered_tendsto_zero :
    Filter.Tendsto
      (fun i =>
        factorLoadingGramRecoverer (Λ i) *
          factorRawIdiosyncraticFactorCrossNormalized (F i) (U i)) l (nhds 0)
  raw_noise_recovered_tendsto_zero :
    Filter.Tendsto
      (fun i =>
        factorLoadingGramRecoverer (Λ i) *
          factorRawIdiosyncraticGramNormalized (U i) *
            (factorLoadingGramRecoverer (Λ i))ᵀ) l (nhds 0)

namespace ApproximateFactorAsymptoticRawMomentMatrixWLLNBridge

omit [DecidableEq n] [DecidableEq k] in
/-- Raw cross/noise moment WLLNs supply the whole-matrix recovered perturbation
WLLN used by the factor-PCA theorem route. -/
theorem toMatrixWLLNBridge
    {ι : Type*} {l : Filter ι}
    {X : ι → n → k → ℝ} {Λ : ι → Matrix k r ℝ}
    {F : ι → n → r → ℝ} {U : ι → Matrix n k ℝ}
    (h : ApproximateFactorAsymptoticRawMomentMatrixWLLNBridge l X Λ F U) :
    ApproximateFactorAsymptoticMatrixWLLNBridge l X Λ F U where
  eventually_approximate_factor := h.eventually_approximate_factor
  eventually_loading_pervasiveness := h.eventually_loading_pervasiveness
  eventually_score_normalization := h.eventually_score_normalization
  normalized_perturbation_tendsto_zero := by
    have hleft :
        Filter.Tendsto
          (fun i =>
            factorRecoveredIdiosyncraticCrossLeftNormalized
              (Λ i) (F i) (U i)) l (nhds 0) := by
      refine h.raw_cross_left_recovered_tendsto_zero.congr' ?_
      exact Filter.Eventually.of_forall fun i => by
        simpa using
          (factorRecoveredIdiosyncraticCrossLeftNormalized_eq_raw_mul_recoverer
            (Λ i) (F i) (U i)).symm
    have hright :
        Filter.Tendsto
          (fun i =>
            factorRecoveredIdiosyncraticCrossRightNormalized
              (Λ i) (F i) (U i)) l (nhds 0) := by
      refine h.raw_cross_right_recovered_tendsto_zero.congr' ?_
      exact Filter.Eventually.of_forall fun i => by
        simpa using
          (factorRecoveredIdiosyncraticCrossRightNormalized_eq_recoverer_mul_raw
            (Λ i) (F i) (U i)).symm
    have hnoise :
        Filter.Tendsto
          (fun i =>
            factorRecoveredIdiosyncraticNoiseGramNormalized
              (Λ i) (U i)) l (nhds 0) := by
      refine h.raw_noise_recovered_tendsto_zero.congr' ?_
      exact Filter.Eventually.of_forall fun i => by
        simpa using
          (factorRecoveredIdiosyncraticNoiseGramNormalized_eq_recoverer_mul_raw_mul
            (Λ i) (U i)).symm
    have hsum :
        Filter.Tendsto
          (fun i =>
            factorRecoveredIdiosyncraticCrossLeftNormalized
                (Λ i) (F i) (U i) +
              factorRecoveredIdiosyncraticCrossRightNormalized
                (Λ i) (F i) (U i) +
                factorRecoveredIdiosyncraticNoiseGramNormalized
                  (Λ i) (U i)) l (nhds 0) := by
      simpa using (hleft.add hright).add hnoise
    refine hsum.congr' ?_
    exact Filter.Eventually.of_forall fun i => by
      simpa [add_assoc] using
        (factorRecoveredIdiosyncraticGramNormalizedPerturbation_eq_cross_add_noise
          (Λ i) (F i) (U i)).symm

omit [DecidableEq n] [DecidableEq k] in
/-- Raw moment WLLNs supply the normalized-Rayleigh bridge. -/
theorem toNormalizedRayleighBridge
    {ι : Type*} {l : Filter ι}
    {X : ι → n → k → ℝ} {Λ : ι → Matrix k r ℝ}
    {F : ι → n → r → ℝ} {U : ι → Matrix n k ℝ}
    (h : ApproximateFactorAsymptoticRawMomentMatrixWLLNBridge l X Λ F U) :
    ApproximateFactorAsymptoticNormalizedRayleighBridge l X Λ F U :=
  ApproximateFactorAsymptoticMatrixWLLNBridge.toNormalizedRayleighBridge
    (ApproximateFactorAsymptoticRawMomentMatrixWLLNBridge.toMatrixWLLNBridge h)

omit [DecidableEq n] [DecidableEq k] in
/-- Raw moment WLLNs supply the older unnormalized perturbation bridge. -/
theorem toPerturbationBridge
    [Nonempty n] {ι : Type*} {l : Filter ι}
    {X : ι → n → k → ℝ} {Λ : ι → Matrix k r ℝ}
    {F : ι → n → r → ℝ} {U : ι → Matrix n k ℝ}
    (h : ApproximateFactorAsymptoticRawMomentMatrixWLLNBridge l X Λ F U) :
    ApproximateFactorAsymptoticPerturbationBridge l X Λ F U :=
  ApproximateFactorAsymptoticMatrixWLLNBridge.toPerturbationBridge
    (ApproximateFactorAsymptoticRawMomentMatrixWLLNBridge.toMatrixWLLNBridge h)

end ApproximateFactorAsymptoticRawMomentMatrixWLLNBridge

/-- Hansen-style asymptotic bridge whose primitive stochastic inputs are the
three coordinate WLLNs for the normalized recovered cross/noise terms
`n⁻¹F'E`, `n⁻¹E'F`, and `n⁻¹E'E`.

This is the theorem-facing boundary closest to Hansen's approximate-factor
cross-term argument: the algebraic decomposition is proved here, while the
scalar WLLNs for the three displayed terms remain the probabilistic inputs. -/
structure ApproximateFactorAsymptoticCrossNoiseWLLNBridge
    {ι : Type*} (l : Filter ι)
    (X : ι → n → k → ℝ) (Λ : ι → Matrix k r ℝ)
    (F : ι → n → r → ℝ) (U : ι → Matrix n k ℝ) : Prop where
  eventually_approximate_factor :
    Filter.Eventually
      (fun i => factorApproxSampleFactorModel (X i) (Λ i) (F i) (U i)) l
  eventually_loading_pervasiveness :
    Filter.Eventually (fun i => factorLoadingPervasiveness (Λ i)) l
  eventually_score_normalization :
    Filter.Eventually (fun i => factorScoreNormalization (F i)) l
  cross_left_entry_tendsto_zero : ∀ a b : r,
    Filter.Tendsto
      (fun i =>
        factorRecoveredIdiosyncraticCrossLeftNormalized
          (Λ i) (F i) (U i) a b) l (nhds 0)
  cross_right_entry_tendsto_zero : ∀ a b : r,
    Filter.Tendsto
      (fun i =>
        factorRecoveredIdiosyncraticCrossRightNormalized
          (Λ i) (F i) (U i) a b) l (nhds 0)
  noise_entry_tendsto_zero : ∀ a b : r,
    Filter.Tendsto
      (fun i =>
        factorRecoveredIdiosyncraticNoiseGramNormalized
          (Λ i) (U i) a b) l (nhds 0)

namespace ApproximateFactorAsymptoticCrossNoiseWLLNBridge

omit [DecidableEq n] [DecidableEq k] in
/-- The three cross/noise coordinate WLLNs imply coordinate convergence of the
whole normalized recovered perturbation. -/
theorem normalized_entry_tendsto_zero
    {ι : Type*} {l : Filter ι}
    {X : ι → n → k → ℝ} {Λ : ι → Matrix k r ℝ}
    {F : ι → n → r → ℝ} {U : ι → Matrix n k ℝ}
    (h : ApproximateFactorAsymptoticCrossNoiseWLLNBridge l X Λ F U)
    (a b : r) :
    Filter.Tendsto
      (fun i =>
        (factorRecoveredIdiosyncraticGramNormalizedPerturbation
          (Λ i) (F i) (U i)) a b) l (nhds 0) := by
  have hrightNoise :=
    (h.cross_right_entry_tendsto_zero a b).add
      (h.noise_entry_tendsto_zero a b)
  have hsum :=
    (h.cross_left_entry_tendsto_zero a b).add hrightNoise
  have hsum0 :
      Filter.Tendsto
        (fun i =>
          factorRecoveredIdiosyncraticCrossLeftNormalized
            (Λ i) (F i) (U i) a b +
            (factorRecoveredIdiosyncraticCrossRightNormalized
              (Λ i) (F i) (U i) a b +
              factorRecoveredIdiosyncraticNoiseGramNormalized
                (Λ i) (U i) a b)) l (nhds 0) := by
    simpa using hsum
  refine hsum0.congr' ?_
  exact Filter.Eventually.of_forall fun i => by
    change
      factorRecoveredIdiosyncraticCrossLeftNormalized
          (Λ i) (F i) (U i) a b +
        (factorRecoveredIdiosyncraticCrossRightNormalized
            (Λ i) (F i) (U i) a b +
          factorRecoveredIdiosyncraticNoiseGramNormalized
            (Λ i) (U i) a b) =
          (factorRecoveredIdiosyncraticGramNormalizedPerturbation
            (Λ i) (F i) (U i)) a b
    rw [factorRecoveredIdiosyncraticGramNormalizedPerturbation_apply_eq_cross_add_noise]
    ring

omit [DecidableEq n] [DecidableEq k] in
/-- The three cross/noise coordinate WLLNs supply the coordinate-WLLN bridge
used by the factor-PCA theorem route. -/
theorem toCoordinateWLLNBridge
    {ι : Type*} {l : Filter ι}
    {X : ι → n → k → ℝ} {Λ : ι → Matrix k r ℝ}
    {F : ι → n → r → ℝ} {U : ι → Matrix n k ℝ}
    (h : ApproximateFactorAsymptoticCrossNoiseWLLNBridge l X Λ F U) :
    ApproximateFactorAsymptoticCoordinateWLLNBridge l X Λ F U where
  eventually_approximate_factor := h.eventually_approximate_factor
  eventually_loading_pervasiveness := h.eventually_loading_pervasiveness
  eventually_score_normalization := h.eventually_score_normalization
  normalized_entry_tendsto_zero :=
    ApproximateFactorAsymptoticCrossNoiseWLLNBridge.normalized_entry_tendsto_zero h

omit [DecidableEq n] [DecidableEq k] in
/-- The three cross/noise coordinate WLLNs imply the matrix/operator WLLN for
the normalized recovered perturbation. -/
theorem toMatrixWLLNBridge
    {ι : Type*} {l : Filter ι}
    {X : ι → n → k → ℝ} {Λ : ι → Matrix k r ℝ}
    {F : ι → n → r → ℝ} {U : ι → Matrix n k ℝ}
    (h : ApproximateFactorAsymptoticCrossNoiseWLLNBridge l X Λ F U) :
    ApproximateFactorAsymptoticMatrixWLLNBridge l X Λ F U where
  eventually_approximate_factor := h.eventually_approximate_factor
  eventually_loading_pervasiveness := h.eventually_loading_pervasiveness
  eventually_score_normalization := h.eventually_score_normalization
  normalized_perturbation_tendsto_zero := by
    refine tendsto_pi_nhds.mpr fun a => ?_
    refine tendsto_pi_nhds.mpr fun b => ?_
    exact
      ApproximateFactorAsymptoticCrossNoiseWLLNBridge.normalized_entry_tendsto_zero h a b

omit [DecidableEq n] [DecidableEq k] in
/-- The three cross/noise coordinate WLLNs supply the normalized-Rayleigh
bridge. -/
theorem toNormalizedRayleighBridge
    {ι : Type*} {l : Filter ι}
    {X : ι → n → k → ℝ} {Λ : ι → Matrix k r ℝ}
    {F : ι → n → r → ℝ} {U : ι → Matrix n k ℝ}
    (h : ApproximateFactorAsymptoticCrossNoiseWLLNBridge l X Λ F U) :
    ApproximateFactorAsymptoticNormalizedRayleighBridge l X Λ F U :=
  ApproximateFactorAsymptoticCoordinateWLLNBridge.toNormalizedRayleighBridge
    (ApproximateFactorAsymptoticCrossNoiseWLLNBridge.toCoordinateWLLNBridge h)

omit [DecidableEq n] [DecidableEq k] in
/-- The three cross/noise coordinate WLLNs supply the older unnormalized
perturbation bridge. -/
theorem toPerturbationBridge
    [Nonempty n] {ι : Type*} {l : Filter ι}
    {X : ι → n → k → ℝ} {Λ : ι → Matrix k r ℝ}
    {F : ι → n → r → ℝ} {U : ι → Matrix n k ℝ}
    (h : ApproximateFactorAsymptoticCrossNoiseWLLNBridge l X Λ F U) :
    ApproximateFactorAsymptoticPerturbationBridge l X Λ F U :=
  ApproximateFactorAsymptoticCoordinateWLLNBridge.toPerturbationBridge
    (ApproximateFactorAsymptoticCrossNoiseWLLNBridge.toCoordinateWLLNBridge h)

end ApproximateFactorAsymptoticCrossNoiseWLLNBridge

omit [Fintype n] [DecidableEq n] [DecidableEq k] [DecidableEq r] in
/-- If a full-rank sample factor matrix can be recovered from the raw data by a
fixed linear map, then the raw data matrix has selected rank at least `r`. -/
theorem factorDataMatrix_rank_ge_of_factor_recovery
    (X : n → k → ℝ) (F : n → r → ℝ) (L : Matrix r k ℝ)
    (hrecover : factorDataMatrix X * Lᵀ = factorScoreDataMatrix F)
    (hFrank : (factorScoreDataMatrix F).rank = Fintype.card r) :
    Fintype.card r ≤ (factorDataMatrix X).rank := by
  have hrank_le :
      (factorScoreDataMatrix F).rank ≤ (factorDataMatrix X).rank := by
    rw [← hrecover]
    exact Matrix.rank_mul_le_left (factorDataMatrix X) Lᵀ
  simpa [hFrank] using hrank_le

omit [Fintype n] [DecidableEq n] [DecidableEq k] in
/-- If the raw data are exactly `F Λ'`, the loading matrix has a left inverse,
and the sample factor score matrix has rank `r`, then the observed data matrix
has the selected rank needed by Hansen Theorem 11.9. -/
theorem factorDataMatrix_rank_ge_of_exact_factor_leftInverse
    (X : n → k → ℝ) (Λ : Matrix k r ℝ) (F : n → r → ℝ) (L : Matrix r k ℝ)
    (hExact : factorExactSampleFactorModel X Λ F)
    (hLeft : L * Λ = 1)
    (hFrank : (factorScoreDataMatrix F).rank = Fintype.card r) :
    Fintype.card r ≤ (factorDataMatrix X).rank := by
  have hrecover : factorDataMatrix X * Lᵀ = factorScoreDataMatrix F := by
    calc
      factorDataMatrix X * Lᵀ
          = (factorScoreDataMatrix F * Λᵀ) * Lᵀ := by
              rw [hExact]
              rfl
      _ = factorScoreDataMatrix F * (Λᵀ * Lᵀ) := by
              rw [Matrix.mul_assoc]
      _ = factorScoreDataMatrix F * (L * Λ)ᵀ := by
              rw [Matrix.transpose_mul]
      _ = factorScoreDataMatrix F := by
              rw [hLeft, Matrix.transpose_one, Matrix.mul_one]
  exact factorDataMatrix_rank_ge_of_factor_recovery X F L hrecover hFrank

omit [Fintype n] [DecidableEq n] [DecidableEq k] in
/-- Bundled version of
`factorDataMatrix_rank_ge_of_exact_factor_leftInverse` for Hansen-facing raw
sample factor conditions. -/
theorem factorDataMatrix_rank_ge_of_exactSampleFactorRankCondition
    (X : n → k → ℝ) (Λ : Matrix k r ℝ) (F : n → r → ℝ)
    (hraw : ExactSampleFactorRankCondition X Λ F) :
    Fintype.card r ≤ (factorDataMatrix X).rank := by
  rcases hraw.loading_left_inverse with ⟨L, hLeft⟩
  exact factorDataMatrix_rank_ge_of_exact_factor_leftInverse X Λ F L
    hraw.exact_factor hLeft hraw.sample_factor_rank

omit [Fintype n] [DecidableEq n] [DecidableEq k] in
/-- Additive noisy-factor bridge to the raw selected-rank condition.

If `X = FΛ' + U`, `Λ` has a left inverse `L`, and the same recovering direction
annihilates the idiosyncratic sample component (`U L' = 0`), then `XL' = F`.
Full selected rank of the sample factor matrix therefore gives the raw
data-matrix rank certificate used by Hansen Theorem 11.9. -/
theorem factorDataMatrix_rank_ge_of_approx_factor_leftInverse_annihilates_noise
    (X : n → k → ℝ) (Λ : Matrix k r ℝ) (F : n → r → ℝ)
    (U : Matrix n k ℝ) (L : Matrix r k ℝ)
    (hApprox : factorApproxSampleFactorModel X Λ F U)
    (hLeft : L * Λ = 1) (hNoise : U * Lᵀ = 0)
    (hFrank : (factorScoreDataMatrix F).rank = Fintype.card r) :
    Fintype.card r ≤ (factorDataMatrix X).rank := by
  have hrecover : factorDataMatrix X * Lᵀ = factorScoreDataMatrix F := by
    calc
      factorDataMatrix X * Lᵀ
          = (factorScoreDataMatrix F * Λᵀ + U) * Lᵀ := by
              rw [hApprox]
              rfl
      _ = (factorScoreDataMatrix F * Λᵀ) * Lᵀ + U * Lᵀ := by
              rw [Matrix.add_mul]
      _ = factorScoreDataMatrix F * (Λᵀ * Lᵀ) + U * Lᵀ := by
              rw [Matrix.mul_assoc]
      _ = factorScoreDataMatrix F * (L * Λ)ᵀ + U * Lᵀ := by
              rw [Matrix.transpose_mul]
      _ = factorScoreDataMatrix F := by
              rw [hLeft, Matrix.transpose_one, Matrix.mul_one, hNoise, add_zero]
  exact factorDataMatrix_rank_ge_of_factor_recovery X F L hrecover hFrank

omit [Fintype n] [DecidableEq n] [DecidableEq k] in
/-- Bundled additive noisy-factor rank bridge for Hansen-facing approximate
sample factor conditions. -/
theorem factorDataMatrix_rank_ge_of_approxSampleFactorRankCondition
    (X : n → k → ℝ) (Λ : Matrix k r ℝ) (F : n → r → ℝ)
    (U : Matrix n k ℝ)
    (hraw : ApproximateSampleFactorRankCondition X Λ F U) :
    Fintype.card r ≤ (factorDataMatrix X).rank := by
  rcases hraw.recoverable_loadings with ⟨L, hLeft, hNoise⟩
  exact factorDataMatrix_rank_ge_of_approx_factor_leftInverse_annihilates_noise
    X Λ F U L hraw.approximate_factor hLeft hNoise hraw.sample_factor_rank

omit [Fintype n] [DecidableEq n] [DecidableEq k] in
/-- Hansen-shaped pervasiveness/idiosyncratic finite-sample conditions imply
the raw data-matrix selected-rank condition used by Theorem 11.9. -/
theorem factorDataMatrix_rank_ge_of_approxSampleFactorPervasiveCondition
    (X : n → k → ℝ) (Λ : Matrix k r ℝ) (F : n → r → ℝ)
    (U : Matrix n k ℝ)
    (hraw : ApproximateSampleFactorPervasiveCondition X Λ F U) :
    Fintype.card r ≤ (factorDataMatrix X).rank :=
  factorDataMatrix_rank_ge_of_approxSampleFactorRankCondition X Λ F U
    hraw.toApproximateSampleFactorRankCondition

omit [DecidableEq n] [DecidableEq k] in
/-- Hansen-shaped pervasiveness/idiosyncratic finite-sample conditions imply
the sample-covariance selected-rank condition used to get positive selected PCA
eigenvalues. -/
theorem factorSampleCovariance_rank_ge_of_approxSampleFactorPervasiveCondition
    [Nonempty n] (X : n → k → ℝ) (Λ : Matrix k r ℝ) (F : n → r → ℝ)
    (U : Matrix n k ℝ)
    (hraw : ApproximateSampleFactorPervasiveCondition X Λ F U) :
    Fintype.card r ≤ (factorSampleCovariance X).rank :=
  factorSampleCovariance_rank_ge_of_dataMatrix_rank_ge (r := r) X
    (factorDataMatrix_rank_ge_of_approxSampleFactorPervasiveCondition
      X Λ F U hraw)

omit [DecidableEq n] [DecidableEq k] in
/-- Primitive finite-sample sample-factor/pervasiveness/idiosyncratic
conditions imply the raw data-matrix selected-rank condition used by
Theorem 11.9. -/
theorem factorDataMatrix_rank_ge_of_approxSampleFactorPrimitiveCondition
    (X : n → k → ℝ) (Λ : Matrix k r ℝ) (F : n → r → ℝ)
    (U : Matrix n k ℝ)
    (hraw : ApproximateSampleFactorPrimitiveCondition X Λ F U) :
    Fintype.card r ≤ (factorDataMatrix X).rank :=
  factorDataMatrix_rank_ge_of_approxSampleFactorPervasiveCondition
    X Λ F U
    (ApproximateSampleFactorPrimitiveCondition.toApproximateSampleFactorPervasiveCondition hraw)

omit [DecidableEq n] [DecidableEq k] in
/-- Primitive finite-sample sample-factor/pervasiveness/idiosyncratic
conditions imply the sample-covariance selected-rank condition used by the
canonical diagonal PCA endpoint. -/
theorem factorSampleCovariance_rank_ge_of_approxSampleFactorPrimitiveCondition
    [Nonempty n] (X : n → k → ℝ) (Λ : Matrix k r ℝ) (F : n → r → ℝ)
    (U : Matrix n k ℝ)
    (hraw : ApproximateSampleFactorPrimitiveCondition X Λ F U) :
    Fintype.card r ≤ (factorSampleCovariance X).rank :=
  factorSampleCovariance_rank_ge_of_approxSampleFactorPervasiveCondition
    X Λ F U
    (ApproximateSampleFactorPrimitiveCondition.toApproximateSampleFactorPervasiveCondition hraw)

omit [DecidableEq n] [DecidableEq k] in
/-- Primitive finite-sample perturbation conditions imply the raw data-matrix
selected-rank condition used by Theorem 11.9.

Unlike `factorDataMatrix_rank_ge_of_approxSampleFactorPrimitiveCondition`, this
route permits nonzero recovered idiosyncratic scores and controls their
cross/noise Gram contribution instead of assuming exact loading orthogonality. -/
theorem factorDataMatrix_rank_ge_of_approxSampleFactorPerturbationCondition
    [Nonempty n] (X : n → k → ℝ) (Λ : Matrix k r ℝ) (F : n → r → ℝ)
    (U : Matrix n k ℝ)
    (hraw : ApproximateSampleFactorPerturbationCondition X Λ F U) :
    Fintype.card r ≤ (factorDataMatrix X).rank :=
  factorDataMatrix_rank_ge_of_approx_factor_recovered_perturbation X Λ F U
    hraw.approximate_factor
    (factorLoadingGram_nonsingular_of_pervasiveness Λ hraw.loading_pervasiveness)
    hraw.recovered_idiosyncratic_gram_dominated

omit [DecidableEq n] [DecidableEq k] in
/-- Primitive finite-sample perturbation conditions imply the sample-covariance
selected-rank condition used by the canonical diagonal PCA endpoint. -/
theorem factorSampleCovariance_rank_ge_of_approxSampleFactorPerturbationCondition
    [Nonempty n] (X : n → k → ℝ) (Λ : Matrix k r ℝ) (F : n → r → ℝ)
    (U : Matrix n k ℝ)
    (hraw : ApproximateSampleFactorPerturbationCondition X Λ F U) :
    Fintype.card r ≤ (factorSampleCovariance X).rank :=
  factorSampleCovariance_rank_ge_of_dataMatrix_rank_ge (r := r) X
    (factorDataMatrix_rank_ge_of_approxSampleFactorPerturbationCondition
      X Λ F U hraw)

/-- Concrete leading-eigenspace equation behind the factor-PCA certificate:
columns of `H` diagonalize the sample covariance with eigenvalue matrix `D`. -/
def factorLeadingEigenspace
    (Shat : Matrix k k ℝ) (H : Matrix k r ℝ) (D : Matrix r r ℝ) : Prop :=
  Shat * H = H * D

/-- The first `r` ordered PCA eigenvectors, written as factor-loading columns.
The cardinality hypothesis is the deterministic rank condition needed to choose
`r` leading directions inside the `k`-dimensional covariance matrix. -/
noncomputable def factorLeadingPCEigenvectors
    {Shat : Matrix k k ℝ} (hShat : Shat.IsHermitian)
    (hcard : Fintype.card r ≤ Fintype.card k) : Matrix k r ℝ :=
  fun a j =>
    orderedPCEigenvector hShat
      (Fin.castLE hcard ((Fintype.equivFin r) j)) a

/-- The ordered eigenvalues attached to `factorLeadingPCEigenvectors`. -/
noncomputable def factorLeadingPCEigenvalues
    {Shat : Matrix k k ℝ} (hShat : Shat.IsHermitian)
    (hcard : Fintype.card r ≤ Fintype.card k) : r → ℝ :=
  fun j =>
    orderedPCEigenvalue hShat
      (Fin.castLE hcard ((Fintype.equivFin r) j))

omit [Fintype r] [DecidableEq r] in
/-- Ordered-eigenvalue-list form of the zero-padded spectral equivalence
between `n⁻¹XX'` and `n⁻¹X'X`.

This upgrades the characteristic-polynomial bridge to sorted Hermitian
eigenvalue lists, using positive semidefiniteness to place the added zero roots
after the genuine Gram eigenvalues. -/
theorem factorObservationGram_sampleCovariance_padded_eigenvalues₀_eq
    (X : n → k → ℝ) :
    List.ofFn (factorObservationGram_isHermitian X).eigenvalues₀ ++
        List.replicate (Fintype.card k) (0 : ℝ) =
      List.ofFn (factorSampleCovariance_isHermitian X).eigenvalues₀ ++
        List.replicate (Fintype.card n) (0 : ℝ) := by
  let lobs := List.ofFn (factorObservationGram_isHermitian X).eigenvalues₀
  let lsample := List.ofFn (factorSampleCovariance_isHermitian X).eigenvalues₀
  have hObsRoots : (factorObservationGram X).charpoly.roots = (lobs : Multiset ℝ) := by
    simpa [lobs, Function.comp_def] using
      (factorObservationGram_isHermitian X).roots_charpoly_eq_eigenvalues₀
  have hSampleRoots :
      (factorSampleCovariance X).charpoly.roots = (lsample : Multiset ℝ) := by
    simpa [lsample, Function.comp_def] using
      (factorSampleCovariance_isHermitian X).roots_charpoly_eq_eigenvalues₀
  have hpad : Fintype.card k • ({0} : Multiset ℝ) + (lobs : Multiset ℝ) =
      Fintype.card n • ({0} : Multiset ℝ) + (lsample : Multiset ℝ) := by
    simpa [hObsRoots, hSampleRoots] using
      factorObservationGram_sampleCovariance_roots_with_zero_padding (n := n) (k := k) X
  have hsObs : lobs.SortedGE := by
    exact (factorObservationGram_isHermitian X).eigenvalues₀_antitone.sortedGE_ofFn
  have hsSample : lsample.SortedGE := by
    exact (factorSampleCovariance_isHermitian X).eigenvalues₀_antitone.sortedGE_ofFn
  have h0Obs : ∀ x ∈ lobs, 0 ≤ x := by
    intro x hx
    dsimp [lobs] at hx
    rw [List.mem_ofFn] at hx
    rcases hx with ⟨i, rfl⟩
    have hproof : (factorObservationGram_posSemidef X).1 =
        factorObservationGram_isHermitian X := Subsingleton.elim _ _
    simpa [Matrix.IsHermitian.eigenvalues, hproof] using
      (factorObservationGram_posSemidef X).eigenvalues_nonneg
        ((Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card n))) i)
  have h0Sample : ∀ x ∈ lsample, 0 ≤ x := by
    intro x hx
    dsimp [lsample] at hx
    rw [List.mem_ofFn] at hx
    rcases hx with ⟨i, rfl⟩
    have hproof : (factorSampleCovariance_posSemidef X).1 =
        factorSampleCovariance_isHermitian X := Subsingleton.elim _ _
    simpa [Matrix.IsHermitian.eigenvalues, hproof] using
      (factorSampleCovariance_posSemidef X).eigenvalues_nonneg
        ((Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card k))) i)
  exact factorPadded_sorted_nonneg_lists_eq_of_multiset_eq
    hsObs hsSample h0Obs h0Sample hpad

omit [DecidableEq r] in
/-- Leading ordered eigenvalue sums agree between `n⁻¹XX'` and `n⁻¹X'X`, as
long as both sides have at least `r` displayed eigenvalues.

This is the order-theoretic deletion of the padded zero roots in
`factorObservationGram_sampleCovariance_padded_eigenvalues₀_eq`. -/
theorem factorObservationGram_sampleCovariance_eigenvalues₀_sum_eq
    (hcard : Fintype.card r ≤ Fintype.card k)
    (hcardObs : Fintype.card r ≤ Fintype.card n) (X : n → k → ℝ) :
    (∑ j : Fin (Fintype.card r),
        (factorObservationGram_isHermitian X).eigenvalues₀ (Fin.castLE hcardObs j)) =
      ∑ j : Fin (Fintype.card r),
        (factorSampleCovariance_isHermitian X).eigenvalues₀ (Fin.castLE hcard j) := by
  have hpadded := factorObservationGram_sampleCovariance_padded_eigenvalues₀_eq X
  have htake := congrArg (fun l : List ℝ => (l.take (Fintype.card r)).sum) hpadded
  simp only at htake
  have hobs_take :
      ((List.ofFn (factorObservationGram_isHermitian X).eigenvalues₀ ++
        List.replicate (Fintype.card k) (0 : ℝ)).take (Fintype.card r)).sum =
        ((List.ofFn (factorObservationGram_isHermitian X).eigenvalues₀).take
          (Fintype.card r)).sum := by
    rw [List.take_append_of_le_length]
    simp [hcardObs]
  have hsample_take :
      ((List.ofFn (factorSampleCovariance_isHermitian X).eigenvalues₀ ++
        List.replicate (Fintype.card n) (0 : ℝ)).take (Fintype.card r)).sum =
        ((List.ofFn (factorSampleCovariance_isHermitian X).eigenvalues₀).take
          (Fintype.card r)).sum := by
    rw [List.take_append_of_le_length]
    simp [hcard]
  rw [hobs_take, hsample_take] at htake
  rw [factorList_sum_take_ofFn_eq_finset_sum_castLE hcardObs,
    factorList_sum_take_ofFn_eq_finset_sum_castLE hcard] at htake
  exact htake

omit [DecidableEq r] in
/-- Hansen Theorem 11.9 spectral-transfer bridge: the leading `r` eigenvalue
sum of the observation Gram `n⁻¹XX'` equals the leading `r` eigenvalue sum of
the sample covariance `n⁻¹X'X`. -/
theorem factorObservationGram_sampleCovariance_leadingEigenvalue_sum_eq
    (hcard : Fintype.card r ≤ Fintype.card k)
    (hcardObs : Fintype.card r ≤ Fintype.card n) (X : n → k → ℝ) :
    (∑ j : r, factorLeadingPCEigenvalues (r := r)
        (factorObservationGram_isHermitian X) hcardObs j) =
      ∑ j : r, factorLeadingPCEigenvalues (r := r)
        (factorSampleCovariance_isHermitian X) hcard j := by
  classical
  have hfin :=
    factorObservationGram_sampleCovariance_eigenvalues₀_sum_eq
      (r := r) hcard hcardObs X
  simpa [factorLeadingPCEigenvalues, orderedPCEigenvalue] using
    (Equiv.sum_comp (Fintype.equivFin r)
      (fun j : Fin (Fintype.card r) =>
        (factorObservationGram_isHermitian X).eigenvalues₀
          (Fin.castLE hcardObs j))).trans
    (hfin.trans
      ((Equiv.sum_comp (Fintype.equivFin r)
        (fun j : Fin (Fintype.card r) =>
          (factorSampleCovariance_isHermitian X).eigenvalues₀
            (Fin.castLE hcard j))).symm))

omit [Fintype n] [DecidableEq n] [DecidableEq r] in
/-- Positive semidefiniteness of the sample/objective matrix gives nonnegative
selected ordered PCA eigenvalues. -/
theorem factorLeadingPCEigenvalues_nonneg_of_posSemidef
    {Shat : Matrix k k ℝ} (hShat : Shat.IsHermitian)
    (hcard : Fintype.card r ≤ Fintype.card k)
    (hpsd : Shat.PosSemidef) :
    ∀ j, 0 ≤ factorLeadingPCEigenvalues (r := r) hShat hcard j := by
  intro j
  have hproof : hpsd.1 = hShat := Subsingleton.elim _ _
  simpa [factorLeadingPCEigenvalues, orderedPCEigenvalue,
    orderedPCEigenIndex, Matrix.IsHermitian.eigenvalues, hproof] using
    hpsd.eigenvalues_nonneg
      (orderedPCEigenIndex (Fin.castLE hcard ((Fintype.equivFin r) j)))

omit [Fintype n] [DecidableEq n] [DecidableEq r] in
/-- For a positive semidefinite sample/objective matrix, nonzero selected
ordered PCA eigenvalues are exactly the positive eigenvalues needed for
Hansen's canonical `D^{1/2}` / `D^{-1/2}` scaling. -/
theorem factorLeadingPCEigenvalues_pos_of_posSemidef_ne_zero
    {Shat : Matrix k k ℝ} (hShat : Shat.IsHermitian)
    (hcard : Fintype.card r ≤ Fintype.card k)
    (hpsd : Shat.PosSemidef)
    (hne : ∀ j, factorLeadingPCEigenvalues (r := r) hShat hcard j ≠ 0) :
    ∀ j, 0 < factorLeadingPCEigenvalues (r := r) hShat hcard j := by
  intro j
  exact lt_of_le_of_ne
    (factorLeadingPCEigenvalues_nonneg_of_posSemidef
      (r := r) hShat hcard hpsd j)
    (hne j).symm

omit [Fintype n] [DecidableEq n] in
/-- Nonsingularity of the selected diagonal eigenvalue block gives the positive
selected eigenvalues required by Hansen Theorem 11.9's canonical scaling, using
positive semidefiniteness to rule out negative nonzero eigenvalues. -/
theorem factorLeadingPCEigenvalues_pos_of_posSemidef_selected_diagonal_isUnit
    {Shat : Matrix k k ℝ} (hShat : Shat.IsHermitian)
    (hcard : Fintype.card r ≤ Fintype.card k)
    (hpsd : Shat.PosSemidef)
    (hunit : IsUnit (Matrix.diagonal
      (factorLeadingPCEigenvalues (r := r) hShat hcard)).det) :
    ∀ j, 0 < factorLeadingPCEigenvalues (r := r) hShat hcard j := by
  refine factorLeadingPCEigenvalues_pos_of_posSemidef_ne_zero
    (r := r) hShat hcard hpsd ?_
  have hdiagUnit : IsUnit
      (Matrix.diagonal (factorLeadingPCEigenvalues (r := r) hShat hcard)) :=
    (Matrix.isUnit_iff_isUnit_det
      (Matrix.diagonal (factorLeadingPCEigenvalues (r := r) hShat hcard))).mpr hunit
  have hfunUnit : IsUnit (factorLeadingPCEigenvalues (r := r) hShat hcard) :=
    Matrix.isUnit_diagonal.mp hdiagUnit
  intro j
  exact isUnit_iff_ne_zero.mp (hfunUnit.apply j)

omit [Fintype n] [DecidableEq n] [DecidableEq r] in
private theorem orderedPCEigenvalue_nonneg_of_posSemidef
    {Shat : Matrix k k ℝ} (hShat : Shat.IsHermitian)
    (hpsd : Shat.PosSemidef) (j : Fin (Fintype.card k)) :
    0 ≤ orderedPCEigenvalue hShat j := by
  let e : Fin (Fintype.card k) ≃ k :=
    Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card k))
  have hproof : hpsd.1 = hShat := Subsingleton.elim _ _
  simpa [orderedPCEigenvalue, Matrix.IsHermitian.eigenvalues, e, hproof] using
    hpsd.eigenvalues_nonneg (e j)

omit [Fintype n] [DecidableEq n] [DecidableEq r] in
private theorem hermitian_rank_eq_card_nonzero_ordered_eigenvalues
    {Shat : Matrix k k ℝ} (hShat : Shat.IsHermitian) :
    Shat.rank =
      Fintype.card
        {j : Fin (Fintype.card k) // orderedPCEigenvalue hShat j ≠ 0} := by
  classical
  let e : Fin (Fintype.card k) ≃ k :=
    Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card k))
  let nonzeroEquiv :
      {j : Fin (Fintype.card k) // orderedPCEigenvalue hShat j ≠ 0} ≃
        {a : k // hShat.eigenvalues a ≠ 0} := {
    toFun j := ⟨e j.1, by
      simpa [orderedPCEigenvalue, Matrix.IsHermitian.eigenvalues, e] using j.2⟩
    invFun a := ⟨e.symm a.1, by
      simpa [orderedPCEigenvalue, Matrix.IsHermitian.eigenvalues, e] using a.2⟩
    left_inv j := by
      ext
      simp [e]
    right_inv a := by
      ext
      simp [e] }
  rw [hShat.rank_eq_card_non_zero_eigs]
  exact (Fintype.card_congr nonzeroEquiv).symm

omit [Fintype n] [DecidableEq n] [DecidableEq r] in
/-- A positive semidefinite sample/objective matrix with rank at least `r` has
strictly positive selected ordered PCA eigenvalues. This is the exact
selected-rank bridge behind Hansen Theorem 11.9's canonical diagonal scaling. -/
theorem factorLeadingPCEigenvalues_pos_of_posSemidef_rank_ge
    {Shat : Matrix k k ℝ} (hShat : Shat.IsHermitian)
    (hcard : Fintype.card r ≤ Fintype.card k)
    (hpsd : Shat.PosSemidef) (hrank : Fintype.card r ≤ Shat.rank) :
    ∀ j, 0 < factorLeadingPCEigenvalues (r := r) hShat hcard j := by
  classical
  intro j
  let idx : Fin (Fintype.card k) :=
    Fin.castLE hcard ((Fintype.equivFin r) j)
  have hdown :
      ∀ i j : Fin (Fintype.card k), j ≤ i →
        orderedPCEigenvalue hShat i ≠ 0 →
          orderedPCEigenvalue hShat j ≠ 0 := by
    intro i j hji hi hzero
    have hle : orderedPCEigenvalue hShat i ≤ orderedPCEigenvalue hShat j :=
      orderedPCEigenvalue_antitone hShat hji
    have hnonneg : 0 ≤ orderedPCEigenvalue hShat i :=
      orderedPCEigenvalue_nonneg_of_posSemidef hShat hpsd i
    have hzero_i : orderedPCEigenvalue hShat i = 0 :=
      le_antisymm (by simpa [hzero] using hle) hnonneg
    exact hi hzero_i
  have hrank_ordered :
      Fintype.card r ≤
        Fintype.card
          {i : Fin (Fintype.card k) // orderedPCEigenvalue hShat i ≠ 0} := by
    simpa [hermitian_rank_eq_card_nonzero_ordered_eigenvalues hShat] using hrank
  have hidx_lt_r : (idx : ℕ) < Fintype.card r := by
    simp [idx]
  have hidx_nonzero : orderedPCEigenvalue hShat idx ≠ 0 := by
    have hidx_lt_count :
        idx <
          Fintype.card
            {i : Fin (Fintype.card k) // orderedPCEigenvalue hShat i ≠ 0} :=
      lt_of_lt_of_le hidx_lt_r hrank_ordered
    exact (Fin.lt_card_filter_univ_iff_apply_of_imp
      (fun i : Fin (Fintype.card k) => orderedPCEigenvalue hShat i ≠ 0)
      hdown).mp (by simpa [Fintype.card_subtype] using hidx_lt_count)
  exact lt_of_le_of_ne
    (factorLeadingPCEigenvalues_nonneg_of_posSemidef
      (r := r) hShat hcard hpsd j)
    (by simpa [factorLeadingPCEigenvalues, idx] using hidx_nonzero.symm)

omit [Fintype n] [DecidableEq n] in
/-- Positive selected eigenvalues make the selected diagonal eigenvalue block
nonsingular. This is the converse bridge to
`factorLeadingPCEigenvalues_pos_of_posSemidef_selected_diagonal_isUnit`. -/
theorem factorLeadingPCEigenvalues_selected_diagonal_isUnit_of_pos
    {Shat : Matrix k k ℝ} (hShat : Shat.IsHermitian)
    (hcard : Fintype.card r ≤ Fintype.card k)
    (hpos : ∀ j, 0 < factorLeadingPCEigenvalues (r := r) hShat hcard j) :
    IsUnit (Matrix.diagonal
      (factorLeadingPCEigenvalues (r := r) hShat hcard)).det := by
  have hright :
      Matrix.diagonal (factorLeadingPCEigenvalues (r := r) hShat hcard) *
          Matrix.diagonal
            (fun j => (factorLeadingPCEigenvalues (r := r) hShat hcard j)⁻¹) =
        1 := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [(hpos i).ne']
    · simp [hij]
  exact Matrix.isUnit_det_of_right_inverse
    (A := Matrix.diagonal (factorLeadingPCEigenvalues (r := r) hShat hcard))
    (B := Matrix.diagonal
      (fun j => (factorLeadingPCEigenvalues (r := r) hShat hcard j)⁻¹))
    hright

omit [Fintype n] [DecidableEq n] in
/-- A positive semidefinite sample/objective matrix with rank at least `r`
makes the selected diagonal PCA eigenvalue block nonsingular. -/
theorem factorLeadingPCEigenvalues_selected_diagonal_isUnit_of_posSemidef_rank_ge
    {Shat : Matrix k k ℝ} (hShat : Shat.IsHermitian)
    (hcard : Fintype.card r ≤ Fintype.card k)
    (hpsd : Shat.PosSemidef) (hrank : Fintype.card r ≤ Shat.rank) :
    IsUnit (Matrix.diagonal
      (factorLeadingPCEigenvalues (r := r) hShat hcard)).det :=
  factorLeadingPCEigenvalues_selected_diagonal_isUnit_of_pos
    (r := r) hShat hcard
    (factorLeadingPCEigenvalues_pos_of_posSemidef_rank_ge
      (r := r) hShat hcard hpsd hrank)

omit [Fintype n] [DecidableEq n] [DecidableEq r] in
/-- Positive definiteness of the sample/objective matrix gives positive
selected ordered PCA eigenvalues. This is stronger than the exact selected-rank
condition but useful when a raw full-rank sample covariance assumption is
available. -/
theorem factorLeadingPCEigenvalues_pos_of_posDef
    {Shat : Matrix k k ℝ} (hShat : Shat.IsHermitian)
    (hcard : Fintype.card r ≤ Fintype.card k)
    (hposDef : Shat.PosDef) :
    ∀ j, 0 < factorLeadingPCEigenvalues (r := r) hShat hcard j := by
  intro j
  have hproof : hposDef.1 = hShat := Subsingleton.elim _ _
  simpa [factorLeadingPCEigenvalues, orderedPCEigenvalue,
    orderedPCEigenIndex, Matrix.IsHermitian.eigenvalues, hproof] using
    hposDef.eigenvalues_pos
      (orderedPCEigenIndex (Fin.castLE hcard ((Fintype.equivFin r) j)))

/-- The selected leading PCA eigenvectors have orthonormal columns. -/
theorem factorLeadingPCEigenvectors_orthonormal
    {Shat : Matrix k k ℝ} (hShat : Shat.IsHermitian)
    (hcard : Fintype.card r ≤ Fintype.card k) :
    (factorLeadingPCEigenvectors (r := r) hShat hcard)ᵀ *
        factorLeadingPCEigenvectors (r := r) hShat hcard = 1 := by
  classical
  ext i j
  rw [Matrix.mul_apply]
  have hdot := orderedPCEigenvector_dotProduct hShat
    (Fin.castLE hcard ((Fintype.equivFin r) i))
    (Fin.castLE hcard ((Fintype.equivFin r) j))
  have hiff :
      Fin.castLE hcard ((Fintype.equivFin r) i) =
          Fin.castLE hcard ((Fintype.equivFin r) j) ↔ i = j := by
    constructor
    · intro h
      exact (Fintype.equivFin r).injective (Fin.castLE_injective hcard h)
    · intro h
      subst h
      rfl
  simpa [factorLeadingPCEigenvectors, Matrix.transpose_apply, dotProduct,
    Matrix.one_apply, hiff] using hdot

/-- The selected leading PCA eigenvectors solve the diagonal eigenspace equation
used in Hansen Theorem 11.9. -/
theorem factorLeadingPCEigenvectors_eigenspace
    {Shat : Matrix k k ℝ} (hShat : Shat.IsHermitian)
    (hcard : Fintype.card r ≤ Fintype.card k) :
    factorLeadingEigenspace Shat
      (factorLeadingPCEigenvectors (r := r) hShat hcard)
      (Matrix.diagonal (factorLeadingPCEigenvalues (r := r) hShat hcard)) := by
  classical
  ext a j
  have heig := orderedPCEigenvector_eigenvector hShat
    (Fin.castLE hcard ((Fintype.equivFin r) j))
  have haj := congrFun heig a
  simpa [factorLeadingEigenspace, factorLeadingPCEigenvectors,
    factorLeadingPCEigenvalues, Matrix.mul_apply, Matrix.mulVec, Matrix.diagonal,
    mul_comm] using haj

/-- Hansen Theorem 11.9 concentrated spectral objective. Under the normalized
factor-score parametrization, maximizing the concentrated least-squares
criterion is equivalent to maximizing this trace over matrices with orthonormal
columns. -/
noncomputable def factorConcentratedObjective
    (Shat : Matrix k k ℝ) (H : Matrix k r ℝ) : ℝ :=
  Matrix.trace (Hᵀ * Shat * H)

omit [DecidableEq n] [DecidableEq k] [DecidableEq r] in
/-- The arbitrary-score profiled cross-covariance trace is the concentrated PCA
objective of the observation-space Gram matrix at the normalized score frame. -/
theorem factorSampleCrossCovariance_trace_eq_observationGram_objective
    [Nonempty n] (X : n → k → ℝ) (F : n → r → ℝ) :
    Matrix.trace
        ((factorSampleCrossCovariance X F)ᵀ *
          factorSampleCrossCovariance X F) =
      factorConcentratedObjective (factorObservationGram X)
        (factorNormalizedScoreFrame F) := by
  rw [factorConcentratedObjective,
    factorSampleCrossCovariance_trace_eq_observationGram_trace]

/-- Hansen Theorem 11.9 concentrated least-squares criterion after profiling
out normalized factor scores. Minimizing this criterion is equivalent to
maximizing `factorConcentratedObjective`. -/
noncomputable def factorConcentratedLeastSquaresCriterion
    (Shat : Matrix k k ℝ) (H : Matrix k r ℝ) : ℝ :=
  Matrix.trace Shat - factorConcentratedObjective Shat H

/-- Hansen Theorem 11.9's original unprofiled least-squares criterion under
candidate loadings `Λ` and normalized factor scores `Fhat`. -/
noncomputable def factorLeastSquaresCriterion
    (X : n → k → ℝ) (Λ : Matrix k r ℝ) (Fhat : n → r → ℝ) : ℝ :=
  (Fintype.card n : ℝ)⁻¹ * ∑ i : n,
    (fun a : k => X i a - (Λ *ᵥ Fhat i) a) ⬝ᵥ
      (fun a : k => X i a - (Λ *ᵥ Fhat i) a)

omit [DecidableEq k] in
private theorem dotProduct_self_nonneg_real (x : k → ℝ) : 0 ≤ x ⬝ᵥ x := by
  rw [dotProduct]
  exact Finset.sum_nonneg (fun i _ => mul_self_nonneg (x i))

omit [Fintype n] [DecidableEq n] [DecidableEq k] [DecidableEq r] in
/-- Frobenius-square nonnegativity in trace form. This is the nonnegative
remainder used by the least-squares completion-of-squares profile argument. -/
theorem trace_transpose_mul_self_nonneg (A : Matrix k r ℝ) :
    0 ≤ Matrix.trace (Aᵀ * A) := by
  rw [Matrix.trace]
  exact Finset.sum_nonneg (fun j _ => by
    simpa [Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, dotProduct] using
      dotProduct_self_nonneg_real (fun a : k => A a j))

omit [DecidableEq n] [DecidableEq k] [DecidableEq r] in
/-- Raw finite-sample expansion of Hansen Theorem 11.9's unprofiled
least-squares criterion. This is the algebraic starting point for completing
the square in the normalized-score profiling argument. -/
theorem factorLeastSquaresCriterion_eq_sum_expand
    (X : n → k → ℝ) (Λ : Matrix k r ℝ) (Fhat : n → r → ℝ) :
    factorLeastSquaresCriterion X Λ Fhat =
      (Fintype.card n : ℝ)⁻¹ * ∑ i : n,
        ((X i) ⬝ᵥ (X i) - 2 * ((X i) ⬝ᵥ (Λ *ᵥ Fhat i)) +
          ((Λ *ᵥ Fhat i) ⬝ᵥ (Λ *ᵥ Fhat i))) := by
  unfold factorLeastSquaresCriterion
  congr 1
  refine Finset.sum_congr rfl ?_
  intro i _
  change ((X i - Λ *ᵥ Fhat i) ⬝ᵥ (X i - Λ *ᵥ Fhat i)) =
    X i ⬝ᵥ X i - 2 * (X i ⬝ᵥ Λ *ᵥ Fhat i) +
      (Λ *ᵥ Fhat i ⬝ᵥ Λ *ᵥ Fhat i)
  rw [sub_dotProduct, dotProduct_sub, dotProduct_sub]
  rw [dotProduct_comm (Λ *ᵥ Fhat i) (X i)]
  ring

omit [DecidableEq n] [DecidableEq k] [DecidableEq r] in
/-- Hansen Theorem 11.9's raw least-squares criterion is nonnegative. -/
theorem factorLeastSquaresCriterion_nonneg
    (X : n → k → ℝ) (Λ : Matrix k r ℝ) (Fhat : n → r → ℝ) :
    0 ≤ factorLeastSquaresCriterion X Λ Fhat := by
  unfold factorLeastSquaresCriterion
  exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
    (Finset.sum_nonneg (fun i _ =>
      dotProduct_self_nonneg_real (fun a : k => X i a - (Λ *ᵥ Fhat i) a)))

omit [Fintype r] [DecidableEq n] [DecidableEq k] [DecidableEq r] in
/-- Trace form of the first term in the raw least-squares expansion:
`trace(n⁻¹ X'X) = n⁻¹∑‖X_i‖²`. -/
theorem factorSampleCovariance_trace_eq_sum_dotProduct
    (X : n → k → ℝ) :
    Matrix.trace (factorSampleCovariance X) =
      (Fintype.card n : ℝ)⁻¹ * ∑ i : n, (X i) ⬝ᵥ (X i) := by
  rw [factorSampleCovariance, Matrix.trace]
  simp only [Matrix.diag, Matrix.smul_apply, Matrix.sum_apply,
    Matrix.vecMulVec_apply, smul_eq_mul, dotProduct]
  rw [← Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]

omit [Fintype k] [DecidableEq n] [DecidableEq k] [DecidableEq r] in
/-- Cross moments are linear in a fixed loading matrix applied to the score
array. This is the loading-profile normal-equation engine for Theorem 11.9. -/
theorem factorSampleCrossCovariance_left_linearMap
    (Λ : Matrix k r ℝ) (Fhat : n → r → ℝ) :
    factorSampleCrossCovariance (fun i => Λ *ᵥ Fhat i) Fhat =
      Λ * factorScoreSampleCovariance Fhat := by
  rw [factorSampleCrossCovariance, factorScoreSampleCovariance]
  simp_rw [← Matrix.mul_vecMulVec]
  rw [← Matrix.mul_sum, Matrix.mul_smul]

omit [Fintype k] [DecidableEq n] [DecidableEq k] in
/-- Under Hansen's normalization, refitting loadings against a fixed score
array returns the loading matrix itself. -/
theorem factorSampleCrossCovariance_fitted_self_of_normalized
    (Λ : Matrix k r ℝ) (Fhat : n → r → ℝ)
    (hF : factorScoreNormalization Fhat) :
    factorSampleCrossCovariance (fun i => Λ *ᵥ Fhat i) Fhat = Λ := by
  rw [factorSampleCrossCovariance_left_linearMap, hF, Matrix.mul_one]

omit [Fintype k] [Fintype r] [DecidableEq n] [DecidableEq k] [DecidableEq r] in
/-- Cross moments are additive in the data argument. -/
theorem factorSampleCrossCovariance_sub_left
    (X Y : n → k → ℝ) (Fhat : n → r → ℝ) :
    factorSampleCrossCovariance (fun i => X i - Y i) Fhat =
      factorSampleCrossCovariance X Fhat - factorSampleCrossCovariance Y Fhat := by
  ext a b
  simp [factorSampleCrossCovariance_apply, Finset.sum_sub_distrib, sub_mul]
  ring

omit [Fintype k] [DecidableEq n] [DecidableEq k] in
/-- Fixed-score residual orthogonality after refitting loadings by the sample
cross covariance. This is the normal-equation half of the deterministic
profile bridge for Hansen Theorem 11.9. -/
theorem factorSampleCrossCovariance_residual_of_crossCovariance_normalized
    (X : n → k → ℝ) (Fhat : n → r → ℝ)
    (hF : factorScoreNormalization Fhat) :
    factorSampleCrossCovariance
        (fun i => X i - factorSampleCrossCovariance X Fhat *ᵥ Fhat i) Fhat = 0 := by
  rw [factorSampleCrossCovariance_sub_left]
  rw [factorSampleCrossCovariance_left_linearMap]
  rw [hF, Matrix.mul_one, sub_self]

omit [DecidableEq n] [DecidableEq k] [DecidableEq r] in
/-- Trace form of the sample cross term in Hansen Theorem 11.9's normalized
least-squares criterion. -/
theorem trace_loading_transpose_mul_factorSampleCrossCovariance_eq_sum_dot
    (X : n → k → ℝ) (Λ : Matrix k r ℝ) (Fhat : n → r → ℝ) :
    Matrix.trace (Λᵀ * factorSampleCrossCovariance X Fhat) =
      (Fintype.card n : ℝ)⁻¹ * ∑ i : n, (X i) ⬝ᵥ (Λ *ᵥ Fhat i) := by
  classical
  rw [Matrix.trace]
  simp only [Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply,
    factorSampleCrossCovariance_apply, dotProduct, Matrix.mulVec]
  calc
    ∑ j : r, ∑ a : k,
        Λ a j * ((Fintype.card n : ℝ)⁻¹ * ∑ i : n, X i a * Fhat i j)
        =
      ∑ j : r, ∑ a : k,
        (Fintype.card n : ℝ)⁻¹ *
          ∑ i : n, X i a * (Λ a j * Fhat i j) := by
        refine Finset.sum_congr rfl ?_
        intro j _
        refine Finset.sum_congr rfl ?_
        intro a _
        calc
          Λ a j * ((Fintype.card n : ℝ)⁻¹ * ∑ i : n, X i a * Fhat i j)
              = (Fintype.card n : ℝ)⁻¹ *
                  (Λ a j * ∑ i : n, X i a * Fhat i j) := by
                  ring
          _ = (Fintype.card n : ℝ)⁻¹ *
                  ∑ i : n, Λ a j * (X i a * Fhat i j) := by
                  rw [Finset.mul_sum]
          _ = (Fintype.card n : ℝ)⁻¹ *
                  ∑ i : n, X i a * (Λ a j * Fhat i j) := by
                  congr 1
                  refine Finset.sum_congr rfl ?_
                  intro i _
                  ring
    _ =
      (Fintype.card n : ℝ)⁻¹ *
        ∑ j : r, ∑ a : k, ∑ i : n, X i a * (Λ a j * Fhat i j) := by
        calc
          ∑ j : r, ∑ a : k,
              (Fintype.card n : ℝ)⁻¹ *
                ∑ i : n, X i a * (Λ a j * Fhat i j)
              =
            ∑ j : r, (Fintype.card n : ℝ)⁻¹ *
              ∑ a : k, ∑ i : n, X i a * (Λ a j * Fhat i j) := by
              refine Finset.sum_congr rfl ?_
              intro j _
              rw [Finset.mul_sum]
          _ =
            (Fintype.card n : ℝ)⁻¹ *
              ∑ j : r, ∑ a : k, ∑ i : n,
                X i a * (Λ a j * Fhat i j) := by
              rw [Finset.mul_sum]
    _ =
      (Fintype.card n : ℝ)⁻¹ *
        ∑ i : n, ∑ a : k, ∑ j : r, X i a * (Λ a j * Fhat i j) := by
        congr 1
        calc
          ∑ j : r, ∑ a : k, ∑ i : n, X i a * (Λ a j * Fhat i j)
              =
            ∑ a : k, ∑ i : n, ∑ j : r, X i a * (Λ a j * Fhat i j) := by
              rw [Finset.sum_comm]
              refine Finset.sum_congr rfl ?_
              intro a _
              rw [Finset.sum_comm]
          _ =
            ∑ i : n, ∑ a : k, ∑ j : r, X i a * (Λ a j * Fhat i j) := by
              rw [Finset.sum_comm]
    _ =
      (Fintype.card n : ℝ)⁻¹ *
        ∑ i : n, ∑ a : k, X i a * ∑ j : r, Λ a j * Fhat i j := by
        congr 1
        refine Finset.sum_congr rfl ?_
        intro i _
        refine Finset.sum_congr rfl ?_
        intro a _
        rw [Finset.mul_sum]

omit [DecidableEq n] [DecidableEq k] in
/-- With Hansen-normalized scores, the fitted-value square term in the raw
least-squares criterion is the loading Gram trace. -/
theorem trace_loading_gram_eq_sum_fitted_dot_of_normalized
    (Λ : Matrix k r ℝ) (Fhat : n → r → ℝ)
    (hF : factorScoreNormalization Fhat) :
    Matrix.trace (Λᵀ * Λ) =
      (Fintype.card n : ℝ)⁻¹ *
        ∑ i : n, (Λ *ᵥ Fhat i) ⬝ᵥ (Λ *ᵥ Fhat i) := by
  calc
    Matrix.trace (Λᵀ * Λ) =
        Matrix.trace
          (Λᵀ * factorSampleCrossCovariance (fun i => Λ *ᵥ Fhat i) Fhat) := by
          rw [factorSampleCrossCovariance_fitted_self_of_normalized Λ Fhat hF]
    _ = (Fintype.card n : ℝ)⁻¹ *
        ∑ i : n, (Λ *ᵥ Fhat i) ⬝ᵥ (Λ *ᵥ Fhat i) := by
          rw [trace_loading_transpose_mul_factorSampleCrossCovariance_eq_sum_dot]

omit [DecidableEq n] [DecidableEq k] in
/-- Normalized-score expansion of Hansen Theorem 11.9's raw least-squares
criterion in trace/cross-moment form. -/
theorem factorLeastSquaresCriterion_eq_trace_sub_two_cross_add_loading_gram
    (X : n → k → ℝ) (Λ : Matrix k r ℝ) (Fhat : n → r → ℝ)
    (hF : factorScoreNormalization Fhat) :
    factorLeastSquaresCriterion X Λ Fhat =
      Matrix.trace (factorSampleCovariance X) -
        2 * Matrix.trace (Λᵀ * factorSampleCrossCovariance X Fhat) +
        Matrix.trace (Λᵀ * Λ) := by
  rw [factorLeastSquaresCriterion_eq_sum_expand]
  rw [factorSampleCovariance_trace_eq_sum_dotProduct]
  rw [trace_loading_transpose_mul_factorSampleCrossCovariance_eq_sum_dot]
  rw [trace_loading_gram_eq_sum_fitted_dot_of_normalized Λ Fhat hF]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

omit [Fintype n] [DecidableEq n] [DecidableEq k] [DecidableEq r] in
/-- Matrix completion of squares for finite-dimensional loadings. -/
theorem trace_sub_transpose_mul_sub
    (A B : Matrix k r ℝ) :
    Matrix.trace ((A - B)ᵀ * (A - B)) =
      Matrix.trace (Aᵀ * A) - 2 * Matrix.trace (Aᵀ * B) +
        Matrix.trace (Bᵀ * B) := by
  have hcomm : Matrix.trace (Bᵀ * A) = Matrix.trace (Aᵀ * B) := by
    calc
      Matrix.trace (Bᵀ * A) = Matrix.trace ((Bᵀ * A)ᵀ) := by
        rw [Matrix.trace_transpose]
      _ = Matrix.trace (Aᵀ * B) := by
        rw [Matrix.transpose_mul, Matrix.transpose_transpose]
  rw [Matrix.transpose_sub]
  rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub]
  rw [Matrix.trace_sub, Matrix.trace_sub, Matrix.trace_sub]
  rw [hcomm]
  ring

omit [DecidableEq n] [DecidableEq k] in
/-- Completion of squares for Hansen Theorem 11.9's normalized-score
least-squares criterion. For a fixed normalized score array, the profiled
loading is the sample cross moment `n⁻¹∑ X_i F_i'`. -/
theorem factorLeastSquaresCriterion_eq_trace_sub_cross_gram_add_square
    (X : n → k → ℝ) (Λ : Matrix k r ℝ) (Fhat : n → r → ℝ)
    (hF : factorScoreNormalization Fhat) :
    factorLeastSquaresCriterion X Λ Fhat =
      Matrix.trace (factorSampleCovariance X) -
        Matrix.trace
          ((factorSampleCrossCovariance X Fhat)ᵀ *
            factorSampleCrossCovariance X Fhat) +
        Matrix.trace
          ((Λ - factorSampleCrossCovariance X Fhat)ᵀ *
            (Λ - factorSampleCrossCovariance X Fhat)) := by
  rw [factorLeastSquaresCriterion_eq_trace_sub_two_cross_add_loading_gram
    X Λ Fhat hF]
  rw [trace_sub_transpose_mul_sub Λ (factorSampleCrossCovariance X Fhat)]
  ring

omit [DecidableEq n] [DecidableEq k] in
/-- The profiled loading for fixed normalized scores has criterion value
`trace(Ŝ) - trace(C_F'C_F)`. -/
theorem factorLeastSquaresCriterion_profiled_eq_trace_sub_cross_gram
    (X : n → k → ℝ) (Fhat : n → r → ℝ)
    (hF : factorScoreNormalization Fhat) :
    factorLeastSquaresCriterion X (factorSampleCrossCovariance X Fhat) Fhat =
      Matrix.trace (factorSampleCovariance X) -
        Matrix.trace
          ((factorSampleCrossCovariance X Fhat)ᵀ *
            factorSampleCrossCovariance X Fhat) := by
  rw [factorLeastSquaresCriterion_eq_trace_sub_cross_gram_add_square X
    (factorSampleCrossCovariance X Fhat) Fhat hF]
  simp

omit [DecidableEq n] [DecidableEq k] in
/-- Fixed-score profiling lower bound for Hansen Theorem 11.9: every loading
matrix is no better than the sample-cross-moment loading for the same
normalized score array. -/
theorem trace_sub_cross_gram_le_factorLeastSquaresCriterion
    (X : n → k → ℝ) (Λ : Matrix k r ℝ) (Fhat : n → r → ℝ)
    (hF : factorScoreNormalization Fhat) :
    Matrix.trace (factorSampleCovariance X) -
        Matrix.trace
          ((factorSampleCrossCovariance X Fhat)ᵀ *
            factorSampleCrossCovariance X Fhat) ≤
      factorLeastSquaresCriterion X Λ Fhat := by
  rw [factorLeastSquaresCriterion_eq_trace_sub_cross_gram_add_square X Λ Fhat hF]
  have hnonneg :
      0 ≤ Matrix.trace
        ((Λ - factorSampleCrossCovariance X Fhat)ᵀ *
          (Λ - factorSampleCrossCovariance X Fhat)) :=
    trace_transpose_mul_self_nonneg (Λ - factorSampleCrossCovariance X Fhat)
  linarith

/-- Literal normalized joint least-squares minimizer for Hansen Theorem 11.9:
among all loadings and score arrays satisfying `n⁻¹∑ F_iF_i' = I_r`, the
candidate pair has no larger residual sum of squares. -/
structure FactorLeastSquaresNormalizedMinimizer
    (X : n → k → ℝ) (Λhat : Matrix k r ℝ) (Fhat : n → r → ℝ) : Prop where
  score_normalization : factorScoreNormalization Fhat
  minimizes :
    ∀ (Λ : Matrix k r ℝ) (F : n → r → ℝ), factorScoreNormalization F →
      factorLeastSquaresCriterion X Λhat Fhat ≤ factorLeastSquaresCriterion X Λ F

/-- Deterministic bridge from Hansen's unprofiled normalized least-squares
problem to the profiled PCA criterion.

This records the algebraic profile step: identify the PCA pair's unprofiled
residual sum with the profiled criterion at `H`, and show that this profiled
value lower-bounds every normalized joint candidate. -/
structure FactorLeastSquaresProfileBridge
    (Shat : Matrix k k ℝ) (H : Matrix k r ℝ)
    (Λhat : Matrix k r ℝ) (X : n → k → ℝ) (Fhat : n → r → ℝ) : Prop where
  criterion_eq_concentrated :
    factorLeastSquaresCriterion X Λhat Fhat =
      factorConcentratedLeastSquaresCriterion Shat H
  concentrated_lower_bound :
    ∀ (Λ : Matrix k r ℝ) (F : n → r → ℝ), factorScoreNormalization F →
      factorConcentratedLeastSquaresCriterion Shat H ≤
        factorLeastSquaresCriterion X Λ F

omit [DecidableEq n] [DecidableEq k] in
/-- Build the deterministic profile bridge from the exact Eckart-Young/Ky Fan
cross-covariance trace inequality.

The assumption `hBound` is the sharp spectral statement for the premise-taking
Theorem 11.9 joint least-squares proof: every normalized score
array has profiled cross-covariance trace no larger than the PCA objective. -/
theorem FactorLeastSquaresProfileBridge.of_crossCovariance_trace_bound
    (Shat : Matrix k k ℝ) (H : Matrix k r ℝ)
    (Λhat : Matrix k r ℝ) (X : n → k → ℝ) (Fhat : n → r → ℝ)
    (hSample : Shat = factorSampleCovariance X)
    (hFhat : factorScoreNormalization Fhat)
    (hLoad : Λhat = factorSampleCrossCovariance X Fhat)
    (hObj :
      Matrix.trace (Λhatᵀ * Λhat) = factorConcentratedObjective Shat H)
    (hBound : ∀ F : n → r → ℝ, factorScoreNormalization F →
      Matrix.trace
          ((factorSampleCrossCovariance X F)ᵀ *
            factorSampleCrossCovariance X F) ≤
        factorConcentratedObjective Shat H) :
    FactorLeastSquaresProfileBridge Shat H Λhat X Fhat where
  criterion_eq_concentrated := by
    calc
      factorLeastSquaresCriterion X Λhat Fhat =
          factorLeastSquaresCriterion X
            (factorSampleCrossCovariance X Fhat) Fhat := by
            rw [hLoad]
      _ = Matrix.trace (factorSampleCovariance X) -
          Matrix.trace
            ((factorSampleCrossCovariance X Fhat)ᵀ *
              factorSampleCrossCovariance X Fhat) := by
            rw [factorLeastSquaresCriterion_profiled_eq_trace_sub_cross_gram
              X Fhat hFhat]
      _ = factorConcentratedLeastSquaresCriterion Shat H := by
            have htraceSample :
                Matrix.trace Shat = Matrix.trace (factorSampleCovariance X) := by
              rw [hSample]
            rw [factorConcentratedLeastSquaresCriterion, htraceSample]
            rw [← hLoad, hObj]
  concentrated_lower_bound := by
    intro Λ F hF
    have hprofile :=
      trace_sub_cross_gram_le_factorLeastSquaresCriterion X Λ F hF
    have hcross := hBound F hF
    have hleft :
        factorConcentratedLeastSquaresCriterion Shat H ≤
          Matrix.trace (factorSampleCovariance X) -
            Matrix.trace
              ((factorSampleCrossCovariance X F)ᵀ *
                factorSampleCrossCovariance X F) := by
      have htraceSample :
          Matrix.trace Shat = Matrix.trace (factorSampleCovariance X) := by
        rw [hSample]
      rw [factorConcentratedLeastSquaresCriterion, htraceSample]
      linarith
    exact hleft.trans hprofile

omit [DecidableEq n] [DecidableEq k] [DecidableEq r] in
/-- The concentrated factor-PCA trace objective is the sum of the column
Rayleigh quotients. This is the deterministic bridge used by Ky Fan style
arguments. -/
theorem factorConcentratedObjective_eq_sum_column_quadratic
    (Shat : Matrix k k ℝ) (H : Matrix k r ℝ) :
    factorConcentratedObjective Shat H =
      ∑ j : r, (fun a => H a j) ⬝ᵥ (Shat *ᵥ fun a => H a j) := by
  classical
  unfold factorConcentratedObjective
  rw [Matrix.trace]
  refine Finset.sum_congr rfl ?_
  intro j _
  calc
    Matrix.diag (Hᵀ * Shat * H) j
        = ∑ a, (∑ b, H b j * Shat b a) * H a j := by
            simp [Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply]
    _ = ∑ a, ∑ b, (H b j * Shat b a) * H a j := by
            refine Finset.sum_congr rfl ?_
            intro a _
            rw [Finset.sum_mul]
    _ = ∑ b, ∑ a, (H b j * Shat b a) * H a j := by
            rw [Finset.sum_comm]
    _ = ∑ b, H b j * ∑ a, Shat b a * H a j := by
            refine Finset.sum_congr rfl ?_
            intro b _
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl ?_
            intro a _
            ring
    _ = (fun a => H a j) ⬝ᵥ (Shat *ᵥ fun a => H a j) := by
            simp [dotProduct, Matrix.mulVec]

/-- Global maximizer predicate for the concentrated factor-PCA spectral
objective over orthonormal loading directions. -/
structure FactorConcentratedObjectiveMaximizer
    (Shat : Matrix k k ℝ) (H : Matrix k r ℝ) : Prop where
  orthonormal : Hᵀ * H = 1
  maximizes :
    ∀ G : Matrix k r ℝ, Gᵀ * G = 1 →
      factorConcentratedObjective Shat G ≤ factorConcentratedObjective Shat H

/-- Global minimizer predicate for Hansen Theorem 11.9's concentrated
least-squares criterion over orthonormal loading directions. -/
structure FactorConcentratedLeastSquaresCriterionMinimizer
    (Shat : Matrix k k ℝ) (H : Matrix k r ℝ) : Prop where
  orthonormal : Hᵀ * H = 1
  minimizes :
    ∀ G : Matrix k r ℝ, Gᵀ * G = 1 →
      factorConcentratedLeastSquaresCriterion Shat H ≤
        factorConcentratedLeastSquaresCriterion Shat G

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

omit [Fintype n] [Fintype k] [DecidableEq n] [DecidableEq k] in
/-- Canonical diagonal `D^{1/2}` scaling used by Hansen Theorem 11.9. -/
noncomputable def factorPCDiagonalSqrtD (d : r → ℝ) : Matrix r r ℝ :=
  Matrix.diagonal fun j => Real.sqrt (d j)

omit [Fintype n] [Fintype k] [DecidableEq n] [DecidableEq k] in
/-- Canonical diagonal `D^{-1/2}` scaling used by Hansen Theorem 11.9. -/
noncomputable def factorPCDiagonalInvSqrtD (d : r → ℝ) : Matrix r r ℝ :=
  Matrix.diagonal fun j => (Real.sqrt (d j))⁻¹

private theorem inv_sqrt_mul_self_mul_inv_sqrt {x : ℝ} (hx : 0 < x) :
    (Real.sqrt x)⁻¹ * x * (Real.sqrt x)⁻¹ = 1 := by
  have hsqrt_ne : Real.sqrt x ≠ 0 := (Real.sqrt_pos_of_pos hx).ne'
  have hsqrt_sq : Real.sqrt x * Real.sqrt x = x :=
    Real.mul_self_sqrt hx.le
  calc
    (Real.sqrt x)⁻¹ * x * (Real.sqrt x)⁻¹ =
        (Real.sqrt x)⁻¹ * (Real.sqrt x * Real.sqrt x) * (Real.sqrt x)⁻¹ := by
          rw [hsqrt_sq]
    _ = ((Real.sqrt x)⁻¹ * Real.sqrt x) * Real.sqrt x * (Real.sqrt x)⁻¹ := by
          rw [← mul_assoc]
    _ = 1 := by
          rw [inv_mul_cancel₀ hsqrt_ne, one_mul, mul_inv_cancel₀ hsqrt_ne]

private theorem mul_inv_sqrt_eq_sqrt {x : ℝ} (hx : 0 < x) :
    x * (Real.sqrt x)⁻¹ = Real.sqrt x := by
  have hsqrt_ne : Real.sqrt x ≠ 0 := (Real.sqrt_pos_of_pos hx).ne'
  have hsqrt_sq : Real.sqrt x * Real.sqrt x = x :=
    Real.mul_self_sqrt hx.le
  calc
    x * (Real.sqrt x)⁻¹ =
        (Real.sqrt x * Real.sqrt x) * (Real.sqrt x)⁻¹ := by
          rw [hsqrt_sq]
    _ = Real.sqrt x * (Real.sqrt x * (Real.sqrt x)⁻¹) := by
          rw [mul_assoc]
    _ = Real.sqrt x := by
          rw [mul_inv_cancel₀ hsqrt_ne, mul_one]

omit [Fintype n] [Fintype k] [DecidableEq n] [DecidableEq k] in
/-- Canonical diagonal `D^{-1/2}` normalizes a positive diagonal eigenvalue matrix. -/
theorem factorPCDiagonalInvSqrtD_mul_diagonal_mul_transpose
    (d : r → ℝ) (hpos : ∀ j, 0 < d j) :
    factorPCDiagonalInvSqrtD d * Matrix.diagonal d *
        (factorPCDiagonalInvSqrtD d)ᵀ = 1 := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [factorPCDiagonalInvSqrtD,
      inv_sqrt_mul_self_mul_inv_sqrt (hpos i)]
  · simp [factorPCDiagonalInvSqrtD, hij]

omit [Fintype n] [Fintype k] [DecidableEq n] [DecidableEq k] in
/-- Canonical diagonal `D^{-1/2}` converts positive diagonal eigenvalues to
`D^{1/2}`. -/
theorem diagonal_mul_factorPCDiagonalInvSqrtD_transpose
    (d : r → ℝ) (hpos : ∀ j, 0 < d j) :
    Matrix.diagonal d * (factorPCDiagonalInvSqrtD d)ᵀ =
      factorPCDiagonalSqrtD d := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [factorPCDiagonalSqrtD, factorPCDiagonalInvSqrtD,
      mul_inv_sqrt_eq_sqrt (hpos i)]
  · simp [factorPCDiagonalSqrtD, factorPCDiagonalInvSqrtD, hij]

omit [Fintype n] [Fintype k] [DecidableEq n] [DecidableEq k] in
/-- Canonical positive diagonal PCA scales cancel in the fitted common
component. This is the deterministic identity behind Hansen's
`Λ̂F̂_i = H H' X_i` projection formula. -/
@[simp]
theorem factorPCDiagonalSqrtD_mul_factorPCDiagonalInvSqrtD
    (d : r → ℝ) (hpos : ∀ j, 0 < d j) :
    factorPCDiagonalSqrtD d * factorPCDiagonalInvSqrtD d = 1 := by
  ext i j
  by_cases hij : i = j
  · subst j
    have hsqrt_ne : Real.sqrt (d i) ≠ 0 :=
      (Real.sqrt_pos_of_pos (hpos i)).ne'
    simp [factorPCDiagonalSqrtD, factorPCDiagonalInvSqrtD, hsqrt_ne]
  · simp [factorPCDiagonalSqrtD, factorPCDiagonalInvSqrtD, hij]

omit [Fintype n] [DecidableEq n] [DecidableEq k] in
/-- Hansen Theorem 11.9 fitted-value identity for canonical positive PCA
scaling: the product of the PCA loading and score estimators is the projection
of the observation onto the selected loading directions. -/
@[simp]
theorem factorLoadingEstimator_mulVec_factorScoreEstimator_diagonal
    (H : Matrix k r ℝ) (d : r → ℝ) (hpos : ∀ j, 0 < d j) (x : k → ℝ) :
    factorLoadingEstimator H (factorPCDiagonalSqrtD d) *ᵥ
        factorScoreEstimator H (factorPCDiagonalInvSqrtD d) x =
      (H * Hᵀ) *ᵥ x := by
  unfold factorLoadingEstimator factorScoreEstimator
  calc
    (H * factorPCDiagonalSqrtD d) *ᵥ
        (factorPCDiagonalInvSqrtD d *ᵥ (Hᵀ *ᵥ x)) =
        ((H * factorPCDiagonalSqrtD d) * factorPCDiagonalInvSqrtD d) *ᵥ
          (Hᵀ *ᵥ x) := by
            exact Matrix.mulVec_mulVec (Hᵀ *ᵥ x)
              (H * factorPCDiagonalSqrtD d) (factorPCDiagonalInvSqrtD d)
    _ = (H * (factorPCDiagonalSqrtD d * factorPCDiagonalInvSqrtD d)) *ᵥ
          (Hᵀ *ᵥ x) := by
            rw [Matrix.mul_assoc]
    _ = H *ᵥ (Hᵀ *ᵥ x) := by
            rw [factorPCDiagonalSqrtD_mul_factorPCDiagonalInvSqrtD d hpos,
              Matrix.mul_one]
    _ = (H * Hᵀ) *ᵥ x := by
            exact Matrix.mulVec_mulVec x H Hᵀ

omit [Fintype n] [DecidableEq n] [DecidableEq k] in
/-- For canonical positive diagonal PCA scaling, the loading Gram trace equals
the concentrated PCA objective value. This is the equality side of the
normalized joint least-squares profile bridge for Hansen Theorem 11.9. -/
theorem factorLoadingEstimator_diagonal_trace_gram_eq_concentratedObjective
    (Shat : Matrix k k ℝ) (H : Matrix k r ℝ) (d : r → ℝ)
    (hLead : factorLeadingEigenspace Shat H (Matrix.diagonal d))
    (hOrth : Hᵀ * H = 1) (hpos : ∀ j, 0 < d j) :
    Matrix.trace
        ((factorLoadingEstimator H (factorPCDiagonalSqrtD d))ᵀ *
          factorLoadingEstimator H (factorPCDiagonalSqrtD d)) =
      factorConcentratedObjective Shat H := by
  have hgram :
      (factorLoadingEstimator H (factorPCDiagonalSqrtD d))ᵀ *
          factorLoadingEstimator H (factorPCDiagonalSqrtD d) =
        Matrix.diagonal d := by
    unfold factorLoadingEstimator
    calc
      (H * factorPCDiagonalSqrtD d)ᵀ * (H * factorPCDiagonalSqrtD d)
          = (factorPCDiagonalSqrtD d)ᵀ * Hᵀ *
              (H * factorPCDiagonalSqrtD d) := by
                rw [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = (factorPCDiagonalSqrtD d)ᵀ * ((Hᵀ * H) *
              factorPCDiagonalSqrtD d) := by
                simp only [Matrix.mul_assoc]
      _ = (factorPCDiagonalSqrtD d)ᵀ * (1 * factorPCDiagonalSqrtD d) := by
                rw [hOrth]
      _ = (factorPCDiagonalSqrtD d)ᵀ * factorPCDiagonalSqrtD d := by
                rw [Matrix.one_mul]
      _ = Matrix.diagonal d := by
                ext i j
                by_cases hij : i = j
                · subst j
                  simp [factorPCDiagonalSqrtD, Real.mul_self_sqrt (hpos i).le]
                · simp [factorPCDiagonalSqrtD, hij]
  have hmiddle : Hᵀ * Shat * H = Matrix.diagonal d := by
    calc
      Hᵀ * Shat * H = Hᵀ * (Shat * H) := by
        rw [Matrix.mul_assoc]
      _ = Hᵀ * (H * Matrix.diagonal d) := by
        rw [hLead]
      _ = Hᵀ * H * Matrix.diagonal d := by
        rw [Matrix.mul_assoc]
      _ = Matrix.diagonal d := by
        rw [hOrth, Matrix.one_mul]
  simp [factorConcentratedObjective, hgram, hmiddle]

omit [Fintype n] [Fintype k] [DecidableEq n] [DecidableEq k] in
/-- The fixed-loading least-squares score scale for canonical positive
diagonal PCA scaling. -/
theorem factorPCDiagonalSqrtD_leastSquares_score_scale
    (d : r → ℝ) (hpos : ∀ j, 0 < d j) :
    ((factorPCDiagonalSqrtD d)ᵀ * factorPCDiagonalSqrtD d)⁻¹ *
        (factorPCDiagonalSqrtD d)ᵀ = factorPCDiagonalInvSqrtD d := by
  have hgram :
      (factorPCDiagonalSqrtD d)ᵀ * factorPCDiagonalSqrtD d =
        Matrix.diagonal d := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [factorPCDiagonalSqrtD, Real.mul_self_sqrt (hpos i).le]
    · simp [factorPCDiagonalSqrtD, hij]
  have hD_right_inverse :
      Matrix.diagonal d * Matrix.diagonal (fun j => (d j)⁻¹) = 1 := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [(hpos i).ne']
    · simp [hij]
  have hDunit : IsUnit (Matrix.diagonal d).det :=
    Matrix.isUnit_det_of_right_inverse (A := Matrix.diagonal d)
      (B := Matrix.diagonal fun j => (d j)⁻¹) hD_right_inverse
  have hD_mul_invSqrt :
      Matrix.diagonal d * factorPCDiagonalInvSqrtD d =
        factorPCDiagonalSqrtD d := by
    simpa [factorPCDiagonalInvSqrtD] using
      diagonal_mul_factorPCDiagonalInvSqrtD_transpose d hpos
  calc
    ((factorPCDiagonalSqrtD d)ᵀ * factorPCDiagonalSqrtD d)⁻¹ *
        (factorPCDiagonalSqrtD d)ᵀ =
        (Matrix.diagonal d)⁻¹ * factorPCDiagonalSqrtD d := by
          rw [hgram]
          simp [factorPCDiagonalSqrtD]
    _ = factorPCDiagonalInvSqrtD d := by
          rw [← hD_mul_invSqrt]
          exact Matrix.nonsing_inv_mul_cancel_left (Matrix.diagonal d)
            (factorPCDiagonalInvSqrtD d) hDunit

omit [Fintype n] [DecidableEq n] [DecidableEq k] in
/-- Positive diagonal eigenvalues provide Hansen Theorem 11.9's canonical PCA
scaling certificate without arbitrary square-root data. -/
theorem factorPCScaling_diagonal_of_pos
    (H : Matrix k r ℝ) (d : r → ℝ)
    (hOrth : Hᵀ * H = 1) (hpos : ∀ j, 0 < d j) :
    FactorPCScaling H (Matrix.diagonal d)
      (factorPCDiagonalSqrtD d) (factorPCDiagonalInvSqrtD d) where
  eigenvectors_orthonormal := hOrth
  score_scale_normalizes :=
    factorPCDiagonalInvSqrtD_mul_diagonal_mul_transpose d hpos
  loading_scale :=
    diagonal_mul_factorPCDiagonalInvSqrtD_transpose d hpos
  leastSquares_score_scale :=
    factorPCDiagonalSqrtD_leastSquares_score_scale d hpos

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
/-- A concentrated objective maximizer is the same Hansen least-squares
solution written as a minimizer of the profiled criterion. -/
theorem factorConcentratedLeastSquaresCriterionMinimizer_of_objectiveMaximizer
    (Shat : Matrix k k ℝ) (H : Matrix k r ℝ)
    (hOpt : FactorConcentratedObjectiveMaximizer Shat H) :
    FactorConcentratedLeastSquaresCriterionMinimizer Shat H where
  orthonormal := hOpt.orthonormal
  minimizes := by
    intro G hG
    have hmax := hOpt.maximizes G hG
    simpa [factorConcentratedLeastSquaresCriterion] using
      sub_le_sub_left hmax (Matrix.trace Shat)

/-- If the Mathlib-facing Ky Fan trace inequality is available for the leading
ordered PCA eigenvectors, they are a global maximizer of Hansen Theorem 11.9's
concentrated factor-PCA objective. -/
theorem factorLeadingPCEigenvectors_concentratedObjectiveMaximizer_of_kyFan
    {Shat : Matrix k k ℝ} (hShat : Shat.IsHermitian)
    (hcard : Fintype.card r ≤ Fintype.card k)
    (hKyFan : ∀ G : Matrix k r ℝ, Gᵀ * G = 1 →
      factorConcentratedObjective Shat G ≤
        factorConcentratedObjective Shat
          (factorLeadingPCEigenvectors (r := r) hShat hcard)) :
    FactorConcentratedObjectiveMaximizer Shat
      (factorLeadingPCEigenvectors (r := r) hShat hcard) :=
  factorConcentratedObjectiveMaximizer_of_trace_maximal Shat
    (factorLeadingPCEigenvectors (r := r) hShat hcard)
    (factorLeadingPCEigenvectors_orthonormal (r := r) hShat hcard)
    hKyFan

/-- The leading ordered PCA eigenspace gives Hansen Theorem 11.9's concentrated
objective maximizer certificate once the Ky Fan trace inequality is supplied. -/
theorem factorLeadingPCEigenvectors_concentratedObjectiveMaximizer_of_kyFan_trace_bound
    {Shat : Matrix k k ℝ} (hShat : Shat.IsHermitian)
    (hcard : Fintype.card r ≤ Fintype.card k)
    (hKyFan : ∀ G : Matrix k r ℝ, Gᵀ * G = 1 →
      factorConcentratedObjective Shat G ≤
        ∑ j : r, factorLeadingPCEigenvalues (r := r) hShat hcard j) :
    FactorConcentratedObjectiveMaximizer Shat
      (factorLeadingPCEigenvectors (r := r) hShat hcard) := by
  refine factorLeadingPCEigenvectors_concentratedObjectiveMaximizer_of_kyFan
    (r := r) hShat hcard ?_
  intro G hG
  refine (hKyFan G hG).trans_eq ?_
  rw [factorConcentratedObjective_eq_sum_eigenvalues_of_normalized Shat
    (factorLeadingPCEigenvectors (r := r) hShat hcard)
    (factorLeadingPCEigenvalues (r := r) hShat hcard)
    (factorLeadingPCEigenvectors_eigenspace (r := r) hShat hcard)
    (factorLeadingPCEigenvectors_orthonormal (r := r) hShat hcard)]

/-- Ky Fan trace inequality in Hansen Theorem 11.9's factor-PCA notation:
any orthonormal `r`-frame has concentrated objective bounded by the sum of the
leading `r` ordered eigenvalues of the sample covariance matrix. -/
theorem factorConcentratedObjective_le_sum_leadingPCEigenvalues
    {Shat : Matrix k k ℝ} (hShat : Shat.IsHermitian)
    (hcard : Fintype.card r ≤ Fintype.card k)
    (G : Matrix k r ℝ) (hG : Gᵀ * G = 1) :
    factorConcentratedObjective Shat G ≤
      ∑ j : r, factorLeadingPCEigenvalues (r := r) hShat hcard j := by
  rw [factorConcentratedObjective_eq_sum_column_quadratic]
  simpa [factorLeadingPCEigenvalues] using
    hermitian_sum_column_quadratic_le_sum_largest_eigenvalues
      (M := Shat) hShat hcard G hG

-- Observation-space Ky Fan bound for Hansen Theorem 11.9's arbitrary-score
-- trace inequality: every Hansen-normalized score array has
-- profiled cross-covariance trace bounded by the leading `r` eigenvalues of
-- `n⁻¹XX'`.
omit [DecidableEq k] in
theorem factorSampleCrossCovariance_trace_le_sum_observationGram_leadingEigenvalues
    [Nonempty n] (hcardObs : Fintype.card r ≤ Fintype.card n)
    (X : n → k → ℝ) (F : n → r → ℝ)
    (hF : factorScoreNormalization F) :
    Matrix.trace
        ((factorSampleCrossCovariance X F)ᵀ *
          factorSampleCrossCovariance X F) ≤
      ∑ j : r, factorLeadingPCEigenvalues (r := r)
        (factorObservationGram_isHermitian X) hcardObs j := by
  classical
  rw [factorSampleCrossCovariance_trace_eq_observationGram_objective]
  exact factorConcentratedObjective_le_sum_leadingPCEigenvalues
    (r := r) (factorObservationGram_isHermitian X) hcardObs
    (factorNormalizedScoreFrame F)
    (factorNormalizedScoreFrame_orthonormal F hF)

/-- Reduction of the exact cross-covariance trace bound to the
spectral transfer from the observation-space Gram `n⁻¹XX'` to the sample
covariance `n⁻¹X'X`. The no-extra-premise wrapper below supplies this transfer
from the zero-padded spectrum bridge. -/
theorem
    factorPCTheorem11_9_crossCovariance_trace_bound_of_observationGram_eigenvalue_bound
    [Nonempty n] (hcard : Fintype.card r ≤ Fintype.card k)
    (hcardObs : Fintype.card r ≤ Fintype.card n) (X : n → k → ℝ)
    (hObsToSample :
      (∑ j : r, factorLeadingPCEigenvalues (r := r)
        (factorObservationGram_isHermitian X) hcardObs j) ≤
        factorConcentratedObjective (factorSampleCovariance X)
          (factorLeadingPCEigenvectors (r := r)
            (factorSampleCovariance_isHermitian X) hcard)) :
    ∀ F : n → r → ℝ, factorScoreNormalization F →
      Matrix.trace
          ((factorSampleCrossCovariance X F)ᵀ *
            factorSampleCrossCovariance X F) ≤
        factorConcentratedObjective (factorSampleCovariance X)
          (factorLeadingPCEigenvectors (r := r)
            (factorSampleCovariance_isHermitian X) hcard) := by
  intro F hF
  exact
    (factorSampleCrossCovariance_trace_le_sum_observationGram_leadingEigenvalues
      (r := r) hcardObs X F hF).trans hObsToSample

omit [DecidableEq n] in
/-- Hansen Theorem 11.9 arbitrary-score cross-covariance trace bound with the
observation-Gram spectral transfer fully discharged.

Every Hansen-normalized score array has profiled cross-covariance trace bounded
by the principal-component objective value computed from the leading
eigenvectors of the sample covariance `n⁻¹X'X`. -/
theorem factorPCTheorem11_9_crossCovariance_trace_bound
    [Nonempty n] (hcard : Fintype.card r ≤ Fintype.card k)
    (hcardObs : Fintype.card r ≤ Fintype.card n) (X : n → k → ℝ) :
    ∀ F : n → r → ℝ, factorScoreNormalization F →
      Matrix.trace
          ((factorSampleCrossCovariance X F)ᵀ *
            factorSampleCrossCovariance X F) ≤
        factorConcentratedObjective (factorSampleCovariance X)
            (factorLeadingPCEigenvectors (r := r)
            (factorSampleCovariance_isHermitian X) hcard) := by
  classical
  refine
    factorPCTheorem11_9_crossCovariance_trace_bound_of_observationGram_eigenvalue_bound
      (r := r) hcard hcardObs X ?_
  have hsum :=
    factorObservationGram_sampleCovariance_leadingEigenvalue_sum_eq
      (r := r) hcard hcardObs X
  have hobj :
      factorConcentratedObjective (factorSampleCovariance X)
          (factorLeadingPCEigenvectors (r := r)
            (factorSampleCovariance_isHermitian X) hcard) =
        ∑ j : r, factorLeadingPCEigenvalues (r := r)
          (factorSampleCovariance_isHermitian X) hcard j := by
    rw [factorConcentratedObjective_eq_sum_eigenvalues_of_normalized
      (factorSampleCovariance X)
      (factorLeadingPCEigenvectors (r := r)
        (factorSampleCovariance_isHermitian X) hcard)
      (factorLeadingPCEigenvalues (r := r)
        (factorSampleCovariance_isHermitian X) hcard)
      (factorLeadingPCEigenvectors_eigenspace (r := r)
        (factorSampleCovariance_isHermitian X) hcard)
      (factorLeadingPCEigenvectors_orthonormal (r := r)
        (factorSampleCovariance_isHermitian X) hcard)]
  exact le_of_eq (hsum.trans hobj.symm)

/-- The leading ordered PCA eigenspace is an unconditional global maximizer of
Hansen Theorem 11.9's concentrated factor-PCA objective. -/
theorem factorLeadingPCEigenvectors_concentratedObjectiveMaximizer
    {Shat : Matrix k k ℝ} (hShat : Shat.IsHermitian)
    (hcard : Fintype.card r ≤ Fintype.card k) :
    FactorConcentratedObjectiveMaximizer Shat
      (factorLeadingPCEigenvectors (r := r) hShat hcard) :=
  factorLeadingPCEigenvectors_concentratedObjectiveMaximizer_of_kyFan_trace_bound
    (r := r) hShat hcard
    (fun G hG =>
      factorConcentratedObjective_le_sum_leadingPCEigenvalues
        (r := r) hShat hcard G hG)

/-- The leading ordered PCA eigenspace minimizes Hansen Theorem 11.9's
concentrated least-squares criterion. -/
theorem factorLeadingPCEigenvectors_concentratedLeastSquaresCriterionMinimizer
    {Shat : Matrix k k ℝ} (hShat : Shat.IsHermitian)
    (hcard : Fintype.card r ≤ Fintype.card k) :
    FactorConcentratedLeastSquaresCriterionMinimizer Shat
      (factorLeadingPCEigenvectors (r := r) hShat hcard) :=
  factorConcentratedLeastSquaresCriterionMinimizer_of_objectiveMaximizer Shat
    (factorLeadingPCEigenvectors (r := r) hShat hcard)
    (factorLeadingPCEigenvectors_concentratedObjectiveMaximizer
      (r := r) hShat hcard)

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
  unfold factorScoreEstimator factorScoreLeastSquares factorLoadingEstimator olsBetaStar
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

omit [DecidableEq n] in
/-- Hansen Theorem 11.9, ordered leading-eigenspace route.

Once the Ky Fan trace inequality is supplied for the leading ordered PCA
eigenvectors, the principal-component factor estimator satisfies the sample
covariance equation, leading-eigenspace/global-optimizer certificate, loading
formula, score formula, and Hansen factor-score normalization. -/
theorem factorPCSolution_of_leadingPCEigenvectors_kyFan_trace_bound
    {Shat : Matrix k k ℝ} (hShat : Shat.IsHermitian)
    (hcard : Fintype.card r ≤ Fintype.card k)
    (sqrtD invSqrtD : Matrix r r ℝ) (X : n → k → ℝ)
    (hSample : Shat = factorSampleCovariance X)
    (hscale : FactorPCScaling
      (factorLeadingPCEigenvectors (r := r) hShat hcard)
      (Matrix.diagonal (factorLeadingPCEigenvalues (r := r) hShat hcard))
      sqrtD invSqrtD)
    (hKyFan : ∀ G : Matrix k r ℝ, Gᵀ * G = 1 →
      factorConcentratedObjective Shat G ≤
        ∑ j : r, factorLeadingPCEigenvalues (r := r) hShat hcard j) :
    FactorPCSolution Shat
      (factorLeadingPCEigenvectors (r := r) hShat hcard)
      sqrtD invSqrtD
      (factorLoadingEstimator
        (factorLeadingPCEigenvectors (r := r) hShat hcard) sqrtD)
      X
      (fun i =>
        factorScoreEstimator
          (factorLeadingPCEigenvectors (r := r) hShat hcard)
          invSqrtD (X i))
      (factorLeadingEigenspace Shat
          (factorLeadingPCEigenvectors (r := r) hShat hcard)
          (Matrix.diagonal
            (factorLeadingPCEigenvalues (r := r) hShat hcard)) ∧
        FactorConcentratedObjectiveMaximizer Shat
          (factorLeadingPCEigenvectors (r := r) hShat hcard))
      (factorScoreNormalization
        (fun i =>
          factorScoreEstimator
            (factorLeadingPCEigenvectors (r := r) hShat hcard)
            invSqrtD (X i))) := by
  exact factorPCSolution_of_concentratedObjective_optimizer Shat
    (factorLeadingPCEigenvectors (r := r) hShat hcard)
    (Matrix.diagonal (factorLeadingPCEigenvalues (r := r) hShat hcard))
    sqrtD invSqrtD X hSample
    (factorLeadingPCEigenvectors_eigenspace (r := r) hShat hcard)
    hscale
    (factorLeadingPCEigenvectors_concentratedObjectiveMaximizer_of_kyFan_trace_bound
      (r := r) hShat hcard hKyFan)

omit [DecidableEq n] in
/-- Hansen Theorem 11.9, ordered leading-eigenspace route.

The leading ordered PCA eigenvectors satisfy the sample-covariance eigenspace
equation, globally maximize the concentrated factor-PCA objective by Ky Fan's
trace inequality, and assemble the loading formula, score formula, and Hansen
factor-score normalization under the deterministic PCA scaling equations. -/
theorem factorPCSolution_of_leadingPCEigenvectors
    {Shat : Matrix k k ℝ} (hShat : Shat.IsHermitian)
    (hcard : Fintype.card r ≤ Fintype.card k)
    (sqrtD invSqrtD : Matrix r r ℝ) (X : n → k → ℝ)
    (hSample : Shat = factorSampleCovariance X)
    (hscale : FactorPCScaling
      (factorLeadingPCEigenvectors (r := r) hShat hcard)
      (Matrix.diagonal (factorLeadingPCEigenvalues (r := r) hShat hcard))
      sqrtD invSqrtD) :
    FactorPCSolution Shat
      (factorLeadingPCEigenvectors (r := r) hShat hcard)
      sqrtD invSqrtD
      (factorLoadingEstimator
        (factorLeadingPCEigenvectors (r := r) hShat hcard) sqrtD)
      X
      (fun i =>
        factorScoreEstimator
          (factorLeadingPCEigenvectors (r := r) hShat hcard)
          invSqrtD (X i))
      (factorLeadingEigenspace Shat
          (factorLeadingPCEigenvectors (r := r) hShat hcard)
          (Matrix.diagonal
            (factorLeadingPCEigenvalues (r := r) hShat hcard)) ∧
        FactorConcentratedObjectiveMaximizer Shat
          (factorLeadingPCEigenvectors (r := r) hShat hcard))
      (factorScoreNormalization
        (fun i =>
          factorScoreEstimator
            (factorLeadingPCEigenvectors (r := r) hShat hcard)
            invSqrtD (X i))) :=
  factorPCSolution_of_leadingPCEigenvectors_kyFan_trace_bound
    (r := r) hShat hcard sqrtD invSqrtD X hSample hscale
    (fun G hG =>
      factorConcentratedObjective_le_sum_leadingPCEigenvalues
        (r := r) hShat hcard G hG)

omit [DecidableEq n] in
/-- Hansen Theorem 11.9, ordered leading-eigenspace route specialized to the
sample second-moment matrix `Ŝ = n⁻¹∑ X_iX_i'`.

This wrapper derives the Hermitian premise from
`factorSampleCovariance_isHermitian`, leaving only the deterministic PCA scaling
equations explicit. -/
theorem factorPCSolution_of_sampleCovariance_leadingPCEigenvectors
    (hcard : Fintype.card r ≤ Fintype.card k)
    (sqrtD invSqrtD : Matrix r r ℝ) (X : n → k → ℝ)
    (hscale : FactorPCScaling
      (factorLeadingPCEigenvectors (r := r)
        (factorSampleCovariance_isHermitian X) hcard)
      (Matrix.diagonal
        (factorLeadingPCEigenvalues (r := r)
          (factorSampleCovariance_isHermitian X) hcard))
      sqrtD invSqrtD) :
    FactorPCSolution (factorSampleCovariance X)
      (factorLeadingPCEigenvectors (r := r)
        (factorSampleCovariance_isHermitian X) hcard)
      sqrtD invSqrtD
      (factorLoadingEstimator
        (factorLeadingPCEigenvectors (r := r)
          (factorSampleCovariance_isHermitian X) hcard) sqrtD)
      X
      (fun i =>
        factorScoreEstimator
          (factorLeadingPCEigenvectors (r := r)
            (factorSampleCovariance_isHermitian X) hcard)
          invSqrtD (X i))
      (factorLeadingEigenspace (factorSampleCovariance X)
          (factorLeadingPCEigenvectors (r := r)
            (factorSampleCovariance_isHermitian X) hcard)
          (Matrix.diagonal
            (factorLeadingPCEigenvalues (r := r)
              (factorSampleCovariance_isHermitian X) hcard)) ∧
        FactorConcentratedObjectiveMaximizer (factorSampleCovariance X)
          (factorLeadingPCEigenvectors (r := r)
            (factorSampleCovariance_isHermitian X) hcard))
      (factorScoreNormalization
        (fun i =>
          factorScoreEstimator
            (factorLeadingPCEigenvectors (r := r)
              (factorSampleCovariance_isHermitian X) hcard)
            invSqrtD (X i))) :=
  factorPCSolution_of_leadingPCEigenvectors
    (r := r) (hShat := factorSampleCovariance_isHermitian X)
    hcard sqrtD invSqrtD X rfl hscale

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

/-- Hansen Theorem 11.9, theorem-facing least-squares factor-PCA certificate.

The fields keep the statement at Hansen's surface: the sample covariance is
diagonalized by the leading loading directions with selected eigenvalue matrix
`D`; those directions solve the global concentrated least-squares problem; the
loadings and scores have Hansen's formulas; the scores are also the
fixed-loading least-squares scores; and the normalized-score normal equation
recovers the loadings. -/
structure FactorPCTheorem11_9
    (Shat : Matrix k k ℝ) (H : Matrix k r ℝ) (D sqrtD invSqrtD : Matrix r r ℝ)
    (Λhat : Matrix k r ℝ) (X : n → k → ℝ) (Fhat : n → r → ℝ) : Prop where
  sample_covariance_eq : Shat = factorSampleCovariance X
  eigenvectors_orthonormal : Hᵀ * H = 1
  leading_eigenspace : factorLeadingEigenspace Shat H D
  objective_eq_trace_eigenvalues : factorConcentratedObjective Shat H = Matrix.trace D
  concentrated_objective_maximizer : FactorConcentratedObjectiveMaximizer Shat H
  concentrated_leastSquares_minimizer :
    FactorConcentratedLeastSquaresCriterionMinimizer Shat H
  loading_eq : Λhat = factorLoadingEstimator H sqrtD
  factor_score_eq : ∀ i, Fhat i = factorScoreEstimator H invSqrtD (X i)
  leastSquares_score_eq : ∀ i, Fhat i = factorScoreLeastSquares Λhat (X i)
  score_normalization : factorScoreNormalization Fhat
  loading_normalEquation : factorSampleCrossCovariance X Fhat = Λhat

omit [DecidableEq n] [DecidableEq k] in
/-- Convert the theorem-facing PCA package into Hansen's original normalized
joint least-squares minimizer once the deterministic profiling bridge is
available. -/
theorem factorPCTheorem11_9_jointLeastSquaresMinimizer_of_profileBridge
    {Shat : Matrix k k ℝ} {H : Matrix k r ℝ}
    {D sqrtD invSqrtD : Matrix r r ℝ}
    {Λhat : Matrix k r ℝ} {X : n → k → ℝ} {Fhat : n → r → ℝ}
    (h : FactorPCTheorem11_9 Shat H D sqrtD invSqrtD Λhat X Fhat)
    (hprofile : FactorLeastSquaresProfileBridge Shat H Λhat X Fhat) :
    FactorLeastSquaresNormalizedMinimizer X Λhat Fhat where
  score_normalization := h.score_normalization
  minimizes := by
    intro Λ F hF
    rw [hprofile.criterion_eq_concentrated]
    exact hprofile.concentrated_lower_bound Λ F hF

omit [DecidableEq n] [DecidableEq k] in
/-- Convert a theorem-facing factor-PCA certificate into Hansen's original
normalized joint least-squares minimizer from the exact cross-covariance trace
bound. This is the completed deterministic
square-completion half of the literal Theorem 11.9 surface. -/
theorem FactorLeastSquaresProfileBridge.of_factorPCTheorem11_9_crossCovariance_trace_bound
    {Shat : Matrix k k ℝ} {H : Matrix k r ℝ}
    {D sqrtD invSqrtD : Matrix r r ℝ}
    {Λhat : Matrix k r ℝ} {X : n → k → ℝ} {Fhat : n → r → ℝ}
    (h : FactorPCTheorem11_9 Shat H D sqrtD invSqrtD Λhat X Fhat)
    (hLoadingTrace :
      Matrix.trace (Λhatᵀ * Λhat) = factorConcentratedObjective Shat H)
    (hBound : ∀ F : n → r → ℝ, factorScoreNormalization F →
      Matrix.trace
          ((factorSampleCrossCovariance X F)ᵀ *
            factorSampleCrossCovariance X F) ≤
        factorConcentratedObjective Shat H) :
    FactorLeastSquaresProfileBridge Shat H Λhat X Fhat :=
  FactorLeastSquaresProfileBridge.of_crossCovariance_trace_bound
    Shat H Λhat X Fhat h.sample_covariance_eq h.score_normalization
    h.loading_normalEquation.symm hLoadingTrace hBound

omit [DecidableEq n] [DecidableEq k] in
/-- Hansen Theorem 11.9 as a normalized joint least-squares minimizer, with the
global spectral input stated as the exact cross-covariance trace bound over
normalized score arrays. -/
theorem factorPCTheorem11_9_jointLeastSquaresMinimizer_of_crossCovariance_trace_bound
    {Shat : Matrix k k ℝ} {H : Matrix k r ℝ}
    {D sqrtD invSqrtD : Matrix r r ℝ}
    {Λhat : Matrix k r ℝ} {X : n → k → ℝ} {Fhat : n → r → ℝ}
    (h : FactorPCTheorem11_9 Shat H D sqrtD invSqrtD Λhat X Fhat)
    (hLoadingTrace :
      Matrix.trace (Λhatᵀ * Λhat) = factorConcentratedObjective Shat H)
    (hBound : ∀ F : n → r → ℝ, factorScoreNormalization F →
      Matrix.trace
          ((factorSampleCrossCovariance X F)ᵀ *
            factorSampleCrossCovariance X F) ≤
        factorConcentratedObjective Shat H) :
    FactorLeastSquaresNormalizedMinimizer X Λhat Fhat :=
  factorPCTheorem11_9_jointLeastSquaresMinimizer_of_profileBridge h
    (FactorLeastSquaresProfileBridge.of_factorPCTheorem11_9_crossCovariance_trace_bound
      h hLoadingTrace hBound)

omit [DecidableEq n] [DecidableEq k] in
/-- Assemble Hansen Theorem 11.9 from a concrete leading-eigenspace equation,
PCA scaling identities, and the global Ky Fan concentrated-objective optimizer.

This is the reusable theorem-facing bridge: the only spectral input is the
optimizer certificate, while the score/loading formulas and normal equations are
proved by deterministic least-squares algebra. -/
theorem factorPCTheorem11_9_of_concentratedObjective_optimizer
    (Shat : Matrix k k ℝ) (H : Matrix k r ℝ)
    (D sqrtD invSqrtD : Matrix r r ℝ) (X : n → k → ℝ)
    (hSample : Shat = factorSampleCovariance X)
    (hLead : factorLeadingEigenspace Shat H D)
    (hscale : FactorPCScaling H D sqrtD invSqrtD)
    (hOpt : FactorConcentratedObjectiveMaximizer Shat H) :
    FactorPCTheorem11_9 Shat H D sqrtD invSqrtD
      (factorLoadingEstimator H sqrtD) X
      (fun i => factorScoreEstimator H invSqrtD (X i)) where
  sample_covariance_eq := hSample
  eigenvectors_orthonormal := hscale.eigenvectors_orthonormal
  leading_eigenspace := hLead
  objective_eq_trace_eigenvalues :=
    factorConcentratedObjective_eq_trace_eigenvalues_of_normalized
      Shat H D hLead hscale.eigenvectors_orthonormal
  concentrated_objective_maximizer := hOpt
  concentrated_leastSquares_minimizer :=
    factorConcentratedLeastSquaresCriterionMinimizer_of_objectiveMaximizer
      Shat H hOpt
  loading_eq := rfl
  factor_score_eq := fun _ => rfl
  leastSquares_score_eq := by
    intro i
    exact factorScoreEstimator_eq_leastSquaresScore H D sqrtD invSqrtD (X i) hscale
  score_normalization :=
    factorScoreNormalization_of_eigenspace_scores Shat H D sqrtD invSqrtD X
      hSample hLead hscale
  loading_normalEquation :=
    factorSampleCrossCovariance_eq_loading_of_eigenspace_scores Shat H
      D sqrtD invSqrtD X hSample hLead hscale

omit [DecidableEq n] in
/-- Hansen Theorem 11.9, ordered leading-eigenspace/eigenvalue endpoint.

The selected columns are Mathlib's ordered Hermitian PCA eigenvectors, the
eigenvalue matrix is the diagonal matrix of the first `r` ordered eigenvalues,
and Ky Fan's trace inequality supplies the global least-squares optimizer
property. -/
theorem factorPCTheorem11_9_of_leadingPCEigenvectors
    {Shat : Matrix k k ℝ} (hShat : Shat.IsHermitian)
    (hcard : Fintype.card r ≤ Fintype.card k)
    (sqrtD invSqrtD : Matrix r r ℝ) (X : n → k → ℝ)
    (hSample : Shat = factorSampleCovariance X)
    (hscale : FactorPCScaling
      (factorLeadingPCEigenvectors (r := r) hShat hcard)
      (Matrix.diagonal (factorLeadingPCEigenvalues (r := r) hShat hcard))
      sqrtD invSqrtD) :
    FactorPCTheorem11_9 Shat
      (factorLeadingPCEigenvectors (r := r) hShat hcard)
      (Matrix.diagonal (factorLeadingPCEigenvalues (r := r) hShat hcard))
      sqrtD invSqrtD
      (factorLoadingEstimator
        (factorLeadingPCEigenvectors (r := r) hShat hcard) sqrtD)
      X
      (fun i =>
        factorScoreEstimator
          (factorLeadingPCEigenvectors (r := r) hShat hcard)
          invSqrtD (X i)) :=
  factorPCTheorem11_9_of_concentratedObjective_optimizer Shat
    (factorLeadingPCEigenvectors (r := r) hShat hcard)
    (Matrix.diagonal (factorLeadingPCEigenvalues (r := r) hShat hcard))
    sqrtD invSqrtD X hSample
    (factorLeadingPCEigenvectors_eigenspace (r := r) hShat hcard)
    hscale
    (factorLeadingPCEigenvectors_concentratedObjectiveMaximizer
      (r := r) hShat hcard)

omit [DecidableEq n] in
/-- Hansen Theorem 11.9 specialized to the sample second-moment matrix
`Ŝ = n⁻¹∑ X_iX_i'`.

This is the closed factor-PCA theorem-facing endpoint in this file: Hermitianity
of `Ŝ` is proved by `factorSampleCovariance_isHermitian`, and the leading
eigenspace/global-optimality claim is supplied by the ordered PCA and Ky Fan
support already developed for Chapter 11. -/
theorem factorPCTheorem11_9_of_sampleCovariance_leadingPCEigenvectors
    (hcard : Fintype.card r ≤ Fintype.card k)
    (sqrtD invSqrtD : Matrix r r ℝ) (X : n → k → ℝ)
    (hscale : FactorPCScaling
      (factorLeadingPCEigenvectors (r := r)
        (factorSampleCovariance_isHermitian X) hcard)
      (Matrix.diagonal
        (factorLeadingPCEigenvalues (r := r)
          (factorSampleCovariance_isHermitian X) hcard))
      sqrtD invSqrtD) :
    FactorPCTheorem11_9 (factorSampleCovariance X)
      (factorLeadingPCEigenvectors (r := r)
        (factorSampleCovariance_isHermitian X) hcard)
      (Matrix.diagonal
        (factorLeadingPCEigenvalues (r := r)
          (factorSampleCovariance_isHermitian X) hcard))
      sqrtD invSqrtD
      (factorLoadingEstimator
        (factorLeadingPCEigenvectors (r := r)
          (factorSampleCovariance_isHermitian X) hcard) sqrtD)
      X
      (fun i =>
        factorScoreEstimator
          (factorLeadingPCEigenvectors (r := r)
            (factorSampleCovariance_isHermitian X) hcard)
          invSqrtD (X i)) :=
  factorPCTheorem11_9_of_leadingPCEigenvectors
    (r := r) (hShat := factorSampleCovariance_isHermitian X)
    hcard sqrtD invSqrtD X rfl hscale

omit [DecidableEq n] in
/-- Hansen Theorem 11.9 with canonical diagonal PCA scaling.

When the selected ordered eigenvalues are positive, the loading and score
scales are Hansen's diagonal `D^{1/2}` and `D^{-1/2}`, so callers no longer
need to provide an arbitrary `FactorPCScaling` certificate. -/
theorem factorPCTheorem11_9_of_leadingPCEigenvectors_positive_eigenvalues
    {Shat : Matrix k k ℝ} (hShat : Shat.IsHermitian)
    (hcard : Fintype.card r ≤ Fintype.card k) (X : n → k → ℝ)
    (hSample : Shat = factorSampleCovariance X)
    (hpos : ∀ j, 0 < factorLeadingPCEigenvalues (r := r) hShat hcard j) :
    FactorPCTheorem11_9 Shat
      (factorLeadingPCEigenvectors (r := r) hShat hcard)
      (Matrix.diagonal (factorLeadingPCEigenvalues (r := r) hShat hcard))
      (factorPCDiagonalSqrtD (factorLeadingPCEigenvalues (r := r) hShat hcard))
      (factorPCDiagonalInvSqrtD (factorLeadingPCEigenvalues (r := r) hShat hcard))
      (factorLoadingEstimator
        (factorLeadingPCEigenvectors (r := r) hShat hcard)
        (factorPCDiagonalSqrtD (factorLeadingPCEigenvalues (r := r) hShat hcard)))
      X
      (fun i =>
        factorScoreEstimator
          (factorLeadingPCEigenvectors (r := r) hShat hcard)
          (factorPCDiagonalInvSqrtD
            (factorLeadingPCEigenvalues (r := r) hShat hcard)) (X i)) :=
  factorPCTheorem11_9_of_leadingPCEigenvectors
    (r := r) hShat hcard
    (factorPCDiagonalSqrtD (factorLeadingPCEigenvalues (r := r) hShat hcard))
    (factorPCDiagonalInvSqrtD (factorLeadingPCEigenvalues (r := r) hShat hcard))
    X hSample
    (factorPCScaling_diagonal_of_pos
      (factorLeadingPCEigenvectors (r := r) hShat hcard)
      (factorLeadingPCEigenvalues (r := r) hShat hcard)
      (factorLeadingPCEigenvectors_orthonormal (r := r) hShat hcard)
      hpos)

omit [DecidableEq n] in
/-- Hansen Theorem 11.9 specialized to the sample second-moment matrix with
canonical diagonal PCA scaling under positive selected eigenvalues. -/
theorem factorPCTheorem11_9_of_sampleCovariance_leadingPCEigenvectors_positive_eigenvalues
    (hcard : Fintype.card r ≤ Fintype.card k) (X : n → k → ℝ)
    (hpos : ∀ j,
      0 < factorLeadingPCEigenvalues (r := r)
        (factorSampleCovariance_isHermitian X) hcard j) :
    FactorPCTheorem11_9 (factorSampleCovariance X)
      (factorLeadingPCEigenvectors (r := r)
        (factorSampleCovariance_isHermitian X) hcard)
      (Matrix.diagonal
        (factorLeadingPCEigenvalues (r := r)
          (factorSampleCovariance_isHermitian X) hcard))
      (factorPCDiagonalSqrtD
        (factorLeadingPCEigenvalues (r := r)
          (factorSampleCovariance_isHermitian X) hcard))
      (factorPCDiagonalInvSqrtD
        (factorLeadingPCEigenvalues (r := r)
          (factorSampleCovariance_isHermitian X) hcard))
      (factorLoadingEstimator
        (factorLeadingPCEigenvectors (r := r)
          (factorSampleCovariance_isHermitian X) hcard)
        (factorPCDiagonalSqrtD
          (factorLeadingPCEigenvalues (r := r)
            (factorSampleCovariance_isHermitian X) hcard)))
      X
      (fun i =>
        factorScoreEstimator
          (factorLeadingPCEigenvectors (r := r)
            (factorSampleCovariance_isHermitian X) hcard)
          (factorPCDiagonalInvSqrtD
            (factorLeadingPCEigenvalues (r := r)
              (factorSampleCovariance_isHermitian X) hcard)) (X i)) :=
  factorPCTheorem11_9_of_leadingPCEigenvectors_positive_eigenvalues
    (r := r) (hShat := factorSampleCovariance_isHermitian X)
    hcard X rfl hpos

omit [DecidableEq n] [DecidableEq r] in
/-- For the sample second-moment matrix, selected rank at least `r` gives the
positive leading ordered PCA eigenvalues needed for canonical diagonal scaling. -/
theorem factorLeadingPCEigenvalues_pos_of_sampleCovariance_rank_ge
    (hcard : Fintype.card r ≤ Fintype.card k) (X : n → k → ℝ)
    (hrank : Fintype.card r ≤ (factorSampleCovariance X).rank) :
    ∀ j,
      0 < factorLeadingPCEigenvalues (r := r)
        (factorSampleCovariance_isHermitian X) hcard j :=
  factorLeadingPCEigenvalues_pos_of_posSemidef_rank_ge
    (r := r) (factorSampleCovariance_isHermitian X) hcard
    (factorSampleCovariance_posSemidef X) hrank

omit [Fintype n] [DecidableEq n] [DecidableEq r] in
/-- Positive selected ordered PCA eigenvalues imply the corresponding selected
rank condition.  This is the converse citation bridge to
`factorLeadingPCEigenvalues_pos_of_posSemidef_rank_ge`. -/
theorem factor_rank_ge_of_leadingPCEigenvalues_pos
    {Shat : Matrix k k ℝ} (hShat : Shat.IsHermitian)
    (hcard : Fintype.card r ≤ Fintype.card k)
    (hpos : ∀ j, 0 < factorLeadingPCEigenvalues (r := r) hShat hcard j) :
    Fintype.card r ≤ Shat.rank := by
  classical
  let selectedIndex : r → Fin (Fintype.card k) :=
    fun j => Fin.castLE hcard ((Fintype.equivFin r) j)
  let toNonzero :
      r → {i : Fin (Fintype.card k) // orderedPCEigenvalue hShat i ≠ 0} :=
    fun j => ⟨selectedIndex j, by
      exact ne_of_gt (by
        simpa [factorLeadingPCEigenvalues, selectedIndex] using hpos j)⟩
  have hinj : Function.Injective toNonzero := by
    intro a b hab
    apply (Fintype.equivFin r).injective
    apply Fin.ext
    have hval := congrArg
      (fun x : {i : Fin (Fintype.card k) // orderedPCEigenvalue hShat i ≠ 0} =>
        (x.1 : ℕ)) hab
    simpa [toNonzero, selectedIndex] using hval
  have hcount :
      Fintype.card r ≤
        Fintype.card
          {i : Fin (Fintype.card k) // orderedPCEigenvalue hShat i ≠ 0} :=
    Fintype.card_le_of_injective toNonzero hinj
  simpa [hermitian_rank_eq_card_nonzero_ordered_eigenvalues hShat] using hcount

omit [DecidableEq n] [DecidableEq r] in
/-- Sample-covariance specialization of
`factor_rank_ge_of_leadingPCEigenvalues_pos`. -/
theorem factorSampleCovariance_rank_ge_of_leadingPCEigenvalues_pos
    (hcard : Fintype.card r ≤ Fintype.card k) (X : n → k → ℝ)
    (hpos : ∀ j,
      0 < factorLeadingPCEigenvalues (r := r)
        (factorSampleCovariance_isHermitian X) hcard j) :
    Fintype.card r ≤ (factorSampleCovariance X).rank :=
  factor_rank_ge_of_leadingPCEigenvalues_pos
    (r := r) (factorSampleCovariance_isHermitian X) hcard hpos

omit [DecidableEq n] in
/-- For the sample second-moment matrix, selected rank at least `r` makes the
selected leading diagonal eigenvalue block nonsingular. -/
theorem factorLeadingPCEigenvalues_sampleCovariance_selected_diagonal_isUnit_of_rank_ge
    (hcard : Fintype.card r ≤ Fintype.card k) (X : n → k → ℝ)
    (hrank : Fintype.card r ≤ (factorSampleCovariance X).rank) :
    IsUnit (Matrix.diagonal
      (factorLeadingPCEigenvalues (r := r)
        (factorSampleCovariance_isHermitian X) hcard)).det :=
  factorLeadingPCEigenvalues_selected_diagonal_isUnit_of_posSemidef_rank_ge
    (r := r) (factorSampleCovariance_isHermitian X) hcard
    (factorSampleCovariance_posSemidef X) hrank

omit [DecidableEq n] in
/-- Hansen Theorem 11.9 specialized to the sample second-moment matrix with
canonical diagonal PCA scaling from the sharp selected-rank condition
`rank(Ŝ) ≥ r`. -/
theorem factorPCTheorem11_9_of_sampleCovariance_rank_ge
    (hcard : Fintype.card r ≤ Fintype.card k) (X : n → k → ℝ)
    (hrank : Fintype.card r ≤ (factorSampleCovariance X).rank) :
    FactorPCTheorem11_9 (factorSampleCovariance X)
      (factorLeadingPCEigenvectors (r := r)
        (factorSampleCovariance_isHermitian X) hcard)
      (Matrix.diagonal
        (factorLeadingPCEigenvalues (r := r)
          (factorSampleCovariance_isHermitian X) hcard))
      (factorPCDiagonalSqrtD
        (factorLeadingPCEigenvalues (r := r)
          (factorSampleCovariance_isHermitian X) hcard))
      (factorPCDiagonalInvSqrtD
        (factorLeadingPCEigenvalues (r := r)
          (factorSampleCovariance_isHermitian X) hcard))
      (factorLoadingEstimator
        (factorLeadingPCEigenvectors (r := r)
          (factorSampleCovariance_isHermitian X) hcard)
        (factorPCDiagonalSqrtD
          (factorLeadingPCEigenvalues (r := r)
            (factorSampleCovariance_isHermitian X) hcard)))
      X
      (fun i =>
        factorScoreEstimator
          (factorLeadingPCEigenvectors (r := r)
            (factorSampleCovariance_isHermitian X) hcard)
          (factorPCDiagonalInvSqrtD
            (factorLeadingPCEigenvalues (r := r)
              (factorSampleCovariance_isHermitian X) hcard)) (X i)) :=
  factorPCTheorem11_9_of_sampleCovariance_leadingPCEigenvectors_positive_eigenvalues
    (r := r) hcard X
    (factorLeadingPCEigenvalues_pos_of_sampleCovariance_rank_ge
      (r := r) hcard X hrank)

omit [DecidableEq n] in
omit [DecidableEq n] in
set_option linter.style.longLine false in
/-- Hansen Theorem 11.9 as a normalized joint least-squares minimizer, using
the sharp sample-covariance selected-rank route and an explicit deterministic
profile bridge from the unprofiled LS criterion to the PCA criterion. -/
theorem factorPCTheorem11_9_jointLeastSquaresMinimizer_of_sampleCovariance_rank_ge
    (hcard : Fintype.card r ≤ Fintype.card k) (X : n → k → ℝ)
    (hrank : Fintype.card r ≤ (factorSampleCovariance X).rank)
    (hprofile : FactorLeastSquaresProfileBridge (factorSampleCovariance X)
      (factorLeadingPCEigenvectors (r := r)
        (factorSampleCovariance_isHermitian X) hcard)
      (factorLoadingEstimator
        (factorLeadingPCEigenvectors (r := r)
          (factorSampleCovariance_isHermitian X) hcard)
        (factorPCDiagonalSqrtD
          (factorLeadingPCEigenvalues (r := r)
            (factorSampleCovariance_isHermitian X) hcard)))
      X
      (fun i =>
        factorScoreEstimator
          (factorLeadingPCEigenvectors (r := r)
            (factorSampleCovariance_isHermitian X) hcard)
          (factorPCDiagonalInvSqrtD
            (factorLeadingPCEigenvalues (r := r)
              (factorSampleCovariance_isHermitian X) hcard)) (X i))) :
    FactorLeastSquaresNormalizedMinimizer X
      (factorLoadingEstimator
        (factorLeadingPCEigenvectors (r := r)
          (factorSampleCovariance_isHermitian X) hcard)
        (factorPCDiagonalSqrtD
          (factorLeadingPCEigenvalues (r := r)
            (factorSampleCovariance_isHermitian X) hcard)))
      (fun i =>
        factorScoreEstimator
          (factorLeadingPCEigenvectors (r := r)
            (factorSampleCovariance_isHermitian X) hcard)
          (factorPCDiagonalInvSqrtD
            (factorLeadingPCEigenvalues (r := r)
              (factorSampleCovariance_isHermitian X) hcard)) (X i)) :=
  factorPCTheorem11_9_jointLeastSquaresMinimizer_of_profileBridge
    (factorPCTheorem11_9_of_sampleCovariance_rank_ge
      (r := r) hcard X hrank)
    hprofile

omit [DecidableEq n] in
set_option linter.style.longLine false in
/-- Hansen Theorem 11.9 as a normalized joint least-squares minimizer from the
sharp sample-covariance selected-rank route and the exact cross-covariance
trace inequality over normalized score arrays.

Compared with `factorPCTheorem11_9_jointLeastSquaresMinimizer_of_sampleCovariance_rank_ge`,
this wrapper proves the deterministic profile bridge internally by completing
the square, leaving only the global Eckart-Young/Ky Fan trace bound as an
explicit premise. -/
theorem
    factorPCTheorem11_9_jointLSMinimizer_of_sampleCovariance_rank_ge_crossTraceBound
    (hcard : Fintype.card r ≤ Fintype.card k) (X : n → k → ℝ)
    (hrank : Fintype.card r ≤ (factorSampleCovariance X).rank)
    (hBound : ∀ F : n → r → ℝ, factorScoreNormalization F →
      Matrix.trace
          ((factorSampleCrossCovariance X F)ᵀ *
            factorSampleCrossCovariance X F) ≤
        factorConcentratedObjective (factorSampleCovariance X)
          (factorLeadingPCEigenvectors (r := r)
            (factorSampleCovariance_isHermitian X) hcard)) :
    FactorLeastSquaresNormalizedMinimizer X
      (factorLoadingEstimator
        (factorLeadingPCEigenvectors (r := r)
          (factorSampleCovariance_isHermitian X) hcard)
        (factorPCDiagonalSqrtD
          (factorLeadingPCEigenvalues (r := r)
            (factorSampleCovariance_isHermitian X) hcard)))
      (fun i =>
        factorScoreEstimator
          (factorLeadingPCEigenvectors (r := r)
            (factorSampleCovariance_isHermitian X) hcard)
          (factorPCDiagonalInvSqrtD
            (factorLeadingPCEigenvalues (r := r)
              (factorSampleCovariance_isHermitian X) hcard)) (X i)) := by
  let hpos :=
    factorLeadingPCEigenvalues_pos_of_sampleCovariance_rank_ge
      (r := r) hcard X hrank
  let hPCA :=
    factorPCTheorem11_9_of_sampleCovariance_rank_ge
      (r := r) hcard X hrank
  refine factorPCTheorem11_9_jointLeastSquaresMinimizer_of_crossCovariance_trace_bound
    hPCA ?_ hBound
  exact factorLoadingEstimator_diagonal_trace_gram_eq_concentratedObjective
    (factorSampleCovariance X)
    (factorLeadingPCEigenvectors (r := r)
      (factorSampleCovariance_isHermitian X) hcard)
    (factorLeadingPCEigenvalues (r := r)
      (factorSampleCovariance_isHermitian X) hcard)
    (factorLeadingPCEigenvectors_eigenspace (r := r)
      (factorSampleCovariance_isHermitian X) hcard)
    (factorLeadingPCEigenvectors_orthonormal (r := r)
      (factorSampleCovariance_isHermitian X) hcard)
    hpos

set_option linter.style.longLine false in
/-- Hansen Theorem 11.9 normalized joint least-squares minimizer from the
sample-covariance rank route and the observation-Gram spectral-transfer bound.

This premise-taking compatibility wrapper states the finite-dimensional
spectral transfer as the one-sided inequality needed by the minimization proof;
`factorPCTheorem11_9_crossCovariance_trace_bound` now derives that transfer
internally. -/
theorem
    factorPCTheorem11_9_jointLSMinimizer_of_sampleCovariance_rank_ge_observationGramEigenBound
    [Nonempty n] (hcard : Fintype.card r ≤ Fintype.card k)
    (hcardObs : Fintype.card r ≤ Fintype.card n) (X : n → k → ℝ)
    (hrank : Fintype.card r ≤ (factorSampleCovariance X).rank)
    (hObsToSample :
      (∑ j : r, factorLeadingPCEigenvalues (r := r)
        (factorObservationGram_isHermitian X) hcardObs j) ≤
        factorConcentratedObjective (factorSampleCovariance X)
          (factorLeadingPCEigenvectors (r := r)
            (factorSampleCovariance_isHermitian X) hcard)) :
    FactorLeastSquaresNormalizedMinimizer X
      (factorLoadingEstimator
        (factorLeadingPCEigenvectors (r := r)
          (factorSampleCovariance_isHermitian X) hcard)
        (factorPCDiagonalSqrtD
          (factorLeadingPCEigenvalues (r := r)
            (factorSampleCovariance_isHermitian X) hcard)))
      (fun i =>
        factorScoreEstimator
          (factorLeadingPCEigenvectors (r := r)
            (factorSampleCovariance_isHermitian X) hcard)
          (factorPCDiagonalInvSqrtD
            (factorLeadingPCEigenvalues (r := r)
              (factorSampleCovariance_isHermitian X) hcard)) (X i)) :=
  factorPCTheorem11_9_jointLSMinimizer_of_sampleCovariance_rank_ge_crossTraceBound
    (r := r) hcard X hrank
    (factorPCTheorem11_9_crossCovariance_trace_bound_of_observationGram_eigenvalue_bound
      (r := r) hcard hcardObs X hObsToSample)

omit [DecidableEq n] in
set_option linter.style.longLine false in
/-- Hansen Theorem 11.9 as a normalized joint least-squares minimizer from only
the selected sample-covariance rank condition.

The arbitrary-score cross-covariance trace bound is proved internally from the
observation-Gram Ky Fan bound and the deterministic `n⁻¹XX'`/`n⁻¹X'X`
spectral-transfer theorem, so callers no longer need to supply a separate
profile bridge, cross-trace bound, or observation-Gram eigenvalue inequality. -/
theorem factorPCTheorem11_9_jointLSMinimizer_of_sampleCovariance_rank_ge
    [Nonempty n] (hcard : Fintype.card r ≤ Fintype.card k)
    (hcardObs : Fintype.card r ≤ Fintype.card n) (X : n → k → ℝ)
    (hrank : Fintype.card r ≤ (factorSampleCovariance X).rank) :
    FactorLeastSquaresNormalizedMinimizer X
      (factorLoadingEstimator
        (factorLeadingPCEigenvectors (r := r)
          (factorSampleCovariance_isHermitian X) hcard)
        (factorPCDiagonalSqrtD
          (factorLeadingPCEigenvalues (r := r)
            (factorSampleCovariance_isHermitian X) hcard)))
      (fun i =>
        factorScoreEstimator
          (factorLeadingPCEigenvectors (r := r)
            (factorSampleCovariance_isHermitian X) hcard)
          (factorPCDiagonalInvSqrtD
            (factorLeadingPCEigenvalues (r := r)
              (factorSampleCovariance_isHermitian X) hcard)) (X i)) :=
  factorPCTheorem11_9_jointLSMinimizer_of_sampleCovariance_rank_ge_crossTraceBound
    (r := r) hcard X hrank
    (factorPCTheorem11_9_crossCovariance_trace_bound
      (r := r) hcard hcardObs X)

omit [DecidableEq n] [DecidableEq k] [DecidableEq r] in
/-- The selected sample-covariance rank condition in Hansen Theorem 11.9 already
implies enough observations to support `r` normalized score directions. -/
theorem factor_card_observations_le_of_sampleCovariance_rank_ge
    [Nonempty n] (X : n → k → ℝ)
    (hrank : Fintype.card r ≤ (factorSampleCovariance X).rank) :
    Fintype.card r ≤ Fintype.card n := by
  have hObsRank : Fintype.card r ≤ (factorObservationGram X).rank := by
    simpa [factorObservationGram_rank_eq_sampleCovariance_rank (X := X)] using hrank
  exact le_trans hObsRank (Matrix.rank_le_card_width (factorObservationGram X))

omit [DecidableEq n] in
set_option linter.style.longLine false in
/-- Hansen Theorem 11.9 normalized joint least-squares minimizer from only the
sharp selected sample-covariance rank condition.

This removes the redundant `r ≤ n` caller premise: it follows from
`rank(Ŝ) ≥ r` by transferring rank to the observation Gram matrix. -/
theorem factorPCTheorem11_9_jointLSMinimizer_of_sampleCovariance_rank_ge_only
    [Nonempty n] (hcard : Fintype.card r ≤ Fintype.card k)
    (X : n → k → ℝ)
    (hrank : Fintype.card r ≤ (factorSampleCovariance X).rank) :
    FactorLeastSquaresNormalizedMinimizer X
      (factorLoadingEstimator
        (factorLeadingPCEigenvectors (r := r)
          (factorSampleCovariance_isHermitian X) hcard)
        (factorPCDiagonalSqrtD
          (factorLeadingPCEigenvalues (r := r)
            (factorSampleCovariance_isHermitian X) hcard)))
      (fun i =>
        factorScoreEstimator
          (factorLeadingPCEigenvectors (r := r)
            (factorSampleCovariance_isHermitian X) hcard)
          (factorPCDiagonalInvSqrtD
            (factorLeadingPCEigenvalues (r := r)
              (factorSampleCovariance_isHermitian X) hcard)) (X i)) :=
  factorPCTheorem11_9_jointLSMinimizer_of_sampleCovariance_rank_ge
    (r := r) hcard
    (factor_card_observations_le_of_sampleCovariance_rank_ge (r := r) X hrank)
    X hrank

omit [DecidableEq n] in
set_option linter.style.longLine false in
/-- Citeable Hansen Theorem 11.9 surface from the sharp selected
sample-covariance rank condition: the PCA formula certificate and the literal
normalized joint least-squares minimizer hold together. -/
theorem factorPCTheorem11_9_with_jointLSMinimizer_of_sampleCovariance_rank_ge
    [Nonempty n] (hcard : Fintype.card r ≤ Fintype.card k)
    (X : n → k → ℝ)
    (hrank : Fintype.card r ≤ (factorSampleCovariance X).rank) :
    FactorPCTheorem11_9 (factorSampleCovariance X)
      (factorLeadingPCEigenvectors (r := r)
        (factorSampleCovariance_isHermitian X) hcard)
      (Matrix.diagonal
        (factorLeadingPCEigenvalues (r := r)
          (factorSampleCovariance_isHermitian X) hcard))
      (factorPCDiagonalSqrtD
        (factorLeadingPCEigenvalues (r := r)
          (factorSampleCovariance_isHermitian X) hcard))
      (factorPCDiagonalInvSqrtD
        (factorLeadingPCEigenvalues (r := r)
          (factorSampleCovariance_isHermitian X) hcard))
      (factorLoadingEstimator
        (factorLeadingPCEigenvectors (r := r)
          (factorSampleCovariance_isHermitian X) hcard)
        (factorPCDiagonalSqrtD
          (factorLeadingPCEigenvalues (r := r)
            (factorSampleCovariance_isHermitian X) hcard)))
      X
      (fun i =>
        factorScoreEstimator
          (factorLeadingPCEigenvectors (r := r)
            (factorSampleCovariance_isHermitian X) hcard)
          (factorPCDiagonalInvSqrtD
            (factorLeadingPCEigenvalues (r := r)
              (factorSampleCovariance_isHermitian X) hcard)) (X i)) ∧
    FactorLeastSquaresNormalizedMinimizer X
      (factorLoadingEstimator
        (factorLeadingPCEigenvectors (r := r)
          (factorSampleCovariance_isHermitian X) hcard)
        (factorPCDiagonalSqrtD
          (factorLeadingPCEigenvalues (r := r)
            (factorSampleCovariance_isHermitian X) hcard)))
      (fun i =>
        factorScoreEstimator
          (factorLeadingPCEigenvectors (r := r)
            (factorSampleCovariance_isHermitian X) hcard)
          (factorPCDiagonalInvSqrtD
            (factorLeadingPCEigenvalues (r := r)
              (factorSampleCovariance_isHermitian X) hcard)) (X i)) :=
  ⟨factorPCTheorem11_9_of_sampleCovariance_rank_ge (r := r) hcard X hrank,
    factorPCTheorem11_9_jointLSMinimizer_of_sampleCovariance_rank_ge_only
      (r := r) hcard X hrank⟩

omit [DecidableEq n] in
set_option linter.style.longLine false in
/-- Citeable Hansen Theorem 11.9 surface from the displayed positive selected
PCA eigenvalues: the PCA formula certificate and the literal normalized joint
least-squares minimizer hold together. -/
theorem factorPCTheorem11_9_with_jointLSMinimizer_of_sampleCovariance_positive_eigenvalues
    [Nonempty n] (hcard : Fintype.card r ≤ Fintype.card k)
    (X : n → k → ℝ)
    (hpos : ∀ j,
      0 < factorLeadingPCEigenvalues (r := r)
        (factorSampleCovariance_isHermitian X) hcard j) :
    FactorPCTheorem11_9 (factorSampleCovariance X)
      (factorLeadingPCEigenvectors (r := r)
        (factorSampleCovariance_isHermitian X) hcard)
      (Matrix.diagonal
        (factorLeadingPCEigenvalues (r := r)
          (factorSampleCovariance_isHermitian X) hcard))
      (factorPCDiagonalSqrtD
        (factorLeadingPCEigenvalues (r := r)
          (factorSampleCovariance_isHermitian X) hcard))
      (factorPCDiagonalInvSqrtD
        (factorLeadingPCEigenvalues (r := r)
          (factorSampleCovariance_isHermitian X) hcard))
      (factorLoadingEstimator
        (factorLeadingPCEigenvectors (r := r)
          (factorSampleCovariance_isHermitian X) hcard)
        (factorPCDiagonalSqrtD
          (factorLeadingPCEigenvalues (r := r)
            (factorSampleCovariance_isHermitian X) hcard)))
      X
      (fun i =>
        factorScoreEstimator
          (factorLeadingPCEigenvectors (r := r)
            (factorSampleCovariance_isHermitian X) hcard)
          (factorPCDiagonalInvSqrtD
            (factorLeadingPCEigenvalues (r := r)
              (factorSampleCovariance_isHermitian X) hcard)) (X i)) ∧
    FactorLeastSquaresNormalizedMinimizer X
      (factorLoadingEstimator
        (factorLeadingPCEigenvectors (r := r)
          (factorSampleCovariance_isHermitian X) hcard)
        (factorPCDiagonalSqrtD
          (factorLeadingPCEigenvalues (r := r)
            (factorSampleCovariance_isHermitian X) hcard)))
      (fun i =>
        factorScoreEstimator
          (factorLeadingPCEigenvectors (r := r)
            (factorSampleCovariance_isHermitian X) hcard)
          (factorPCDiagonalInvSqrtD
            (factorLeadingPCEigenvalues (r := r)
              (factorSampleCovariance_isHermitian X) hcard)) (X i)) :=
  factorPCTheorem11_9_with_jointLSMinimizer_of_sampleCovariance_rank_ge
    (r := r) hcard X
    (factorSampleCovariance_rank_ge_of_leadingPCEigenvalues_pos
      (r := r) hcard X hpos)

omit [DecidableEq n] in
/-- Hansen Theorem 11.9 specialized to the sample second-moment matrix with
canonical diagonal PCA scaling from the raw data-matrix selected-rank condition
`rank(X) ≥ r`. For nonempty samples this is equivalent to the selected-rank
condition on `Ŝ = n⁻¹X'X`. -/
theorem factorPCTheorem11_9_of_dataMatrix_rank_ge
    [Nonempty n] (hcard : Fintype.card r ≤ Fintype.card k) (X : n → k → ℝ)
    (hrank : Fintype.card r ≤ (factorDataMatrix X).rank) :
    FactorPCTheorem11_9 (factorSampleCovariance X)
      (factorLeadingPCEigenvectors (r := r)
        (factorSampleCovariance_isHermitian X) hcard)
      (Matrix.diagonal
        (factorLeadingPCEigenvalues (r := r)
          (factorSampleCovariance_isHermitian X) hcard))
      (factorPCDiagonalSqrtD
        (factorLeadingPCEigenvalues (r := r)
          (factorSampleCovariance_isHermitian X) hcard))
      (factorPCDiagonalInvSqrtD
        (factorLeadingPCEigenvalues (r := r)
          (factorSampleCovariance_isHermitian X) hcard))
      (factorLoadingEstimator
        (factorLeadingPCEigenvectors (r := r)
          (factorSampleCovariance_isHermitian X) hcard)
        (factorPCDiagonalSqrtD
          (factorLeadingPCEigenvalues (r := r)
            (factorSampleCovariance_isHermitian X) hcard)))
      X
      (fun i =>
        factorScoreEstimator
          (factorLeadingPCEigenvectors (r := r)
            (factorSampleCovariance_isHermitian X) hcard)
          (factorPCDiagonalInvSqrtD
            (factorLeadingPCEigenvalues (r := r)
              (factorSampleCovariance_isHermitian X) hcard)) (X i)) :=
  factorPCTheorem11_9_of_sampleCovariance_rank_ge
    (r := r) hcard X
    (factorSampleCovariance_rank_ge_of_dataMatrix_rank_ge (r := r) X hrank)

omit [DecidableEq n] in
set_option linter.style.longLine false in
/-- Hansen Theorem 11.9 normalized joint least-squares minimizer from the raw
data-matrix selected-rank condition.

This combines raw rank recovery with the no-extra-premise cross-covariance
trace bound, removing the need to assume a sample-covariance rank certificate
or a separate deterministic profiling bound. -/
theorem factorPCTheorem11_9_jointLSMinimizer_of_dataMatrix_rank_ge
    [Nonempty n] (hcard : Fintype.card r ≤ Fintype.card k)
    (hcardObs : Fintype.card r ≤ Fintype.card n) (X : n → k → ℝ)
    (hrank : Fintype.card r ≤ (factorDataMatrix X).rank) :
    FactorLeastSquaresNormalizedMinimizer X
      (factorLoadingEstimator
        (factorLeadingPCEigenvectors (r := r)
          (factorSampleCovariance_isHermitian X) hcard)
        (factorPCDiagonalSqrtD
          (factorLeadingPCEigenvalues (r := r)
            (factorSampleCovariance_isHermitian X) hcard)))
      (fun i =>
        factorScoreEstimator
          (factorLeadingPCEigenvectors (r := r)
            (factorSampleCovariance_isHermitian X) hcard)
          (factorPCDiagonalInvSqrtD
            (factorLeadingPCEigenvalues (r := r)
              (factorSampleCovariance_isHermitian X) hcard)) (X i)) :=
  factorPCTheorem11_9_jointLSMinimizer_of_sampleCovariance_rank_ge
    (r := r) hcard hcardObs X
    (factorSampleCovariance_rank_ge_of_dataMatrix_rank_ge (r := r) X hrank)

omit [DecidableEq n] in
/-- Hansen Theorem 11.9 under the concrete full-column-rank condition on the
raw data matrix. This is a stronger but directly checkable route to the
selected-rank requirement. -/
theorem factorPCTheorem11_9_of_dataMatrix_columns_linearIndependent
    [Nonempty n] (hcard : Fintype.card r ≤ Fintype.card k) (X : n → k → ℝ)
    (hlin : LinearIndependent ℝ (factorDataMatrix X).col) :
    FactorPCTheorem11_9 (factorSampleCovariance X)
      (factorLeadingPCEigenvectors (r := r)
        (factorSampleCovariance_isHermitian X) hcard)
      (Matrix.diagonal
        (factorLeadingPCEigenvalues (r := r)
          (factorSampleCovariance_isHermitian X) hcard))
      (factorPCDiagonalSqrtD
        (factorLeadingPCEigenvalues (r := r)
          (factorSampleCovariance_isHermitian X) hcard))
      (factorPCDiagonalInvSqrtD
        (factorLeadingPCEigenvalues (r := r)
          (factorSampleCovariance_isHermitian X) hcard))
      (factorLoadingEstimator
        (factorLeadingPCEigenvectors (r := r)
          (factorSampleCovariance_isHermitian X) hcard)
        (factorPCDiagonalSqrtD
          (factorLeadingPCEigenvalues (r := r)
            (factorSampleCovariance_isHermitian X) hcard)))
      X
      (fun i =>
        factorScoreEstimator
          (factorLeadingPCEigenvectors (r := r)
            (factorSampleCovariance_isHermitian X) hcard)
          (factorPCDiagonalInvSqrtD
            (factorLeadingPCEigenvalues (r := r)
              (factorSampleCovariance_isHermitian X) hcard)) (X i)) :=
  factorPCTheorem11_9_of_dataMatrix_rank_ge (r := r) hcard X
    (by simpa [factorDataMatrix_rank_eq_card_k_of_columns_linearIndependent X hlin] using hcard)

omit [DecidableEq n] in
/-- Hansen Theorem 11.9 from raw exact finite-sample factor inputs.

The primitive assumptions are stated in the original factor-model objects:
`X = F Λ'`, a left inverse for the loading matrix, and full selected rank of
the raw sample factor matrix. These imply the data-matrix selected-rank
certificate used by the deterministic PCA endpoint, without assuming any PCA
solution or eigenspace equation. -/
theorem factorPCTheorem11_9_of_exactSampleFactorRankCondition
    [Nonempty n] (hcard : Fintype.card r ≤ Fintype.card k)
    (X : n → k → ℝ) (Λ : Matrix k r ℝ) (F : n → r → ℝ)
    (hraw : ExactSampleFactorRankCondition X Λ F) :
    FactorPCTheorem11_9 (factorSampleCovariance X)
      (factorLeadingPCEigenvectors (r := r)
        (factorSampleCovariance_isHermitian X) hcard)
      (Matrix.diagonal
        (factorLeadingPCEigenvalues (r := r)
          (factorSampleCovariance_isHermitian X) hcard))
      (factorPCDiagonalSqrtD
        (factorLeadingPCEigenvalues (r := r)
          (factorSampleCovariance_isHermitian X) hcard))
      (factorPCDiagonalInvSqrtD
        (factorLeadingPCEigenvalues (r := r)
          (factorSampleCovariance_isHermitian X) hcard))
      (factorLoadingEstimator
        (factorLeadingPCEigenvectors (r := r)
          (factorSampleCovariance_isHermitian X) hcard)
        (factorPCDiagonalSqrtD
          (factorLeadingPCEigenvalues (r := r)
            (factorSampleCovariance_isHermitian X) hcard)))
      X
      (fun i =>
        factorScoreEstimator
          (factorLeadingPCEigenvectors (r := r)
            (factorSampleCovariance_isHermitian X) hcard)
          (factorPCDiagonalInvSqrtD
            (factorLeadingPCEigenvalues (r := r)
              (factorSampleCovariance_isHermitian X) hcard)) (X i)) :=
  factorPCTheorem11_9_of_dataMatrix_rank_ge (r := r) hcard X
    (factorDataMatrix_rank_ge_of_exactSampleFactorRankCondition X Λ F hraw)

omit [DecidableEq n] in
set_option linter.style.longLine false in
/-- Hansen Theorem 11.9 normalized joint least-squares minimizer from raw exact
finite-sample factor inputs.

The assumptions are the Hansen-facing signal/recoverability primitives:
`X = FΛ'`, a left inverse for the loading matrix, and full selected rank of the
sample factor matrix. They imply the selected-rank PCA signal condition, while
the cross-covariance trace bound is discharged by the existing spectral-transfer
and Ky Fan lemmas. -/
theorem factorPCTheorem11_9_jointLSMinimizer_of_exactSampleFactorRankCondition
    [Nonempty n] (hcard : Fintype.card r ≤ Fintype.card k)
    (hcardObs : Fintype.card r ≤ Fintype.card n)
    (X : n → k → ℝ) (Λ : Matrix k r ℝ) (F : n → r → ℝ)
    (hraw : ExactSampleFactorRankCondition X Λ F) :
    FactorLeastSquaresNormalizedMinimizer X
      (factorLoadingEstimator
        (factorLeadingPCEigenvectors (r := r)
          (factorSampleCovariance_isHermitian X) hcard)
        (factorPCDiagonalSqrtD
          (factorLeadingPCEigenvalues (r := r)
            (factorSampleCovariance_isHermitian X) hcard)))
      (fun i =>
        factorScoreEstimator
          (factorLeadingPCEigenvectors (r := r)
            (factorSampleCovariance_isHermitian X) hcard)
          (factorPCDiagonalInvSqrtD
            (factorLeadingPCEigenvalues (r := r)
              (factorSampleCovariance_isHermitian X) hcard)) (X i)) :=
  factorPCTheorem11_9_jointLSMinimizer_of_dataMatrix_rank_ge
    (r := r) hcard hcardObs X
    (factorDataMatrix_rank_ge_of_exactSampleFactorRankCondition X Λ F hraw)

omit [DecidableEq n] in
/-- Hansen Theorem 11.9 from an additive noisy finite-sample factor rank
condition.

This extends the exact-factor rank bridge to `X = FΛ' + U` when the loadings
are pervasive enough to provide a left inverse that also removes the sample
idiosyncratic component. The conclusion is the same canonical leading-PCA
least-squares estimator endpoint as the selected-rank theorem. -/
theorem factorPCTheorem11_9_of_approxSampleFactorRankCondition
    [Nonempty n] (hcard : Fintype.card r ≤ Fintype.card k)
    (X : n → k → ℝ) (Λ : Matrix k r ℝ) (F : n → r → ℝ)
    (U : Matrix n k ℝ)
    (hraw : ApproximateSampleFactorRankCondition X Λ F U) :
    FactorPCTheorem11_9 (factorSampleCovariance X)
      (factorLeadingPCEigenvectors (r := r)
        (factorSampleCovariance_isHermitian X) hcard)
      (Matrix.diagonal
        (factorLeadingPCEigenvalues (r := r)
          (factorSampleCovariance_isHermitian X) hcard))
      (factorPCDiagonalSqrtD
        (factorLeadingPCEigenvalues (r := r)
          (factorSampleCovariance_isHermitian X) hcard))
      (factorPCDiagonalInvSqrtD
        (factorLeadingPCEigenvalues (r := r)
          (factorSampleCovariance_isHermitian X) hcard))
      (factorLoadingEstimator
        (factorLeadingPCEigenvectors (r := r)
          (factorSampleCovariance_isHermitian X) hcard)
        (factorPCDiagonalSqrtD
          (factorLeadingPCEigenvalues (r := r)
            (factorSampleCovariance_isHermitian X) hcard)))
      X
      (fun i =>
        factorScoreEstimator
          (factorLeadingPCEigenvectors (r := r)
            (factorSampleCovariance_isHermitian X) hcard)
          (factorPCDiagonalInvSqrtD
            (factorLeadingPCEigenvalues (r := r)
              (factorSampleCovariance_isHermitian X) hcard)) (X i)) :=
  factorPCTheorem11_9_of_dataMatrix_rank_ge (r := r) hcard X
    (factorDataMatrix_rank_ge_of_approxSampleFactorRankCondition X Λ F U hraw)

omit [DecidableEq n] in
set_option linter.style.longLine false in
/-- Hansen Theorem 11.9 normalized joint least-squares minimizer from additive
finite-sample factor recoverability.

For `X = FΛ' + U`, a loading left inverse that annihilates the sample
idiosyncratic component recovers the factor-score matrix from `X`; full
selected rank of those scores gives the PCA rank signal, and the
cross-covariance trace bound is then supplied internally by the deterministic
spectral-transfer route. -/
theorem factorPCTheorem11_9_jointLSMinimizer_of_approxSampleFactorRankCondition
    [Nonempty n] (hcard : Fintype.card r ≤ Fintype.card k)
    (hcardObs : Fintype.card r ≤ Fintype.card n)
    (X : n → k → ℝ) (Λ : Matrix k r ℝ) (F : n → r → ℝ)
    (U : Matrix n k ℝ)
    (hraw : ApproximateSampleFactorRankCondition X Λ F U) :
    FactorLeastSquaresNormalizedMinimizer X
      (factorLoadingEstimator
        (factorLeadingPCEigenvectors (r := r)
          (factorSampleCovariance_isHermitian X) hcard)
        (factorPCDiagonalSqrtD
          (factorLeadingPCEigenvalues (r := r)
            (factorSampleCovariance_isHermitian X) hcard)))
      (fun i =>
        factorScoreEstimator
          (factorLeadingPCEigenvectors (r := r)
            (factorSampleCovariance_isHermitian X) hcard)
          (factorPCDiagonalInvSqrtD
            (factorLeadingPCEigenvalues (r := r)
              (factorSampleCovariance_isHermitian X) hcard)) (X i)) :=
  factorPCTheorem11_9_jointLSMinimizer_of_dataMatrix_rank_ge
    (r := r) hcard hcardObs X
    (factorDataMatrix_rank_ge_of_approxSampleFactorRankCondition X Λ F U hraw)

omit [DecidableEq n] in
/-- Hansen Theorem 11.9 from finite-sample pervasiveness and idiosyncratic
orthogonality conditions.

The loading Gram nonsingularity supplies the concrete recoverer
`(Λ'Λ)^{-1}Λ'`, and sample orthogonality `UΛ = 0` makes that recoverer remove
the idiosyncratic component. The result then follows through the existing
approximate-factor selected-rank endpoint. -/
theorem factorPCTheorem11_9_of_approxSampleFactorPervasiveCondition
    [Nonempty n] (hcard : Fintype.card r ≤ Fintype.card k)
    (X : n → k → ℝ) (Λ : Matrix k r ℝ) (F : n → r → ℝ)
    (U : Matrix n k ℝ)
    (hraw : ApproximateSampleFactorPervasiveCondition X Λ F U) :
    FactorPCTheorem11_9 (factorSampleCovariance X)
      (factorLeadingPCEigenvectors (r := r)
        (factorSampleCovariance_isHermitian X) hcard)
      (Matrix.diagonal
        (factorLeadingPCEigenvalues (r := r)
          (factorSampleCovariance_isHermitian X) hcard))
      (factorPCDiagonalSqrtD
        (factorLeadingPCEigenvalues (r := r)
          (factorSampleCovariance_isHermitian X) hcard))
      (factorPCDiagonalInvSqrtD
        (factorLeadingPCEigenvalues (r := r)
          (factorSampleCovariance_isHermitian X) hcard))
      (factorLoadingEstimator
        (factorLeadingPCEigenvectors (r := r)
          (factorSampleCovariance_isHermitian X) hcard)
        (factorPCDiagonalSqrtD
          (factorLeadingPCEigenvalues (r := r)
            (factorSampleCovariance_isHermitian X) hcard)))
      X
      (fun i =>
        factorScoreEstimator
          (factorLeadingPCEigenvectors (r := r)
            (factorSampleCovariance_isHermitian X) hcard)
          (factorPCDiagonalInvSqrtD
            (factorLeadingPCEigenvalues (r := r)
              (factorSampleCovariance_isHermitian X) hcard)) (X i)) :=
  factorPCTheorem11_9_of_approxSampleFactorRankCondition
    (r := r) hcard X Λ F U hraw.toApproximateSampleFactorRankCondition

omit [DecidableEq n] in
set_option linter.style.longLine false in
/-- Hansen Theorem 11.9 normalized joint least-squares minimizer from
finite-sample pervasiveness and idiosyncratic orthogonality conditions.

This is the current strongest theorem-facing approximate-factor route: the
new package derives deterministic recoverability/rank, and the existing
spectral-transfer route discharges the arbitrary normalized-score trace bound. -/
theorem
    factorPCTheorem11_9_jointLSMinimizer_of_approxSampleFactorPervasiveCondition
    [Nonempty n] (hcard : Fintype.card r ≤ Fintype.card k)
    (hcardObs : Fintype.card r ≤ Fintype.card n)
    (X : n → k → ℝ) (Λ : Matrix k r ℝ) (F : n → r → ℝ)
    (U : Matrix n k ℝ)
    (hraw : ApproximateSampleFactorPervasiveCondition X Λ F U) :
    FactorLeastSquaresNormalizedMinimizer X
      (factorLoadingEstimator
        (factorLeadingPCEigenvectors (r := r)
          (factorSampleCovariance_isHermitian X) hcard)
        (factorPCDiagonalSqrtD
          (factorLeadingPCEigenvalues (r := r)
            (factorSampleCovariance_isHermitian X) hcard)))
      (fun i =>
        factorScoreEstimator
          (factorLeadingPCEigenvectors (r := r)
            (factorSampleCovariance_isHermitian X) hcard)
          (factorPCDiagonalInvSqrtD
            (factorLeadingPCEigenvalues (r := r)
              (factorSampleCovariance_isHermitian X) hcard)) (X i)) :=
  factorPCTheorem11_9_jointLSMinimizer_of_approxSampleFactorRankCondition
    (r := r) hcard hcardObs X Λ F U
    hraw.toApproximateSampleFactorRankCondition

omit [DecidableEq n] in
/-- Hansen Theorem 11.9 from primitive finite-sample
sample-factor/pervasiveness/idiosyncratic conditions.

The primitive package derives loading-Gram nonsingularity from a quantitative
pervasiveness lower bound, derives `UΛ = 0` from row-wise idiosyncratic
orthogonality, and derives full factor-score rank from Hansen's sample
normalization before applying the existing approximate-factor PCA endpoint. -/
theorem factorPCTheorem11_9_of_approxSampleFactorPrimitiveCondition
    [Nonempty n] (hcard : Fintype.card r ≤ Fintype.card k)
    (X : n → k → ℝ) (Λ : Matrix k r ℝ) (F : n → r → ℝ)
    (U : Matrix n k ℝ)
    (hraw : ApproximateSampleFactorPrimitiveCondition X Λ F U) :
    FactorPCTheorem11_9 (factorSampleCovariance X)
      (factorLeadingPCEigenvectors (r := r)
        (factorSampleCovariance_isHermitian X) hcard)
      (Matrix.diagonal
        (factorLeadingPCEigenvalues (r := r)
          (factorSampleCovariance_isHermitian X) hcard))
      (factorPCDiagonalSqrtD
        (factorLeadingPCEigenvalues (r := r)
          (factorSampleCovariance_isHermitian X) hcard))
      (factorPCDiagonalInvSqrtD
        (factorLeadingPCEigenvalues (r := r)
          (factorSampleCovariance_isHermitian X) hcard))
      (factorLoadingEstimator
        (factorLeadingPCEigenvectors (r := r)
          (factorSampleCovariance_isHermitian X) hcard)
        (factorPCDiagonalSqrtD
          (factorLeadingPCEigenvalues (r := r)
            (factorSampleCovariance_isHermitian X) hcard)))
      X
      (fun i =>
        factorScoreEstimator
          (factorLeadingPCEigenvectors (r := r)
            (factorSampleCovariance_isHermitian X) hcard)
          (factorPCDiagonalInvSqrtD
            (factorLeadingPCEigenvalues (r := r)
              (factorSampleCovariance_isHermitian X) hcard)) (X i)) :=
  factorPCTheorem11_9_of_approxSampleFactorPervasiveCondition
    (r := r) hcard X Λ F U
    (ApproximateSampleFactorPrimitiveCondition.toApproximateSampleFactorPervasiveCondition hraw)

omit [DecidableEq n] in
set_option linter.style.longLine false in
/-- Hansen Theorem 11.9 normalized joint least-squares minimizer from primitive
finite-sample sample-factor/pervasiveness/idiosyncratic conditions.

This is the strongest current theorem-level wrapper for the approximate-factor
route: it starts from sample normalization, quantitative loading
pervasiveness, and row-wise idiosyncratic-loading orthogonality, then reuses the
closed deterministic spectral-transfer proof for the normalized joint
least-squares conclusion. -/
theorem
    factorPCTheorem11_9_jointLSMinimizer_of_approxSampleFactorPrimitiveCondition
    [Nonempty n] (hcard : Fintype.card r ≤ Fintype.card k)
    (hcardObs : Fintype.card r ≤ Fintype.card n)
    (X : n → k → ℝ) (Λ : Matrix k r ℝ) (F : n → r → ℝ)
    (U : Matrix n k ℝ)
    (hraw : ApproximateSampleFactorPrimitiveCondition X Λ F U) :
    FactorLeastSquaresNormalizedMinimizer X
      (factorLoadingEstimator
        (factorLeadingPCEigenvectors (r := r)
          (factorSampleCovariance_isHermitian X) hcard)
        (factorPCDiagonalSqrtD
          (factorLeadingPCEigenvalues (r := r)
            (factorSampleCovariance_isHermitian X) hcard)))
      (fun i =>
        factorScoreEstimator
          (factorLeadingPCEigenvectors (r := r)
            (factorSampleCovariance_isHermitian X) hcard)
          (factorPCDiagonalInvSqrtD
            (factorLeadingPCEigenvalues (r := r)
              (factorSampleCovariance_isHermitian X) hcard)) (X i)) :=
  factorPCTheorem11_9_jointLSMinimizer_of_approxSampleFactorPervasiveCondition
    (r := r) hcard hcardObs X Λ F U
    (ApproximateSampleFactorPrimitiveCondition.toApproximateSampleFactorPervasiveCondition hraw)

omit [DecidableEq n] in
/-- Hansen Theorem 11.9 from primitive finite-sample perturbation conditions.

This route allows nonzero recovered idiosyncratic scores. The condition is that
the realized recovered cross/noise Gram perturbation is strictly dominated by
the normalized factor signal, which preserves the selected rank needed by the
canonical PCA endpoint. -/
theorem factorPCTheorem11_9_of_approxSampleFactorPerturbationCondition
    [Nonempty n] (hcard : Fintype.card r ≤ Fintype.card k)
    (X : n → k → ℝ) (Λ : Matrix k r ℝ) (F : n → r → ℝ)
    (U : Matrix n k ℝ)
    (hraw : ApproximateSampleFactorPerturbationCondition X Λ F U) :
    FactorPCTheorem11_9 (factorSampleCovariance X)
      (factorLeadingPCEigenvectors (r := r)
        (factorSampleCovariance_isHermitian X) hcard)
      (Matrix.diagonal
        (factorLeadingPCEigenvalues (r := r)
          (factorSampleCovariance_isHermitian X) hcard))
      (factorPCDiagonalSqrtD
        (factorLeadingPCEigenvalues (r := r)
          (factorSampleCovariance_isHermitian X) hcard))
      (factorPCDiagonalInvSqrtD
        (factorLeadingPCEigenvalues (r := r)
          (factorSampleCovariance_isHermitian X) hcard))
      (factorLoadingEstimator
        (factorLeadingPCEigenvectors (r := r)
          (factorSampleCovariance_isHermitian X) hcard)
        (factorPCDiagonalSqrtD
          (factorLeadingPCEigenvalues (r := r)
            (factorSampleCovariance_isHermitian X) hcard)))
      X
      (fun i =>
        factorScoreEstimator
          (factorLeadingPCEigenvectors (r := r)
            (factorSampleCovariance_isHermitian X) hcard)
          (factorPCDiagonalInvSqrtD
            (factorLeadingPCEigenvalues (r := r)
              (factorSampleCovariance_isHermitian X) hcard)) (X i)) :=
  factorPCTheorem11_9_of_dataMatrix_rank_ge (r := r) hcard X
    (factorDataMatrix_rank_ge_of_approxSampleFactorPerturbationCondition
      X Λ F U hraw)

omit [DecidableEq n] in
set_option linter.style.longLine false in
/-- Hansen Theorem 11.9 normalized joint least-squares minimizer from primitive
finite-sample perturbation conditions.

The selected-rank signal is derived from loading pervasiveness, factor-score
normalization, and domination of the recovered idiosyncratic cross/noise Gram.
The arbitrary-score trace bound is still discharged by the existing
observation-Gram/sample-covariance spectral-transfer route. -/
theorem
    factorPCTheorem11_9_jointLSMinimizer_of_approxSampleFactorPerturbationCondition
    [Nonempty n] (hcard : Fintype.card r ≤ Fintype.card k)
    (hcardObs : Fintype.card r ≤ Fintype.card n)
    (X : n → k → ℝ) (Λ : Matrix k r ℝ) (F : n → r → ℝ)
    (U : Matrix n k ℝ)
    (hraw : ApproximateSampleFactorPerturbationCondition X Λ F U) :
    FactorLeastSquaresNormalizedMinimizer X
      (factorLoadingEstimator
        (factorLeadingPCEigenvectors (r := r)
          (factorSampleCovariance_isHermitian X) hcard)
        (factorPCDiagonalSqrtD
          (factorLeadingPCEigenvalues (r := r)
            (factorSampleCovariance_isHermitian X) hcard)))
      (fun i =>
        factorScoreEstimator
          (factorLeadingPCEigenvectors (r := r)
            (factorSampleCovariance_isHermitian X) hcard)
          (factorPCDiagonalInvSqrtD
            (factorLeadingPCEigenvalues (r := r)
              (factorSampleCovariance_isHermitian X) hcard)) (X i)) :=
  factorPCTheorem11_9_jointLSMinimizer_of_dataMatrix_rank_ge
    (r := r) hcard hcardObs X
    (factorDataMatrix_rank_ge_of_approxSampleFactorPerturbationCondition
      X Λ F U hraw)

omit [DecidableEq n] in
set_option linter.style.longLine false in
/-- Hansen Theorem 11.9 normalized joint least-squares minimizer from the raw
data-matrix selected-rank condition, with no separate observation-count premise.

The needed `r ≤ n` condition follows from the implied sample-covariance rank
condition and the observation-Gram rank transfer. -/
theorem factorPCTheorem11_9_jointLSMinimizer_of_dataMatrix_rank_ge_only
    [Nonempty n] (hcard : Fintype.card r ≤ Fintype.card k)
    (X : n → k → ℝ)
    (hrank : Fintype.card r ≤ (factorDataMatrix X).rank) :
    FactorLeastSquaresNormalizedMinimizer X
      (factorLoadingEstimator
        (factorLeadingPCEigenvectors (r := r)
          (factorSampleCovariance_isHermitian X) hcard)
        (factorPCDiagonalSqrtD
          (factorLeadingPCEigenvalues (r := r)
            (factorSampleCovariance_isHermitian X) hcard)))
      (fun i =>
        factorScoreEstimator
          (factorLeadingPCEigenvectors (r := r)
            (factorSampleCovariance_isHermitian X) hcard)
          (factorPCDiagonalInvSqrtD
            (factorLeadingPCEigenvalues (r := r)
              (factorSampleCovariance_isHermitian X) hcard)) (X i)) :=
  factorPCTheorem11_9_jointLSMinimizer_of_sampleCovariance_rank_ge_only
    (r := r) hcard X
    (factorSampleCovariance_rank_ge_of_dataMatrix_rank_ge (r := r) X hrank)

omit [DecidableEq n] in
set_option linter.style.longLine false in
/-- Hansen Theorem 11.9 normalized joint least-squares minimizer from raw exact
finite-sample factor inputs, with the observation-count side condition derived
internally from the selected-rank signal. -/
theorem factorPCTheorem11_9_jointLSMinimizer_of_exactSampleFactorRankCondition_only
    [Nonempty n] (hcard : Fintype.card r ≤ Fintype.card k)
    (X : n → k → ℝ) (Λ : Matrix k r ℝ) (F : n → r → ℝ)
    (hraw : ExactSampleFactorRankCondition X Λ F) :
    FactorLeastSquaresNormalizedMinimizer X
      (factorLoadingEstimator
        (factorLeadingPCEigenvectors (r := r)
          (factorSampleCovariance_isHermitian X) hcard)
        (factorPCDiagonalSqrtD
          (factorLeadingPCEigenvalues (r := r)
            (factorSampleCovariance_isHermitian X) hcard)))
      (fun i =>
        factorScoreEstimator
          (factorLeadingPCEigenvectors (r := r)
            (factorSampleCovariance_isHermitian X) hcard)
          (factorPCDiagonalInvSqrtD
            (factorLeadingPCEigenvalues (r := r)
              (factorSampleCovariance_isHermitian X) hcard)) (X i)) :=
  factorPCTheorem11_9_jointLSMinimizer_of_dataMatrix_rank_ge_only
    (r := r) hcard X
    (factorDataMatrix_rank_ge_of_exactSampleFactorRankCondition X Λ F hraw)

omit [DecidableEq n] in
set_option linter.style.longLine false in
/-- Hansen Theorem 11.9 normalized joint least-squares minimizer from additive
finite-sample factor recoverability, with the observation-count side condition
derived internally from the selected-rank signal. -/
theorem factorPCTheorem11_9_jointLSMinimizer_of_approxSampleFactorRankCondition_only
    [Nonempty n] (hcard : Fintype.card r ≤ Fintype.card k)
    (X : n → k → ℝ) (Λ : Matrix k r ℝ) (F : n → r → ℝ)
    (U : Matrix n k ℝ)
    (hraw : ApproximateSampleFactorRankCondition X Λ F U) :
    FactorLeastSquaresNormalizedMinimizer X
      (factorLoadingEstimator
        (factorLeadingPCEigenvectors (r := r)
          (factorSampleCovariance_isHermitian X) hcard)
        (factorPCDiagonalSqrtD
          (factorLeadingPCEigenvalues (r := r)
            (factorSampleCovariance_isHermitian X) hcard)))
      (fun i =>
        factorScoreEstimator
          (factorLeadingPCEigenvectors (r := r)
            (factorSampleCovariance_isHermitian X) hcard)
          (factorPCDiagonalInvSqrtD
            (factorLeadingPCEigenvalues (r := r)
              (factorSampleCovariance_isHermitian X) hcard)) (X i)) :=
  factorPCTheorem11_9_jointLSMinimizer_of_dataMatrix_rank_ge_only
    (r := r) hcard X
    (factorDataMatrix_rank_ge_of_approxSampleFactorRankCondition X Λ F U hraw)

omit [DecidableEq n] in
set_option linter.style.longLine false in
/-- Hansen Theorem 11.9 normalized joint least-squares minimizer from
finite-sample pervasiveness and idiosyncratic orthogonality, with the
observation-count side condition derived internally. -/
theorem
    factorPCTheorem11_9_jointLSMinimizer_of_approxSampleFactorPervasiveCondition_only
    [Nonempty n] (hcard : Fintype.card r ≤ Fintype.card k)
    (X : n → k → ℝ) (Λ : Matrix k r ℝ) (F : n → r → ℝ)
    (U : Matrix n k ℝ)
    (hraw : ApproximateSampleFactorPervasiveCondition X Λ F U) :
    FactorLeastSquaresNormalizedMinimizer X
      (factorLoadingEstimator
        (factorLeadingPCEigenvectors (r := r)
          (factorSampleCovariance_isHermitian X) hcard)
        (factorPCDiagonalSqrtD
          (factorLeadingPCEigenvalues (r := r)
            (factorSampleCovariance_isHermitian X) hcard)))
      (fun i =>
        factorScoreEstimator
          (factorLeadingPCEigenvectors (r := r)
            (factorSampleCovariance_isHermitian X) hcard)
          (factorPCDiagonalInvSqrtD
            (factorLeadingPCEigenvalues (r := r)
              (factorSampleCovariance_isHermitian X) hcard)) (X i)) :=
  factorPCTheorem11_9_jointLSMinimizer_of_approxSampleFactorRankCondition_only
    (r := r) hcard X Λ F U hraw.toApproximateSampleFactorRankCondition

omit [DecidableEq n] in
set_option linter.style.longLine false in
/-- Hansen Theorem 11.9 normalized joint least-squares minimizer from primitive
finite-sample sample-factor/pervasiveness/idiosyncratic conditions, with the
observation-count side condition derived internally. -/
theorem
    factorPCTheorem11_9_jointLSMinimizer_of_approxSampleFactorPrimitiveCondition_only
    [Nonempty n] (hcard : Fintype.card r ≤ Fintype.card k)
    (X : n → k → ℝ) (Λ : Matrix k r ℝ) (F : n → r → ℝ)
    (U : Matrix n k ℝ)
    (hraw : ApproximateSampleFactorPrimitiveCondition X Λ F U) :
    FactorLeastSquaresNormalizedMinimizer X
      (factorLoadingEstimator
        (factorLeadingPCEigenvectors (r := r)
          (factorSampleCovariance_isHermitian X) hcard)
        (factorPCDiagonalSqrtD
          (factorLeadingPCEigenvalues (r := r)
            (factorSampleCovariance_isHermitian X) hcard)))
      (fun i =>
        factorScoreEstimator
          (factorLeadingPCEigenvectors (r := r)
            (factorSampleCovariance_isHermitian X) hcard)
          (factorPCDiagonalInvSqrtD
            (factorLeadingPCEigenvalues (r := r)
              (factorSampleCovariance_isHermitian X) hcard)) (X i)) :=
  factorPCTheorem11_9_jointLSMinimizer_of_approxSampleFactorPervasiveCondition_only
    (r := r) hcard X Λ F U
    (ApproximateSampleFactorPrimitiveCondition.toApproximateSampleFactorPervasiveCondition hraw)

omit [DecidableEq n] in
set_option linter.style.longLine false in
/-- Hansen Theorem 11.9 normalized joint least-squares minimizer from primitive
finite-sample perturbation conditions, with the observation-count side condition
derived internally from the selected-rank signal. -/
theorem
    factorPCTheorem11_9_jointLSMinimizer_of_approxSampleFactorPerturbationCondition_only
    [Nonempty n] (hcard : Fintype.card r ≤ Fintype.card k)
    (X : n → k → ℝ) (Λ : Matrix k r ℝ) (F : n → r → ℝ)
    (U : Matrix n k ℝ)
    (hraw : ApproximateSampleFactorPerturbationCondition X Λ F U) :
    FactorLeastSquaresNormalizedMinimizer X
      (factorLoadingEstimator
        (factorLeadingPCEigenvectors (r := r)
          (factorSampleCovariance_isHermitian X) hcard)
        (factorPCDiagonalSqrtD
          (factorLeadingPCEigenvalues (r := r)
            (factorSampleCovariance_isHermitian X) hcard)))
      (fun i =>
        factorScoreEstimator
          (factorLeadingPCEigenvectors (r := r)
            (factorSampleCovariance_isHermitian X) hcard)
          (factorPCDiagonalInvSqrtD
            (factorLeadingPCEigenvalues (r := r)
              (factorSampleCovariance_isHermitian X) hcard)) (X i)) :=
  factorPCTheorem11_9_jointLSMinimizer_of_dataMatrix_rank_ge_only
    (r := r) hcard X
    (factorDataMatrix_rank_ge_of_approxSampleFactorPerturbationCondition
      X Λ F U hraw)

omit [DecidableEq n] in
set_option linter.style.longLine false in
/-- Citeable Hansen Theorem 11.9 surface from raw data-matrix selected rank:
the PCA formula certificate and the literal normalized joint least-squares
minimizer hold together. -/
theorem factorPCTheorem11_9_with_jointLSMinimizer_of_dataMatrix_rank_ge
    [Nonempty n] (hcard : Fintype.card r ≤ Fintype.card k)
    (X : n → k → ℝ)
    (hrank : Fintype.card r ≤ (factorDataMatrix X).rank) :
    FactorPCTheorem11_9 (factorSampleCovariance X)
      (factorLeadingPCEigenvectors (r := r)
        (factorSampleCovariance_isHermitian X) hcard)
      (Matrix.diagonal
        (factorLeadingPCEigenvalues (r := r)
          (factorSampleCovariance_isHermitian X) hcard))
      (factorPCDiagonalSqrtD
        (factorLeadingPCEigenvalues (r := r)
          (factorSampleCovariance_isHermitian X) hcard))
      (factorPCDiagonalInvSqrtD
        (factorLeadingPCEigenvalues (r := r)
          (factorSampleCovariance_isHermitian X) hcard))
      (factorLoadingEstimator
        (factorLeadingPCEigenvectors (r := r)
          (factorSampleCovariance_isHermitian X) hcard)
        (factorPCDiagonalSqrtD
          (factorLeadingPCEigenvalues (r := r)
            (factorSampleCovariance_isHermitian X) hcard)))
      X
      (fun i =>
        factorScoreEstimator
          (factorLeadingPCEigenvectors (r := r)
            (factorSampleCovariance_isHermitian X) hcard)
          (factorPCDiagonalInvSqrtD
            (factorLeadingPCEigenvalues (r := r)
              (factorSampleCovariance_isHermitian X) hcard)) (X i)) ∧
    FactorLeastSquaresNormalizedMinimizer X
      (factorLoadingEstimator
        (factorLeadingPCEigenvectors (r := r)
          (factorSampleCovariance_isHermitian X) hcard)
        (factorPCDiagonalSqrtD
          (factorLeadingPCEigenvalues (r := r)
            (factorSampleCovariance_isHermitian X) hcard)))
      (fun i =>
        factorScoreEstimator
          (factorLeadingPCEigenvectors (r := r)
            (factorSampleCovariance_isHermitian X) hcard)
          (factorPCDiagonalInvSqrtD
            (factorLeadingPCEigenvalues (r := r)
              (factorSampleCovariance_isHermitian X) hcard)) (X i)) :=
  ⟨factorPCTheorem11_9_of_dataMatrix_rank_ge (r := r) hcard X hrank,
    factorPCTheorem11_9_jointLSMinimizer_of_dataMatrix_rank_ge_only
      (r := r) hcard X hrank⟩

omit [DecidableEq n] in
set_option linter.style.longLine false in
/-- Citeable Hansen Theorem 11.9 surface from raw exact finite-sample factor
inputs: the PCA formula certificate and normalized joint least-squares minimizer
hold together. -/
theorem factorPCTheorem11_9_with_jointLSMinimizer_of_exactSampleFactorRankCondition
    [Nonempty n] (hcard : Fintype.card r ≤ Fintype.card k)
    (X : n → k → ℝ) (Λ : Matrix k r ℝ) (F : n → r → ℝ)
    (hraw : ExactSampleFactorRankCondition X Λ F) :
    FactorPCTheorem11_9 (factorSampleCovariance X)
      (factorLeadingPCEigenvectors (r := r)
        (factorSampleCovariance_isHermitian X) hcard)
      (Matrix.diagonal
        (factorLeadingPCEigenvalues (r := r)
          (factorSampleCovariance_isHermitian X) hcard))
      (factorPCDiagonalSqrtD
        (factorLeadingPCEigenvalues (r := r)
          (factorSampleCovariance_isHermitian X) hcard))
      (factorPCDiagonalInvSqrtD
        (factorLeadingPCEigenvalues (r := r)
          (factorSampleCovariance_isHermitian X) hcard))
      (factorLoadingEstimator
        (factorLeadingPCEigenvectors (r := r)
          (factorSampleCovariance_isHermitian X) hcard)
        (factorPCDiagonalSqrtD
          (factorLeadingPCEigenvalues (r := r)
            (factorSampleCovariance_isHermitian X) hcard)))
      X
      (fun i =>
        factorScoreEstimator
          (factorLeadingPCEigenvectors (r := r)
            (factorSampleCovariance_isHermitian X) hcard)
          (factorPCDiagonalInvSqrtD
            (factorLeadingPCEigenvalues (r := r)
              (factorSampleCovariance_isHermitian X) hcard)) (X i)) ∧
    FactorLeastSquaresNormalizedMinimizer X
      (factorLoadingEstimator
        (factorLeadingPCEigenvectors (r := r)
          (factorSampleCovariance_isHermitian X) hcard)
        (factorPCDiagonalSqrtD
          (factorLeadingPCEigenvalues (r := r)
            (factorSampleCovariance_isHermitian X) hcard)))
      (fun i =>
        factorScoreEstimator
          (factorLeadingPCEigenvectors (r := r)
            (factorSampleCovariance_isHermitian X) hcard)
          (factorPCDiagonalInvSqrtD
            (factorLeadingPCEigenvalues (r := r)
              (factorSampleCovariance_isHermitian X) hcard)) (X i)) :=
  ⟨factorPCTheorem11_9_of_exactSampleFactorRankCondition
      (r := r) hcard X Λ F hraw,
    factorPCTheorem11_9_jointLSMinimizer_of_exactSampleFactorRankCondition_only
      (r := r) hcard X Λ F hraw⟩

omit [DecidableEq n] in
set_option linter.style.longLine false in
/-- Citeable Hansen Theorem 11.9 surface from additive finite-sample factor
recoverability: the PCA formula certificate and normalized joint least-squares
minimizer hold together. -/
theorem factorPCTheorem11_9_with_jointLSMinimizer_of_approxSampleFactorRankCondition
    [Nonempty n] (hcard : Fintype.card r ≤ Fintype.card k)
    (X : n → k → ℝ) (Λ : Matrix k r ℝ) (F : n → r → ℝ)
    (U : Matrix n k ℝ)
    (hraw : ApproximateSampleFactorRankCondition X Λ F U) :
    FactorPCTheorem11_9 (factorSampleCovariance X)
      (factorLeadingPCEigenvectors (r := r)
        (factorSampleCovariance_isHermitian X) hcard)
      (Matrix.diagonal
        (factorLeadingPCEigenvalues (r := r)
          (factorSampleCovariance_isHermitian X) hcard))
      (factorPCDiagonalSqrtD
        (factorLeadingPCEigenvalues (r := r)
          (factorSampleCovariance_isHermitian X) hcard))
      (factorPCDiagonalInvSqrtD
        (factorLeadingPCEigenvalues (r := r)
          (factorSampleCovariance_isHermitian X) hcard))
      (factorLoadingEstimator
        (factorLeadingPCEigenvectors (r := r)
          (factorSampleCovariance_isHermitian X) hcard)
        (factorPCDiagonalSqrtD
          (factorLeadingPCEigenvalues (r := r)
            (factorSampleCovariance_isHermitian X) hcard)))
      X
      (fun i =>
        factorScoreEstimator
          (factorLeadingPCEigenvectors (r := r)
            (factorSampleCovariance_isHermitian X) hcard)
          (factorPCDiagonalInvSqrtD
            (factorLeadingPCEigenvalues (r := r)
              (factorSampleCovariance_isHermitian X) hcard)) (X i)) ∧
    FactorLeastSquaresNormalizedMinimizer X
      (factorLoadingEstimator
        (factorLeadingPCEigenvectors (r := r)
          (factorSampleCovariance_isHermitian X) hcard)
        (factorPCDiagonalSqrtD
          (factorLeadingPCEigenvalues (r := r)
            (factorSampleCovariance_isHermitian X) hcard)))
      (fun i =>
        factorScoreEstimator
          (factorLeadingPCEigenvectors (r := r)
            (factorSampleCovariance_isHermitian X) hcard)
          (factorPCDiagonalInvSqrtD
            (factorLeadingPCEigenvalues (r := r)
              (factorSampleCovariance_isHermitian X) hcard)) (X i)) :=
  ⟨factorPCTheorem11_9_of_approxSampleFactorRankCondition
      (r := r) hcard X Λ F U hraw,
    factorPCTheorem11_9_jointLSMinimizer_of_approxSampleFactorRankCondition_only
      (r := r) hcard X Λ F U hraw⟩

omit [DecidableEq n] in
set_option linter.style.longLine false in
/-- Citeable Hansen Theorem 11.9 surface from finite-sample pervasiveness and
idiosyncratic orthogonality: the PCA formula certificate and normalized joint
least-squares minimizer hold together. -/
theorem
    factorPCTheorem11_9_with_jointLSMinimizer_of_approxSampleFactorPervasiveCondition
    [Nonempty n] (hcard : Fintype.card r ≤ Fintype.card k)
    (X : n → k → ℝ) (Λ : Matrix k r ℝ) (F : n → r → ℝ)
    (U : Matrix n k ℝ)
    (hraw : ApproximateSampleFactorPervasiveCondition X Λ F U) :
    FactorPCTheorem11_9 (factorSampleCovariance X)
      (factorLeadingPCEigenvectors (r := r)
        (factorSampleCovariance_isHermitian X) hcard)
      (Matrix.diagonal
        (factorLeadingPCEigenvalues (r := r)
          (factorSampleCovariance_isHermitian X) hcard))
      (factorPCDiagonalSqrtD
        (factorLeadingPCEigenvalues (r := r)
          (factorSampleCovariance_isHermitian X) hcard))
      (factorPCDiagonalInvSqrtD
        (factorLeadingPCEigenvalues (r := r)
          (factorSampleCovariance_isHermitian X) hcard))
      (factorLoadingEstimator
        (factorLeadingPCEigenvectors (r := r)
          (factorSampleCovariance_isHermitian X) hcard)
        (factorPCDiagonalSqrtD
          (factorLeadingPCEigenvalues (r := r)
            (factorSampleCovariance_isHermitian X) hcard)))
      X
      (fun i =>
        factorScoreEstimator
          (factorLeadingPCEigenvectors (r := r)
            (factorSampleCovariance_isHermitian X) hcard)
          (factorPCDiagonalInvSqrtD
            (factorLeadingPCEigenvalues (r := r)
              (factorSampleCovariance_isHermitian X) hcard)) (X i)) ∧
    FactorLeastSquaresNormalizedMinimizer X
      (factorLoadingEstimator
        (factorLeadingPCEigenvectors (r := r)
          (factorSampleCovariance_isHermitian X) hcard)
        (factorPCDiagonalSqrtD
          (factorLeadingPCEigenvalues (r := r)
            (factorSampleCovariance_isHermitian X) hcard)))
      (fun i =>
        factorScoreEstimator
          (factorLeadingPCEigenvectors (r := r)
            (factorSampleCovariance_isHermitian X) hcard)
          (factorPCDiagonalInvSqrtD
            (factorLeadingPCEigenvalues (r := r)
              (factorSampleCovariance_isHermitian X) hcard)) (X i)) :=
  ⟨factorPCTheorem11_9_of_approxSampleFactorPervasiveCondition
      (r := r) hcard X Λ F U hraw,
    factorPCTheorem11_9_jointLSMinimizer_of_approxSampleFactorPervasiveCondition_only
      (r := r) hcard X Λ F U hraw⟩

omit [DecidableEq n] in
set_option linter.style.longLine false in
/-- Citeable Hansen Theorem 11.9 surface from primitive finite-sample
sample-factor/pervasiveness/idiosyncratic conditions: the PCA formula
certificate and normalized joint least-squares minimizer hold together. -/
theorem
    factorPCTheorem11_9_with_jointLSMinimizer_of_approxSampleFactorPrimitiveCondition
    [Nonempty n] (hcard : Fintype.card r ≤ Fintype.card k)
    (X : n → k → ℝ) (Λ : Matrix k r ℝ) (F : n → r → ℝ)
    (U : Matrix n k ℝ)
    (hraw : ApproximateSampleFactorPrimitiveCondition X Λ F U) :
    FactorPCTheorem11_9 (factorSampleCovariance X)
      (factorLeadingPCEigenvectors (r := r)
        (factorSampleCovariance_isHermitian X) hcard)
      (Matrix.diagonal
        (factorLeadingPCEigenvalues (r := r)
          (factorSampleCovariance_isHermitian X) hcard))
      (factorPCDiagonalSqrtD
        (factorLeadingPCEigenvalues (r := r)
          (factorSampleCovariance_isHermitian X) hcard))
      (factorPCDiagonalInvSqrtD
        (factorLeadingPCEigenvalues (r := r)
          (factorSampleCovariance_isHermitian X) hcard))
      (factorLoadingEstimator
        (factorLeadingPCEigenvectors (r := r)
          (factorSampleCovariance_isHermitian X) hcard)
        (factorPCDiagonalSqrtD
          (factorLeadingPCEigenvalues (r := r)
            (factorSampleCovariance_isHermitian X) hcard)))
      X
      (fun i =>
        factorScoreEstimator
          (factorLeadingPCEigenvectors (r := r)
            (factorSampleCovariance_isHermitian X) hcard)
          (factorPCDiagonalInvSqrtD
            (factorLeadingPCEigenvalues (r := r)
              (factorSampleCovariance_isHermitian X) hcard)) (X i)) ∧
    FactorLeastSquaresNormalizedMinimizer X
      (factorLoadingEstimator
        (factorLeadingPCEigenvectors (r := r)
          (factorSampleCovariance_isHermitian X) hcard)
        (factorPCDiagonalSqrtD
          (factorLeadingPCEigenvalues (r := r)
            (factorSampleCovariance_isHermitian X) hcard)))
      (fun i =>
        factorScoreEstimator
          (factorLeadingPCEigenvectors (r := r)
            (factorSampleCovariance_isHermitian X) hcard)
          (factorPCDiagonalInvSqrtD
            (factorLeadingPCEigenvalues (r := r)
              (factorSampleCovariance_isHermitian X) hcard)) (X i)) :=
  ⟨factorPCTheorem11_9_of_approxSampleFactorPrimitiveCondition
      (r := r) hcard X Λ F U hraw,
    factorPCTheorem11_9_jointLSMinimizer_of_approxSampleFactorPrimitiveCondition_only
      (r := r) hcard X Λ F U hraw⟩

omit [DecidableEq n] in
set_option linter.style.longLine false in
/-- Citeable Hansen Theorem 11.9 surface from primitive finite-sample
perturbation conditions: the PCA formula certificate and normalized joint
least-squares minimizer hold together. -/
theorem
    factorPCTheorem11_9_with_jointLSMinimizer_of_approxSampleFactorPerturbationCondition
    [Nonempty n] (hcard : Fintype.card r ≤ Fintype.card k)
    (X : n → k → ℝ) (Λ : Matrix k r ℝ) (F : n → r → ℝ)
    (U : Matrix n k ℝ)
    (hraw : ApproximateSampleFactorPerturbationCondition X Λ F U) :
    FactorPCTheorem11_9 (factorSampleCovariance X)
      (factorLeadingPCEigenvectors (r := r)
        (factorSampleCovariance_isHermitian X) hcard)
      (Matrix.diagonal
        (factorLeadingPCEigenvalues (r := r)
          (factorSampleCovariance_isHermitian X) hcard))
      (factorPCDiagonalSqrtD
        (factorLeadingPCEigenvalues (r := r)
          (factorSampleCovariance_isHermitian X) hcard))
      (factorPCDiagonalInvSqrtD
        (factorLeadingPCEigenvalues (r := r)
          (factorSampleCovariance_isHermitian X) hcard))
      (factorLoadingEstimator
        (factorLeadingPCEigenvectors (r := r)
          (factorSampleCovariance_isHermitian X) hcard)
        (factorPCDiagonalSqrtD
          (factorLeadingPCEigenvalues (r := r)
            (factorSampleCovariance_isHermitian X) hcard)))
      X
      (fun i =>
        factorScoreEstimator
          (factorLeadingPCEigenvectors (r := r)
            (factorSampleCovariance_isHermitian X) hcard)
          (factorPCDiagonalInvSqrtD
            (factorLeadingPCEigenvalues (r := r)
              (factorSampleCovariance_isHermitian X) hcard)) (X i)) ∧
    FactorLeastSquaresNormalizedMinimizer X
      (factorLoadingEstimator
        (factorLeadingPCEigenvectors (r := r)
          (factorSampleCovariance_isHermitian X) hcard)
        (factorPCDiagonalSqrtD
          (factorLeadingPCEigenvalues (r := r)
            (factorSampleCovariance_isHermitian X) hcard)))
      (fun i =>
        factorScoreEstimator
          (factorLeadingPCEigenvectors (r := r)
            (factorSampleCovariance_isHermitian X) hcard)
          (factorPCDiagonalInvSqrtD
            (factorLeadingPCEigenvalues (r := r)
              (factorSampleCovariance_isHermitian X) hcard)) (X i)) :=
  ⟨factorPCTheorem11_9_of_approxSampleFactorPerturbationCondition
      (r := r) hcard X Λ F U hraw,
    factorPCTheorem11_9_jointLSMinimizer_of_approxSampleFactorPerturbationCondition_only
      (r := r) hcard X Λ F U hraw⟩

omit [DecidableEq n] in
set_option linter.style.longLine false in
/-- Hansen Theorem 11.9 eventually follows from the concrete asymptotic
perturbation bridge.

This narrows the remaining stochastic gap to one matrix-convergence statement:
the recovered idiosyncratic cross/noise Gram has uniform Rayleigh quotient
`o(1)` relative to Hansen's normalized factor signal. Once that holds
eventually, the proof reuses the finite-sample perturbation route and the
closed deterministic PCA/spectral-transfer theorem. -/
theorem factorPCTheorem11_9_eventually_of_approxFactorAsymptoticPerturbationBridge
    [Nonempty n] {ι : Type*} {l : Filter ι}
    (hcard : Fintype.card r ≤ Fintype.card k)
    (X : ι → n → k → ℝ) (Λ : ι → Matrix k r ℝ)
    (F : ι → n → r → ℝ) (U : ι → Matrix n k ℝ)
    (h : ApproximateFactorAsymptoticPerturbationBridge l X Λ F U) :
    Filter.Eventually
      (fun i =>
        FactorPCTheorem11_9 (factorSampleCovariance (X i))
          (factorLeadingPCEigenvectors (r := r)
            (factorSampleCovariance_isHermitian (X i)) hcard)
          (Matrix.diagonal
            (factorLeadingPCEigenvalues (r := r)
              (factorSampleCovariance_isHermitian (X i)) hcard))
          (factorPCDiagonalSqrtD
            (factorLeadingPCEigenvalues (r := r)
              (factorSampleCovariance_isHermitian (X i)) hcard))
          (factorPCDiagonalInvSqrtD
            (factorLeadingPCEigenvalues (r := r)
              (factorSampleCovariance_isHermitian (X i)) hcard))
          (factorLoadingEstimator
            (factorLeadingPCEigenvectors (r := r)
              (factorSampleCovariance_isHermitian (X i)) hcard)
            (factorPCDiagonalSqrtD
              (factorLeadingPCEigenvalues (r := r)
                (factorSampleCovariance_isHermitian (X i)) hcard)))
          (X i)
          (fun row =>
            factorScoreEstimator
              (factorLeadingPCEigenvectors (r := r)
                (factorSampleCovariance_isHermitian (X i)) hcard)
              (factorPCDiagonalInvSqrtD
                (factorLeadingPCEigenvalues (r := r)
                  (factorSampleCovariance_isHermitian (X i)) hcard)) (X i row))) l := by
  exact
    (ApproximateFactorAsymptoticPerturbationBridge.eventually_perturbationCondition
      h).mono
      (fun i hi =>
        factorPCTheorem11_9_of_approxSampleFactorPerturbationCondition
          (r := r) hcard (X i) (Λ i) (F i) (U i) hi)

omit [DecidableEq n] in
set_option linter.style.longLine false in
/-- Hansen Theorem 11.9 normalized joint least-squares minimizer eventually
follows from the concrete asymptotic perturbation bridge. -/
theorem
    factorPCTheorem11_9_jointLSMinimizer_eventually_of_approxFactorAsymptoticPerturbationBridge
    [Nonempty n] {ι : Type*} {l : Filter ι}
    (hcard : Fintype.card r ≤ Fintype.card k)
    (hcardObs : Fintype.card r ≤ Fintype.card n)
    (X : ι → n → k → ℝ) (Λ : ι → Matrix k r ℝ)
    (F : ι → n → r → ℝ) (U : ι → Matrix n k ℝ)
    (h : ApproximateFactorAsymptoticPerturbationBridge l X Λ F U) :
    Filter.Eventually
      (fun i =>
        FactorLeastSquaresNormalizedMinimizer (X i)
          (factorLoadingEstimator
            (factorLeadingPCEigenvectors (r := r)
              (factorSampleCovariance_isHermitian (X i)) hcard)
            (factorPCDiagonalSqrtD
              (factorLeadingPCEigenvalues (r := r)
                (factorSampleCovariance_isHermitian (X i)) hcard)))
          (fun row =>
            factorScoreEstimator
              (factorLeadingPCEigenvectors (r := r)
                (factorSampleCovariance_isHermitian (X i)) hcard)
              (factorPCDiagonalInvSqrtD
                (factorLeadingPCEigenvalues (r := r)
                  (factorSampleCovariance_isHermitian (X i)) hcard)) (X i row))) l := by
  exact
    (ApproximateFactorAsymptoticPerturbationBridge.eventually_perturbationCondition
      h).mono
      (fun i hi =>
        factorPCTheorem11_9_jointLSMinimizer_of_approxSampleFactorPerturbationCondition
          (r := r) hcard hcardObs (X i) (Λ i) (F i) (U i) hi)

set_option linter.style.longLine false in
omit [DecidableEq n] in
/-- Hansen Theorem 11.9 normalized joint least-squares minimizer eventually
follows from the concrete asymptotic perturbation bridge, with no separate
observation-count premise.

For each sufficiently large index the perturbation bridge gives the selected
rank condition, which already implies the `r ≤ n` score-normalization dimension
side condition. -/
theorem
    factorPCTheorem11_9_jointLSMinimizer_eventually_of_approxFactorAsymptoticPerturbationBridge_only
    [Nonempty n] {ι : Type*} {l : Filter ι}
    (hcard : Fintype.card r ≤ Fintype.card k)
    (X : ι → n → k → ℝ) (Λ : ι → Matrix k r ℝ)
    (F : ι → n → r → ℝ) (U : ι → Matrix n k ℝ)
    (h : ApproximateFactorAsymptoticPerturbationBridge l X Λ F U) :
    Filter.Eventually
      (fun i =>
        FactorLeastSquaresNormalizedMinimizer (X i)
          (factorLoadingEstimator
            (factorLeadingPCEigenvectors (r := r)
              (factorSampleCovariance_isHermitian (X i)) hcard)
            (factorPCDiagonalSqrtD
              (factorLeadingPCEigenvalues (r := r)
                (factorSampleCovariance_isHermitian (X i)) hcard)))
          (fun row =>
            factorScoreEstimator
              (factorLeadingPCEigenvectors (r := r)
                (factorSampleCovariance_isHermitian (X i)) hcard)
              (factorPCDiagonalInvSqrtD
                (factorLeadingPCEigenvalues (r := r)
                  (factorSampleCovariance_isHermitian (X i)) hcard)) (X i row))) l := by
  exact
    (ApproximateFactorAsymptoticPerturbationBridge.eventually_perturbationCondition
      h).mono
      (fun i hi =>
        factorPCTheorem11_9_jointLSMinimizer_of_approxSampleFactorPerturbationCondition_only
          (r := r) hcard (X i) (Λ i) (F i) (U i) hi)

set_option linter.style.longLine false in
omit [DecidableEq n] in
/-- Hansen Theorem 11.9 eventually follows from the normalized recovered-Gram
Rayleigh bridge. This is the preferred theorem-facing stochastic boundary for
the approximate-factor asymptotic statement. -/
theorem factorPCTheorem11_9_eventually_of_approxFactorAsymptoticNormalizedRayleighBridge
    [Nonempty n] {ι : Type*} {l : Filter ι}
    (hcard : Fintype.card r ≤ Fintype.card k)
    (X : ι → n → k → ℝ) (Λ : ι → Matrix k r ℝ)
    (F : ι → n → r → ℝ) (U : ι → Matrix n k ℝ)
    (h : ApproximateFactorAsymptoticNormalizedRayleighBridge l X Λ F U) :
    Filter.Eventually
      (fun i =>
        FactorPCTheorem11_9 (factorSampleCovariance (X i))
          (factorLeadingPCEigenvectors (r := r)
            (factorSampleCovariance_isHermitian (X i)) hcard)
          (Matrix.diagonal
            (factorLeadingPCEigenvalues (r := r)
              (factorSampleCovariance_isHermitian (X i)) hcard))
          (factorPCDiagonalSqrtD
            (factorLeadingPCEigenvalues (r := r)
              (factorSampleCovariance_isHermitian (X i)) hcard))
          (factorPCDiagonalInvSqrtD
            (factorLeadingPCEigenvalues (r := r)
              (factorSampleCovariance_isHermitian (X i)) hcard))
          (factorLoadingEstimator
            (factorLeadingPCEigenvectors (r := r)
              (factorSampleCovariance_isHermitian (X i)) hcard)
            (factorPCDiagonalSqrtD
              (factorLeadingPCEigenvalues (r := r)
                (factorSampleCovariance_isHermitian (X i)) hcard)))
          (X i)
          (fun row =>
            factorScoreEstimator
              (factorLeadingPCEigenvectors (r := r)
                (factorSampleCovariance_isHermitian (X i)) hcard)
              (factorPCDiagonalInvSqrtD
                (factorLeadingPCEigenvalues (r := r)
                  (factorSampleCovariance_isHermitian (X i)) hcard)) (X i row))) l :=
  factorPCTheorem11_9_eventually_of_approxFactorAsymptoticPerturbationBridge
    hcard X Λ F U
    (ApproximateFactorAsymptoticNormalizedRayleighBridge.toPerturbationBridge h)

set_option linter.style.longLine false in
omit [DecidableEq n] in
/-- Hansen Theorem 11.9 normalized joint least-squares minimizer eventually
follows from the normalized recovered-Gram Rayleigh bridge. -/
theorem
    factorPCTheorem11_9_jointLS_eventually_of_approxFactorNormalizedRayleighBridge
    [Nonempty n] {ι : Type*} {l : Filter ι}
    (hcard : Fintype.card r ≤ Fintype.card k)
    (hcardObs : Fintype.card r ≤ Fintype.card n)
    (X : ι → n → k → ℝ) (Λ : ι → Matrix k r ℝ)
    (F : ι → n → r → ℝ) (U : ι → Matrix n k ℝ)
    (h : ApproximateFactorAsymptoticNormalizedRayleighBridge l X Λ F U) :
    Filter.Eventually
      (fun i =>
        FactorLeastSquaresNormalizedMinimizer (X i)
          (factorLoadingEstimator
            (factorLeadingPCEigenvectors (r := r)
              (factorSampleCovariance_isHermitian (X i)) hcard)
            (factorPCDiagonalSqrtD
              (factorLeadingPCEigenvalues (r := r)
                (factorSampleCovariance_isHermitian (X i)) hcard)))
          (fun row =>
            factorScoreEstimator
              (factorLeadingPCEigenvectors (r := r)
                (factorSampleCovariance_isHermitian (X i)) hcard)
              (factorPCDiagonalInvSqrtD
                (factorLeadingPCEigenvalues (r := r)
                  (factorSampleCovariance_isHermitian (X i)) hcard)) (X i row))) l :=
  factorPCTheorem11_9_jointLSMinimizer_eventually_of_approxFactorAsymptoticPerturbationBridge
    hcard hcardObs X Λ F U
    (ApproximateFactorAsymptoticNormalizedRayleighBridge.toPerturbationBridge h)

set_option linter.style.longLine false in
omit [DecidableEq n] in
/-- Hansen Theorem 11.9 normalized joint least-squares minimizer eventually
follows from the normalized recovered-Gram Rayleigh bridge, with the
observation-count side condition derived internally. -/
theorem
    factorPCTheorem11_9_jointLS_eventually_of_approxFactorNormalizedRayleighBridge_only
    [Nonempty n] {ι : Type*} {l : Filter ι}
    (hcard : Fintype.card r ≤ Fintype.card k)
    (X : ι → n → k → ℝ) (Λ : ι → Matrix k r ℝ)
    (F : ι → n → r → ℝ) (U : ι → Matrix n k ℝ)
    (h : ApproximateFactorAsymptoticNormalizedRayleighBridge l X Λ F U) :
    Filter.Eventually
      (fun i =>
        FactorLeastSquaresNormalizedMinimizer (X i)
          (factorLoadingEstimator
            (factorLeadingPCEigenvectors (r := r)
              (factorSampleCovariance_isHermitian (X i)) hcard)
            (factorPCDiagonalSqrtD
              (factorLeadingPCEigenvalues (r := r)
                (factorSampleCovariance_isHermitian (X i)) hcard)))
          (fun row =>
            factorScoreEstimator
              (factorLeadingPCEigenvectors (r := r)
                (factorSampleCovariance_isHermitian (X i)) hcard)
              (factorPCDiagonalInvSqrtD
                (factorLeadingPCEigenvalues (r := r)
                  (factorSampleCovariance_isHermitian (X i)) hcard)) (X i row))) l :=
  factorPCTheorem11_9_jointLSMinimizer_eventually_of_approxFactorAsymptoticPerturbationBridge_only
    hcard X Λ F U
    (ApproximateFactorAsymptoticNormalizedRayleighBridge.toPerturbationBridge h)

set_option linter.style.longLine false in
omit [DecidableEq n] in
/-- Hansen Theorem 11.9 eventually follows from a scalar envelope for the
normalized recovered-Gram Rayleigh quotient. -/
theorem factorPCTheorem11_9_eventually_of_approxFactorAsymptoticNormalizedEnvelopeBridge
    [Nonempty n] {ι : Type*} {l : Filter ι}
    (hcard : Fintype.card r ≤ Fintype.card k)
    (X : ι → n → k → ℝ) (Λ : ι → Matrix k r ℝ)
    (F : ι → n → r → ℝ) (U : ι → Matrix n k ℝ)
    (ρ : ι → ℝ)
    (h : ApproximateFactorAsymptoticNormalizedEnvelopeBridge l X Λ F U ρ) :
    Filter.Eventually
      (fun i =>
        FactorPCTheorem11_9 (factorSampleCovariance (X i))
          (factorLeadingPCEigenvectors (r := r)
            (factorSampleCovariance_isHermitian (X i)) hcard)
          (Matrix.diagonal
            (factorLeadingPCEigenvalues (r := r)
              (factorSampleCovariance_isHermitian (X i)) hcard))
          (factorPCDiagonalSqrtD
            (factorLeadingPCEigenvalues (r := r)
              (factorSampleCovariance_isHermitian (X i)) hcard))
          (factorPCDiagonalInvSqrtD
            (factorLeadingPCEigenvalues (r := r)
              (factorSampleCovariance_isHermitian (X i)) hcard))
          (factorLoadingEstimator
            (factorLeadingPCEigenvectors (r := r)
              (factorSampleCovariance_isHermitian (X i)) hcard)
            (factorPCDiagonalSqrtD
              (factorLeadingPCEigenvalues (r := r)
                (factorSampleCovariance_isHermitian (X i)) hcard)))
          (X i)
          (fun row =>
            factorScoreEstimator
              (factorLeadingPCEigenvectors (r := r)
                (factorSampleCovariance_isHermitian (X i)) hcard)
              (factorPCDiagonalInvSqrtD
                (factorLeadingPCEigenvalues (r := r)
                  (factorSampleCovariance_isHermitian (X i)) hcard)) (X i row))) l :=
  factorPCTheorem11_9_eventually_of_approxFactorAsymptoticNormalizedRayleighBridge
    hcard X Λ F U
    (ApproximateFactorAsymptoticNormalizedEnvelopeBridge.toNormalizedRayleighBridge h)

set_option linter.style.longLine false in
omit [DecidableEq n] in
/-- Hansen Theorem 11.9 normalized joint least-squares minimizer eventually
follows from a scalar envelope for the normalized recovered-Gram Rayleigh
quotient. -/
theorem
    factorPCTheorem11_9_jointLS_eventually_of_approxFactorNormalizedEnvelopeBridge
    [Nonempty n] {ι : Type*} {l : Filter ι}
    (hcard : Fintype.card r ≤ Fintype.card k)
    (hcardObs : Fintype.card r ≤ Fintype.card n)
    (X : ι → n → k → ℝ) (Λ : ι → Matrix k r ℝ)
    (F : ι → n → r → ℝ) (U : ι → Matrix n k ℝ)
    (ρ : ι → ℝ)
    (h : ApproximateFactorAsymptoticNormalizedEnvelopeBridge l X Λ F U ρ) :
    Filter.Eventually
      (fun i =>
        FactorLeastSquaresNormalizedMinimizer (X i)
          (factorLoadingEstimator
            (factorLeadingPCEigenvectors (r := r)
              (factorSampleCovariance_isHermitian (X i)) hcard)
            (factorPCDiagonalSqrtD
              (factorLeadingPCEigenvalues (r := r)
                (factorSampleCovariance_isHermitian (X i)) hcard)))
          (fun row =>
            factorScoreEstimator
              (factorLeadingPCEigenvectors (r := r)
                (factorSampleCovariance_isHermitian (X i)) hcard)
              (factorPCDiagonalInvSqrtD
                (factorLeadingPCEigenvalues (r := r)
                  (factorSampleCovariance_isHermitian (X i)) hcard)) (X i row))) l :=
  factorPCTheorem11_9_jointLS_eventually_of_approxFactorNormalizedRayleighBridge
    hcard hcardObs X Λ F U
    (ApproximateFactorAsymptoticNormalizedEnvelopeBridge.toNormalizedRayleighBridge h)

set_option linter.style.longLine false in
omit [DecidableEq n] in
/-- Hansen Theorem 11.9 eventually follows from a coordinatewise scalar
envelope for the normalized recovered-Gram perturbation. -/
theorem factorPCTheorem11_9_eventually_of_approxFactorAsymptoticEntrywiseEnvelopeBridge
    [Nonempty n] {ι : Type*} {l : Filter ι}
    (hcard : Fintype.card r ≤ Fintype.card k)
    (X : ι → n → k → ℝ) (Λ : ι → Matrix k r ℝ)
    (F : ι → n → r → ℝ) (U : ι → Matrix n k ℝ)
    (η : ι → ℝ)
    (h : ApproximateFactorAsymptoticEntrywiseEnvelopeBridge l X Λ F U η) :
    Filter.Eventually
      (fun i =>
        FactorPCTheorem11_9 (factorSampleCovariance (X i))
          (factorLeadingPCEigenvectors (r := r)
            (factorSampleCovariance_isHermitian (X i)) hcard)
          (Matrix.diagonal
            (factorLeadingPCEigenvalues (r := r)
              (factorSampleCovariance_isHermitian (X i)) hcard))
          (factorPCDiagonalSqrtD
            (factorLeadingPCEigenvalues (r := r)
              (factorSampleCovariance_isHermitian (X i)) hcard))
          (factorPCDiagonalInvSqrtD
            (factorLeadingPCEigenvalues (r := r)
              (factorSampleCovariance_isHermitian (X i)) hcard))
          (factorLoadingEstimator
            (factorLeadingPCEigenvectors (r := r)
              (factorSampleCovariance_isHermitian (X i)) hcard)
            (factorPCDiagonalSqrtD
              (factorLeadingPCEigenvalues (r := r)
                (factorSampleCovariance_isHermitian (X i)) hcard)))
          (X i)
          (fun row =>
            factorScoreEstimator
              (factorLeadingPCEigenvectors (r := r)
                (factorSampleCovariance_isHermitian (X i)) hcard)
              (factorPCDiagonalInvSqrtD
                (factorLeadingPCEigenvalues (r := r)
                  (factorSampleCovariance_isHermitian (X i)) hcard)) (X i row))) l :=
  factorPCTheorem11_9_eventually_of_approxFactorAsymptoticNormalizedRayleighBridge
    hcard X Λ F U
    (ApproximateFactorAsymptoticEntrywiseEnvelopeBridge.toNormalizedRayleighBridge h)

set_option linter.style.longLine false in
omit [DecidableEq n] in
/-- Hansen Theorem 11.9 normalized joint least-squares minimizer eventually
follows from a coordinatewise scalar envelope for the normalized recovered-Gram
perturbation. -/
theorem
    factorPCTheorem11_9_jointLS_eventually_of_approxFactorEntrywiseEnvelopeBridge
    [Nonempty n] {ι : Type*} {l : Filter ι}
    (hcard : Fintype.card r ≤ Fintype.card k)
    (hcardObs : Fintype.card r ≤ Fintype.card n)
    (X : ι → n → k → ℝ) (Λ : ι → Matrix k r ℝ)
    (F : ι → n → r → ℝ) (U : ι → Matrix n k ℝ)
    (η : ι → ℝ)
    (h : ApproximateFactorAsymptoticEntrywiseEnvelopeBridge l X Λ F U η) :
    Filter.Eventually
      (fun i =>
        FactorLeastSquaresNormalizedMinimizer (X i)
          (factorLoadingEstimator
            (factorLeadingPCEigenvectors (r := r)
              (factorSampleCovariance_isHermitian (X i)) hcard)
            (factorPCDiagonalSqrtD
              (factorLeadingPCEigenvalues (r := r)
                (factorSampleCovariance_isHermitian (X i)) hcard)))
          (fun row =>
            factorScoreEstimator
              (factorLeadingPCEigenvectors (r := r)
                (factorSampleCovariance_isHermitian (X i)) hcard)
              (factorPCDiagonalInvSqrtD
                (factorLeadingPCEigenvalues (r := r)
                  (factorSampleCovariance_isHermitian (X i)) hcard)) (X i row))) l :=
  factorPCTheorem11_9_jointLS_eventually_of_approxFactorNormalizedRayleighBridge
    hcard hcardObs X Λ F U
    (ApproximateFactorAsymptoticEntrywiseEnvelopeBridge.toNormalizedRayleighBridge h)

set_option linter.style.longLine false in
omit [DecidableEq n] in
/-- Hansen Theorem 11.9 eventually follows from coordinate WLLNs for every
entry of the normalized recovered-Gram perturbation. -/
theorem factorPCTheorem11_9_eventually_of_approxFactorAsymptoticCoordinateWLLNBridge
    [Nonempty n] {ι : Type*} {l : Filter ι}
    (hcard : Fintype.card r ≤ Fintype.card k)
    (X : ι → n → k → ℝ) (Λ : ι → Matrix k r ℝ)
    (F : ι → n → r → ℝ) (U : ι → Matrix n k ℝ)
    (h : ApproximateFactorAsymptoticCoordinateWLLNBridge l X Λ F U) :
    Filter.Eventually
      (fun i =>
        FactorPCTheorem11_9 (factorSampleCovariance (X i))
          (factorLeadingPCEigenvectors (r := r)
            (factorSampleCovariance_isHermitian (X i)) hcard)
          (Matrix.diagonal
            (factorLeadingPCEigenvalues (r := r)
              (factorSampleCovariance_isHermitian (X i)) hcard))
          (factorPCDiagonalSqrtD
            (factorLeadingPCEigenvalues (r := r)
              (factorSampleCovariance_isHermitian (X i)) hcard))
          (factorPCDiagonalInvSqrtD
            (factorLeadingPCEigenvalues (r := r)
              (factorSampleCovariance_isHermitian (X i)) hcard))
          (factorLoadingEstimator
            (factorLeadingPCEigenvectors (r := r)
              (factorSampleCovariance_isHermitian (X i)) hcard)
            (factorPCDiagonalSqrtD
              (factorLeadingPCEigenvalues (r := r)
                (factorSampleCovariance_isHermitian (X i)) hcard)))
          (X i)
          (fun row =>
            factorScoreEstimator
              (factorLeadingPCEigenvectors (r := r)
                (factorSampleCovariance_isHermitian (X i)) hcard)
              (factorPCDiagonalInvSqrtD
                (factorLeadingPCEigenvalues (r := r)
                  (factorSampleCovariance_isHermitian (X i)) hcard)) (X i row))) l :=
  factorPCTheorem11_9_eventually_of_approxFactorAsymptoticEntrywiseEnvelopeBridge
    hcard X Λ F U
    (fun i =>
      factorRecoveredIdiosyncraticGramNormalizedEntrywiseAbsSum
        (Λ i) (F i) (U i))
    (ApproximateFactorAsymptoticCoordinateWLLNBridge.toEntrywiseEnvelopeBridge h)

set_option linter.style.longLine false in
omit [DecidableEq n] in
/-- Hansen Theorem 11.9 normalized joint least-squares minimizer eventually
follows from coordinate WLLNs for every entry of the normalized recovered-Gram
perturbation. -/
theorem
    factorPCTheorem11_9_jointLS_eventually_of_approxFactorCoordinateWLLNBridge
    [Nonempty n] {ι : Type*} {l : Filter ι}
    (hcard : Fintype.card r ≤ Fintype.card k)
    (hcardObs : Fintype.card r ≤ Fintype.card n)
    (X : ι → n → k → ℝ) (Λ : ι → Matrix k r ℝ)
    (F : ι → n → r → ℝ) (U : ι → Matrix n k ℝ)
    (h : ApproximateFactorAsymptoticCoordinateWLLNBridge l X Λ F U) :
    Filter.Eventually
      (fun i =>
        FactorLeastSquaresNormalizedMinimizer (X i)
          (factorLoadingEstimator
            (factorLeadingPCEigenvectors (r := r)
              (factorSampleCovariance_isHermitian (X i)) hcard)
            (factorPCDiagonalSqrtD
              (factorLeadingPCEigenvalues (r := r)
                (factorSampleCovariance_isHermitian (X i)) hcard)))
          (fun row =>
            factorScoreEstimator
              (factorLeadingPCEigenvectors (r := r)
                (factorSampleCovariance_isHermitian (X i)) hcard)
              (factorPCDiagonalInvSqrtD
                (factorLeadingPCEigenvalues (r := r)
                  (factorSampleCovariance_isHermitian (X i)) hcard)) (X i row))) l :=
  factorPCTheorem11_9_jointLS_eventually_of_approxFactorEntrywiseEnvelopeBridge
    hcard hcardObs X Λ F U
    (fun i =>
      factorRecoveredIdiosyncraticGramNormalizedEntrywiseAbsSum
        (Λ i) (F i) (U i))
    (ApproximateFactorAsymptoticCoordinateWLLNBridge.toEntrywiseEnvelopeBridge h)

set_option linter.style.longLine false in
omit [DecidableEq n] in
/-- Hansen Theorem 11.9 eventually follows from a matrix/operator WLLN for the
whole normalized recovered-Gram perturbation. -/
theorem factorPCTheorem11_9_eventually_of_approxFactorAsymptoticMatrixWLLNBridge
    [Nonempty n] {ι : Type*} {l : Filter ι}
    (hcard : Fintype.card r ≤ Fintype.card k)
    (X : ι → n → k → ℝ) (Λ : ι → Matrix k r ℝ)
    (F : ι → n → r → ℝ) (U : ι → Matrix n k ℝ)
    (h : ApproximateFactorAsymptoticMatrixWLLNBridge l X Λ F U) :
    Filter.Eventually
      (fun i =>
        FactorPCTheorem11_9 (factorSampleCovariance (X i))
          (factorLeadingPCEigenvectors (r := r)
            (factorSampleCovariance_isHermitian (X i)) hcard)
          (Matrix.diagonal
            (factorLeadingPCEigenvalues (r := r)
              (factorSampleCovariance_isHermitian (X i)) hcard))
          (factorPCDiagonalSqrtD
            (factorLeadingPCEigenvalues (r := r)
              (factorSampleCovariance_isHermitian (X i)) hcard))
          (factorPCDiagonalInvSqrtD
            (factorLeadingPCEigenvalues (r := r)
              (factorSampleCovariance_isHermitian (X i)) hcard))
          (factorLoadingEstimator
            (factorLeadingPCEigenvectors (r := r)
              (factorSampleCovariance_isHermitian (X i)) hcard)
            (factorPCDiagonalSqrtD
              (factorLeadingPCEigenvalues (r := r)
                (factorSampleCovariance_isHermitian (X i)) hcard)))
          (X i)
          (fun row =>
            factorScoreEstimator
              (factorLeadingPCEigenvectors (r := r)
                (factorSampleCovariance_isHermitian (X i)) hcard)
              (factorPCDiagonalInvSqrtD
                (factorLeadingPCEigenvalues (r := r)
                  (factorSampleCovariance_isHermitian (X i)) hcard)) (X i row))) l :=
  factorPCTheorem11_9_eventually_of_approxFactorAsymptoticCoordinateWLLNBridge
    hcard X Λ F U
    (ApproximateFactorAsymptoticMatrixWLLNBridge.toCoordinateWLLNBridge h)

set_option linter.style.longLine false in
omit [DecidableEq n] in
/-- Hansen Theorem 11.9 normalized joint least-squares minimizer eventually
follows from a matrix/operator WLLN for the normalized recovered-Gram
perturbation. -/
theorem factorPCTheorem11_9_jointLS_eventually_of_approxFactorMatrixWLLNBridge
    [Nonempty n] {ι : Type*} {l : Filter ι}
    (hcard : Fintype.card r ≤ Fintype.card k)
    (hcardObs : Fintype.card r ≤ Fintype.card n)
    (X : ι → n → k → ℝ) (Λ : ι → Matrix k r ℝ)
    (F : ι → n → r → ℝ) (U : ι → Matrix n k ℝ)
    (h : ApproximateFactorAsymptoticMatrixWLLNBridge l X Λ F U) :
    Filter.Eventually
      (fun i =>
        FactorLeastSquaresNormalizedMinimizer (X i)
          (factorLoadingEstimator
            (factorLeadingPCEigenvectors (r := r)
              (factorSampleCovariance_isHermitian (X i)) hcard)
            (factorPCDiagonalSqrtD
              (factorLeadingPCEigenvalues (r := r)
                (factorSampleCovariance_isHermitian (X i)) hcard)))
          (fun row =>
            factorScoreEstimator
              (factorLeadingPCEigenvectors (r := r)
                (factorSampleCovariance_isHermitian (X i)) hcard)
              (factorPCDiagonalInvSqrtD
                (factorLeadingPCEigenvalues (r := r)
                  (factorSampleCovariance_isHermitian (X i)) hcard)) (X i row))) l :=
  factorPCTheorem11_9_jointLS_eventually_of_approxFactorCoordinateWLLNBridge
    hcard hcardObs X Λ F U
    (ApproximateFactorAsymptoticMatrixWLLNBridge.toCoordinateWLLNBridge h)

set_option linter.style.longLine false in
omit [DecidableEq n] in
/-- Hansen Theorem 11.9 eventually follows from the three primitive
cross/noise coordinate WLLNs for `n⁻¹F'E`, `n⁻¹E'F`, and `n⁻¹E'E`. -/
theorem factorPCTheorem11_9_eventually_of_approxFactorAsymptoticCrossNoiseWLLNBridge
    [Nonempty n] {ι : Type*} {l : Filter ι}
    (hcard : Fintype.card r ≤ Fintype.card k)
    (X : ι → n → k → ℝ) (Λ : ι → Matrix k r ℝ)
    (F : ι → n → r → ℝ) (U : ι → Matrix n k ℝ)
    (h : ApproximateFactorAsymptoticCrossNoiseWLLNBridge l X Λ F U) :
    Filter.Eventually
      (fun i =>
        FactorPCTheorem11_9 (factorSampleCovariance (X i))
          (factorLeadingPCEigenvectors (r := r)
            (factorSampleCovariance_isHermitian (X i)) hcard)
          (Matrix.diagonal
            (factorLeadingPCEigenvalues (r := r)
              (factorSampleCovariance_isHermitian (X i)) hcard))
          (factorPCDiagonalSqrtD
            (factorLeadingPCEigenvalues (r := r)
              (factorSampleCovariance_isHermitian (X i)) hcard))
          (factorPCDiagonalInvSqrtD
            (factorLeadingPCEigenvalues (r := r)
              (factorSampleCovariance_isHermitian (X i)) hcard))
          (factorLoadingEstimator
            (factorLeadingPCEigenvectors (r := r)
              (factorSampleCovariance_isHermitian (X i)) hcard)
            (factorPCDiagonalSqrtD
              (factorLeadingPCEigenvalues (r := r)
                (factorSampleCovariance_isHermitian (X i)) hcard)))
          (X i)
          (fun row =>
            factorScoreEstimator
              (factorLeadingPCEigenvectors (r := r)
                (factorSampleCovariance_isHermitian (X i)) hcard)
              (factorPCDiagonalInvSqrtD
                (factorLeadingPCEigenvalues (r := r)
                  (factorSampleCovariance_isHermitian (X i)) hcard)) (X i row))) l :=
  factorPCTheorem11_9_eventually_of_approxFactorAsymptoticCoordinateWLLNBridge
    hcard X Λ F U
    (ApproximateFactorAsymptoticCrossNoiseWLLNBridge.toCoordinateWLLNBridge h)

set_option linter.style.longLine false in
omit [DecidableEq n] in
/-- Hansen Theorem 11.9 normalized joint least-squares minimizer eventually
follows from the three primitive cross/noise coordinate WLLNs for `n⁻¹F'E`,
`n⁻¹E'F`, and `n⁻¹E'E`. -/
theorem factorPCTheorem11_9_jointLS_eventually_of_approxFactorCrossNoiseWLLNBridge
    [Nonempty n] {ι : Type*} {l : Filter ι}
    (hcard : Fintype.card r ≤ Fintype.card k)
    (hcardObs : Fintype.card r ≤ Fintype.card n)
    (X : ι → n → k → ℝ) (Λ : ι → Matrix k r ℝ)
    (F : ι → n → r → ℝ) (U : ι → Matrix n k ℝ)
    (h : ApproximateFactorAsymptoticCrossNoiseWLLNBridge l X Λ F U) :
    Filter.Eventually
      (fun i =>
        FactorLeastSquaresNormalizedMinimizer (X i)
          (factorLoadingEstimator
            (factorLeadingPCEigenvectors (r := r)
              (factorSampleCovariance_isHermitian (X i)) hcard)
            (factorPCDiagonalSqrtD
              (factorLeadingPCEigenvalues (r := r)
                (factorSampleCovariance_isHermitian (X i)) hcard)))
          (fun row =>
            factorScoreEstimator
              (factorLeadingPCEigenvectors (r := r)
                (factorSampleCovariance_isHermitian (X i)) hcard)
              (factorPCDiagonalInvSqrtD
                (factorLeadingPCEigenvalues (r := r)
                  (factorSampleCovariance_isHermitian (X i)) hcard)) (X i row))) l :=
  factorPCTheorem11_9_jointLS_eventually_of_approxFactorCoordinateWLLNBridge
    hcard hcardObs X Λ F U
    (ApproximateFactorAsymptoticCrossNoiseWLLNBridge.toCoordinateWLLNBridge h)

omit [DecidableEq n] in
/-- Hansen Theorem 11.9 specialized to the sample second-moment matrix with
canonical diagonal PCA scaling from nonsingularity of the selected eigenvalue
block. Positive semidefiniteness of the sample covariance turns nonzero selected
eigenvalues into the strict positivity needed for `D^{-1/2}`. -/
theorem factorPCTheorem11_9_of_sampleCovariance_selected_diagonal_isUnit
    (hcard : Fintype.card r ≤ Fintype.card k) (X : n → k → ℝ)
    (hunit : IsUnit (Matrix.diagonal
      (factorLeadingPCEigenvalues (r := r)
        (factorSampleCovariance_isHermitian X) hcard)).det) :
    FactorPCTheorem11_9 (factorSampleCovariance X)
      (factorLeadingPCEigenvectors (r := r)
        (factorSampleCovariance_isHermitian X) hcard)
      (Matrix.diagonal
        (factorLeadingPCEigenvalues (r := r)
          (factorSampleCovariance_isHermitian X) hcard))
      (factorPCDiagonalSqrtD
        (factorLeadingPCEigenvalues (r := r)
          (factorSampleCovariance_isHermitian X) hcard))
      (factorPCDiagonalInvSqrtD
        (factorLeadingPCEigenvalues (r := r)
          (factorSampleCovariance_isHermitian X) hcard))
      (factorLoadingEstimator
        (factorLeadingPCEigenvectors (r := r)
          (factorSampleCovariance_isHermitian X) hcard)
        (factorPCDiagonalSqrtD
          (factorLeadingPCEigenvalues (r := r)
            (factorSampleCovariance_isHermitian X) hcard)))
      X
      (fun i =>
        factorScoreEstimator
          (factorLeadingPCEigenvectors (r := r)
            (factorSampleCovariance_isHermitian X) hcard)
          (factorPCDiagonalInvSqrtD
            (factorLeadingPCEigenvalues (r := r)
              (factorSampleCovariance_isHermitian X) hcard)) (X i)) :=
  factorPCTheorem11_9_of_sampleCovariance_leadingPCEigenvectors_positive_eigenvalues
    (r := r) hcard X
    (factorLeadingPCEigenvalues_pos_of_posSemidef_selected_diagonal_isUnit
      (r := r) (factorSampleCovariance_isHermitian X) hcard
      (factorSampleCovariance_posSemidef X) hunit)

omit [DecidableEq n] in
/-- Hansen Theorem 11.9 specialized to the sample second-moment matrix with
canonical diagonal PCA scaling from full positive definiteness of the sample
covariance. This is a convenient raw full-rank route to the selected eigenvalue
positivity condition. -/
theorem factorPCTheorem11_9_of_sampleCovariance_posDef
    (hcard : Fintype.card r ≤ Fintype.card k) (X : n → k → ℝ)
    (hposDef : (factorSampleCovariance X).PosDef) :
    FactorPCTheorem11_9 (factorSampleCovariance X)
      (factorLeadingPCEigenvectors (r := r)
        (factorSampleCovariance_isHermitian X) hcard)
      (Matrix.diagonal
        (factorLeadingPCEigenvalues (r := r)
          (factorSampleCovariance_isHermitian X) hcard))
      (factorPCDiagonalSqrtD
        (factorLeadingPCEigenvalues (r := r)
          (factorSampleCovariance_isHermitian X) hcard))
      (factorPCDiagonalInvSqrtD
        (factorLeadingPCEigenvalues (r := r)
          (factorSampleCovariance_isHermitian X) hcard))
      (factorLoadingEstimator
        (factorLeadingPCEigenvectors (r := r)
          (factorSampleCovariance_isHermitian X) hcard)
        (factorPCDiagonalSqrtD
          (factorLeadingPCEigenvalues (r := r)
            (factorSampleCovariance_isHermitian X) hcard)))
      X
      (fun i =>
        factorScoreEstimator
          (factorLeadingPCEigenvectors (r := r)
            (factorSampleCovariance_isHermitian X) hcard)
          (factorPCDiagonalInvSqrtD
            (factorLeadingPCEigenvalues (r := r)
              (factorSampleCovariance_isHermitian X) hcard)) (X i)) :=
  factorPCTheorem11_9_of_sampleCovariance_leadingPCEigenvectors_positive_eigenvalues
    (r := r) hcard X
    (factorLeadingPCEigenvalues_pos_of_posDef
      (r := r) (factorSampleCovariance_isHermitian X) hcard hposDef)

/-- Hansen Assumption 11.1, in a finite-dimensional theorem-facing package. -/
structure ApproximateFactorAssumption
    (Λ : Matrix k r ℝ) (Ψ : Matrix k k ℝ) where
  bounded_idiosyncratic_covariance : ∃ B : ℝ, 0 ≤ B ∧ ∀ x : k → ℝ,
    x ⬝ᵥ (Ψ *ᵥ x) ≤ B * (x ⬝ᵥ x)
  pervasive_loadings : factorLoadingPervasiveness Λ

omit [Fintype n] [DecidableEq n] [DecidableEq k] [DecidableEq r] in
/-- Concrete loading-pervasiveness consequence of Hansen Assumption 11.1. -/
theorem approximateFactor_loading_pervasiveness
    (Λ : Matrix k r ℝ) (Ψ : Matrix k k ℝ)
    (h : ApproximateFactorAssumption Λ Ψ) :
    factorLoadingPervasiveness Λ :=
  h.pervasive_loadings

omit [Fintype n] [DecidableEq n] [DecidableEq k] [DecidableEq r] in
/-- Variance bound for the idealized factor-score error, exposed as the reusable
consequence of Assumption 11.1 used in the chapter prose. -/
theorem approximateFactor_scoreVariance_bound
    (Λ : Matrix k r ℝ) (Ψ : Matrix k k ℝ)
    (h : ApproximateFactorAssumption Λ Ψ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x : k → ℝ, x ⬝ᵥ (Ψ *ᵥ x) ≤ B * (x ⬝ᵥ x) :=
  h.bounded_idiosyncratic_covariance

/-- Hansen-facing Assumption 11.1 plus the single stochastic primitive needed
for the rank/signal part of Theorem 11.9.

The last field is the uniform Rayleigh `o(1)` condition for the normalized
recovered idiosyncratic Gram
`n⁻¹(F'E + E'F + E'E)`. It is weaker than separately assuming the three
coordinate WLLN families for `n⁻¹F'E`, `n⁻¹E'F`, and `n⁻¹E'E`, while keeping
Assumption 11.1's bounded covariance and pervasiveness data on the theorem
surface. -/
structure ApproximateFactorAssumptionNormalizedRayleighBridge
    {ι : Type*} (l : Filter ι)
    (X : ι → n → k → ℝ) (Λ : ι → Matrix k r ℝ)
    (F : ι → n → r → ℝ) (U : ι → Matrix n k ℝ)
    (Ψ : ι → Matrix k k ℝ) : Prop where
  eventually_approximate_factor :
    Filter.Eventually
      (fun i => factorApproxSampleFactorModel (X i) (Λ i) (F i) (U i)) l
  eventually_assumption11_1 :
    Filter.Eventually (fun i => ApproximateFactorAssumption (Λ i) (Ψ i)) l
  eventually_score_normalization :
    Filter.Eventually (fun i => factorScoreNormalization (F i)) l
  normalized_rayleigh_tendsto_zero :
    factorRecoveredIdiosyncraticGramNormalizedRayleighTendstoZero l Λ F U

namespace ApproximateFactorAssumptionNormalizedRayleighBridge

omit [DecidableEq n] [DecidableEq k] in
/-- Assumption 11.1 plus the normalized recovered-Gram Rayleigh primitive
supplies the normalized-Rayleigh bridge used by the PCA theorem route. -/
theorem toNormalizedRayleighBridge
    {ι : Type*} {l : Filter ι}
    {X : ι → n → k → ℝ} {Λ : ι → Matrix k r ℝ}
    {F : ι → n → r → ℝ} {U : ι → Matrix n k ℝ}
    {Ψ : ι → Matrix k k ℝ}
    (h : ApproximateFactorAssumptionNormalizedRayleighBridge l X Λ F U Ψ) :
    ApproximateFactorAsymptoticNormalizedRayleighBridge l X Λ F U where
  eventually_approximate_factor := h.eventually_approximate_factor
  eventually_loading_pervasiveness :=
    h.eventually_assumption11_1.mono fun _ hi => hi.pervasive_loadings
  eventually_score_normalization := h.eventually_score_normalization
  normalized_rayleigh_tendsto_zero := h.normalized_rayleigh_tendsto_zero

omit [DecidableEq n] [DecidableEq k] in
/-- Assumption 11.1 plus the normalized recovered-Gram Rayleigh primitive
supplies the older perturbation bridge consumed by the finite-sample rank
proof. -/
theorem toPerturbationBridge
    [Nonempty n] {ι : Type*} {l : Filter ι}
    {X : ι → n → k → ℝ} {Λ : ι → Matrix k r ℝ}
    {F : ι → n → r → ℝ} {U : ι → Matrix n k ℝ}
    {Ψ : ι → Matrix k k ℝ}
    (h : ApproximateFactorAssumptionNormalizedRayleighBridge l X Λ F U Ψ) :
    ApproximateFactorAsymptoticPerturbationBridge l X Λ F U :=
  ApproximateFactorAsymptoticNormalizedRayleighBridge.toPerturbationBridge
    (ApproximateFactorAssumptionNormalizedRayleighBridge.toNormalizedRayleighBridge h)

omit [DecidableEq n] [DecidableEq k] in
/-- The bounded-covariance half of Assumption 11.1 is retained explicitly by
the normalized-Rayleigh Hansen-facing bridge. -/
theorem eventually_scoreVariance_bound
    {ι : Type*} {l : Filter ι}
    {X : ι → n → k → ℝ} {Λ : ι → Matrix k r ℝ}
    {F : ι → n → r → ℝ} {U : ι → Matrix n k ℝ}
    {Ψ : ι → Matrix k k ℝ}
    (h : ApproximateFactorAssumptionNormalizedRayleighBridge l X Λ F U Ψ) :
    Filter.Eventually
      (fun i =>
        ∃ B : ℝ, 0 ≤ B ∧ ∀ x : k → ℝ,
          x ⬝ᵥ ((Ψ i) *ᵥ x) ≤ B * (x ⬝ᵥ x)) l :=
  h.eventually_assumption11_1.mono fun _ hi =>
    hi.bounded_idiosyncratic_covariance

end ApproximateFactorAssumptionNormalizedRayleighBridge

/-- Hansen-facing Assumption 11.1 plus a whole-matrix WLLN for the normalized
recovered idiosyncratic perturbation.

This replaces the three separate scalar cross/noise WLLN families with one
matrix statement
`n⁻¹(F'E + E'F + E'E) -> 0`, then derives the uniform Rayleigh `o(1)` bridge
by the existing finite-dimensional matrix-to-Rayleigh machinery. -/
structure ApproximateFactorAssumptionMatrixWLLNBridge
    {ι : Type*} (l : Filter ι)
    (X : ι → n → k → ℝ) (Λ : ι → Matrix k r ℝ)
    (F : ι → n → r → ℝ) (U : ι → Matrix n k ℝ)
    (Ψ : ι → Matrix k k ℝ) : Prop where
  eventually_approximate_factor :
    Filter.Eventually
      (fun i => factorApproxSampleFactorModel (X i) (Λ i) (F i) (U i)) l
  eventually_assumption11_1 :
    Filter.Eventually (fun i => ApproximateFactorAssumption (Λ i) (Ψ i)) l
  eventually_score_normalization :
    Filter.Eventually (fun i => factorScoreNormalization (F i)) l
  normalized_perturbation_tendsto_zero :
    Filter.Tendsto
      (fun i =>
        factorRecoveredIdiosyncraticGramNormalizedPerturbation
          (Λ i) (F i) (U i)) l (nhds 0)

namespace ApproximateFactorAssumptionMatrixWLLNBridge

omit [DecidableEq n] [DecidableEq k] in
/-- Assumption 11.1 plus one whole-matrix recovered-perturbation WLLN supplies
the matrix/operator bridge used by the PCA theorem route. -/
theorem toMatrixWLLNBridge
    {ι : Type*} {l : Filter ι}
    {X : ι → n → k → ℝ} {Λ : ι → Matrix k r ℝ}
    {F : ι → n → r → ℝ} {U : ι → Matrix n k ℝ}
    {Ψ : ι → Matrix k k ℝ}
    (h : ApproximateFactorAssumptionMatrixWLLNBridge l X Λ F U Ψ) :
    ApproximateFactorAsymptoticMatrixWLLNBridge l X Λ F U where
  eventually_approximate_factor := h.eventually_approximate_factor
  eventually_loading_pervasiveness :=
    h.eventually_assumption11_1.mono fun _ hi => hi.pervasive_loadings
  eventually_score_normalization := h.eventually_score_normalization
  normalized_perturbation_tendsto_zero := h.normalized_perturbation_tendsto_zero

omit [DecidableEq n] [DecidableEq k] in
/-- The matrix-WLLN facade supplies the normalized-Rayleigh bridge. -/
theorem toNormalizedRayleighBridge
    {ι : Type*} {l : Filter ι}
    {X : ι → n → k → ℝ} {Λ : ι → Matrix k r ℝ}
    {F : ι → n → r → ℝ} {U : ι → Matrix n k ℝ}
    {Ψ : ι → Matrix k k ℝ}
    (h : ApproximateFactorAssumptionMatrixWLLNBridge l X Λ F U Ψ) :
    ApproximateFactorAsymptoticNormalizedRayleighBridge l X Λ F U :=
  ApproximateFactorAsymptoticMatrixWLLNBridge.toNormalizedRayleighBridge
    (ApproximateFactorAssumptionMatrixWLLNBridge.toMatrixWLLNBridge h)

omit [DecidableEq n] [DecidableEq k] in
/-- The matrix-WLLN facade can be viewed as the weaker normalized-Rayleigh
Hansen-facing facade. -/
theorem toNormalizedRayleighAssumptionBridge
    {ι : Type*} {l : Filter ι}
    {X : ι → n → k → ℝ} {Λ : ι → Matrix k r ℝ}
    {F : ι → n → r → ℝ} {U : ι → Matrix n k ℝ}
    {Ψ : ι → Matrix k k ℝ}
    (h : ApproximateFactorAssumptionMatrixWLLNBridge l X Λ F U Ψ) :
    ApproximateFactorAssumptionNormalizedRayleighBridge l X Λ F U Ψ where
  eventually_approximate_factor := h.eventually_approximate_factor
  eventually_assumption11_1 := h.eventually_assumption11_1
  eventually_score_normalization := h.eventually_score_normalization
  normalized_rayleigh_tendsto_zero := by
    have hbridge :=
      ApproximateFactorAssumptionMatrixWLLNBridge.toNormalizedRayleighBridge h
    exact hbridge.normalized_rayleigh_tendsto_zero

omit [DecidableEq n] [DecidableEq k] in
/-- The matrix-WLLN facade supplies the older perturbation bridge consumed by
the finite-sample rank proof. -/
theorem toPerturbationBridge
    [Nonempty n] {ι : Type*} {l : Filter ι}
    {X : ι → n → k → ℝ} {Λ : ι → Matrix k r ℝ}
    {F : ι → n → r → ℝ} {U : ι → Matrix n k ℝ}
    {Ψ : ι → Matrix k k ℝ}
    (h : ApproximateFactorAssumptionMatrixWLLNBridge l X Λ F U Ψ) :
    ApproximateFactorAsymptoticPerturbationBridge l X Λ F U :=
  ApproximateFactorAsymptoticMatrixWLLNBridge.toPerturbationBridge
    (ApproximateFactorAssumptionMatrixWLLNBridge.toMatrixWLLNBridge h)

omit [DecidableEq n] [DecidableEq k] in
/-- The bounded-covariance half of Assumption 11.1 is retained explicitly by
the matrix-WLLN Hansen-facing bridge. -/
theorem eventually_scoreVariance_bound
    {ι : Type*} {l : Filter ι}
    {X : ι → n → k → ℝ} {Λ : ι → Matrix k r ℝ}
    {F : ι → n → r → ℝ} {U : ι → Matrix n k ℝ}
    {Ψ : ι → Matrix k k ℝ}
    (h : ApproximateFactorAssumptionMatrixWLLNBridge l X Λ F U Ψ) :
    Filter.Eventually
      (fun i =>
        ∃ B : ℝ, 0 ≤ B ∧ ∀ x : k → ℝ,
          x ⬝ᵥ ((Ψ i) *ᵥ x) ≤ B * (x ⬝ᵥ x)) l :=
  h.eventually_assumption11_1.mono fun _ hi =>
    hi.bounded_idiosyncratic_covariance

end ApproximateFactorAssumptionMatrixWLLNBridge

/-- Hansen-facing Assumption 11.1 plus raw cross/noise moment WLLNs.

This is closer to Hansen's approximate-factor proof than the single recovered
perturbation WLLN: the stochastic inputs are the raw normalized terms
`n⁻¹F'U`, `n⁻¹U'F`, and `n⁻¹U'U` after applying the deterministic
loading-Gram recoverer. The remaining probability work is to derive these
matrix WLLNs from row dependence, centering/cross-term, and integrability
conditions; bounded covariance/pervasiveness alone is retained but not treated
as sufficient. -/
structure ApproximateFactorAssumptionRawMomentMatrixWLLNBridge
    {ι : Type*} (l : Filter ι)
    (X : ι → n → k → ℝ) (Λ : ι → Matrix k r ℝ)
    (F : ι → n → r → ℝ) (U : ι → Matrix n k ℝ)
    (Ψ : ι → Matrix k k ℝ) : Prop where
  eventually_approximate_factor :
    Filter.Eventually
      (fun i => factorApproxSampleFactorModel (X i) (Λ i) (F i) (U i)) l
  eventually_assumption11_1 :
    Filter.Eventually (fun i => ApproximateFactorAssumption (Λ i) (Ψ i)) l
  eventually_score_normalization :
    Filter.Eventually (fun i => factorScoreNormalization (F i)) l
  raw_cross_left_recovered_tendsto_zero :
    Filter.Tendsto
      (fun i =>
        factorRawFactorIdiosyncraticCrossNormalized (F i) (U i) *
          (factorLoadingGramRecoverer (Λ i))ᵀ) l (nhds 0)
  raw_cross_right_recovered_tendsto_zero :
    Filter.Tendsto
      (fun i =>
        factorLoadingGramRecoverer (Λ i) *
          factorRawIdiosyncraticFactorCrossNormalized (F i) (U i)) l (nhds 0)
  raw_noise_recovered_tendsto_zero :
    Filter.Tendsto
      (fun i =>
        factorLoadingGramRecoverer (Λ i) *
          factorRawIdiosyncraticGramNormalized (U i) *
            (factorLoadingGramRecoverer (Λ i))ᵀ) l (nhds 0)

namespace ApproximateFactorAssumptionRawMomentMatrixWLLNBridge

omit [DecidableEq n] [DecidableEq k] in
/-- Assumption 11.1 plus raw moment WLLNs supplies the raw-moment bridge used
by the factor-PCA theorem route. -/
theorem toRawMomentMatrixWLLNBridge
    {ι : Type*} {l : Filter ι}
    {X : ι → n → k → ℝ} {Λ : ι → Matrix k r ℝ}
    {F : ι → n → r → ℝ} {U : ι → Matrix n k ℝ}
    {Ψ : ι → Matrix k k ℝ}
    (h : ApproximateFactorAssumptionRawMomentMatrixWLLNBridge l X Λ F U Ψ) :
    ApproximateFactorAsymptoticRawMomentMatrixWLLNBridge l X Λ F U where
  eventually_approximate_factor := h.eventually_approximate_factor
  eventually_loading_pervasiveness :=
    h.eventually_assumption11_1.mono fun _ hi => hi.pervasive_loadings
  eventually_score_normalization := h.eventually_score_normalization
  raw_cross_left_recovered_tendsto_zero :=
    h.raw_cross_left_recovered_tendsto_zero
  raw_cross_right_recovered_tendsto_zero :=
    h.raw_cross_right_recovered_tendsto_zero
  raw_noise_recovered_tendsto_zero := h.raw_noise_recovered_tendsto_zero

omit [DecidableEq n] [DecidableEq k] in
/-- Assumption 11.1 plus raw moment WLLNs supplies the whole-matrix recovered
perturbation WLLN facade. -/
theorem toMatrixWLLNAssumptionBridge
    {ι : Type*} {l : Filter ι}
    {X : ι → n → k → ℝ} {Λ : ι → Matrix k r ℝ}
    {F : ι → n → r → ℝ} {U : ι → Matrix n k ℝ}
    {Ψ : ι → Matrix k k ℝ}
    (h : ApproximateFactorAssumptionRawMomentMatrixWLLNBridge l X Λ F U Ψ) :
    ApproximateFactorAssumptionMatrixWLLNBridge l X Λ F U Ψ where
  eventually_approximate_factor := h.eventually_approximate_factor
  eventually_assumption11_1 := h.eventually_assumption11_1
  eventually_score_normalization := h.eventually_score_normalization
  normalized_perturbation_tendsto_zero := by
    have hbridge :=
      ApproximateFactorAssumptionRawMomentMatrixWLLNBridge.toRawMomentMatrixWLLNBridge h
    have hmatrix :=
      ApproximateFactorAsymptoticRawMomentMatrixWLLNBridge.toMatrixWLLNBridge hbridge
    exact hmatrix.normalized_perturbation_tendsto_zero

omit [DecidableEq n] [DecidableEq k] in
/-- Assumption 11.1 plus raw moment WLLNs supplies the normalized-Rayleigh
facade. -/
theorem toNormalizedRayleighAssumptionBridge
    {ι : Type*} {l : Filter ι}
    {X : ι → n → k → ℝ} {Λ : ι → Matrix k r ℝ}
    {F : ι → n → r → ℝ} {U : ι → Matrix n k ℝ}
    {Ψ : ι → Matrix k k ℝ}
    (h : ApproximateFactorAssumptionRawMomentMatrixWLLNBridge l X Λ F U Ψ) :
    ApproximateFactorAssumptionNormalizedRayleighBridge l X Λ F U Ψ :=
  ApproximateFactorAssumptionMatrixWLLNBridge.toNormalizedRayleighAssumptionBridge
    (ApproximateFactorAssumptionRawMomentMatrixWLLNBridge.toMatrixWLLNAssumptionBridge h)

omit [DecidableEq n] [DecidableEq k] in
/-- The bounded-covariance half of Assumption 11.1 is retained explicitly by
the raw-moment Hansen-facing bridge. -/
theorem eventually_scoreVariance_bound
    {ι : Type*} {l : Filter ι}
    {X : ι → n → k → ℝ} {Λ : ι → Matrix k r ℝ}
    {F : ι → n → r → ℝ} {U : ι → Matrix n k ℝ}
    {Ψ : ι → Matrix k k ℝ}
    (h : ApproximateFactorAssumptionRawMomentMatrixWLLNBridge l X Λ F U Ψ) :
    Filter.Eventually
      (fun i =>
        ∃ B : ℝ, 0 ≤ B ∧ ∀ x : k → ℝ,
          x ⬝ᵥ ((Ψ i) *ᵥ x) ≤ B * (x ⬝ᵥ x)) l :=
  h.eventually_assumption11_1.mono fun _ hi =>
    hi.bounded_idiosyncratic_covariance

end ApproximateFactorAssumptionRawMomentMatrixWLLNBridge

/-- Hansen-facing Assumption 11.1 plus unrecovered raw moment WLLNs.

This narrows the older raw-moment facade. Instead of assuming WLLNs after the
loading-Gram recoverer has already been applied, it asks for the unrecovered
raw cross moments `n⁻¹F'U`, `n⁻¹U'F`, a centered raw idiosyncratic Gram WLLN
`n⁻¹U'U - Ψ -> 0`, convergence of the covariance target `Ψ`, and shrinkage of
the concrete recoverer `(Λ'Λ)^{-1}Λ'`. The deterministic matrix-continuity
bridge below then derives the recovered raw moment WLLNs consumed by the
existing Theorem 11.9 route. -/
structure ApproximateFactorAssumptionUnrecoveredMomentWLLNBridge
    {ι : Type*} (l : Filter ι)
    (X : ι → n → k → ℝ) (Λ : ι → Matrix k r ℝ)
    (F : ι → n → r → ℝ) (U : ι → Matrix n k ℝ)
    (Ψ : ι → Matrix k k ℝ) (Ψlim : Matrix k k ℝ) : Prop where
  eventually_approximate_factor :
    Filter.Eventually
      (fun i => factorApproxSampleFactorModel (X i) (Λ i) (F i) (U i)) l
  eventually_assumption11_1 :
    Filter.Eventually (fun i => ApproximateFactorAssumption (Λ i) (Ψ i)) l
  eventually_score_normalization :
    Filter.Eventually (fun i => factorScoreNormalization (F i)) l
  loading_recoverer_tendsto_zero :
    Filter.Tendsto (fun i => factorLoadingGramRecoverer (Λ i)) l (nhds 0)
  covariance_target_tendsto :
    Filter.Tendsto Ψ l (nhds Ψlim)
  raw_cross_left_tendsto_zero :
    Filter.Tendsto
      (fun i => factorRawFactorIdiosyncraticCrossNormalized (F i) (U i)) l
      (nhds 0)
  raw_cross_right_tendsto_zero :
    Filter.Tendsto
      (fun i => factorRawIdiosyncraticFactorCrossNormalized (F i) (U i)) l
      (nhds 0)
  raw_noise_centered_tendsto_zero :
    Filter.Tendsto
      (fun i => factorRawIdiosyncraticGramNormalized (U i) - Ψ i) l
      (nhds 0)

namespace ApproximateFactorAssumptionUnrecoveredMomentWLLNBridge

omit [DecidableEq n] [DecidableEq k] in
/-- The centered raw idiosyncratic Gram WLLN plus covariance-target convergence
gives the uncentered raw Gram limit. -/
theorem raw_idiosyncratic_gram_tendsto_covariance
    {ι : Type*} {l : Filter ι}
    {X : ι → n → k → ℝ} {Λ : ι → Matrix k r ℝ}
    {F : ι → n → r → ℝ} {U : ι → Matrix n k ℝ}
    {Ψ : ι → Matrix k k ℝ} {Ψlim : Matrix k k ℝ}
    (h : ApproximateFactorAssumptionUnrecoveredMomentWLLNBridge
      l X Λ F U Ψ Ψlim) :
    Filter.Tendsto
      (fun i => factorRawIdiosyncraticGramNormalized (U i)) l
      (nhds Ψlim) := by
  have hsum :=
    h.raw_noise_centered_tendsto_zero.add h.covariance_target_tendsto
  simpa [sub_add_cancel] using hsum

omit [DecidableEq n] [DecidableEq k] in
/-- Unrecovered raw moment WLLNs plus recoverer shrinkage supply the recovered
raw moment WLLNs used by the existing factor-PCA theorem route. -/
theorem toRawMomentMatrixWLLNBridge
    {ι : Type*} {l : Filter ι}
    {X : ι → n → k → ℝ} {Λ : ι → Matrix k r ℝ}
    {F : ι → n → r → ℝ} {U : ι → Matrix n k ℝ}
    {Ψ : ι → Matrix k k ℝ} {Ψlim : Matrix k k ℝ}
    (h : ApproximateFactorAssumptionUnrecoveredMomentWLLNBridge
      l X Λ F U Ψ Ψlim) :
    ApproximateFactorAssumptionRawMomentMatrixWLLNBridge l X Λ F U Ψ where
  eventually_approximate_factor := h.eventually_approximate_factor
  eventually_assumption11_1 := h.eventually_assumption11_1
  eventually_score_normalization := h.eventually_score_normalization
  raw_cross_left_recovered_tendsto_zero := by
    have hLtr :
        Filter.Tendsto
          (fun i => (factorLoadingGramRecoverer (Λ i))ᵀ) l
          (nhds (0 : Matrix k r ℝ)) := by
      simpa using tendsto_matrix_transpose h.loading_recoverer_tendsto_zero
    have hprod :=
      tendsto_matrix_mul h.raw_cross_left_tendsto_zero hLtr
    simpa using hprod
  raw_cross_right_recovered_tendsto_zero := by
    have hprod :=
      tendsto_matrix_mul h.loading_recoverer_tendsto_zero
        h.raw_cross_right_tendsto_zero
    simpa using hprod
  raw_noise_recovered_tendsto_zero := by
    have hLtr :
        Filter.Tendsto
          (fun i => (factorLoadingGramRecoverer (Λ i))ᵀ) l
          (nhds (0 : Matrix k r ℝ)) := by
      simpa using tendsto_matrix_transpose h.loading_recoverer_tendsto_zero
    have hraw :=
      raw_idiosyncratic_gram_tendsto_covariance h
    have hleft :=
      tendsto_matrix_mul h.loading_recoverer_tendsto_zero hraw
    have hleft_zero :
        Filter.Tendsto
          (fun i =>
            factorLoadingGramRecoverer (Λ i) *
              factorRawIdiosyncraticGramNormalized (U i)) l
          (nhds (0 : Matrix r k ℝ)) := by
      simpa using hleft
    have hprod := tendsto_matrix_mul hleft_zero hLtr
    simpa [Matrix.mul_assoc] using hprod

omit [DecidableEq n] [DecidableEq k] in
/-- The unrecovered-moment bridge supplies the whole-matrix recovered
perturbation WLLN facade. -/
theorem toMatrixWLLNAssumptionBridge
    {ι : Type*} {l : Filter ι}
    {X : ι → n → k → ℝ} {Λ : ι → Matrix k r ℝ}
    {F : ι → n → r → ℝ} {U : ι → Matrix n k ℝ}
    {Ψ : ι → Matrix k k ℝ} {Ψlim : Matrix k k ℝ}
    (h : ApproximateFactorAssumptionUnrecoveredMomentWLLNBridge
      l X Λ F U Ψ Ψlim) :
    ApproximateFactorAssumptionMatrixWLLNBridge l X Λ F U Ψ :=
  ApproximateFactorAssumptionRawMomentMatrixWLLNBridge.toMatrixWLLNAssumptionBridge
    (ApproximateFactorAssumptionUnrecoveredMomentWLLNBridge.toRawMomentMatrixWLLNBridge h)

omit [DecidableEq n] [DecidableEq k] in
/-- The unrecovered-moment bridge supplies the normalized-Rayleigh Assumption
11.1 facade. -/
theorem toNormalizedRayleighAssumptionBridge
    {ι : Type*} {l : Filter ι}
    {X : ι → n → k → ℝ} {Λ : ι → Matrix k r ℝ}
    {F : ι → n → r → ℝ} {U : ι → Matrix n k ℝ}
    {Ψ : ι → Matrix k k ℝ} {Ψlim : Matrix k k ℝ}
    (h : ApproximateFactorAssumptionUnrecoveredMomentWLLNBridge
      l X Λ F U Ψ Ψlim) :
    ApproximateFactorAssumptionNormalizedRayleighBridge l X Λ F U Ψ :=
  ApproximateFactorAssumptionMatrixWLLNBridge.toNormalizedRayleighAssumptionBridge
    (ApproximateFactorAssumptionUnrecoveredMomentWLLNBridge.toMatrixWLLNAssumptionBridge h)

omit [DecidableEq n] [DecidableEq k] in
/-- The bounded-covariance half of Assumption 11.1 is retained explicitly by
the unrecovered-moment Hansen-facing bridge. -/
theorem eventually_scoreVariance_bound
    {ι : Type*} {l : Filter ι}
    {X : ι → n → k → ℝ} {Λ : ι → Matrix k r ℝ}
    {F : ι → n → r → ℝ} {U : ι → Matrix n k ℝ}
    {Ψ : ι → Matrix k k ℝ} {Ψlim : Matrix k k ℝ}
    (h : ApproximateFactorAssumptionUnrecoveredMomentWLLNBridge
      l X Λ F U Ψ Ψlim) :
    Filter.Eventually
      (fun i =>
        ∃ B : ℝ, 0 ≤ B ∧ ∀ x : k → ℝ,
          x ⬝ᵥ ((Ψ i) *ᵥ x) ≤ B * (x ⬝ᵥ x)) l :=
  h.eventually_assumption11_1.mono fun _ hi =>
    hi.bounded_idiosyncratic_covariance

end ApproximateFactorAssumptionUnrecoveredMomentWLLNBridge

/-- Hansen-facing Assumption 11.1 plus entrywise unrecovered raw moment WLLNs.

This is the scalar-coordinate version of
`ApproximateFactorAssumptionUnrecoveredMomentWLLNBridge`. It asks for entrywise
convergence of the loading recoverer `(Λ'Λ)^{-1}Λ'`, the covariance target, and
the raw unrecovered cross/noise moments. Finite dimensionality then reconstructs
the matrix convergence hypotheses consumed by the existing Theorem 11.9 route.
-/
structure ApproximateFactorAssumptionUnrecoveredEntrywiseWLLNBridge
    {ι : Type*} (l : Filter ι)
    (X : ι → n → k → ℝ) (Λ : ι → Matrix k r ℝ)
    (F : ι → n → r → ℝ) (U : ι → Matrix n k ℝ)
    (Ψ : ι → Matrix k k ℝ) (Ψlim : Matrix k k ℝ) : Prop where
  eventually_approximate_factor :
    Filter.Eventually
      (fun i => factorApproxSampleFactorModel (X i) (Λ i) (F i) (U i)) l
  eventually_assumption11_1 :
    Filter.Eventually (fun i => ApproximateFactorAssumption (Λ i) (Ψ i)) l
  eventually_score_normalization :
    Filter.Eventually (fun i => factorScoreNormalization (F i)) l
  loading_recoverer_entry_tendsto_zero : ∀ a b,
    Filter.Tendsto
      (fun i => factorLoadingGramRecoverer (Λ i) a b) l (nhds 0)
  covariance_target_entry_tendsto : ∀ a b,
    Filter.Tendsto (fun i => Ψ i a b) l (nhds (Ψlim a b))
  raw_cross_left_entry_tendsto_zero : ∀ a b,
    Filter.Tendsto
      (fun i => factorRawFactorIdiosyncraticCrossNormalized (F i) (U i) a b)
      l (nhds 0)
  raw_cross_right_entry_tendsto_zero : ∀ a b,
    Filter.Tendsto
      (fun i => factorRawIdiosyncraticFactorCrossNormalized (F i) (U i) a b)
      l (nhds 0)
  raw_noise_centered_entry_tendsto_zero : ∀ a b,
    Filter.Tendsto
      (fun i => (factorRawIdiosyncraticGramNormalized (U i) - Ψ i) a b)
      l (nhds 0)

namespace ApproximateFactorAssumptionUnrecoveredEntrywiseWLLNBridge

omit [DecidableEq n] [DecidableEq k] in
/-- Entrywise shrinkage of the concrete loading recoverer gives matrix
shrinkage of the same recoverer. -/
theorem loading_recoverer_tendsto_zero
    {ι : Type*} {l : Filter ι}
    {X : ι → n → k → ℝ} {Λ : ι → Matrix k r ℝ}
    {F : ι → n → r → ℝ} {U : ι → Matrix n k ℝ}
    {Ψ : ι → Matrix k k ℝ} {Ψlim : Matrix k k ℝ}
    (h : ApproximateFactorAssumptionUnrecoveredEntrywiseWLLNBridge
      l X Λ F U Ψ Ψlim) :
    Filter.Tendsto (fun i => factorLoadingGramRecoverer (Λ i)) l (nhds 0) :=
  tendsto_matrix_of_entries fun a b => by
    simpa using h.loading_recoverer_entry_tendsto_zero a b

omit [DecidableEq n] [DecidableEq k] in
/-- Entrywise convergence of the idiosyncratic covariance target gives matrix
convergence of the same target. -/
theorem covariance_target_tendsto
    {ι : Type*} {l : Filter ι}
    {X : ι → n → k → ℝ} {Λ : ι → Matrix k r ℝ}
    {F : ι → n → r → ℝ} {U : ι → Matrix n k ℝ}
    {Ψ : ι → Matrix k k ℝ} {Ψlim : Matrix k k ℝ}
    (h : ApproximateFactorAssumptionUnrecoveredEntrywiseWLLNBridge
      l X Λ F U Ψ Ψlim) :
    Filter.Tendsto Ψ l (nhds Ψlim) :=
  tendsto_matrix_of_entries h.covariance_target_entry_tendsto

omit [DecidableEq n] [DecidableEq k] in
/-- Entrywise WLLNs for `n⁻¹F'U` give matrix convergence of the raw left cross
moment. -/
theorem raw_cross_left_tendsto_zero
    {ι : Type*} {l : Filter ι}
    {X : ι → n → k → ℝ} {Λ : ι → Matrix k r ℝ}
    {F : ι → n → r → ℝ} {U : ι → Matrix n k ℝ}
    {Ψ : ι → Matrix k k ℝ} {Ψlim : Matrix k k ℝ}
    (h : ApproximateFactorAssumptionUnrecoveredEntrywiseWLLNBridge
      l X Λ F U Ψ Ψlim) :
    Filter.Tendsto
      (fun i => factorRawFactorIdiosyncraticCrossNormalized (F i) (U i)) l
      (nhds 0) :=
  tendsto_matrix_of_entries fun a b => by
    simpa using h.raw_cross_left_entry_tendsto_zero a b

omit [DecidableEq n] [DecidableEq k] in
/-- Entrywise WLLNs for `n⁻¹U'F` give matrix convergence of the raw right cross
moment. -/
theorem raw_cross_right_tendsto_zero
    {ι : Type*} {l : Filter ι}
    {X : ι → n → k → ℝ} {Λ : ι → Matrix k r ℝ}
    {F : ι → n → r → ℝ} {U : ι → Matrix n k ℝ}
    {Ψ : ι → Matrix k k ℝ} {Ψlim : Matrix k k ℝ}
    (h : ApproximateFactorAssumptionUnrecoveredEntrywiseWLLNBridge
      l X Λ F U Ψ Ψlim) :
    Filter.Tendsto
      (fun i => factorRawIdiosyncraticFactorCrossNormalized (F i) (U i)) l
      (nhds 0) :=
  tendsto_matrix_of_entries fun a b => by
    simpa using h.raw_cross_right_entry_tendsto_zero a b

omit [DecidableEq n] [DecidableEq k] in
/-- Entrywise centered WLLNs for `n⁻¹U'U - Ψ` give matrix convergence of the
centered raw idiosyncratic Gram. -/
theorem raw_noise_centered_tendsto_zero
    {ι : Type*} {l : Filter ι}
    {X : ι → n → k → ℝ} {Λ : ι → Matrix k r ℝ}
    {F : ι → n → r → ℝ} {U : ι → Matrix n k ℝ}
    {Ψ : ι → Matrix k k ℝ} {Ψlim : Matrix k k ℝ}
    (h : ApproximateFactorAssumptionUnrecoveredEntrywiseWLLNBridge
      l X Λ F U Ψ Ψlim) :
    Filter.Tendsto
      (fun i => factorRawIdiosyncraticGramNormalized (U i) - Ψ i) l
      (nhds 0) :=
  tendsto_matrix_of_entries fun a b => by
    simpa using h.raw_noise_centered_entry_tendsto_zero a b

omit [DecidableEq n] [DecidableEq k] in
/-- Entrywise unrecovered WLLNs supply the matrix unrecovered-moment bridge
already consumed by the factor-PCA theorem route. -/
theorem toUnrecoveredMomentWLLNBridge
    {ι : Type*} {l : Filter ι}
    {X : ι → n → k → ℝ} {Λ : ι → Matrix k r ℝ}
    {F : ι → n → r → ℝ} {U : ι → Matrix n k ℝ}
    {Ψ : ι → Matrix k k ℝ} {Ψlim : Matrix k k ℝ}
    (h : ApproximateFactorAssumptionUnrecoveredEntrywiseWLLNBridge
      l X Λ F U Ψ Ψlim) :
    ApproximateFactorAssumptionUnrecoveredMomentWLLNBridge
      l X Λ F U Ψ Ψlim where
  eventually_approximate_factor := h.eventually_approximate_factor
  eventually_assumption11_1 := h.eventually_assumption11_1
  eventually_score_normalization := h.eventually_score_normalization
  loading_recoverer_tendsto_zero := loading_recoverer_tendsto_zero h
  covariance_target_tendsto := covariance_target_tendsto h
  raw_cross_left_tendsto_zero := raw_cross_left_tendsto_zero h
  raw_cross_right_tendsto_zero := raw_cross_right_tendsto_zero h
  raw_noise_centered_tendsto_zero := raw_noise_centered_tendsto_zero h

omit [DecidableEq n] [DecidableEq k] in
/-- Entrywise unrecovered WLLNs supply the recovered raw-moment bridge. -/
theorem toRawMomentMatrixWLLNBridge
    {ι : Type*} {l : Filter ι}
    {X : ι → n → k → ℝ} {Λ : ι → Matrix k r ℝ}
    {F : ι → n → r → ℝ} {U : ι → Matrix n k ℝ}
    {Ψ : ι → Matrix k k ℝ} {Ψlim : Matrix k k ℝ}
    (h : ApproximateFactorAssumptionUnrecoveredEntrywiseWLLNBridge
      l X Λ F U Ψ Ψlim) :
    ApproximateFactorAssumptionRawMomentMatrixWLLNBridge l X Λ F U Ψ :=
  ApproximateFactorAssumptionUnrecoveredMomentWLLNBridge.toRawMomentMatrixWLLNBridge
    (ApproximateFactorAssumptionUnrecoveredEntrywiseWLLNBridge.toUnrecoveredMomentWLLNBridge h)

omit [DecidableEq n] [DecidableEq k] in
/-- Entrywise unrecovered WLLNs supply the whole-matrix recovered perturbation
WLLN facade. -/
theorem toMatrixWLLNAssumptionBridge
    {ι : Type*} {l : Filter ι}
    {X : ι → n → k → ℝ} {Λ : ι → Matrix k r ℝ}
    {F : ι → n → r → ℝ} {U : ι → Matrix n k ℝ}
    {Ψ : ι → Matrix k k ℝ} {Ψlim : Matrix k k ℝ}
    (h : ApproximateFactorAssumptionUnrecoveredEntrywiseWLLNBridge
      l X Λ F U Ψ Ψlim) :
    ApproximateFactorAssumptionMatrixWLLNBridge l X Λ F U Ψ :=
  ApproximateFactorAssumptionUnrecoveredMomentWLLNBridge.toMatrixWLLNAssumptionBridge
    (ApproximateFactorAssumptionUnrecoveredEntrywiseWLLNBridge.toUnrecoveredMomentWLLNBridge h)

omit [DecidableEq n] [DecidableEq k] in
/-- Entrywise unrecovered WLLNs supply the normalized-Rayleigh Assumption 11.1
facade. -/
theorem toNormalizedRayleighAssumptionBridge
    {ι : Type*} {l : Filter ι}
    {X : ι → n → k → ℝ} {Λ : ι → Matrix k r ℝ}
    {F : ι → n → r → ℝ} {U : ι → Matrix n k ℝ}
    {Ψ : ι → Matrix k k ℝ} {Ψlim : Matrix k k ℝ}
    (h : ApproximateFactorAssumptionUnrecoveredEntrywiseWLLNBridge
      l X Λ F U Ψ Ψlim) :
    ApproximateFactorAssumptionNormalizedRayleighBridge l X Λ F U Ψ :=
  ApproximateFactorAssumptionUnrecoveredMomentWLLNBridge.toNormalizedRayleighAssumptionBridge
    (ApproximateFactorAssumptionUnrecoveredEntrywiseWLLNBridge.toUnrecoveredMomentWLLNBridge h)

omit [DecidableEq n] [DecidableEq k] in
/-- The bounded-covariance half of Assumption 11.1 is retained explicitly by
the entrywise unrecovered-moment Hansen-facing bridge. -/
theorem eventually_scoreVariance_bound
    {ι : Type*} {l : Filter ι}
    {X : ι → n → k → ℝ} {Λ : ι → Matrix k r ℝ}
    {F : ι → n → r → ℝ} {U : ι → Matrix n k ℝ}
    {Ψ : ι → Matrix k k ℝ} {Ψlim : Matrix k k ℝ}
    (h : ApproximateFactorAssumptionUnrecoveredEntrywiseWLLNBridge
      l X Λ F U Ψ Ψlim) :
    Filter.Eventually
      (fun i =>
        ∃ B : ℝ, 0 ≤ B ∧ ∀ x : k → ℝ,
          x ⬝ᵥ ((Ψ i) *ᵥ x) ≤ B * (x ⬝ᵥ x)) l :=
  h.eventually_assumption11_1.mono fun _ hi =>
    hi.bounded_idiosyncratic_covariance

end ApproximateFactorAssumptionUnrecoveredEntrywiseWLLNBridge

/-- Hansen-facing Assumption 11.1 plus envelope-controlled unrecovered raw
moment WLLNs.

This is a scalar-envelope version of
`ApproximateFactorAssumptionUnrecoveredEntrywiseWLLNBridge`. Instead of asking
for each entrywise limit directly, it asks for five scalar envelopes tending to
zero: one each for the loading-Gram recoverer, the covariance target, the raw
`n⁻¹F'U` cross moment, the raw `n⁻¹U'F` cross moment, and the centered raw
`n⁻¹U'U - Ψ` moment. This matches the usual Hansen proof shape where a single
maximal or uniform bound is proved for each displayed matrix family. -/
structure ApproximateFactorAssumptionUnrecoveredEntrywiseEnvelopeWLLNBridge
    {ι : Type*} (l : Filter ι)
    (X : ι → n → k → ℝ) (Λ : ι → Matrix k r ℝ)
    (F : ι → n → r → ℝ) (U : ι → Matrix n k ℝ)
    (Ψ : ι → Matrix k k ℝ) (Ψlim : Matrix k k ℝ)
    (ρL ρΨ ρFU ρUF ρUU : ι → ℝ) : Prop where
  eventually_approximate_factor :
    Filter.Eventually
      (fun i => factorApproxSampleFactorModel (X i) (Λ i) (F i) (U i)) l
  eventually_assumption11_1 :
    Filter.Eventually (fun i => ApproximateFactorAssumption (Λ i) (Ψ i)) l
  eventually_score_normalization :
    Filter.Eventually (fun i => factorScoreNormalization (F i)) l
  loading_recoverer_entry_abs_bound : ∀ a b,
    Filter.Eventually
      (fun i => |factorLoadingGramRecoverer (Λ i) a b| ≤ ρL i) l
  loading_recoverer_envelope_tendsto_zero :
    Filter.Tendsto ρL l (nhds 0)
  covariance_target_entry_abs_bound : ∀ a b,
    Filter.Eventually
      (fun i => |Ψ i a b - Ψlim a b| ≤ ρΨ i) l
  covariance_target_envelope_tendsto_zero :
    Filter.Tendsto ρΨ l (nhds 0)
  raw_cross_left_entry_abs_bound : ∀ a b,
    Filter.Eventually
      (fun i =>
        |factorRawFactorIdiosyncraticCrossNormalized (F i) (U i) a b| ≤
          ρFU i) l
  raw_cross_left_envelope_tendsto_zero :
    Filter.Tendsto ρFU l (nhds 0)
  raw_cross_right_entry_abs_bound : ∀ a b,
    Filter.Eventually
      (fun i =>
        |factorRawIdiosyncraticFactorCrossNormalized (F i) (U i) a b| ≤
          ρUF i) l
  raw_cross_right_envelope_tendsto_zero :
    Filter.Tendsto ρUF l (nhds 0)
  raw_noise_centered_entry_abs_bound : ∀ a b,
    Filter.Eventually
      (fun i =>
        |(factorRawIdiosyncraticGramNormalized (U i) - Ψ i) a b| ≤ ρUU i) l
  raw_noise_centered_envelope_tendsto_zero :
    Filter.Tendsto ρUU l (nhds 0)

namespace ApproximateFactorAssumptionUnrecoveredEntrywiseEnvelopeWLLNBridge

omit [DecidableEq n] [DecidableEq k] in
/-- Envelope-controlled unrecovered WLLNs supply the existing entrywise
unrecovered-moment bridge. -/
theorem toUnrecoveredEntrywiseWLLNBridge
    {ι : Type*} {l : Filter ι}
    {X : ι → n → k → ℝ} {Λ : ι → Matrix k r ℝ}
    {F : ι → n → r → ℝ} {U : ι → Matrix n k ℝ}
    {Ψ : ι → Matrix k k ℝ} {Ψlim : Matrix k k ℝ}
    {ρL ρΨ ρFU ρUF ρUU : ι → ℝ}
    (h : ApproximateFactorAssumptionUnrecoveredEntrywiseEnvelopeWLLNBridge
      l X Λ F U Ψ Ψlim ρL ρΨ ρFU ρUF ρUU) :
    ApproximateFactorAssumptionUnrecoveredEntrywiseWLLNBridge
      l X Λ F U Ψ Ψlim where
  eventually_approximate_factor := h.eventually_approximate_factor
  eventually_assumption11_1 := h.eventually_assumption11_1
  eventually_score_normalization := h.eventually_score_normalization
  loading_recoverer_entry_tendsto_zero := fun a b =>
    tendsto_zero_of_eventually_abs_le
      (h.loading_recoverer_entry_abs_bound a b)
      h.loading_recoverer_envelope_tendsto_zero
  covariance_target_entry_tendsto := fun a b =>
    tendsto_of_eventually_abs_sub_le
      (h.covariance_target_entry_abs_bound a b)
      h.covariance_target_envelope_tendsto_zero
  raw_cross_left_entry_tendsto_zero := fun a b =>
    tendsto_zero_of_eventually_abs_le
      (h.raw_cross_left_entry_abs_bound a b)
      h.raw_cross_left_envelope_tendsto_zero
  raw_cross_right_entry_tendsto_zero := fun a b =>
    tendsto_zero_of_eventually_abs_le
      (h.raw_cross_right_entry_abs_bound a b)
      h.raw_cross_right_envelope_tendsto_zero
  raw_noise_centered_entry_tendsto_zero := fun a b =>
    tendsto_zero_of_eventually_abs_le
      (h.raw_noise_centered_entry_abs_bound a b)
      h.raw_noise_centered_envelope_tendsto_zero

set_option linter.style.longLine false in
omit [DecidableEq n] [DecidableEq k] in
/-- Envelope-controlled unrecovered WLLNs supply the matrix unrecovered-moment
bridge consumed by the factor-PCA theorem route. -/
theorem toUnrecoveredMomentWLLNBridge
    {ι : Type*} {l : Filter ι}
    {X : ι → n → k → ℝ} {Λ : ι → Matrix k r ℝ}
    {F : ι → n → r → ℝ} {U : ι → Matrix n k ℝ}
    {Ψ : ι → Matrix k k ℝ} {Ψlim : Matrix k k ℝ}
    {ρL ρΨ ρFU ρUF ρUU : ι → ℝ}
    (h : ApproximateFactorAssumptionUnrecoveredEntrywiseEnvelopeWLLNBridge
      l X Λ F U Ψ Ψlim ρL ρΨ ρFU ρUF ρUU) :
    ApproximateFactorAssumptionUnrecoveredMomentWLLNBridge
      l X Λ F U Ψ Ψlim :=
  ApproximateFactorAssumptionUnrecoveredEntrywiseWLLNBridge.toUnrecoveredMomentWLLNBridge
    (ApproximateFactorAssumptionUnrecoveredEntrywiseEnvelopeWLLNBridge.toUnrecoveredEntrywiseWLLNBridge h)

set_option linter.style.longLine false in
omit [DecidableEq n] [DecidableEq k] in
/-- Envelope-controlled unrecovered WLLNs supply the whole-matrix recovered
perturbation WLLN facade. This exposes the matrix bridge used by the
Theorem 11.9 PCA route without asking callers to manually unpack the
entrywise-envelope route first. -/
theorem toMatrixWLLNAssumptionBridge
    {ι : Type*} {l : Filter ι}
    {X : ι → n → k → ℝ} {Λ : ι → Matrix k r ℝ}
    {F : ι → n → r → ℝ} {U : ι → Matrix n k ℝ}
    {Ψ : ι → Matrix k k ℝ} {Ψlim : Matrix k k ℝ}
    {ρL ρΨ ρFU ρUF ρUU : ι → ℝ}
    (h : ApproximateFactorAssumptionUnrecoveredEntrywiseEnvelopeWLLNBridge
      l X Λ F U Ψ Ψlim ρL ρΨ ρFU ρUF ρUU) :
    ApproximateFactorAssumptionMatrixWLLNBridge l X Λ F U Ψ :=
  ApproximateFactorAssumptionUnrecoveredMomentWLLNBridge.toMatrixWLLNAssumptionBridge
    (ApproximateFactorAssumptionUnrecoveredEntrywiseEnvelopeWLLNBridge.toUnrecoveredMomentWLLNBridge h)

set_option linter.style.longLine false in
omit [DecidableEq n] [DecidableEq k] in
/-- Envelope-controlled unrecovered WLLNs supply the normalized-Rayleigh
Assumption 11.1 facade. -/
theorem toNormalizedRayleighAssumptionBridge
    {ι : Type*} {l : Filter ι}
    {X : ι → n → k → ℝ} {Λ : ι → Matrix k r ℝ}
    {F : ι → n → r → ℝ} {U : ι → Matrix n k ℝ}
    {Ψ : ι → Matrix k k ℝ} {Ψlim : Matrix k k ℝ}
    {ρL ρΨ ρFU ρUF ρUU : ι → ℝ}
    (h : ApproximateFactorAssumptionUnrecoveredEntrywiseEnvelopeWLLNBridge
      l X Λ F U Ψ Ψlim ρL ρΨ ρFU ρUF ρUU) :
    ApproximateFactorAssumptionNormalizedRayleighBridge l X Λ F U Ψ :=
  ApproximateFactorAssumptionUnrecoveredMomentWLLNBridge.toNormalizedRayleighAssumptionBridge
    (ApproximateFactorAssumptionUnrecoveredEntrywiseEnvelopeWLLNBridge.toUnrecoveredMomentWLLNBridge h)

omit [DecidableEq n] [DecidableEq k] in
/-- The bounded-covariance half of Assumption 11.1 is retained explicitly by
the envelope unrecovered-moment Hansen-facing bridge. -/
theorem eventually_scoreVariance_bound
    {ι : Type*} {l : Filter ι}
    {X : ι → n → k → ℝ} {Λ : ι → Matrix k r ℝ}
    {F : ι → n → r → ℝ} {U : ι → Matrix n k ℝ}
    {Ψ : ι → Matrix k k ℝ} {Ψlim : Matrix k k ℝ}
    {ρL ρΨ ρFU ρUF ρUU : ι → ℝ}
    (h : ApproximateFactorAssumptionUnrecoveredEntrywiseEnvelopeWLLNBridge
      l X Λ F U Ψ Ψlim ρL ρΨ ρFU ρUF ρUU) :
    Filter.Eventually
      (fun i =>
        ∃ B : ℝ, 0 ≤ B ∧ ∀ x : k → ℝ,
          x ⬝ᵥ ((Ψ i) *ᵥ x) ≤ B * (x ⬝ᵥ x)) l :=
  h.eventually_assumption11_1.mono fun _ hi =>
    hi.bounded_idiosyncratic_covariance

end ApproximateFactorAssumptionUnrecoveredEntrywiseEnvelopeWLLNBridge

/-- Hansen-facing Assumption 11.1 plus inverse-loading-envelope unrecovered raw
moment WLLNs.

This is the entrywise-envelope route with the loading-recoverer envelope
derived from more primitive Hansen-style bounds: entries of `(Λ'Λ)⁻¹`, entries
of `Λ`, and the product condition `(# factors)ρInvρΛ → 0`. The other raw
moment envelopes are the same covariance-target and idiosyncratic moment
envelopes used by `ApproximateFactorAssumptionUnrecoveredEntrywiseEnvelopeWLLNBridge`. -/
structure ApproximateFactorAssumptionUnrecoveredInverseLoadingEnvelopeWLLNBridge
    {ι : Type*} (l : Filter ι)
    (X : ι → n → k → ℝ) (Λ : ι → Matrix k r ℝ)
    (F : ι → n → r → ℝ) (U : ι → Matrix n k ℝ)
    (Ψ : ι → Matrix k k ℝ) (Ψlim : Matrix k k ℝ)
    (ρInv ρΛ ρΨ ρFU ρUF ρUU : ι → ℝ) : Prop where
  eventually_approximate_factor :
    Filter.Eventually
      (fun i => factorApproxSampleFactorModel (X i) (Λ i) (F i) (U i)) l
  eventually_assumption11_1 :
    Filter.Eventually (fun i => ApproximateFactorAssumption (Λ i) (Ψ i)) l
  eventually_score_normalization :
    Filter.Eventually (fun i => factorScoreNormalization (F i)) l
  loading_inverse_entry_abs_bound :
    Filter.Eventually
      (fun i => ∀ a c, |(((Λ i)ᵀ * Λ i)⁻¹) a c| ≤ ρInv i) l
  loading_entry_abs_bound :
    Filter.Eventually (fun i => ∀ b c, |Λ i b c| ≤ ρΛ i) l
  loading_inverse_envelope_nonneg :
    Filter.Eventually (fun i => 0 ≤ ρInv i) l
  loading_inverse_product_tendsto_zero :
    Filter.Tendsto
      (fun i => (Fintype.card r : ℝ) * ρInv i * ρΛ i) l (nhds 0)
  covariance_target_entry_abs_bound : ∀ a b,
    Filter.Eventually
      (fun i => |Ψ i a b - Ψlim a b| ≤ ρΨ i) l
  covariance_target_envelope_tendsto_zero :
    Filter.Tendsto ρΨ l (nhds 0)
  raw_cross_left_entry_abs_bound : ∀ a b,
    Filter.Eventually
      (fun i =>
        |factorRawFactorIdiosyncraticCrossNormalized (F i) (U i) a b| ≤
          ρFU i) l
  raw_cross_left_envelope_tendsto_zero :
    Filter.Tendsto ρFU l (nhds 0)
  raw_cross_right_entry_abs_bound : ∀ a b,
    Filter.Eventually
      (fun i =>
        |factorRawIdiosyncraticFactorCrossNormalized (F i) (U i) a b| ≤
          ρUF i) l
  raw_cross_right_envelope_tendsto_zero :
    Filter.Tendsto ρUF l (nhds 0)
  raw_noise_centered_entry_abs_bound : ∀ a b,
    Filter.Eventually
      (fun i =>
        |(factorRawIdiosyncraticGramNormalized (U i) - Ψ i) a b| ≤ ρUU i) l
  raw_noise_centered_envelope_tendsto_zero :
    Filter.Tendsto ρUU l (nhds 0)

namespace ApproximateFactorAssumptionUnrecoveredInverseLoadingEnvelopeWLLNBridge

omit [DecidableEq n] [DecidableEq k] in
/-- Inverse/loading-envelope unrecovered WLLNs supply the existing entrywise
unrecovered-moment bridge. -/
theorem toUnrecoveredEntrywiseWLLNBridge
    {ι : Type*} {l : Filter ι}
    {X : ι → n → k → ℝ} {Λ : ι → Matrix k r ℝ}
    {F : ι → n → r → ℝ} {U : ι → Matrix n k ℝ}
    {Ψ : ι → Matrix k k ℝ} {Ψlim : Matrix k k ℝ}
    {ρInv ρΛ ρΨ ρFU ρUF ρUU : ι → ℝ}
    (h : ApproximateFactorAssumptionUnrecoveredInverseLoadingEnvelopeWLLNBridge
      l X Λ F U Ψ Ψlim ρInv ρΛ ρΨ ρFU ρUF ρUU) :
    ApproximateFactorAssumptionUnrecoveredEntrywiseWLLNBridge
      l X Λ F U Ψ Ψlim where
  eventually_approximate_factor := h.eventually_approximate_factor
  eventually_assumption11_1 := h.eventually_assumption11_1
  eventually_score_normalization := h.eventually_score_normalization
  loading_recoverer_entry_tendsto_zero :=
    factorLoadingGramRecoverer_entry_tendsto_zero_of_inverse_loading_entry_bounds
      h.loading_inverse_entry_abs_bound h.loading_entry_abs_bound
      h.loading_inverse_envelope_nonneg
      h.loading_inverse_product_tendsto_zero
  covariance_target_entry_tendsto := fun a b =>
    tendsto_of_eventually_abs_sub_le
      (h.covariance_target_entry_abs_bound a b)
      h.covariance_target_envelope_tendsto_zero
  raw_cross_left_entry_tendsto_zero := fun a b =>
    tendsto_zero_of_eventually_abs_le
      (h.raw_cross_left_entry_abs_bound a b)
      h.raw_cross_left_envelope_tendsto_zero
  raw_cross_right_entry_tendsto_zero := fun a b =>
    tendsto_zero_of_eventually_abs_le
      (h.raw_cross_right_entry_abs_bound a b)
      h.raw_cross_right_envelope_tendsto_zero
  raw_noise_centered_entry_tendsto_zero := fun a b =>
    tendsto_zero_of_eventually_abs_le
      (h.raw_noise_centered_entry_abs_bound a b)
      h.raw_noise_centered_envelope_tendsto_zero

set_option linter.style.longLine false in
omit [DecidableEq n] [DecidableEq k] in
/-- Inverse/loading-envelope unrecovered WLLNs supply the matrix
unrecovered-moment bridge consumed by the factor-PCA theorem route. -/
theorem toUnrecoveredMomentWLLNBridge
    {ι : Type*} {l : Filter ι}
    {X : ι → n → k → ℝ} {Λ : ι → Matrix k r ℝ}
    {F : ι → n → r → ℝ} {U : ι → Matrix n k ℝ}
    {Ψ : ι → Matrix k k ℝ} {Ψlim : Matrix k k ℝ}
    {ρInv ρΛ ρΨ ρFU ρUF ρUU : ι → ℝ}
    (h : ApproximateFactorAssumptionUnrecoveredInverseLoadingEnvelopeWLLNBridge
      l X Λ F U Ψ Ψlim ρInv ρΛ ρΨ ρFU ρUF ρUU) :
    ApproximateFactorAssumptionUnrecoveredMomentWLLNBridge
      l X Λ F U Ψ Ψlim :=
  ApproximateFactorAssumptionUnrecoveredEntrywiseWLLNBridge.toUnrecoveredMomentWLLNBridge
    (ApproximateFactorAssumptionUnrecoveredInverseLoadingEnvelopeWLLNBridge.toUnrecoveredEntrywiseWLLNBridge h)

set_option linter.style.longLine false in
omit [DecidableEq n] [DecidableEq k] in
/-- Inverse/loading-envelope unrecovered WLLNs supply the whole-matrix recovered
perturbation WLLN facade. -/
theorem toMatrixWLLNAssumptionBridge
    {ι : Type*} {l : Filter ι}
    {X : ι → n → k → ℝ} {Λ : ι → Matrix k r ℝ}
    {F : ι → n → r → ℝ} {U : ι → Matrix n k ℝ}
    {Ψ : ι → Matrix k k ℝ} {Ψlim : Matrix k k ℝ}
    {ρInv ρΛ ρΨ ρFU ρUF ρUU : ι → ℝ}
    (h : ApproximateFactorAssumptionUnrecoveredInverseLoadingEnvelopeWLLNBridge
      l X Λ F U Ψ Ψlim ρInv ρΛ ρΨ ρFU ρUF ρUU) :
    ApproximateFactorAssumptionMatrixWLLNBridge l X Λ F U Ψ :=
  ApproximateFactorAssumptionUnrecoveredMomentWLLNBridge.toMatrixWLLNAssumptionBridge
    (ApproximateFactorAssumptionUnrecoveredInverseLoadingEnvelopeWLLNBridge.toUnrecoveredMomentWLLNBridge h)

set_option linter.style.longLine false in
omit [DecidableEq n] [DecidableEq k] in
/-- Inverse/loading-envelope unrecovered WLLNs supply the normalized-Rayleigh
Assumption 11.1 facade. -/
theorem toNormalizedRayleighAssumptionBridge
    {ι : Type*} {l : Filter ι}
    {X : ι → n → k → ℝ} {Λ : ι → Matrix k r ℝ}
    {F : ι → n → r → ℝ} {U : ι → Matrix n k ℝ}
    {Ψ : ι → Matrix k k ℝ} {Ψlim : Matrix k k ℝ}
    {ρInv ρΛ ρΨ ρFU ρUF ρUU : ι → ℝ}
    (h : ApproximateFactorAssumptionUnrecoveredInverseLoadingEnvelopeWLLNBridge
      l X Λ F U Ψ Ψlim ρInv ρΛ ρΨ ρFU ρUF ρUU) :
    ApproximateFactorAssumptionNormalizedRayleighBridge l X Λ F U Ψ :=
  ApproximateFactorAssumptionUnrecoveredMomentWLLNBridge.toNormalizedRayleighAssumptionBridge
    (ApproximateFactorAssumptionUnrecoveredInverseLoadingEnvelopeWLLNBridge.toUnrecoveredMomentWLLNBridge h)

omit [DecidableEq n] [DecidableEq k] in
/-- The bounded-covariance half of Assumption 11.1 is retained explicitly by
the inverse/loading-envelope Hansen-facing bridge. -/
theorem eventually_scoreVariance_bound
    {ι : Type*} {l : Filter ι}
    {X : ι → n → k → ℝ} {Λ : ι → Matrix k r ℝ}
    {F : ι → n → r → ℝ} {U : ι → Matrix n k ℝ}
    {Ψ : ι → Matrix k k ℝ} {Ψlim : Matrix k k ℝ}
    {ρInv ρΛ ρΨ ρFU ρUF ρUU : ι → ℝ}
    (h : ApproximateFactorAssumptionUnrecoveredInverseLoadingEnvelopeWLLNBridge
      l X Λ F U Ψ Ψlim ρInv ρΛ ρΨ ρFU ρUF ρUU) :
    Filter.Eventually
      (fun i =>
        ∃ B : ℝ, 0 ≤ B ∧ ∀ x : k → ℝ,
          x ⬝ᵥ ((Ψ i) *ᵥ x) ≤ B * (x ⬝ᵥ x)) l :=
  h.eventually_assumption11_1.mono fun _ hi =>
    hi.bounded_idiosyncratic_covariance

end ApproximateFactorAssumptionUnrecoveredInverseLoadingEnvelopeWLLNBridge

/-- Hansen-facing Assumption 11.1 plus cross/noise WLLN bridge.

Assumption 11.1 supplies bounded idiosyncratic covariance and loading
pervasiveness. This compatibility facade keeps the three scalar WLLN fields
explicit; newer normalized-Rayleigh and matrix-WLLN facades above replace those
three fields by one stochastic primitive when that is what the probability
argument proves directly. -/
structure ApproximateFactorAssumptionCrossNoiseWLLNBridge
    {ι : Type*} (l : Filter ι)
    (X : ι → n → k → ℝ) (Λ : ι → Matrix k r ℝ)
    (F : ι → n → r → ℝ) (U : ι → Matrix n k ℝ)
    (Ψ : ι → Matrix k k ℝ) : Prop where
  eventually_approximate_factor :
    Filter.Eventually
      (fun i => factorApproxSampleFactorModel (X i) (Λ i) (F i) (U i)) l
  eventually_assumption11_1 :
    Filter.Eventually (fun i => ApproximateFactorAssumption (Λ i) (Ψ i)) l
  eventually_score_normalization :
    Filter.Eventually (fun i => factorScoreNormalization (F i)) l
  cross_left_entry_tendsto_zero : ∀ a b : r,
    Filter.Tendsto
      (fun i =>
        factorRecoveredIdiosyncraticCrossLeftNormalized
          (Λ i) (F i) (U i) a b) l (nhds 0)
  cross_right_entry_tendsto_zero : ∀ a b : r,
    Filter.Tendsto
      (fun i =>
        factorRecoveredIdiosyncraticCrossRightNormalized
          (Λ i) (F i) (U i) a b) l (nhds 0)
  noise_entry_tendsto_zero : ∀ a b : r,
    Filter.Tendsto
      (fun i =>
        factorRecoveredIdiosyncraticNoiseGramNormalized
          (Λ i) (U i) a b) l (nhds 0)

namespace ApproximateFactorAssumptionCrossNoiseWLLNBridge

omit [DecidableEq n] [DecidableEq k] in
/-- Assumption 11.1 plus scalar cross/noise WLLNs supplies the cross/noise
bridge used by the factor-PCA theorem route. -/
theorem toCrossNoiseWLLNBridge
    {ι : Type*} {l : Filter ι}
    {X : ι → n → k → ℝ} {Λ : ι → Matrix k r ℝ}
    {F : ι → n → r → ℝ} {U : ι → Matrix n k ℝ}
    {Ψ : ι → Matrix k k ℝ}
    (h : ApproximateFactorAssumptionCrossNoiseWLLNBridge l X Λ F U Ψ) :
    ApproximateFactorAsymptoticCrossNoiseWLLNBridge l X Λ F U where
  eventually_approximate_factor := h.eventually_approximate_factor
  eventually_loading_pervasiveness :=
    h.eventually_assumption11_1.mono fun _ hi => hi.pervasive_loadings
  eventually_score_normalization := h.eventually_score_normalization
  cross_left_entry_tendsto_zero := h.cross_left_entry_tendsto_zero
  cross_right_entry_tendsto_zero := h.cross_right_entry_tendsto_zero
  noise_entry_tendsto_zero := h.noise_entry_tendsto_zero

omit [DecidableEq n] [DecidableEq k] in
/-- Assumption 11.1 plus scalar cross/noise WLLNs supplies the matrix/operator
WLLN bridge for the recovered perturbation. -/
theorem toMatrixWLLNBridge
    {ι : Type*} {l : Filter ι}
    {X : ι → n → k → ℝ} {Λ : ι → Matrix k r ℝ}
    {F : ι → n → r → ℝ} {U : ι → Matrix n k ℝ}
    {Ψ : ι → Matrix k k ℝ}
    (h : ApproximateFactorAssumptionCrossNoiseWLLNBridge l X Λ F U Ψ) :
    ApproximateFactorAsymptoticMatrixWLLNBridge l X Λ F U :=
  ApproximateFactorAsymptoticCrossNoiseWLLNBridge.toMatrixWLLNBridge
    (ApproximateFactorAssumptionCrossNoiseWLLNBridge.toCrossNoiseWLLNBridge h)

omit [DecidableEq n] [DecidableEq k] in
/-- Assumption 11.1 plus scalar cross/noise WLLNs supplies the Assumption 11.1
matrix-WLLN facade. This makes the hierarchy explicit: the old scalar facade is
a sufficient condition for the newer whole-matrix stochastic boundary. -/
theorem toMatrixWLLNAssumptionBridge
    {ι : Type*} {l : Filter ι}
    {X : ι → n → k → ℝ} {Λ : ι → Matrix k r ℝ}
    {F : ι → n → r → ℝ} {U : ι → Matrix n k ℝ}
    {Ψ : ι → Matrix k k ℝ}
    (h : ApproximateFactorAssumptionCrossNoiseWLLNBridge l X Λ F U Ψ) :
    ApproximateFactorAssumptionMatrixWLLNBridge l X Λ F U Ψ where
  eventually_approximate_factor := h.eventually_approximate_factor
  eventually_assumption11_1 := h.eventually_assumption11_1
  eventually_score_normalization := h.eventually_score_normalization
  normalized_perturbation_tendsto_zero := by
    have hbridge :=
      ApproximateFactorAssumptionCrossNoiseWLLNBridge.toMatrixWLLNBridge h
    exact hbridge.normalized_perturbation_tendsto_zero

omit [DecidableEq n] [DecidableEq k] in
/-- Assumption 11.1 plus scalar cross/noise WLLNs supplies the weaker
Assumption 11.1 normalized-Rayleigh facade. -/
theorem toNormalizedRayleighAssumptionBridge
    {ι : Type*} {l : Filter ι}
    {X : ι → n → k → ℝ} {Λ : ι → Matrix k r ℝ}
    {F : ι → n → r → ℝ} {U : ι → Matrix n k ℝ}
    {Ψ : ι → Matrix k k ℝ}
    (h : ApproximateFactorAssumptionCrossNoiseWLLNBridge l X Λ F U Ψ) :
    ApproximateFactorAssumptionNormalizedRayleighBridge l X Λ F U Ψ :=
  ApproximateFactorAssumptionMatrixWLLNBridge.toNormalizedRayleighAssumptionBridge
    (ApproximateFactorAssumptionCrossNoiseWLLNBridge.toMatrixWLLNAssumptionBridge h)

omit [DecidableEq n] [DecidableEq k] in
/-- The bounded-covariance half of Assumption 11.1 is retained explicitly by
the Hansen-facing bridge. -/
theorem eventually_scoreVariance_bound
    {ι : Type*} {l : Filter ι}
    {X : ι → n → k → ℝ} {Λ : ι → Matrix k r ℝ}
    {F : ι → n → r → ℝ} {U : ι → Matrix n k ℝ}
    {Ψ : ι → Matrix k k ℝ}
    (h : ApproximateFactorAssumptionCrossNoiseWLLNBridge l X Λ F U Ψ) :
    Filter.Eventually
      (fun i =>
        ∃ B : ℝ, 0 ≤ B ∧ ∀ x : k → ℝ,
          x ⬝ᵥ ((Ψ i) *ᵥ x) ≤ B * (x ⬝ᵥ x)) l :=
  h.eventually_assumption11_1.mono fun _ hi =>
    hi.bounded_idiosyncratic_covariance

end ApproximateFactorAssumptionCrossNoiseWLLNBridge

set_option linter.style.longLine false in
omit [DecidableEq n] in
/-- Hansen Theorem 11.9 eventually follows from Assumption 11.1 plus the single
uniform Rayleigh `o(1)` primitive for the normalized recovered idiosyncratic
Gram.

This is the tightest theorem-facing stochastic facade in this file: the
probability argument only has to prove that
`n⁻¹(F'E + E'F + E'E)` is uniformly negligible in Rayleigh quotient after
loading-Gram recovery. -/
theorem factorPCTheorem11_9_eventually_of_approxFactorAssumption11_1NormalizedRayleighBridge
    [Nonempty n] {ι : Type*} {l : Filter ι}
    (hcard : Fintype.card r ≤ Fintype.card k)
    (X : ι → n → k → ℝ) (Λ : ι → Matrix k r ℝ)
    (F : ι → n → r → ℝ) (U : ι → Matrix n k ℝ)
    (Ψ : ι → Matrix k k ℝ)
    (h : ApproximateFactorAssumptionNormalizedRayleighBridge l X Λ F U Ψ) :
    Filter.Eventually
      (fun i =>
        FactorPCTheorem11_9 (factorSampleCovariance (X i))
          (factorLeadingPCEigenvectors (r := r)
            (factorSampleCovariance_isHermitian (X i)) hcard)
          (Matrix.diagonal
            (factorLeadingPCEigenvalues (r := r)
              (factorSampleCovariance_isHermitian (X i)) hcard))
          (factorPCDiagonalSqrtD
            (factorLeadingPCEigenvalues (r := r)
              (factorSampleCovariance_isHermitian (X i)) hcard))
          (factorPCDiagonalInvSqrtD
            (factorLeadingPCEigenvalues (r := r)
              (factorSampleCovariance_isHermitian (X i)) hcard))
          (factorLoadingEstimator
            (factorLeadingPCEigenvectors (r := r)
              (factorSampleCovariance_isHermitian (X i)) hcard)
            (factorPCDiagonalSqrtD
              (factorLeadingPCEigenvalues (r := r)
                (factorSampleCovariance_isHermitian (X i)) hcard)))
          (X i)
          (fun row =>
            factorScoreEstimator
              (factorLeadingPCEigenvectors (r := r)
                (factorSampleCovariance_isHermitian (X i)) hcard)
              (factorPCDiagonalInvSqrtD
                (factorLeadingPCEigenvalues (r := r)
                  (factorSampleCovariance_isHermitian (X i)) hcard)) (X i row))) l :=
  factorPCTheorem11_9_eventually_of_approxFactorAsymptoticNormalizedRayleighBridge
    hcard X Λ F U
    (ApproximateFactorAssumptionNormalizedRayleighBridge.toNormalizedRayleighBridge h)

set_option linter.style.longLine false in
omit [DecidableEq n] in
/-- Hansen Theorem 11.9 normalized joint least-squares minimizer eventually
follows from Assumption 11.1 plus the single uniform Rayleigh `o(1)` primitive
for the normalized recovered idiosyncratic Gram. -/
theorem factorPCTheorem11_9_jointLS_eventually_of_approxFactorAssumption11_1NormalizedRayleighBridge
    [Nonempty n] {ι : Type*} {l : Filter ι}
    (hcard : Fintype.card r ≤ Fintype.card k)
    (hcardObs : Fintype.card r ≤ Fintype.card n)
    (X : ι → n → k → ℝ) (Λ : ι → Matrix k r ℝ)
    (F : ι → n → r → ℝ) (U : ι → Matrix n k ℝ)
    (Ψ : ι → Matrix k k ℝ)
    (h : ApproximateFactorAssumptionNormalizedRayleighBridge l X Λ F U Ψ) :
    Filter.Eventually
      (fun i =>
        FactorLeastSquaresNormalizedMinimizer (X i)
          (factorLoadingEstimator
            (factorLeadingPCEigenvectors (r := r)
              (factorSampleCovariance_isHermitian (X i)) hcard)
            (factorPCDiagonalSqrtD
              (factorLeadingPCEigenvalues (r := r)
                (factorSampleCovariance_isHermitian (X i)) hcard)))
          (fun row =>
            factorScoreEstimator
              (factorLeadingPCEigenvectors (r := r)
                (factorSampleCovariance_isHermitian (X i)) hcard)
              (factorPCDiagonalInvSqrtD
                (factorLeadingPCEigenvalues (r := r)
                  (factorSampleCovariance_isHermitian (X i)) hcard)) (X i row))) l :=
  factorPCTheorem11_9_jointLS_eventually_of_approxFactorNormalizedRayleighBridge
    hcard hcardObs X Λ F U
    (ApproximateFactorAssumptionNormalizedRayleighBridge.toNormalizedRayleighBridge h)

set_option linter.style.longLine false in
omit [DecidableEq n] in
/-- Hansen Theorem 11.9 normalized joint least-squares minimizer eventually
follows from Assumption 11.1 plus the single normalized-Rayleigh primitive, with
the observation-count side condition derived internally. -/
theorem
    factorPCTheorem11_9_jointLS_eventually_of_approxFactorAssumption11_1NormalizedRayleighBridge_only
    [Nonempty n] {ι : Type*} {l : Filter ι}
    (hcard : Fintype.card r ≤ Fintype.card k)
    (X : ι → n → k → ℝ) (Λ : ι → Matrix k r ℝ)
    (F : ι → n → r → ℝ) (U : ι → Matrix n k ℝ)
    (Ψ : ι → Matrix k k ℝ)
    (h : ApproximateFactorAssumptionNormalizedRayleighBridge l X Λ F U Ψ) :
    Filter.Eventually
      (fun i =>
        FactorLeastSquaresNormalizedMinimizer (X i)
          (factorLoadingEstimator
            (factorLeadingPCEigenvectors (r := r)
              (factorSampleCovariance_isHermitian (X i)) hcard)
            (factorPCDiagonalSqrtD
              (factorLeadingPCEigenvalues (r := r)
                (factorSampleCovariance_isHermitian (X i)) hcard)))
          (fun row =>
            factorScoreEstimator
              (factorLeadingPCEigenvectors (r := r)
                (factorSampleCovariance_isHermitian (X i)) hcard)
              (factorPCDiagonalInvSqrtD
                (factorLeadingPCEigenvalues (r := r)
                  (factorSampleCovariance_isHermitian (X i)) hcard)) (X i row))) l :=
  factorPCTheorem11_9_jointLS_eventually_of_approxFactorNormalizedRayleighBridge_only
    hcard X Λ F U
    (ApproximateFactorAssumptionNormalizedRayleighBridge.toNormalizedRayleighBridge h)

set_option linter.style.longLine false in
omit [DecidableEq n] in
/-- Hansen Theorem 11.9 combined asymptotic endpoint from Assumption 11.1 plus
the normalized-Rayleigh primitive. It returns the PCA formula certificate, the
literal normalized joint least-squares minimizer, and the bounded score-variance
consequence of Assumption 11.1 in one theorem-facing package. -/
theorem factorPCTheorem11_9_with_jointLS_and_scoreVariance_eventually_of_approxFactorAssumption11_1NormalizedRayleighBridge
    [Nonempty n] {ι : Type*} {l : Filter ι}
    (hcard : Fintype.card r ≤ Fintype.card k)
    (hcardObs : Fintype.card r ≤ Fintype.card n)
    (X : ι → n → k → ℝ) (Λ : ι → Matrix k r ℝ)
    (F : ι → n → r → ℝ) (U : ι → Matrix n k ℝ)
    (Ψ : ι → Matrix k k ℝ)
    (h : ApproximateFactorAssumptionNormalizedRayleighBridge l X Λ F U Ψ) :
    Filter.Eventually
      (fun i =>
        FactorPCTheorem11_9 (factorSampleCovariance (X i))
          (factorLeadingPCEigenvectors (r := r)
            (factorSampleCovariance_isHermitian (X i)) hcard)
          (Matrix.diagonal
            (factorLeadingPCEigenvalues (r := r)
              (factorSampleCovariance_isHermitian (X i)) hcard))
          (factorPCDiagonalSqrtD
            (factorLeadingPCEigenvalues (r := r)
              (factorSampleCovariance_isHermitian (X i)) hcard))
          (factorPCDiagonalInvSqrtD
            (factorLeadingPCEigenvalues (r := r)
              (factorSampleCovariance_isHermitian (X i)) hcard))
          (factorLoadingEstimator
            (factorLeadingPCEigenvectors (r := r)
              (factorSampleCovariance_isHermitian (X i)) hcard)
            (factorPCDiagonalSqrtD
              (factorLeadingPCEigenvalues (r := r)
                (factorSampleCovariance_isHermitian (X i)) hcard)))
          (X i)
          (fun row =>
            factorScoreEstimator
              (factorLeadingPCEigenvectors (r := r)
                (factorSampleCovariance_isHermitian (X i)) hcard)
              (factorPCDiagonalInvSqrtD
                (factorLeadingPCEigenvalues (r := r)
                  (factorSampleCovariance_isHermitian (X i)) hcard)) (X i row)) ∧
        FactorLeastSquaresNormalizedMinimizer (X i)
          (factorLoadingEstimator
            (factorLeadingPCEigenvectors (r := r)
              (factorSampleCovariance_isHermitian (X i)) hcard)
            (factorPCDiagonalSqrtD
              (factorLeadingPCEigenvalues (r := r)
                (factorSampleCovariance_isHermitian (X i)) hcard)))
          (fun row =>
            factorScoreEstimator
              (factorLeadingPCEigenvectors (r := r)
                (factorSampleCovariance_isHermitian (X i)) hcard)
              (factorPCDiagonalInvSqrtD
                (factorLeadingPCEigenvalues (r := r)
                  (factorSampleCovariance_isHermitian (X i)) hcard)) (X i row)) ∧
        ∃ B : ℝ, 0 ≤ B ∧ ∀ x : k → ℝ,
          x ⬝ᵥ ((Ψ i) *ᵥ x) ≤ B * (x ⬝ᵥ x)) l := by
  filter_upwards [
    factorPCTheorem11_9_eventually_of_approxFactorAssumption11_1NormalizedRayleighBridge
      hcard X Λ F U Ψ h,
    factorPCTheorem11_9_jointLS_eventually_of_approxFactorAssumption11_1NormalizedRayleighBridge
      hcard hcardObs X Λ F U Ψ h,
    ApproximateFactorAssumptionNormalizedRayleighBridge.eventually_scoreVariance_bound h
  ] with _ hpc hjoint hvar
  exact ⟨hpc, hjoint, hvar⟩

set_option linter.style.longLine false in
omit [DecidableEq n] in
/-- Hansen Theorem 11.9 combined asymptotic endpoint from Assumption 11.1 plus
the normalized-Rayleigh primitive, with the observation-count side condition
derived internally. -/
theorem
    factorPCTheorem11_9_with_jointLS_and_scoreVariance_eventually_of_approxFactorAssumption11_1NormalizedRayleighBridge_only
    [Nonempty n] {ι : Type*} {l : Filter ι}
    (hcard : Fintype.card r ≤ Fintype.card k)
    (X : ι → n → k → ℝ) (Λ : ι → Matrix k r ℝ)
    (F : ι → n → r → ℝ) (U : ι → Matrix n k ℝ)
    (Ψ : ι → Matrix k k ℝ)
    (h : ApproximateFactorAssumptionNormalizedRayleighBridge l X Λ F U Ψ) :
    Filter.Eventually
      (fun i =>
        FactorPCTheorem11_9 (factorSampleCovariance (X i))
          (factorLeadingPCEigenvectors (r := r)
            (factorSampleCovariance_isHermitian (X i)) hcard)
          (Matrix.diagonal
            (factorLeadingPCEigenvalues (r := r)
              (factorSampleCovariance_isHermitian (X i)) hcard))
          (factorPCDiagonalSqrtD
            (factorLeadingPCEigenvalues (r := r)
              (factorSampleCovariance_isHermitian (X i)) hcard))
          (factorPCDiagonalInvSqrtD
            (factorLeadingPCEigenvalues (r := r)
              (factorSampleCovariance_isHermitian (X i)) hcard))
          (factorLoadingEstimator
            (factorLeadingPCEigenvectors (r := r)
              (factorSampleCovariance_isHermitian (X i)) hcard)
            (factorPCDiagonalSqrtD
              (factorLeadingPCEigenvalues (r := r)
                (factorSampleCovariance_isHermitian (X i)) hcard)))
          (X i)
          (fun row =>
            factorScoreEstimator
              (factorLeadingPCEigenvectors (r := r)
                (factorSampleCovariance_isHermitian (X i)) hcard)
              (factorPCDiagonalInvSqrtD
                (factorLeadingPCEigenvalues (r := r)
                  (factorSampleCovariance_isHermitian (X i)) hcard)) (X i row)) ∧
        FactorLeastSquaresNormalizedMinimizer (X i)
          (factorLoadingEstimator
            (factorLeadingPCEigenvectors (r := r)
              (factorSampleCovariance_isHermitian (X i)) hcard)
            (factorPCDiagonalSqrtD
              (factorLeadingPCEigenvalues (r := r)
                (factorSampleCovariance_isHermitian (X i)) hcard)))
          (fun row =>
            factorScoreEstimator
              (factorLeadingPCEigenvectors (r := r)
                (factorSampleCovariance_isHermitian (X i)) hcard)
              (factorPCDiagonalInvSqrtD
                (factorLeadingPCEigenvalues (r := r)
                  (factorSampleCovariance_isHermitian (X i)) hcard)) (X i row)) ∧
        ∃ B : ℝ, 0 ≤ B ∧ ∀ x : k → ℝ,
          x ⬝ᵥ ((Ψ i) *ᵥ x) ≤ B * (x ⬝ᵥ x)) l := by
  filter_upwards [
    factorPCTheorem11_9_eventually_of_approxFactorAssumption11_1NormalizedRayleighBridge
      hcard X Λ F U Ψ h,
    factorPCTheorem11_9_jointLS_eventually_of_approxFactorAssumption11_1NormalizedRayleighBridge_only
      hcard X Λ F U Ψ h,
    ApproximateFactorAssumptionNormalizedRayleighBridge.eventually_scoreVariance_bound h
  ] with _ hpc hjoint hvar
  exact ⟨hpc, hjoint, hvar⟩

set_option linter.style.longLine false in
omit [DecidableEq n] in
/-- Hansen Theorem 11.9 eventually follows from Assumption 11.1 plus a single
whole-matrix WLLN for the normalized recovered idiosyncratic perturbation. -/
theorem factorPCTheorem11_9_eventually_of_approxFactorAssumption11_1MatrixWLLNBridge
    [Nonempty n] {ι : Type*} {l : Filter ι}
    (hcard : Fintype.card r ≤ Fintype.card k)
    (X : ι → n → k → ℝ) (Λ : ι → Matrix k r ℝ)
    (F : ι → n → r → ℝ) (U : ι → Matrix n k ℝ)
    (Ψ : ι → Matrix k k ℝ)
    (h : ApproximateFactorAssumptionMatrixWLLNBridge l X Λ F U Ψ) :
    Filter.Eventually
      (fun i =>
        FactorPCTheorem11_9 (factorSampleCovariance (X i))
          (factorLeadingPCEigenvectors (r := r)
            (factorSampleCovariance_isHermitian (X i)) hcard)
          (Matrix.diagonal
            (factorLeadingPCEigenvalues (r := r)
              (factorSampleCovariance_isHermitian (X i)) hcard))
          (factorPCDiagonalSqrtD
            (factorLeadingPCEigenvalues (r := r)
              (factorSampleCovariance_isHermitian (X i)) hcard))
          (factorPCDiagonalInvSqrtD
            (factorLeadingPCEigenvalues (r := r)
              (factorSampleCovariance_isHermitian (X i)) hcard))
          (factorLoadingEstimator
            (factorLeadingPCEigenvectors (r := r)
              (factorSampleCovariance_isHermitian (X i)) hcard)
            (factorPCDiagonalSqrtD
              (factorLeadingPCEigenvalues (r := r)
                (factorSampleCovariance_isHermitian (X i)) hcard)))
          (X i)
          (fun row =>
            factorScoreEstimator
              (factorLeadingPCEigenvectors (r := r)
                (factorSampleCovariance_isHermitian (X i)) hcard)
              (factorPCDiagonalInvSqrtD
                (factorLeadingPCEigenvalues (r := r)
                  (factorSampleCovariance_isHermitian (X i)) hcard)) (X i row))) l :=
  factorPCTheorem11_9_eventually_of_approxFactorAssumption11_1NormalizedRayleighBridge
    hcard X Λ F U Ψ
    (ApproximateFactorAssumptionMatrixWLLNBridge.toNormalizedRayleighAssumptionBridge h)

set_option linter.style.longLine false in
omit [DecidableEq n] in
/-- Hansen Theorem 11.9 normalized joint least-squares minimizer eventually
follows from Assumption 11.1 plus a single whole-matrix WLLN for the normalized
recovered idiosyncratic perturbation. -/
theorem factorPCTheorem11_9_jointLS_eventually_of_approxFactorAssumption11_1MatrixWLLNBridge
    [Nonempty n] {ι : Type*} {l : Filter ι}
    (hcard : Fintype.card r ≤ Fintype.card k)
    (hcardObs : Fintype.card r ≤ Fintype.card n)
    (X : ι → n → k → ℝ) (Λ : ι → Matrix k r ℝ)
    (F : ι → n → r → ℝ) (U : ι → Matrix n k ℝ)
    (Ψ : ι → Matrix k k ℝ)
    (h : ApproximateFactorAssumptionMatrixWLLNBridge l X Λ F U Ψ) :
    Filter.Eventually
      (fun i =>
        FactorLeastSquaresNormalizedMinimizer (X i)
          (factorLoadingEstimator
            (factorLeadingPCEigenvectors (r := r)
              (factorSampleCovariance_isHermitian (X i)) hcard)
            (factorPCDiagonalSqrtD
              (factorLeadingPCEigenvalues (r := r)
                (factorSampleCovariance_isHermitian (X i)) hcard)))
          (fun row =>
            factorScoreEstimator
              (factorLeadingPCEigenvectors (r := r)
                (factorSampleCovariance_isHermitian (X i)) hcard)
              (factorPCDiagonalInvSqrtD
                (factorLeadingPCEigenvalues (r := r)
                  (factorSampleCovariance_isHermitian (X i)) hcard)) (X i row))) l :=
  factorPCTheorem11_9_jointLS_eventually_of_approxFactorAssumption11_1NormalizedRayleighBridge
    hcard hcardObs X Λ F U Ψ
    (ApproximateFactorAssumptionMatrixWLLNBridge.toNormalizedRayleighAssumptionBridge h)

set_option linter.style.longLine false in
omit [DecidableEq n] in
/-- Hansen Theorem 11.9 eventually follows from Assumption 11.1 plus raw
cross/noise moment WLLNs after deterministic loading-Gram recovery. -/
theorem factorPCTheorem11_9_eventually_of_approxFactorAssumption11_1RawMomentMatrixWLLNBridge
    [Nonempty n] {ι : Type*} {l : Filter ι}
    (hcard : Fintype.card r ≤ Fintype.card k)
    (X : ι → n → k → ℝ) (Λ : ι → Matrix k r ℝ)
    (F : ι → n → r → ℝ) (U : ι → Matrix n k ℝ)
    (Ψ : ι → Matrix k k ℝ)
    (h : ApproximateFactorAssumptionRawMomentMatrixWLLNBridge l X Λ F U Ψ) :
    Filter.Eventually
      (fun i =>
        FactorPCTheorem11_9 (factorSampleCovariance (X i))
          (factorLeadingPCEigenvectors (r := r)
            (factorSampleCovariance_isHermitian (X i)) hcard)
          (Matrix.diagonal
            (factorLeadingPCEigenvalues (r := r)
              (factorSampleCovariance_isHermitian (X i)) hcard))
          (factorPCDiagonalSqrtD
            (factorLeadingPCEigenvalues (r := r)
              (factorSampleCovariance_isHermitian (X i)) hcard))
          (factorPCDiagonalInvSqrtD
            (factorLeadingPCEigenvalues (r := r)
              (factorSampleCovariance_isHermitian (X i)) hcard))
          (factorLoadingEstimator
            (factorLeadingPCEigenvectors (r := r)
              (factorSampleCovariance_isHermitian (X i)) hcard)
            (factorPCDiagonalSqrtD
              (factorLeadingPCEigenvalues (r := r)
                (factorSampleCovariance_isHermitian (X i)) hcard)))
          (X i)
          (fun row =>
            factorScoreEstimator
              (factorLeadingPCEigenvectors (r := r)
                (factorSampleCovariance_isHermitian (X i)) hcard)
              (factorPCDiagonalInvSqrtD
                (factorLeadingPCEigenvalues (r := r)
                  (factorSampleCovariance_isHermitian (X i)) hcard)) (X i row))) l :=
  factorPCTheorem11_9_eventually_of_approxFactorAssumption11_1MatrixWLLNBridge
    hcard X Λ F U Ψ
    (ApproximateFactorAssumptionRawMomentMatrixWLLNBridge.toMatrixWLLNAssumptionBridge h)

set_option linter.style.longLine false in
omit [DecidableEq n] in
/-- Hansen Theorem 11.9 normalized joint least-squares minimizer eventually
follows from Assumption 11.1 plus raw cross/noise moment WLLNs after
deterministic loading-Gram recovery. -/
theorem factorPCTheorem11_9_jointLS_eventually_of_approxFactorAssumption11_1RawMomentMatrixWLLNBridge
    [Nonempty n] {ι : Type*} {l : Filter ι}
    (hcard : Fintype.card r ≤ Fintype.card k)
    (hcardObs : Fintype.card r ≤ Fintype.card n)
    (X : ι → n → k → ℝ) (Λ : ι → Matrix k r ℝ)
    (F : ι → n → r → ℝ) (U : ι → Matrix n k ℝ)
    (Ψ : ι → Matrix k k ℝ)
    (h : ApproximateFactorAssumptionRawMomentMatrixWLLNBridge l X Λ F U Ψ) :
    Filter.Eventually
      (fun i =>
        FactorLeastSquaresNormalizedMinimizer (X i)
          (factorLoadingEstimator
            (factorLeadingPCEigenvectors (r := r)
              (factorSampleCovariance_isHermitian (X i)) hcard)
            (factorPCDiagonalSqrtD
              (factorLeadingPCEigenvalues (r := r)
                (factorSampleCovariance_isHermitian (X i)) hcard)))
          (fun row =>
            factorScoreEstimator
              (factorLeadingPCEigenvectors (r := r)
                (factorSampleCovariance_isHermitian (X i)) hcard)
              (factorPCDiagonalInvSqrtD
                (factorLeadingPCEigenvalues (r := r)
                  (factorSampleCovariance_isHermitian (X i)) hcard)) (X i row))) l :=
  factorPCTheorem11_9_jointLS_eventually_of_approxFactorAssumption11_1MatrixWLLNBridge
    hcard hcardObs X Λ F U Ψ
    (ApproximateFactorAssumptionRawMomentMatrixWLLNBridge.toMatrixWLLNAssumptionBridge h)

set_option linter.style.longLine false in
omit [DecidableEq n] in
/-- Hansen Theorem 11.9 eventually follows from Assumption 11.1 plus
unrecovered raw moment WLLNs and loading-recoverer shrinkage.

This is the narrower Hansen-facing route below the recovered raw-moment facade:
the caller supplies WLLNs for `n⁻¹F'U`, `n⁻¹U'F`, and centered `n⁻¹U'U - Ψ`,
plus convergence of `Ψ` and `(Λ'Λ)^{-1}Λ' -> 0`. The recovered raw moment
WLLNs are then derived deterministically. -/
theorem factorPCTheorem11_9_eventually_of_approxFactorAssumption11_1UnrecoveredMomentWLLNBridge
    [Nonempty n] {ι : Type*} {l : Filter ι}
    (hcard : Fintype.card r ≤ Fintype.card k)
    (X : ι → n → k → ℝ) (Λ : ι → Matrix k r ℝ)
    (F : ι → n → r → ℝ) (U : ι → Matrix n k ℝ)
    (Ψ : ι → Matrix k k ℝ) (Ψlim : Matrix k k ℝ)
    (h : ApproximateFactorAssumptionUnrecoveredMomentWLLNBridge
      l X Λ F U Ψ Ψlim) :
    Filter.Eventually
      (fun i =>
        FactorPCTheorem11_9 (factorSampleCovariance (X i))
          (factorLeadingPCEigenvectors (r := r)
            (factorSampleCovariance_isHermitian (X i)) hcard)
          (Matrix.diagonal
            (factorLeadingPCEigenvalues (r := r)
              (factorSampleCovariance_isHermitian (X i)) hcard))
          (factorPCDiagonalSqrtD
            (factorLeadingPCEigenvalues (r := r)
              (factorSampleCovariance_isHermitian (X i)) hcard))
          (factorPCDiagonalInvSqrtD
            (factorLeadingPCEigenvalues (r := r)
              (factorSampleCovariance_isHermitian (X i)) hcard))
          (factorLoadingEstimator
            (factorLeadingPCEigenvectors (r := r)
              (factorSampleCovariance_isHermitian (X i)) hcard)
            (factorPCDiagonalSqrtD
              (factorLeadingPCEigenvalues (r := r)
                (factorSampleCovariance_isHermitian (X i)) hcard)))
          (X i)
          (fun row =>
            factorScoreEstimator
              (factorLeadingPCEigenvectors (r := r)
                (factorSampleCovariance_isHermitian (X i)) hcard)
              (factorPCDiagonalInvSqrtD
                (factorLeadingPCEigenvalues (r := r)
                  (factorSampleCovariance_isHermitian (X i)) hcard)) (X i row))) l :=
  factorPCTheorem11_9_eventually_of_approxFactorAssumption11_1RawMomentMatrixWLLNBridge
    hcard X Λ F U Ψ
    (ApproximateFactorAssumptionUnrecoveredMomentWLLNBridge.toRawMomentMatrixWLLNBridge h)

set_option linter.style.longLine false in
omit [DecidableEq n] in
/-- Hansen Theorem 11.9 normalized joint least-squares minimizer eventually
follows from Assumption 11.1 plus unrecovered raw moment WLLNs and
loading-recoverer shrinkage. -/
theorem factorPCTheorem11_9_jointLS_eventually_of_approxFactorAssumption11_1UnrecoveredMomentWLLNBridge
    [Nonempty n] {ι : Type*} {l : Filter ι}
    (hcard : Fintype.card r ≤ Fintype.card k)
    (hcardObs : Fintype.card r ≤ Fintype.card n)
    (X : ι → n → k → ℝ) (Λ : ι → Matrix k r ℝ)
    (F : ι → n → r → ℝ) (U : ι → Matrix n k ℝ)
    (Ψ : ι → Matrix k k ℝ) (Ψlim : Matrix k k ℝ)
    (h : ApproximateFactorAssumptionUnrecoveredMomentWLLNBridge
      l X Λ F U Ψ Ψlim) :
    Filter.Eventually
      (fun i =>
        FactorLeastSquaresNormalizedMinimizer (X i)
          (factorLoadingEstimator
            (factorLeadingPCEigenvectors (r := r)
              (factorSampleCovariance_isHermitian (X i)) hcard)
            (factorPCDiagonalSqrtD
              (factorLeadingPCEigenvalues (r := r)
                (factorSampleCovariance_isHermitian (X i)) hcard)))
          (fun row =>
            factorScoreEstimator
              (factorLeadingPCEigenvectors (r := r)
                (factorSampleCovariance_isHermitian (X i)) hcard)
              (factorPCDiagonalInvSqrtD
                (factorLeadingPCEigenvalues (r := r)
                  (factorSampleCovariance_isHermitian (X i)) hcard)) (X i row))) l :=
  factorPCTheorem11_9_jointLS_eventually_of_approxFactorAssumption11_1RawMomentMatrixWLLNBridge
    hcard hcardObs X Λ F U Ψ
    (ApproximateFactorAssumptionUnrecoveredMomentWLLNBridge.toRawMomentMatrixWLLNBridge h)

set_option linter.style.longLine false in
omit [DecidableEq n] in
/-- Hansen Theorem 11.9 eventually follows from Assumption 11.1 plus entrywise
unrecovered raw moment WLLNs and entrywise loading-recoverer shrinkage.

This scalar-coordinate facade is closer to Hansen's proof obligations than the
matrix unrecovered-moment route: the caller proves entrywise limits for
`(Λ'Λ)^{-1}Λ'`, `Ψ`, `n⁻¹F'U`, `n⁻¹U'F`, and centered `n⁻¹U'U - Ψ`; finite
dimensionality upgrades them to the matrix bridge already used by the PCA
theorem. -/
theorem factorPCTheorem11_9_eventually_of_approxFactorAssumption11_1UnrecoveredEntrywiseWLLNBridge
    [Nonempty n] {ι : Type*} {l : Filter ι}
    (hcard : Fintype.card r ≤ Fintype.card k)
    (X : ι → n → k → ℝ) (Λ : ι → Matrix k r ℝ)
    (F : ι → n → r → ℝ) (U : ι → Matrix n k ℝ)
    (Ψ : ι → Matrix k k ℝ) (Ψlim : Matrix k k ℝ)
    (h : ApproximateFactorAssumptionUnrecoveredEntrywiseWLLNBridge
      l X Λ F U Ψ Ψlim) :
    Filter.Eventually
      (fun i =>
        FactorPCTheorem11_9 (factorSampleCovariance (X i))
          (factorLeadingPCEigenvectors (r := r)
            (factorSampleCovariance_isHermitian (X i)) hcard)
          (Matrix.diagonal
            (factorLeadingPCEigenvalues (r := r)
              (factorSampleCovariance_isHermitian (X i)) hcard))
          (factorPCDiagonalSqrtD
            (factorLeadingPCEigenvalues (r := r)
              (factorSampleCovariance_isHermitian (X i)) hcard))
          (factorPCDiagonalInvSqrtD
            (factorLeadingPCEigenvalues (r := r)
              (factorSampleCovariance_isHermitian (X i)) hcard))
          (factorLoadingEstimator
            (factorLeadingPCEigenvectors (r := r)
              (factorSampleCovariance_isHermitian (X i)) hcard)
            (factorPCDiagonalSqrtD
              (factorLeadingPCEigenvalues (r := r)
                (factorSampleCovariance_isHermitian (X i)) hcard)))
          (X i)
          (fun row =>
            factorScoreEstimator
              (factorLeadingPCEigenvectors (r := r)
                (factorSampleCovariance_isHermitian (X i)) hcard)
              (factorPCDiagonalInvSqrtD
                (factorLeadingPCEigenvalues (r := r)
                  (factorSampleCovariance_isHermitian (X i)) hcard)) (X i row))) l :=
  factorPCTheorem11_9_eventually_of_approxFactorAssumption11_1UnrecoveredMomentWLLNBridge
    hcard X Λ F U Ψ Ψlim
    (ApproximateFactorAssumptionUnrecoveredEntrywiseWLLNBridge.toUnrecoveredMomentWLLNBridge h)

set_option linter.style.longLine false in
omit [DecidableEq n] in
/-- Hansen Theorem 11.9 normalized joint least-squares minimizer eventually
follows from Assumption 11.1 plus entrywise unrecovered raw moment WLLNs and
entrywise loading-recoverer shrinkage. -/
theorem factorPCTheorem11_9_jointLS_eventually_of_approxFactorAssumption11_1UnrecoveredEntrywiseWLLNBridge
    [Nonempty n] {ι : Type*} {l : Filter ι}
    (hcard : Fintype.card r ≤ Fintype.card k)
    (hcardObs : Fintype.card r ≤ Fintype.card n)
    (X : ι → n → k → ℝ) (Λ : ι → Matrix k r ℝ)
    (F : ι → n → r → ℝ) (U : ι → Matrix n k ℝ)
    (Ψ : ι → Matrix k k ℝ) (Ψlim : Matrix k k ℝ)
    (h : ApproximateFactorAssumptionUnrecoveredEntrywiseWLLNBridge
      l X Λ F U Ψ Ψlim) :
    Filter.Eventually
      (fun i =>
        FactorLeastSquaresNormalizedMinimizer (X i)
          (factorLoadingEstimator
            (factorLeadingPCEigenvectors (r := r)
              (factorSampleCovariance_isHermitian (X i)) hcard)
            (factorPCDiagonalSqrtD
              (factorLeadingPCEigenvalues (r := r)
                (factorSampleCovariance_isHermitian (X i)) hcard)))
          (fun row =>
            factorScoreEstimator
              (factorLeadingPCEigenvectors (r := r)
                (factorSampleCovariance_isHermitian (X i)) hcard)
              (factorPCDiagonalInvSqrtD
                (factorLeadingPCEigenvalues (r := r)
                  (factorSampleCovariance_isHermitian (X i)) hcard)) (X i row))) l :=
  factorPCTheorem11_9_jointLS_eventually_of_approxFactorAssumption11_1UnrecoveredMomentWLLNBridge
    hcard hcardObs X Λ F U Ψ Ψlim
    (ApproximateFactorAssumptionUnrecoveredEntrywiseWLLNBridge.toUnrecoveredMomentWLLNBridge h)

set_option linter.style.longLine false in
omit [DecidableEq n] in
/-- Hansen Theorem 11.9 eventually follows from Assumption 11.1 plus
envelope-controlled unrecovered raw moment WLLNs.

This narrows the entrywise-unrecovered route by allowing the probability proof
to provide one scalar envelope for each primitive matrix family:
`(Λ'Λ)^{-1}Λ'`, `Ψ`, `n⁻¹F'U`, `n⁻¹U'F`, and centered `n⁻¹U'U - Ψ`. -/
theorem factorPCTheorem11_9_eventually_of_approxFactorAssumption11_1UnrecoveredEntrywiseEnvelopeWLLNBridge
    [Nonempty n] {ι : Type*} {l : Filter ι}
    (hcard : Fintype.card r ≤ Fintype.card k)
    (X : ι → n → k → ℝ) (Λ : ι → Matrix k r ℝ)
    (F : ι → n → r → ℝ) (U : ι → Matrix n k ℝ)
    (Ψ : ι → Matrix k k ℝ) (Ψlim : Matrix k k ℝ)
    (ρL ρΨ ρFU ρUF ρUU : ι → ℝ)
    (h : ApproximateFactorAssumptionUnrecoveredEntrywiseEnvelopeWLLNBridge
      l X Λ F U Ψ Ψlim ρL ρΨ ρFU ρUF ρUU) :
    Filter.Eventually
      (fun i =>
        FactorPCTheorem11_9 (factorSampleCovariance (X i))
          (factorLeadingPCEigenvectors (r := r)
            (factorSampleCovariance_isHermitian (X i)) hcard)
          (Matrix.diagonal
            (factorLeadingPCEigenvalues (r := r)
              (factorSampleCovariance_isHermitian (X i)) hcard))
          (factorPCDiagonalSqrtD
            (factorLeadingPCEigenvalues (r := r)
              (factorSampleCovariance_isHermitian (X i)) hcard))
          (factorPCDiagonalInvSqrtD
            (factorLeadingPCEigenvalues (r := r)
              (factorSampleCovariance_isHermitian (X i)) hcard))
          (factorLoadingEstimator
            (factorLeadingPCEigenvectors (r := r)
              (factorSampleCovariance_isHermitian (X i)) hcard)
            (factorPCDiagonalSqrtD
              (factorLeadingPCEigenvalues (r := r)
                (factorSampleCovariance_isHermitian (X i)) hcard)))
          (X i)
          (fun row =>
            factorScoreEstimator
              (factorLeadingPCEigenvectors (r := r)
                (factorSampleCovariance_isHermitian (X i)) hcard)
              (factorPCDiagonalInvSqrtD
                (factorLeadingPCEigenvalues (r := r)
                  (factorSampleCovariance_isHermitian (X i)) hcard)) (X i row))) l :=
  factorPCTheorem11_9_eventually_of_approxFactorAssumption11_1UnrecoveredEntrywiseWLLNBridge
    hcard X Λ F U Ψ Ψlim
    (ApproximateFactorAssumptionUnrecoveredEntrywiseEnvelopeWLLNBridge.toUnrecoveredEntrywiseWLLNBridge h)

set_option linter.style.longLine false in
omit [DecidableEq n] in
/-- Hansen Theorem 11.9 normalized joint least-squares minimizer eventually
follows from Assumption 11.1 plus envelope-controlled unrecovered raw moment
WLLNs. -/
theorem factorPCTheorem11_9_jointLS_eventually_of_approxFactorAssumption11_1UnrecoveredEntrywiseEnvelopeWLLNBridge
    [Nonempty n] {ι : Type*} {l : Filter ι}
    (hcard : Fintype.card r ≤ Fintype.card k)
    (hcardObs : Fintype.card r ≤ Fintype.card n)
    (X : ι → n → k → ℝ) (Λ : ι → Matrix k r ℝ)
    (F : ι → n → r → ℝ) (U : ι → Matrix n k ℝ)
    (Ψ : ι → Matrix k k ℝ) (Ψlim : Matrix k k ℝ)
    (ρL ρΨ ρFU ρUF ρUU : ι → ℝ)
    (h : ApproximateFactorAssumptionUnrecoveredEntrywiseEnvelopeWLLNBridge
      l X Λ F U Ψ Ψlim ρL ρΨ ρFU ρUF ρUU) :
    Filter.Eventually
      (fun i =>
        FactorLeastSquaresNormalizedMinimizer (X i)
          (factorLoadingEstimator
            (factorLeadingPCEigenvectors (r := r)
              (factorSampleCovariance_isHermitian (X i)) hcard)
            (factorPCDiagonalSqrtD
              (factorLeadingPCEigenvalues (r := r)
                (factorSampleCovariance_isHermitian (X i)) hcard)))
          (fun row =>
            factorScoreEstimator
              (factorLeadingPCEigenvectors (r := r)
                (factorSampleCovariance_isHermitian (X i)) hcard)
              (factorPCDiagonalInvSqrtD
                (factorLeadingPCEigenvalues (r := r)
                  (factorSampleCovariance_isHermitian (X i)) hcard)) (X i row))) l :=
  factorPCTheorem11_9_jointLS_eventually_of_approxFactorAssumption11_1UnrecoveredEntrywiseWLLNBridge
    hcard hcardObs X Λ F U Ψ Ψlim
    (ApproximateFactorAssumptionUnrecoveredEntrywiseEnvelopeWLLNBridge.toUnrecoveredEntrywiseWLLNBridge h)

set_option linter.style.longLine false in
omit [DecidableEq n] in
/-- Hansen Theorem 11.9 eventually follows from Assumption 11.1 plus
inverse-loading-envelope unrecovered raw moment WLLNs.

This is the theorem-facing endpoint for the Hansen-style route where the
loading-recoverer envelope is derived from bounds on `(Λ'Λ)⁻¹`, `Λ`, and
`(# factors)ρInvρΛ → 0`, rather than supplied directly. -/
theorem factorPCTheorem11_9_eventually_of_approxFactorAssumption11_1UnrecoveredInverseLoadingEnvelopeWLLNBridge
    [Nonempty n] {ι : Type*} {l : Filter ι}
    (hcard : Fintype.card r ≤ Fintype.card k)
    (X : ι → n → k → ℝ) (Λ : ι → Matrix k r ℝ)
    (F : ι → n → r → ℝ) (U : ι → Matrix n k ℝ)
    (Ψ : ι → Matrix k k ℝ) (Ψlim : Matrix k k ℝ)
    (ρInv ρΛ ρΨ ρFU ρUF ρUU : ι → ℝ)
    (h : ApproximateFactorAssumptionUnrecoveredInverseLoadingEnvelopeWLLNBridge
      l X Λ F U Ψ Ψlim ρInv ρΛ ρΨ ρFU ρUF ρUU) :
    Filter.Eventually
      (fun i =>
        FactorPCTheorem11_9 (factorSampleCovariance (X i))
          (factorLeadingPCEigenvectors (r := r)
            (factorSampleCovariance_isHermitian (X i)) hcard)
          (Matrix.diagonal
            (factorLeadingPCEigenvalues (r := r)
              (factorSampleCovariance_isHermitian (X i)) hcard))
          (factorPCDiagonalSqrtD
            (factorLeadingPCEigenvalues (r := r)
              (factorSampleCovariance_isHermitian (X i)) hcard))
          (factorPCDiagonalInvSqrtD
            (factorLeadingPCEigenvalues (r := r)
              (factorSampleCovariance_isHermitian (X i)) hcard))
          (factorLoadingEstimator
            (factorLeadingPCEigenvectors (r := r)
              (factorSampleCovariance_isHermitian (X i)) hcard)
            (factorPCDiagonalSqrtD
              (factorLeadingPCEigenvalues (r := r)
                (factorSampleCovariance_isHermitian (X i)) hcard)))
          (X i)
          (fun row =>
            factorScoreEstimator
              (factorLeadingPCEigenvectors (r := r)
                (factorSampleCovariance_isHermitian (X i)) hcard)
              (factorPCDiagonalInvSqrtD
                (factorLeadingPCEigenvalues (r := r)
                  (factorSampleCovariance_isHermitian (X i)) hcard)) (X i row))) l :=
  factorPCTheorem11_9_eventually_of_approxFactorAssumption11_1UnrecoveredEntrywiseWLLNBridge
    hcard X Λ F U Ψ Ψlim
    (ApproximateFactorAssumptionUnrecoveredInverseLoadingEnvelopeWLLNBridge.toUnrecoveredEntrywiseWLLNBridge h)

set_option linter.style.longLine false in
omit [DecidableEq n] in
/-- Hansen Theorem 11.9 normalized joint least-squares minimizer eventually
follows from the inverse-loading-envelope unrecovered raw moment route. -/
theorem factorPCTheorem11_9_jointLS_eventually_of_approxFactorAssumption11_1UnrecoveredInverseLoadingEnvelopeWLLNBridge
    [Nonempty n] {ι : Type*} {l : Filter ι}
    (hcard : Fintype.card r ≤ Fintype.card k)
    (hcardObs : Fintype.card r ≤ Fintype.card n)
    (X : ι → n → k → ℝ) (Λ : ι → Matrix k r ℝ)
    (F : ι → n → r → ℝ) (U : ι → Matrix n k ℝ)
    (Ψ : ι → Matrix k k ℝ) (Ψlim : Matrix k k ℝ)
    (ρInv ρΛ ρΨ ρFU ρUF ρUU : ι → ℝ)
    (h : ApproximateFactorAssumptionUnrecoveredInverseLoadingEnvelopeWLLNBridge
      l X Λ F U Ψ Ψlim ρInv ρΛ ρΨ ρFU ρUF ρUU) :
    Filter.Eventually
      (fun i =>
        FactorLeastSquaresNormalizedMinimizer (X i)
          (factorLoadingEstimator
            (factorLeadingPCEigenvectors (r := r)
              (factorSampleCovariance_isHermitian (X i)) hcard)
            (factorPCDiagonalSqrtD
              (factorLeadingPCEigenvalues (r := r)
                (factorSampleCovariance_isHermitian (X i)) hcard)))
          (fun row =>
            factorScoreEstimator
              (factorLeadingPCEigenvectors (r := r)
                (factorSampleCovariance_isHermitian (X i)) hcard)
              (factorPCDiagonalInvSqrtD
                (factorLeadingPCEigenvalues (r := r)
                  (factorSampleCovariance_isHermitian (X i)) hcard)) (X i row))) l :=
  factorPCTheorem11_9_jointLS_eventually_of_approxFactorAssumption11_1UnrecoveredEntrywiseWLLNBridge
    hcard hcardObs X Λ F U Ψ Ψlim
    (ApproximateFactorAssumptionUnrecoveredInverseLoadingEnvelopeWLLNBridge.toUnrecoveredEntrywiseWLLNBridge h)

set_option linter.style.longLine false in
omit [DecidableEq n] in
/-- Hansen Theorem 11.9 combined asymptotic endpoint for the inverse-loading
envelope route. It exposes the PCA formula, literal normalized joint-LS
minimizer, and bounded score-variance conclusion from the same primitive
Hansen-style envelope assumptions. -/
theorem factorPCTheorem11_9_with_jointLS_and_scoreVariance_eventually_of_approxFactorAssumption11_1UnrecoveredInverseLoadingEnvelopeWLLNBridge
    [Nonempty n] {ι : Type*} {l : Filter ι}
    (hcard : Fintype.card r ≤ Fintype.card k)
    (hcardObs : Fintype.card r ≤ Fintype.card n)
    (X : ι → n → k → ℝ) (Λ : ι → Matrix k r ℝ)
    (F : ι → n → r → ℝ) (U : ι → Matrix n k ℝ)
    (Ψ : ι → Matrix k k ℝ) (Ψlim : Matrix k k ℝ)
    (ρInv ρΛ ρΨ ρFU ρUF ρUU : ι → ℝ)
    (h : ApproximateFactorAssumptionUnrecoveredInverseLoadingEnvelopeWLLNBridge
      l X Λ F U Ψ Ψlim ρInv ρΛ ρΨ ρFU ρUF ρUU) :
    Filter.Eventually
      (fun i =>
        FactorPCTheorem11_9 (factorSampleCovariance (X i))
          (factorLeadingPCEigenvectors (r := r)
            (factorSampleCovariance_isHermitian (X i)) hcard)
          (Matrix.diagonal
            (factorLeadingPCEigenvalues (r := r)
              (factorSampleCovariance_isHermitian (X i)) hcard))
          (factorPCDiagonalSqrtD
            (factorLeadingPCEigenvalues (r := r)
              (factorSampleCovariance_isHermitian (X i)) hcard))
          (factorPCDiagonalInvSqrtD
            (factorLeadingPCEigenvalues (r := r)
              (factorSampleCovariance_isHermitian (X i)) hcard))
          (factorLoadingEstimator
            (factorLeadingPCEigenvectors (r := r)
              (factorSampleCovariance_isHermitian (X i)) hcard)
            (factorPCDiagonalSqrtD
              (factorLeadingPCEigenvalues (r := r)
                (factorSampleCovariance_isHermitian (X i)) hcard)))
          (X i)
          (fun row =>
            factorScoreEstimator
              (factorLeadingPCEigenvectors (r := r)
                (factorSampleCovariance_isHermitian (X i)) hcard)
              (factorPCDiagonalInvSqrtD
                (factorLeadingPCEigenvalues (r := r)
                  (factorSampleCovariance_isHermitian (X i)) hcard)) (X i row)) ∧
        FactorLeastSquaresNormalizedMinimizer (X i)
          (factorLoadingEstimator
            (factorLeadingPCEigenvectors (r := r)
              (factorSampleCovariance_isHermitian (X i)) hcard)
            (factorPCDiagonalSqrtD
              (factorLeadingPCEigenvalues (r := r)
                (factorSampleCovariance_isHermitian (X i)) hcard)))
          (fun row =>
            factorScoreEstimator
              (factorLeadingPCEigenvectors (r := r)
                (factorSampleCovariance_isHermitian (X i)) hcard)
              (factorPCDiagonalInvSqrtD
                (factorLeadingPCEigenvalues (r := r)
                  (factorSampleCovariance_isHermitian (X i)) hcard)) (X i row)) ∧
        ∃ B : ℝ, 0 ≤ B ∧ ∀ x : k → ℝ,
          x ⬝ᵥ ((Ψ i) *ᵥ x) ≤ B * (x ⬝ᵥ x)) l :=
  factorPCTheorem11_9_with_jointLS_and_scoreVariance_eventually_of_approxFactorAssumption11_1NormalizedRayleighBridge
    hcard hcardObs X Λ F U Ψ
    (ApproximateFactorAssumptionUnrecoveredInverseLoadingEnvelopeWLLNBridge.toNormalizedRayleighAssumptionBridge h)

set_option linter.style.longLine false in
omit [DecidableEq n] in
/-- Hansen Theorem 11.9 combined asymptotic endpoint for the whole-matrix WLLN
route. It exposes the PCA formula, literal normalized joint-LS minimizer, and
bounded score-variance conclusion from the same Assumption 11.1 WLLN package. -/
theorem factorPCTheorem11_9_with_jointLS_and_scoreVariance_eventually_of_approxFactorAssumption11_1MatrixWLLNBridge
    [Nonempty n] {ι : Type*} {l : Filter ι}
    (hcard : Fintype.card r ≤ Fintype.card k)
    (hcardObs : Fintype.card r ≤ Fintype.card n)
    (X : ι → n → k → ℝ) (Λ : ι → Matrix k r ℝ)
    (F : ι → n → r → ℝ) (U : ι → Matrix n k ℝ)
    (Ψ : ι → Matrix k k ℝ)
    (h : ApproximateFactorAssumptionMatrixWLLNBridge l X Λ F U Ψ) :
    Filter.Eventually
      (fun i =>
        FactorPCTheorem11_9 (factorSampleCovariance (X i))
          (factorLeadingPCEigenvectors (r := r)
            (factorSampleCovariance_isHermitian (X i)) hcard)
          (Matrix.diagonal
            (factorLeadingPCEigenvalues (r := r)
              (factorSampleCovariance_isHermitian (X i)) hcard))
          (factorPCDiagonalSqrtD
            (factorLeadingPCEigenvalues (r := r)
              (factorSampleCovariance_isHermitian (X i)) hcard))
          (factorPCDiagonalInvSqrtD
            (factorLeadingPCEigenvalues (r := r)
              (factorSampleCovariance_isHermitian (X i)) hcard))
          (factorLoadingEstimator
            (factorLeadingPCEigenvectors (r := r)
              (factorSampleCovariance_isHermitian (X i)) hcard)
            (factorPCDiagonalSqrtD
              (factorLeadingPCEigenvalues (r := r)
                (factorSampleCovariance_isHermitian (X i)) hcard)))
          (X i)
          (fun row =>
            factorScoreEstimator
              (factorLeadingPCEigenvectors (r := r)
                (factorSampleCovariance_isHermitian (X i)) hcard)
              (factorPCDiagonalInvSqrtD
                (factorLeadingPCEigenvalues (r := r)
                  (factorSampleCovariance_isHermitian (X i)) hcard)) (X i row)) ∧
        FactorLeastSquaresNormalizedMinimizer (X i)
          (factorLoadingEstimator
            (factorLeadingPCEigenvectors (r := r)
              (factorSampleCovariance_isHermitian (X i)) hcard)
            (factorPCDiagonalSqrtD
              (factorLeadingPCEigenvalues (r := r)
                (factorSampleCovariance_isHermitian (X i)) hcard)))
          (fun row =>
            factorScoreEstimator
              (factorLeadingPCEigenvectors (r := r)
                (factorSampleCovariance_isHermitian (X i)) hcard)
              (factorPCDiagonalInvSqrtD
                (factorLeadingPCEigenvalues (r := r)
                  (factorSampleCovariance_isHermitian (X i)) hcard)) (X i row)) ∧
        ∃ B : ℝ, 0 ≤ B ∧ ∀ x : k → ℝ,
          x ⬝ᵥ ((Ψ i) *ᵥ x) ≤ B * (x ⬝ᵥ x)) l :=
  factorPCTheorem11_9_with_jointLS_and_scoreVariance_eventually_of_approxFactorAssumption11_1NormalizedRayleighBridge
    hcard hcardObs X Λ F U Ψ
    (ApproximateFactorAssumptionMatrixWLLNBridge.toNormalizedRayleighAssumptionBridge h)

set_option linter.style.longLine false in
omit [DecidableEq n] in
/-- Hansen Theorem 11.9 combined asymptotic endpoint for the recovered raw-moment
WLLN route. -/
theorem factorPCTheorem11_9_with_jointLS_and_scoreVariance_eventually_of_approxFactorAssumption11_1RawMomentMatrixWLLNBridge
    [Nonempty n] {ι : Type*} {l : Filter ι}
    (hcard : Fintype.card r ≤ Fintype.card k)
    (hcardObs : Fintype.card r ≤ Fintype.card n)
    (X : ι → n → k → ℝ) (Λ : ι → Matrix k r ℝ)
    (F : ι → n → r → ℝ) (U : ι → Matrix n k ℝ)
    (Ψ : ι → Matrix k k ℝ)
    (h : ApproximateFactorAssumptionRawMomentMatrixWLLNBridge l X Λ F U Ψ) :
    Filter.Eventually
      (fun i =>
        FactorPCTheorem11_9 (factorSampleCovariance (X i))
          (factorLeadingPCEigenvectors (r := r)
            (factorSampleCovariance_isHermitian (X i)) hcard)
          (Matrix.diagonal
            (factorLeadingPCEigenvalues (r := r)
              (factorSampleCovariance_isHermitian (X i)) hcard))
          (factorPCDiagonalSqrtD
            (factorLeadingPCEigenvalues (r := r)
              (factorSampleCovariance_isHermitian (X i)) hcard))
          (factorPCDiagonalInvSqrtD
            (factorLeadingPCEigenvalues (r := r)
              (factorSampleCovariance_isHermitian (X i)) hcard))
          (factorLoadingEstimator
            (factorLeadingPCEigenvectors (r := r)
              (factorSampleCovariance_isHermitian (X i)) hcard)
            (factorPCDiagonalSqrtD
              (factorLeadingPCEigenvalues (r := r)
                (factorSampleCovariance_isHermitian (X i)) hcard)))
          (X i)
          (fun row =>
            factorScoreEstimator
              (factorLeadingPCEigenvectors (r := r)
                (factorSampleCovariance_isHermitian (X i)) hcard)
              (factorPCDiagonalInvSqrtD
                (factorLeadingPCEigenvalues (r := r)
                  (factorSampleCovariance_isHermitian (X i)) hcard)) (X i row)) ∧
        FactorLeastSquaresNormalizedMinimizer (X i)
          (factorLoadingEstimator
            (factorLeadingPCEigenvectors (r := r)
              (factorSampleCovariance_isHermitian (X i)) hcard)
            (factorPCDiagonalSqrtD
              (factorLeadingPCEigenvalues (r := r)
                (factorSampleCovariance_isHermitian (X i)) hcard)))
          (fun row =>
            factorScoreEstimator
              (factorLeadingPCEigenvectors (r := r)
                (factorSampleCovariance_isHermitian (X i)) hcard)
              (factorPCDiagonalInvSqrtD
                (factorLeadingPCEigenvalues (r := r)
                  (factorSampleCovariance_isHermitian (X i)) hcard)) (X i row)) ∧
        ∃ B : ℝ, 0 ≤ B ∧ ∀ x : k → ℝ,
          x ⬝ᵥ ((Ψ i) *ᵥ x) ≤ B * (x ⬝ᵥ x)) l :=
  factorPCTheorem11_9_with_jointLS_and_scoreVariance_eventually_of_approxFactorAssumption11_1NormalizedRayleighBridge
    hcard hcardObs X Λ F U Ψ
    (ApproximateFactorAssumptionRawMomentMatrixWLLNBridge.toNormalizedRayleighAssumptionBridge h)

set_option linter.style.longLine false in
omit [DecidableEq n] in
/-- Hansen Theorem 11.9 combined asymptotic endpoint for the unrecovered raw
moment WLLN route. -/
theorem factorPCTheorem11_9_with_jointLS_and_scoreVariance_eventually_of_approxFactorAssumption11_1UnrecoveredMomentWLLNBridge
    [Nonempty n] {ι : Type*} {l : Filter ι}
    (hcard : Fintype.card r ≤ Fintype.card k)
    (hcardObs : Fintype.card r ≤ Fintype.card n)
    (X : ι → n → k → ℝ) (Λ : ι → Matrix k r ℝ)
    (F : ι → n → r → ℝ) (U : ι → Matrix n k ℝ)
    (Ψ : ι → Matrix k k ℝ) (Ψlim : Matrix k k ℝ)
    (h : ApproximateFactorAssumptionUnrecoveredMomentWLLNBridge
      l X Λ F U Ψ Ψlim) :
    Filter.Eventually
      (fun i =>
        FactorPCTheorem11_9 (factorSampleCovariance (X i))
          (factorLeadingPCEigenvectors (r := r)
            (factorSampleCovariance_isHermitian (X i)) hcard)
          (Matrix.diagonal
            (factorLeadingPCEigenvalues (r := r)
              (factorSampleCovariance_isHermitian (X i)) hcard))
          (factorPCDiagonalSqrtD
            (factorLeadingPCEigenvalues (r := r)
              (factorSampleCovariance_isHermitian (X i)) hcard))
          (factorPCDiagonalInvSqrtD
            (factorLeadingPCEigenvalues (r := r)
              (factorSampleCovariance_isHermitian (X i)) hcard))
          (factorLoadingEstimator
            (factorLeadingPCEigenvectors (r := r)
              (factorSampleCovariance_isHermitian (X i)) hcard)
            (factorPCDiagonalSqrtD
              (factorLeadingPCEigenvalues (r := r)
                (factorSampleCovariance_isHermitian (X i)) hcard)))
          (X i)
          (fun row =>
            factorScoreEstimator
              (factorLeadingPCEigenvectors (r := r)
                (factorSampleCovariance_isHermitian (X i)) hcard)
              (factorPCDiagonalInvSqrtD
                (factorLeadingPCEigenvalues (r := r)
                  (factorSampleCovariance_isHermitian (X i)) hcard)) (X i row)) ∧
        FactorLeastSquaresNormalizedMinimizer (X i)
          (factorLoadingEstimator
            (factorLeadingPCEigenvectors (r := r)
              (factorSampleCovariance_isHermitian (X i)) hcard)
            (factorPCDiagonalSqrtD
              (factorLeadingPCEigenvalues (r := r)
                (factorSampleCovariance_isHermitian (X i)) hcard)))
          (fun row =>
            factorScoreEstimator
              (factorLeadingPCEigenvectors (r := r)
                (factorSampleCovariance_isHermitian (X i)) hcard)
              (factorPCDiagonalInvSqrtD
                (factorLeadingPCEigenvalues (r := r)
                  (factorSampleCovariance_isHermitian (X i)) hcard)) (X i row)) ∧
        ∃ B : ℝ, 0 ≤ B ∧ ∀ x : k → ℝ,
          x ⬝ᵥ ((Ψ i) *ᵥ x) ≤ B * (x ⬝ᵥ x)) l :=
  factorPCTheorem11_9_with_jointLS_and_scoreVariance_eventually_of_approxFactorAssumption11_1NormalizedRayleighBridge
    hcard hcardObs X Λ F U Ψ
    (ApproximateFactorAssumptionUnrecoveredMomentWLLNBridge.toNormalizedRayleighAssumptionBridge h)

set_option linter.style.longLine false in
omit [DecidableEq n] in
/-- Hansen Theorem 11.9 combined asymptotic endpoint for the entrywise
unrecovered raw moment WLLN route. -/
theorem factorPCTheorem11_9_with_jointLS_and_scoreVariance_eventually_of_approxFactorAssumption11_1UnrecoveredEntrywiseWLLNBridge
    [Nonempty n] {ι : Type*} {l : Filter ι}
    (hcard : Fintype.card r ≤ Fintype.card k)
    (hcardObs : Fintype.card r ≤ Fintype.card n)
    (X : ι → n → k → ℝ) (Λ : ι → Matrix k r ℝ)
    (F : ι → n → r → ℝ) (U : ι → Matrix n k ℝ)
    (Ψ : ι → Matrix k k ℝ) (Ψlim : Matrix k k ℝ)
    (h : ApproximateFactorAssumptionUnrecoveredEntrywiseWLLNBridge
      l X Λ F U Ψ Ψlim) :
    Filter.Eventually
      (fun i =>
        FactorPCTheorem11_9 (factorSampleCovariance (X i))
          (factorLeadingPCEigenvectors (r := r)
            (factorSampleCovariance_isHermitian (X i)) hcard)
          (Matrix.diagonal
            (factorLeadingPCEigenvalues (r := r)
              (factorSampleCovariance_isHermitian (X i)) hcard))
          (factorPCDiagonalSqrtD
            (factorLeadingPCEigenvalues (r := r)
              (factorSampleCovariance_isHermitian (X i)) hcard))
          (factorPCDiagonalInvSqrtD
            (factorLeadingPCEigenvalues (r := r)
              (factorSampleCovariance_isHermitian (X i)) hcard))
          (factorLoadingEstimator
            (factorLeadingPCEigenvectors (r := r)
              (factorSampleCovariance_isHermitian (X i)) hcard)
            (factorPCDiagonalSqrtD
              (factorLeadingPCEigenvalues (r := r)
                (factorSampleCovariance_isHermitian (X i)) hcard)))
          (X i)
          (fun row =>
            factorScoreEstimator
              (factorLeadingPCEigenvectors (r := r)
                (factorSampleCovariance_isHermitian (X i)) hcard)
              (factorPCDiagonalInvSqrtD
                (factorLeadingPCEigenvalues (r := r)
                  (factorSampleCovariance_isHermitian (X i)) hcard)) (X i row)) ∧
        FactorLeastSquaresNormalizedMinimizer (X i)
          (factorLoadingEstimator
            (factorLeadingPCEigenvectors (r := r)
              (factorSampleCovariance_isHermitian (X i)) hcard)
            (factorPCDiagonalSqrtD
              (factorLeadingPCEigenvalues (r := r)
                (factorSampleCovariance_isHermitian (X i)) hcard)))
          (fun row =>
            factorScoreEstimator
              (factorLeadingPCEigenvectors (r := r)
                (factorSampleCovariance_isHermitian (X i)) hcard)
              (factorPCDiagonalInvSqrtD
                (factorLeadingPCEigenvalues (r := r)
                  (factorSampleCovariance_isHermitian (X i)) hcard)) (X i row)) ∧
        ∃ B : ℝ, 0 ≤ B ∧ ∀ x : k → ℝ,
          x ⬝ᵥ ((Ψ i) *ᵥ x) ≤ B * (x ⬝ᵥ x)) l :=
  factorPCTheorem11_9_with_jointLS_and_scoreVariance_eventually_of_approxFactorAssumption11_1NormalizedRayleighBridge
    hcard hcardObs X Λ F U Ψ
    (ApproximateFactorAssumptionUnrecoveredEntrywiseWLLNBridge.toNormalizedRayleighAssumptionBridge h)

set_option linter.style.longLine false in
omit [DecidableEq n] in
/-- Hansen Theorem 11.9 combined asymptotic endpoint for the scalar-envelope
unrecovered raw moment WLLN route. -/
theorem factorPCTheorem11_9_with_jointLS_and_scoreVariance_eventually_of_approxFactorAssumption11_1UnrecoveredEntrywiseEnvelopeWLLNBridge
    [Nonempty n] {ι : Type*} {l : Filter ι}
    (hcard : Fintype.card r ≤ Fintype.card k)
    (hcardObs : Fintype.card r ≤ Fintype.card n)
    (X : ι → n → k → ℝ) (Λ : ι → Matrix k r ℝ)
    (F : ι → n → r → ℝ) (U : ι → Matrix n k ℝ)
    (Ψ : ι → Matrix k k ℝ) (Ψlim : Matrix k k ℝ)
    (ρL ρΨ ρFU ρUF ρUU : ι → ℝ)
    (h : ApproximateFactorAssumptionUnrecoveredEntrywiseEnvelopeWLLNBridge
      l X Λ F U Ψ Ψlim ρL ρΨ ρFU ρUF ρUU) :
    Filter.Eventually
      (fun i =>
        FactorPCTheorem11_9 (factorSampleCovariance (X i))
          (factorLeadingPCEigenvectors (r := r)
            (factorSampleCovariance_isHermitian (X i)) hcard)
          (Matrix.diagonal
            (factorLeadingPCEigenvalues (r := r)
              (factorSampleCovariance_isHermitian (X i)) hcard))
          (factorPCDiagonalSqrtD
            (factorLeadingPCEigenvalues (r := r)
              (factorSampleCovariance_isHermitian (X i)) hcard))
          (factorPCDiagonalInvSqrtD
            (factorLeadingPCEigenvalues (r := r)
              (factorSampleCovariance_isHermitian (X i)) hcard))
          (factorLoadingEstimator
            (factorLeadingPCEigenvectors (r := r)
              (factorSampleCovariance_isHermitian (X i)) hcard)
            (factorPCDiagonalSqrtD
              (factorLeadingPCEigenvalues (r := r)
                (factorSampleCovariance_isHermitian (X i)) hcard)))
          (X i)
          (fun row =>
            factorScoreEstimator
              (factorLeadingPCEigenvectors (r := r)
                (factorSampleCovariance_isHermitian (X i)) hcard)
              (factorPCDiagonalInvSqrtD
                (factorLeadingPCEigenvalues (r := r)
                  (factorSampleCovariance_isHermitian (X i)) hcard)) (X i row)) ∧
        FactorLeastSquaresNormalizedMinimizer (X i)
          (factorLoadingEstimator
            (factorLeadingPCEigenvectors (r := r)
              (factorSampleCovariance_isHermitian (X i)) hcard)
            (factorPCDiagonalSqrtD
              (factorLeadingPCEigenvalues (r := r)
                (factorSampleCovariance_isHermitian (X i)) hcard)))
          (fun row =>
            factorScoreEstimator
              (factorLeadingPCEigenvectors (r := r)
                (factorSampleCovariance_isHermitian (X i)) hcard)
              (factorPCDiagonalInvSqrtD
                (factorLeadingPCEigenvalues (r := r)
                  (factorSampleCovariance_isHermitian (X i)) hcard)) (X i row)) ∧
        ∃ B : ℝ, 0 ≤ B ∧ ∀ x : k → ℝ,
          x ⬝ᵥ ((Ψ i) *ᵥ x) ≤ B * (x ⬝ᵥ x)) l :=
  factorPCTheorem11_9_with_jointLS_and_scoreVariance_eventually_of_approxFactorAssumption11_1NormalizedRayleighBridge
    hcard hcardObs X Λ F U Ψ
    (ApproximateFactorAssumptionUnrecoveredEntrywiseEnvelopeWLLNBridge.toNormalizedRayleighAssumptionBridge h)

set_option linter.style.longLine false in
omit [DecidableEq n] in
/-- Hansen Theorem 11.9 eventually follows from Assumption 11.1 plus the three
primitive recovered cross/noise coordinate WLLNs.

This compatibility endpoint remains useful when the probability work is carried
out term-by-term. The normalized-Rayleigh and matrix-WLLN endpoints above are
the preferred theorem-facing stochastic boundaries when those primitives are
available directly. -/
theorem factorPCTheorem11_9_eventually_of_approxFactorAssumption11_1CrossNoiseWLLNBridge
    [Nonempty n] {ι : Type*} {l : Filter ι}
    (hcard : Fintype.card r ≤ Fintype.card k)
    (X : ι → n → k → ℝ) (Λ : ι → Matrix k r ℝ)
    (F : ι → n → r → ℝ) (U : ι → Matrix n k ℝ)
    (Ψ : ι → Matrix k k ℝ)
    (h : ApproximateFactorAssumptionCrossNoiseWLLNBridge l X Λ F U Ψ) :
    Filter.Eventually
      (fun i =>
        FactorPCTheorem11_9 (factorSampleCovariance (X i))
          (factorLeadingPCEigenvectors (r := r)
            (factorSampleCovariance_isHermitian (X i)) hcard)
          (Matrix.diagonal
            (factorLeadingPCEigenvalues (r := r)
              (factorSampleCovariance_isHermitian (X i)) hcard))
          (factorPCDiagonalSqrtD
            (factorLeadingPCEigenvalues (r := r)
              (factorSampleCovariance_isHermitian (X i)) hcard))
          (factorPCDiagonalInvSqrtD
            (factorLeadingPCEigenvalues (r := r)
              (factorSampleCovariance_isHermitian (X i)) hcard))
          (factorLoadingEstimator
            (factorLeadingPCEigenvectors (r := r)
              (factorSampleCovariance_isHermitian (X i)) hcard)
            (factorPCDiagonalSqrtD
              (factorLeadingPCEigenvalues (r := r)
                (factorSampleCovariance_isHermitian (X i)) hcard)))
          (X i)
          (fun row =>
            factorScoreEstimator
              (factorLeadingPCEigenvectors (r := r)
                (factorSampleCovariance_isHermitian (X i)) hcard)
              (factorPCDiagonalInvSqrtD
                (factorLeadingPCEigenvalues (r := r)
                  (factorSampleCovariance_isHermitian (X i)) hcard)) (X i row))) l :=
  factorPCTheorem11_9_eventually_of_approxFactorAsymptoticCrossNoiseWLLNBridge
    hcard X Λ F U
    (ApproximateFactorAssumptionCrossNoiseWLLNBridge.toCrossNoiseWLLNBridge h)

set_option linter.style.longLine false in
omit [DecidableEq n] in
/-- Hansen Theorem 11.9 normalized joint least-squares minimizer eventually
follows from Assumption 11.1 plus the three primitive recovered cross/noise
coordinate WLLNs. -/
theorem factorPCTheorem11_9_jointLS_eventually_of_approxFactorAssumption11_1CrossNoiseWLLNBridge
    [Nonempty n] {ι : Type*} {l : Filter ι}
    (hcard : Fintype.card r ≤ Fintype.card k)
    (hcardObs : Fintype.card r ≤ Fintype.card n)
    (X : ι → n → k → ℝ) (Λ : ι → Matrix k r ℝ)
    (F : ι → n → r → ℝ) (U : ι → Matrix n k ℝ)
    (Ψ : ι → Matrix k k ℝ)
    (h : ApproximateFactorAssumptionCrossNoiseWLLNBridge l X Λ F U Ψ) :
    Filter.Eventually
      (fun i =>
        FactorLeastSquaresNormalizedMinimizer (X i)
          (factorLoadingEstimator
            (factorLeadingPCEigenvectors (r := r)
              (factorSampleCovariance_isHermitian (X i)) hcard)
            (factorPCDiagonalSqrtD
              (factorLeadingPCEigenvalues (r := r)
                (factorSampleCovariance_isHermitian (X i)) hcard)))
          (fun row =>
            factorScoreEstimator
              (factorLeadingPCEigenvectors (r := r)
                (factorSampleCovariance_isHermitian (X i)) hcard)
              (factorPCDiagonalInvSqrtD
                (factorLeadingPCEigenvalues (r := r)
                  (factorSampleCovariance_isHermitian (X i)) hcard)) (X i row))) l :=
  factorPCTheorem11_9_jointLS_eventually_of_approxFactorCrossNoiseWLLNBridge
    hcard hcardObs X Λ F U
    (ApproximateFactorAssumptionCrossNoiseWLLNBridge.toCrossNoiseWLLNBridge h)

set_option linter.style.longLine false in
omit [DecidableEq n] in
/-- Hansen Theorem 11.9 combined asymptotic endpoint for the recovered
cross/noise coordinate WLLN route. -/
theorem factorPCTheorem11_9_with_jointLS_and_scoreVariance_eventually_of_approxFactorAssumption11_1CrossNoiseWLLNBridge
    [Nonempty n] {ι : Type*} {l : Filter ι}
    (hcard : Fintype.card r ≤ Fintype.card k)
    (hcardObs : Fintype.card r ≤ Fintype.card n)
    (X : ι → n → k → ℝ) (Λ : ι → Matrix k r ℝ)
    (F : ι → n → r → ℝ) (U : ι → Matrix n k ℝ)
    (Ψ : ι → Matrix k k ℝ)
    (h : ApproximateFactorAssumptionCrossNoiseWLLNBridge l X Λ F U Ψ) :
    Filter.Eventually
      (fun i =>
        FactorPCTheorem11_9 (factorSampleCovariance (X i))
          (factorLeadingPCEigenvectors (r := r)
            (factorSampleCovariance_isHermitian (X i)) hcard)
          (Matrix.diagonal
            (factorLeadingPCEigenvalues (r := r)
              (factorSampleCovariance_isHermitian (X i)) hcard))
          (factorPCDiagonalSqrtD
            (factorLeadingPCEigenvalues (r := r)
              (factorSampleCovariance_isHermitian (X i)) hcard))
          (factorPCDiagonalInvSqrtD
            (factorLeadingPCEigenvalues (r := r)
              (factorSampleCovariance_isHermitian (X i)) hcard))
          (factorLoadingEstimator
            (factorLeadingPCEigenvectors (r := r)
              (factorSampleCovariance_isHermitian (X i)) hcard)
            (factorPCDiagonalSqrtD
              (factorLeadingPCEigenvalues (r := r)
                (factorSampleCovariance_isHermitian (X i)) hcard)))
          (X i)
          (fun row =>
            factorScoreEstimator
              (factorLeadingPCEigenvectors (r := r)
                (factorSampleCovariance_isHermitian (X i)) hcard)
              (factorPCDiagonalInvSqrtD
                (factorLeadingPCEigenvalues (r := r)
                  (factorSampleCovariance_isHermitian (X i)) hcard)) (X i row)) ∧
        FactorLeastSquaresNormalizedMinimizer (X i)
          (factorLoadingEstimator
            (factorLeadingPCEigenvectors (r := r)
              (factorSampleCovariance_isHermitian (X i)) hcard)
            (factorPCDiagonalSqrtD
              (factorLeadingPCEigenvalues (r := r)
                (factorSampleCovariance_isHermitian (X i)) hcard)))
          (fun row =>
            factorScoreEstimator
              (factorLeadingPCEigenvectors (r := r)
                (factorSampleCovariance_isHermitian (X i)) hcard)
              (factorPCDiagonalInvSqrtD
                (factorLeadingPCEigenvalues (r := r)
                  (factorSampleCovariance_isHermitian (X i)) hcard)) (X i row)) ∧
        ∃ B : ℝ, 0 ≤ B ∧ ∀ x : k → ℝ,
          x ⬝ᵥ ((Ψ i) *ᵥ x) ≤ B * (x ⬝ᵥ x)) l :=
  factorPCTheorem11_9_with_jointLS_and_scoreVariance_eventually_of_approxFactorAssumption11_1NormalizedRayleighBridge
    hcard hcardObs X Λ F U Ψ
    (ApproximateFactorAssumptionCrossNoiseWLLNBridge.toNormalizedRayleighAssumptionBridge h)

end HansenEconometrics
