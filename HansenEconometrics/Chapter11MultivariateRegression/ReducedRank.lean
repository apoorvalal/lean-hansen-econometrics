import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Data.Matrix.Mul
import HansenEconometrics.LinearAlgebraUtils
import HansenEconometrics.Chapter3FWL

/-!
# Chapter 11 — reduced-rank regression

Hansen Theorem 11.7 gives an eigenvalue/eigenvector characterization of the
reduced-rank MLE. This module records its formula and spectral layer: the
residualized matrix pencil, concentrated determinant objective, concrete
least-squares recovery formulas, the `A⊥` residual-pencil surface, and the
algebraic bridge from normalized generalized eigenvectors to the eigenvalue
product in Hansen's concentrated objectives.

Equation (11.21), its derivation, and its equivalent residual-pencil display
maximize the direct `A⊥` determinant objective and select the largest residual
roots. The theorem's final summary instead says "smallest"; that isolated
minimum-oriented surface is retained below only as explicitly documented typo
compatibility. The canonical theorem-facing surface uses the direct maximizer
and keeps `A⊥' Ahat = 0` in its conclusion. Positive-semidefinite numerators,
positive-definite denominators, and admissible dimension bounds now let the
strengthened whitening construction select a leading ordered generalized-
eigenvector block and prove that the same block carries a global determinant
max certificate. Short compatibility projections package the two determinant
maxima as a G/`A⊥` max/max pair while intentionally forgetting the ordered-root
evidence. The retained leading-root surface also proves the distinct
`det (I - compression)` minimum required by equation (11.20). Under the exact
complement-pencil identity and nonzero selected roots, the canonical dual block
is now proved to lie in the `1 - lambda` residual-pencil eigenspaces. Disjoint
selected/complement roots then give a simultaneous identified max/max
certificate, allowing arbitrary ties within either selected family. The
remaining spectral gap is the cross-boundary tie: representatives must be
chosen jointly inside that tied eigenspace rather than as independent leading
blocks. The residualized-data endpoint also still needs the exact complement-
pencil identity derived from its FWL definitions.

The legacy `ReducedRankMLE` name below denotes only a formula certificate. Raw
Gaussian likelihood, positive-definite covariance, admissibility, and global
likelihood comparison are deliberately separated into `ReducedRankLikelihood`.
The canonical profiled value below uses the corrected raw-Gaussian constant;
Hansen's erroneous printed constant is retained only under an explicit
textbook-literal compatibility name.
-/

open scoped Matrix

namespace HansenEconometrics

open Matrix

variable {k r s m ell : Type*}

section GeneralizedEigenvectors

variable [Fintype k]

/-- Generalized eigenvector equation `A v = λ B v` for a matrix pencil `(A, B)`.

This is the concrete spectral predicate needed by Hansen Theorem 11.7 before a
full reduced-rank likelihood optimizer can be proved. -/
def generalizedEigenvector
    (A B : Matrix k k ℝ) (lambda : ℝ) (v : k → ℝ) : Prop :=
  v ≠ 0 ∧ A *ᵥ v = lambda • (B *ᵥ v)

/-- Columns of `G` solve the generalized eigenvector equations for a matrix
pencil `(A, B)`, with eigenvalues indexed by the reduced-rank coordinate. -/
def generalizedEigenvectorColumns
    (A B : Matrix k k ℝ) (lambda : r → ℝ) (G : Matrix k r ℝ) : Prop :=
  ∀ j : r, generalizedEigenvector A B (lambda j) (fun i => G i j)

/-- Projection from the generalized-eigenvector column package. -/
theorem generalizedEigenvectorColumns_apply
    (A B : Matrix k k ℝ) (lambda : r → ℝ) (G : Matrix k r ℝ)
    (h : generalizedEigenvectorColumns A B lambda G) (j : r) :
    generalizedEigenvector A B (lambda j) (fun i => G i j) :=
  h j

variable [Fintype r] [DecidableEq r]

/-- Generalized-eigenvector columns diagonalize the pencil numerator against
the denominator on the selected column space. This is the matrix form of
`A v_j = λ_j B v_j`, one column at a time. -/
theorem generalizedEigenvectorColumns_mul_eq_mul_diagonal
    (A B : Matrix k k ℝ) (lambda : r → ℝ) (G : Matrix k r ℝ)
    (h : generalizedEigenvectorColumns A B lambda G) :
    A * G = B * G * Matrix.diagonal lambda := by
  ext i j
  have hj := (h j).2
  calc
    (A * G) i j = (A *ᵥ fun a => G a j) i := by
      simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
    _ = (lambda j • (B *ᵥ fun a => G a j)) i := by
      rw [hj]
    _ = (B * G * Matrix.diagonal lambda) i j := by
      simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.diagonal, mul_comm]

/-- Generalized-eigenvector columns convert Hansen's determinant numerator
`G'A G` into the denominator Gram matrix times the diagonal eigenvalue matrix. -/
theorem generalizedEigenvectorColumns_crossGram_eq_mul_diagonal
    (A B : Matrix k k ℝ) (lambda : r → ℝ) (G : Matrix k r ℝ)
    (h : generalizedEigenvectorColumns A B lambda G) :
    Gᵀ * A * G = (Gᵀ * B * G) * Matrix.diagonal lambda := by
  calc
    Gᵀ * A * G = Gᵀ * (A * G) := by
      rw [Matrix.mul_assoc]
    _ = Gᵀ * (B * G * Matrix.diagonal lambda) := by
      rw [generalizedEigenvectorColumns_mul_eq_mul_diagonal A B lambda G h]
    _ = (Gᵀ * B * G) * Matrix.diagonal lambda := by
      simp [Matrix.mul_assoc]

/-- Generalized eigenvector blocks for disjoint roots of the same symmetric
pencil are orthogonal for the denominator bilinear form.

This is the block form of the standard identity
`(λᵢ - μⱼ) gᵢ' B hⱼ = 0`.  No definiteness or normalization is needed:
symmetry of both pencil matrices and separation of the two displayed root
families are sufficient. -/
theorem generalizedEigenvectorColumns_crossGram_eq_zero_of_disjoint_roots
    [Fintype s] [DecidableEq s]
    (A B : Matrix k k ℝ)
    (lambda : r → ℝ) (G : Matrix k r ℝ)
    (mu : s → ℝ) (H : Matrix k s ℝ)
    (hAT : Aᵀ = A) (hBT : Bᵀ = B)
    (hG : generalizedEigenvectorColumns A B lambda G)
    (hH : generalizedEigenvectorColumns A B mu H)
    (hDisjoint : ∀ i j, lambda i ≠ mu j) :
    Gᵀ * B * H = 0 := by
  have hGMat : A * G = B * G * Matrix.diagonal lambda :=
    generalizedEigenvectorColumns_mul_eq_mul_diagonal A B lambda G hG
  have hHMat : A * H = B * H * Matrix.diagonal mu :=
    generalizedEigenvectorColumns_mul_eq_mul_diagonal A B mu H hH
  have hLeft :
      Gᵀ * A * H = (Gᵀ * B * H) * Matrix.diagonal mu := by
    calc
      Gᵀ * A * H = Gᵀ * (A * H) := by rw [Matrix.mul_assoc]
      _ = Gᵀ * (B * H * Matrix.diagonal mu) := by rw [hHMat]
      _ = (Gᵀ * B * H) * Matrix.diagonal mu := by
        simp [Matrix.mul_assoc]
  have hRight :
      Gᵀ * A * H = Matrix.diagonal lambda * (Gᵀ * B * H) := by
    calc
      Gᵀ * A * H = (A * G)ᵀ * H := by
        rw [Matrix.transpose_mul, hAT, Matrix.mul_assoc]
      _ = (B * G * Matrix.diagonal lambda)ᵀ * H := by rw [hGMat]
      _ = Matrix.diagonal lambda * (Gᵀ * B * H) := by
        simp [Matrix.transpose_mul, hBT, Matrix.mul_assoc]
  ext i j
  have hij :
      lambda i * (Gᵀ * B * H) i j = (Gᵀ * B * H) i j * mu j := by
    simpa [Matrix.mul_apply, Matrix.diagonal] using
      congrArg (fun M : Matrix r s ℝ => M i j) (hRight.symm.trans hLeft)
  by_contra hne
  apply hDisjoint i j
  apply mul_left_cancel₀ hne
  calc
    (Gᵀ * B * H) i j * lambda i = lambda i * (Gᵀ * B * H) i j := mul_comm _ _
    _ = (Gᵀ * B * H) i j * mu j := hij

/-- Hansen's normalization for generalized-eigenvector columns:
`G' B G = I`. -/
def generalizedEigenvectorBNormalized
    (B : Matrix k k ℝ) (G : Matrix k r ℝ) : Prop :=
  Gᵀ * B * G = 1

/-- Compression equation for an invariant generalized-eigenspace of a pencil:
`A G = B G C`.  Columnwise generalized eigenvectors are the special case
`C = diagonal lambda`; this form is the deterministic subspace bridge needed
before applying a generalized-eigenvalue determinant variational theorem. -/
def generalizedEigenCompression
    (A B : Matrix k k ℝ) (G : Matrix k r ℝ) (C : Matrix r r ℝ) : Prop :=
  A * G = B * G * C

/-- Determinant ratio in Hansen's concentrated reduced-rank objective. -/
noncomputable def generalizedEigenDetObjective
    (A B : Matrix k k ℝ) (G : Matrix k r ℝ) : ℝ :=
  (Gᵀ * A * G).det / (Gᵀ * B * G).det

/-- Reciprocal determinant ratio used by Hansen's equivalent `argmin`
reduced-rank objectives. -/
noncomputable def generalizedEigenDetReciprocalObjective
    (A B : Matrix k k ℝ) (G : Matrix k r ℝ) : ℝ :=
  (Gᵀ * B * G).det / (Gᵀ * A * G).det

/-- Columnwise generalized eigenvectors give the compression equation with
diagonal compression matrix. -/
theorem generalizedEigenCompression_diagonal_of_columns
    (A B : Matrix k k ℝ) (lambda : r → ℝ) (G : Matrix k r ℝ)
    (h : generalizedEigenvectorColumns A B lambda G) :
    generalizedEigenCompression A B G (Matrix.diagonal lambda) :=
  generalizedEigenvectorColumns_mul_eq_mul_diagonal A B lambda G h

/-- A normalized generalized-eigenspace compression `A G = B G C` makes
Hansen's determinant ratio equal to the determinant of the compressed operator
`C`.  This is the subspace-level determinant bridge behind the usual product
of selected generalized eigenvalues. -/
theorem generalizedEigenDetObjective_eq_det_compression_of_normalized
    (A B : Matrix k k ℝ) (G : Matrix k r ℝ) (C : Matrix r r ℝ)
    (hComp : generalizedEigenCompression A B G C)
    (hNorm : generalizedEigenvectorBNormalized B G) :
    generalizedEigenDetObjective A B G = C.det := by
  change Gᵀ * B * G = 1 at hNorm
  unfold generalizedEigenCompression at hComp
  unfold generalizedEigenDetObjective
  have hCross : Gᵀ * A * G = (Gᵀ * B * G) * C := by
    calc
      Gᵀ * A * G = Gᵀ * (A * G) := by
        rw [Matrix.mul_assoc]
      _ = Gᵀ * (B * G * C) := by
        rw [hComp]
      _ = (Gᵀ * B * G) * C := by
        simp [Matrix.mul_assoc]
  calc
    (Gᵀ * A * G).det / (Gᵀ * B * G).det
        = ((Gᵀ * B * G) * C).det / (Gᵀ * B * G).det := by
          rw [hCross]
    _ = C.det := by
      rw [hNorm]
      simp

/-- Reciprocal version of
`generalizedEigenDetObjective_eq_det_compression_of_normalized`. -/
theorem generalizedEigenDetReciprocalObjective_eq_inv_det_compression_of_normalized
    (A B : Matrix k k ℝ) (G : Matrix k r ℝ) (C : Matrix r r ℝ)
    (hComp : generalizedEigenCompression A B G C)
    (hNorm : generalizedEigenvectorBNormalized B G) :
    generalizedEigenDetReciprocalObjective A B G = C.det⁻¹ := by
  change Gᵀ * B * G = 1 at hNorm
  unfold generalizedEigenCompression at hComp
  unfold generalizedEigenDetReciprocalObjective
  have hCross : Gᵀ * A * G = (Gᵀ * B * G) * C := by
    calc
      Gᵀ * A * G = Gᵀ * (A * G) := by
        rw [Matrix.mul_assoc]
      _ = Gᵀ * (B * G * C) := by
        rw [hComp]
      _ = (Gᵀ * B * G) * C := by
        simp [Matrix.mul_assoc]
  calc
    (Gᵀ * B * G).det / (Gᵀ * A * G).det
        = (1 : ℝ) / ((Gᵀ * B * G) * C).det := by
          rw [hCross, hNorm]
          simp
    _ = C.det⁻¹ := by
      rw [hNorm]
      simp

/-- A normalized competitor's determinant ratio is the determinant of its
compressed numerator `G' A G`.

Unlike `generalizedEigenDetObjective_eq_det_compression_of_normalized`, this
does not assume the competitor spans an invariant generalized eigenspace. It is
therefore the algebraic bridge needed for the actual determinant variational
theorem in Hansen Theorem 11.7. -/
theorem generalizedEigenDetObjective_eq_compressed_det_of_normalized
    (A B : Matrix k k ℝ) (G : Matrix k r ℝ)
    (hNorm : generalizedEigenvectorBNormalized B G) :
    generalizedEigenDetObjective A B G = (Gᵀ * A * G).det := by
  change Gᵀ * B * G = 1 at hNorm
  unfold generalizedEigenDetObjective
  rw [hNorm]
  simp

/-- Reciprocal version of
`generalizedEigenDetObjective_eq_compressed_det_of_normalized`. -/
theorem generalizedEigenDetReciprocalObjective_eq_inv_compressed_det_of_normalized
    (A B : Matrix k k ℝ) (G : Matrix k r ℝ)
    (hNorm : generalizedEigenvectorBNormalized B G) :
    generalizedEigenDetReciprocalObjective A B G = (Gᵀ * A * G).det⁻¹ := by
  change Gᵀ * B * G = 1 at hNorm
  unfold generalizedEigenDetReciprocalObjective
  rw [hNorm]
  simp

/-- Global maximizer predicate for the generalized determinant objective over
`B`-normalized column blocks. This is the abstract normal-likelihood surface
behind Hansen's `G` side. -/
def generalizedEigenDetObjectiveMaximizer
    (A B : Matrix k k ℝ) (G : Matrix k r ℝ) : Prop :=
  generalizedEigenvectorBNormalized B G ∧
    ∀ H : Matrix k r ℝ, generalizedEigenvectorBNormalized B H →
      generalizedEigenDetObjective A B H ≤ generalizedEigenDetObjective A B G

/-- Global minimizer predicate for the generalized determinant objective over
`B`-normalized column blocks. This is the abstract dual `A⊥` surface. -/
def generalizedEigenDetObjectiveMinimizer
    (A B : Matrix k k ℝ) (G : Matrix k r ℝ) : Prop :=
  generalizedEigenvectorBNormalized B G ∧
    ∀ H : Matrix k r ℝ, generalizedEigenvectorBNormalized B H →
      generalizedEigenDetObjective A B G ≤ generalizedEigenDetObjective A B H

/-- A normalized block-level diagonalization equation gives nonzero
generalized-eigenvector columns.

The normalization supplies column nonzeroness, while the matrix equation is
projected one column at a time. This is the reverse bridge to
`generalizedEigenvectorColumns_mul_eq_mul_diagonal`. -/
theorem generalizedEigenvectorColumns_of_mul_eq_mul_diagonal
    (A B : Matrix k k ℝ) (lambda : r → ℝ) (G : Matrix k r ℝ)
    (hNorm : generalizedEigenvectorBNormalized B G)
    (hEq : A * G = B * G * Matrix.diagonal lambda) :
    generalizedEigenvectorColumns A B lambda G := by
  classical
  intro j
  constructor
  · intro hzero
    have hzero' : ∀ i, G i j = 0 := fun i => by
      simpa using congrFun hzero i
    have hentry := congrFun (congrFun hNorm j) j
    simp [Matrix.mul_apply, Matrix.transpose_apply, hzero'] at hentry
  · ext i
    have hentry := congrArg (fun M : Matrix k r ℝ => M i j) hEq
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.diagonal, mul_comm]
      using hentry

section GeneralizedEigenExistence

open scoped Matrix.Norms.Elementwise MatrixOrder

private theorem orthonormalFrameSet_nonempty_of_card_le
    (hcard : Fintype.card r ≤ Fintype.card k) :
    Set.Nonempty {H : Matrix k r ℝ | Hᵀ * H = 1} := by
  classical
  let f : r → k := fun j =>
    (Fintype.equivFin k).symm (Fin.castLE hcard ((Fintype.equivFin r) j))
  have hf : Function.Injective f := by
    intro i j hij
    apply (Fintype.equivFin r).injective
    apply Fin.castLE_injective hcard
    exact (Fintype.equivFin k).symm.injective hij
  let G : Matrix k r ℝ := fun i j => if i = f j then 1 else 0
  refine ⟨G, ?_⟩
  ext i j
  simp [G, Matrix.mul_apply, Matrix.transpose_apply, hf.eq_iff,
    Matrix.one_apply, eq_comm]

omit [Fintype r] in
private theorem orthonormalFrameSet_isCompact [Finite r] :
    IsCompact {H : Matrix k r ℝ | Hᵀ * H = 1} := by
  letI := Fintype.ofFinite r
  rw [Metric.isCompact_iff_isClosed_bounded]
  constructor
  · exact isClosed_eq (by fun_prop) continuous_const
  · rw [isBounded_iff_forall_norm_le]
    refine ⟨1, ?_⟩
    intro H hH
    rw [Matrix.norm_le_iff zero_le_one]
    intro i j
    have hdiag := congrFun (congrFun hH j) j
    have hsum : ∑ a : k, H a j * H a j = 1 := by
      simpa [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] using hdiag
    have hterm : H i j * H i j ≤ ∑ a : k, H a j * H a j :=
      Finset.single_le_sum (fun a _ => mul_self_nonneg (H a j)) (Finset.mem_univ i)
    rw [hsum] at hterm
    rw [Real.norm_eq_abs]
    apply abs_le.mpr
    constructor <;>
      nlinarith [sq_nonneg (H i j - 1), sq_nonneg (H i j + 1)]

/-- A generalized determinant objective attains a global normalized maximum
when its denominator has an explicit invertible whitening.

The proof maximizes the compressed determinant on the compact Stiefel set and
transports the maximizer through the inverse whitening. It assumes neither a
generalized eigenspace nor the desired determinant bound. -/
theorem generalizedEigenDetObjectiveMaximizer_exists_of_whitening
    [DecidableEq k]
    (A B T S : Matrix k k ℝ)
    (hB : B = Tᵀ * T) (hST : S * T = 1) (hTS : T * S = 1)
    (hcard : Fintype.card r ≤ Fintype.card k) :
    ∃ G : Matrix k r ℝ, generalizedEigenDetObjectiveMaximizer A B G := by
  let frameSet : Set (Matrix k r ℝ) := {K | Kᵀ * K = 1}
  let compressedDet : Matrix k r ℝ → ℝ := fun K =>
    ((S * K)ᵀ * A * (S * K)).det
  have hcompact : IsCompact frameSet := orthonormalFrameSet_isCompact
  have hne : frameSet.Nonempty := orthonormalFrameSet_nonempty_of_card_le hcard
  have hcont : Continuous compressedDet := by
    dsimp [compressedDet]
    fun_prop
  obtain ⟨K, hK, hmax⟩ :=
    hcompact.exists_isMaxOn hne hcont.continuousOn
  let G : Matrix k r ℝ := S * K
  have hGNorm : generalizedEigenvectorBNormalized B G := by
    change Gᵀ * B * G = 1
    calc
      Gᵀ * B * G = Kᵀ * (Sᵀ * Tᵀ) * (T * S) * K := by
        simp [G, hB, Matrix.transpose_mul, Matrix.mul_assoc]
      _ = Kᵀ * (T * S)ᵀ * (T * S) * K := by
        rw [Matrix.transpose_mul]
      _ = Kᵀ * K := by rw [hTS]; simp
      _ = 1 := hK
  refine ⟨G, hGNorm, ?_⟩
  intro H hHNorm
  have hTHNorm : (T * H)ᵀ * (T * H) = 1 := by
    calc
      (T * H)ᵀ * (T * H) = Hᵀ * B * H := by
        simp [hB, Matrix.transpose_mul, Matrix.mul_assoc]
      _ = 1 := hHNorm
  have hle := hmax hTHNorm
  change ((S * (T * H))ᵀ * A * (S * (T * H))).det ≤
    ((S * K)ᵀ * A * (S * K)).det at hle
  have hrecover : S * (T * H) = H := by
    rw [← Matrix.mul_assoc, hST, Matrix.one_mul]
  rw [generalizedEigenDetObjective_eq_compressed_det_of_normalized A B H hHNorm,
    generalizedEigenDetObjective_eq_compressed_det_of_normalized A B G hGNorm,
    ← hrecover]
  exact hle

/-- A positive-definite pencil denominator makes the normalized generalized
determinant objective attain a global maximum.

Positive definiteness supplies an invertible Gram factor through Mathlib's
C-star-algebra factorization; the substantive existence argument is
`generalizedEigenDetObjectiveMaximizer_exists_of_whitening`. -/
theorem generalizedEigenDetObjectiveMaximizer_exists_of_posDef
    (A B : Matrix k k ℝ) (hB : B.PosDef)
    (hcard : Fintype.card r ≤ Fintype.card k) :
    ∃ G : Matrix k r ℝ, generalizedEigenDetObjectiveMaximizer A B G := by
  classical
  obtain ⟨T, hTunit, hBT⟩ :=
    CStarAlgebra.isStrictlyPositive_iff_eq_star_mul_self.mp hB.isStrictlyPositive
  have hBT' : B = Tᵀ * T := by
    simpa [star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
      using hBT
  have hTdet : IsUnit T.det := (Matrix.isUnit_iff_isUnit_det T).mp hTunit
  exact generalizedEigenDetObjectiveMaximizer_exists_of_whitening
    A B T T⁻¹ hBT' (Matrix.nonsing_inv_mul T hTdet)
      (Matrix.mul_nonsing_inv T hTdet) hcard

/-- An explicit invertible whitening selects a normalized generalized-
eigenvector block whose roots are the leading ordered eigenvalues of the
whitened Hermitian numerator.

This is the spectral half of the positive-semidefinite determinant theorem:
the construction selects the first `card r` vectors of Mathlib's nonincreasing
Hermitian eigenbasis and transports them through the inverse whitening. -/
theorem generalizedEigenvectorColumns_normalized_leading_exists_of_whitening
    [DecidableEq k]
    (A B T S M : Matrix k k ℝ)
    (hB : B = Tᵀ * T) (hM : M = Sᵀ * A * S)
    (hST : S * T = 1) (hTS : T * S = 1)
    (hMHerm : M.IsHermitian)
    (hcard : Fintype.card r ≤ Fintype.card k) :
    ∃ G : Matrix k r ℝ,
      generalizedEigenvectorColumns A B
          (fun j : r => hMHerm.eigenvalues₀
            (Fin.castLE hcard ((Fintype.equivFin r) j))) G ∧
        generalizedEigenvectorBNormalized B G := by
  classical
  have hTtSt : Tᵀ * Sᵀ = 1 := by
    rw [← Matrix.transpose_mul, hST, Matrix.transpose_one]
  let e : r → k := fun j =>
    (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card k)))
      (Fin.castLE hcard ((Fintype.equivFin r) j))
  have he : Function.Injective e := by
    intro i j hij
    apply (Fintype.equivFin r).injective
    apply Fin.castLE_injective hcard
    exact (Fintype.equivOfCardEq
      (Fintype.card_fin (Fintype.card k))).injective hij
  let Q : Matrix k r ℝ := fun i j =>
    (hMHerm.eigenvectorBasis (e j) : EuclideanSpace ℝ k) i
  let lambda : r → ℝ := fun j => hMHerm.eigenvalues₀
    (Fin.castLE hcard ((Fintype.equivFin r) j))
  have hQNorm : Qᵀ * Q = 1 := by
    ext i j
    rw [Matrix.mul_apply]
    have hinner :=
      (orthonormal_iff_ite.mp hMHerm.eigenvectorBasis.orthonormal) (e i) (e j)
    have hiff : e i = e j ↔ i = j := he.eq_iff
    have hinner' :
        (fun a => Q a i) ⬝ᵥ (fun a => Q a j) = if i = j then 1 else 0 := by
      rw [dotProduct_comm]
      simpa [Q, hiff] using hinner
    simpa [Matrix.transpose_apply, dotProduct, Matrix.one_apply] using hinner'
  have hMQ : M * Q = Q * Matrix.diagonal lambda := by
    ext i j
    have heig := hMHerm.mulVec_eigenvectorBasis (e j)
    have hentry := congrFun heig i
    simpa [Q, lambda, e, Matrix.IsHermitian.eigenvalues, Matrix.mul_apply,
      Matrix.mulVec, dotProduct, Matrix.diagonal, mul_comm] using hentry
  let G : Matrix k r ℝ := S * Q
  have hGNorm : generalizedEigenvectorBNormalized B G := by
    change Gᵀ * B * G = 1
    calc
      Gᵀ * B * G = Qᵀ * (Sᵀ * Tᵀ) * (T * S) * Q := by
        simp [G, hB, Matrix.transpose_mul, Matrix.mul_assoc]
      _ = Qᵀ * (T * S)ᵀ * (T * S) * Q := by
        rw [Matrix.transpose_mul]
      _ = Qᵀ * Q := by rw [hTS]; simp
      _ = 1 := hQNorm
  have hBGSimp : B * G = Tᵀ * Q := by
    calc
      B * G = (Tᵀ * T) * (S * Q) := by rw [hB]
      _ = Tᵀ * ((T * S) * Q) := by simp [Matrix.mul_assoc]
      _ = Tᵀ * Q := by rw [hTS, Matrix.one_mul]
  have hAG : A * G = B * G * Matrix.diagonal lambda := by
    calc
      A * G = (Tᵀ * Sᵀ) * A * (S * Q) := by rw [hTtSt]; simp [G]
      _ = Tᵀ * (M * Q) := by rw [hM]; simp [Matrix.mul_assoc]
      _ = Tᵀ * (Q * Matrix.diagonal lambda) := by rw [hMQ]
      _ = B * G * Matrix.diagonal lambda := by
        rw [hBGSimp]
        exact (Matrix.mul_assoc Tᵀ Q (Matrix.diagonal lambda)).symm
  exact ⟨G,
    generalizedEigenvectorColumns_of_mul_eq_mul_diagonal
      A B lambda G hGNorm hAG,
    hGNorm⟩

/-- A Hermitian generalized pencil with positive-definite denominator has a
normalized block of generalized eigenvectors in every admissible dimension.

This compatibility surface hides the explicit leading-root formula exposed by
`generalizedEigenvectorColumns_normalized_leading_exists_of_whitening`. -/
theorem generalizedEigenvectorColumns_normalized_exists_of_isHermitian_posDef
    (A B : Matrix k k ℝ) (hA : A.IsHermitian) (hB : B.PosDef)
    (hcard : Fintype.card r ≤ Fintype.card k) :
    ∃ (G : Matrix k r ℝ) (lambda : r → ℝ),
      generalizedEigenvectorColumns A B lambda G ∧
        generalizedEigenvectorBNormalized B G := by
  classical
  obtain ⟨T, hTunit, hBT⟩ :=
    CStarAlgebra.isStrictlyPositive_iff_eq_star_mul_self.mp hB.isStrictlyPositive
  have hBT' : B = Tᵀ * T := by
    simpa [star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
      using hBT
  have hTdet : IsUnit T.det := (Matrix.isUnit_iff_isUnit_det T).mp hTunit
  let S : Matrix k k ℝ := T⁻¹
  have hST : S * T = 1 := Matrix.nonsing_inv_mul T hTdet
  have hTS : T * S = 1 := Matrix.mul_nonsing_inv T hTdet
  let M : Matrix k k ℝ := Sᵀ * A * S
  have hM : M.IsHermitian := by
    simpa [M, Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.isHermitian_conjTranspose_mul_mul S hA
  obtain ⟨G, hGEig, hGNorm⟩ :=
    generalizedEigenvectorColumns_normalized_leading_exists_of_whitening
      A B T S M hBT' rfl hST hTS hM hcard
  exact ⟨G,
    (fun j : r => hM.eigenvalues₀
      (Fin.castLE hcard ((Fintype.equivFin r) j))),
    hGEig, hGNorm⟩

end GeneralizedEigenExistence

/-- Normalized generalized-eigenvector columns make Hansen's determinant ratio
equal to the product of the selected generalized eigenvalues. This is the
deterministic bridge from the generalized-eigenvalue statement to the
concentrated likelihood/objective expression. -/
theorem generalizedEigenDetObjective_eq_prod_eigenvalues_of_normalized
    (A B : Matrix k k ℝ) (lambda : r → ℝ) (G : Matrix k r ℝ)
    (h : generalizedEigenvectorColumns A B lambda G)
    (hNorm : generalizedEigenvectorBNormalized B G) :
    generalizedEigenDetObjective A B G = ∏ j, lambda j := by
  change Gᵀ * B * G = 1 at hNorm
  rw [generalizedEigenDetObjective,
    generalizedEigenvectorColumns_crossGram_eq_mul_diagonal A B lambda G h, hNorm]
  simp [Matrix.det_diagonal]

/-- Normalized generalized-eigenvector columns identify the selected compressed
determinant itself with the product of selected generalized eigenvalues. This
is the product side of the determinant variational bridge used in Hansen
Theorem 11.7. -/
theorem generalizedEigenvectorColumns_compressed_det_eq_prod_of_normalized
    (A B : Matrix k k ℝ) (lambda : r → ℝ) (G : Matrix k r ℝ)
    (h : generalizedEigenvectorColumns A B lambda G)
    (hNorm : generalizedEigenvectorBNormalized B G) :
    (Gᵀ * A * G).det = ∏ j, lambda j := by
  rw [← generalizedEigenDetObjective_eq_compressed_det_of_normalized A B G hNorm]
  exact generalizedEigenDetObjective_eq_prod_eigenvalues_of_normalized A B lambda G h hNorm

/-- Positive selected generalized roots make the selected compressed
determinant nonsingular under Hansen normalization.

This is the determinant-side counterpart of the usual nonzero selected-root
product premise: once the selected columns are normalized generalized
eigenvectors, `det(G'AG)` is exactly `∏ λ_j`. -/
theorem generalizedEigenSelectedCompressedDet_ne_zero_of_pos
    (A B : Matrix k k ℝ) (lambda : r → ℝ) (G : Matrix k r ℝ)
    (h : generalizedEigenvectorColumns A B lambda G)
    (hNorm : generalizedEigenvectorBNormalized B G)
    (hLambda : ∀ j, 0 < lambda j) :
    (Gᵀ * A * G).det ≠ 0 := by
  rw [generalizedEigenvectorColumns_compressed_det_eq_prod_of_normalized
    A B lambda G h hNorm]
  exact ne_of_gt (Finset.prod_pos fun j _ => hLambda j)

/-- A nonzero selected compressed determinant makes the selected generalized
root product nonzero.

This is the determinant/product bookkeeping bridge used when a raw spectral
construction proves nonsingularity of the selected compressed block rather than
positivity or pointwise nonzero roots. -/
theorem generalizedEigenSelectedRootProduct_ne_zero_of_compressedDet_ne_zero
    (A B : Matrix k k ℝ) (lambda : r → ℝ) (G : Matrix k r ℝ)
    (h : generalizedEigenvectorColumns A B lambda G)
    (hNorm : generalizedEigenvectorBNormalized B G)
    (hdet : (Gᵀ * A * G).det ≠ 0) :
    (∏ j, lambda j) ≠ 0 := by
  rwa [generalizedEigenvectorColumns_compressed_det_eq_prod_of_normalized
    A B lambda G h hNorm] at hdet

/-- Normalized generalized-eigenvector columns make the reciprocal determinant
ratio equal to the reciprocal product of the selected generalized eigenvalues. -/
theorem generalizedEigenDetReciprocalObjective_eq_inv_prod_eigenvalues_of_normalized
    (A B : Matrix k k ℝ) (lambda : r → ℝ) (G : Matrix k r ℝ)
    (h : generalizedEigenvectorColumns A B lambda G)
    (hNorm : generalizedEigenvectorBNormalized B G) :
    generalizedEigenDetReciprocalObjective A B G = (∏ j, lambda j)⁻¹ := by
  change Gᵀ * B * G = 1 at hNorm
  rw [generalizedEigenDetReciprocalObjective,
    generalizedEigenvectorColumns_crossGram_eq_mul_diagonal A B lambda G h, hNorm]
  simp [Matrix.det_diagonal]

/-- Selected compressed-determinant maximality for a normalized generalized
eigenspace of a pencil `(A, B)`.

This is the exact determinant min-max target for the G side of Hansen Theorem
11.7 before translating the selected determinant into the product of generalized
roots. -/
def generalizedEigenSelectedCompressedDetMaximal
    (A B : Matrix k k ℝ) (G : Matrix k r ℝ) : Prop :=
  ∀ H : Matrix k r ℝ, generalizedEigenvectorBNormalized B H →
    (Hᵀ * A * H).det ≤ (Gᵀ * A * G).det

/-- Selected compressed-determinant minimality for a normalized generalized
eigenspace of a pencil `(A, B)`.

This is the exact determinant min-max target for Hansen's `A⊥` side before
translating the selected determinant into the product of dual generalized
roots. -/
def generalizedEigenSelectedCompressedDetMinimal
    (A B : Matrix k k ℝ) (G : Matrix k r ℝ) : Prop :=
  ∀ H : Matrix k r ℝ, generalizedEigenvectorBNormalized B H →
    (Gᵀ * A * G).det ≤ (Hᵀ * A * H).det

/-- A generalized determinant-objective maximizer supplies the selected
compressed-determinant maximum. This is the normal-likelihood route to the
G-side determinant min-max premise. -/
theorem generalizedEigenSelectedCompressedDetMaximal_of_detObjectiveMaximizer
    (A B : Matrix k k ℝ) (G : Matrix k r ℝ)
    (hOpt : generalizedEigenDetObjectiveMaximizer A B G) :
    generalizedEigenSelectedCompressedDetMaximal A B G := by
  intro H hHNorm
  calc
    (Hᵀ * A * H).det = generalizedEigenDetObjective A B H := by
      exact (generalizedEigenDetObjective_eq_compressed_det_of_normalized
        A B H hHNorm).symm
    _ ≤ generalizedEigenDetObjective A B G := hOpt.2 H hHNorm
    _ = (Gᵀ * A * G).det :=
      generalizedEigenDetObjective_eq_compressed_det_of_normalized A B G hOpt.1

/-- A generalized determinant-objective minimizer supplies the selected
compressed-determinant minimum. This is the normal-likelihood route to the
dual `A⊥` determinant min-max premise. -/
theorem generalizedEigenSelectedCompressedDetMinimal_of_detObjectiveMinimizer
    (A B : Matrix k k ℝ) (G : Matrix k r ℝ)
    (hOpt : generalizedEigenDetObjectiveMinimizer A B G) :
    generalizedEigenSelectedCompressedDetMinimal A B G := by
  intro H hHNorm
  calc
    (Gᵀ * A * G).det = generalizedEigenDetObjective A B G := by
      exact (generalizedEigenDetObjective_eq_compressed_det_of_normalized
        A B G hOpt.1).symm
    _ ≤ generalizedEigenDetObjective A B H := hOpt.2 H hHNorm
    _ = (Hᵀ * A * H).det :=
      generalizedEigenDetObjective_eq_compressed_det_of_normalized A B H hHNorm

/-- Product upper-bound form of the generalized-eigenvalue determinant
min-max theorem. -/
def generalizedEigenDetProductUpperBound
    (A B : Matrix k k ℝ) (lambda : r → ℝ) : Prop :=
  ∀ H : Matrix k r ℝ, generalizedEigenvectorBNormalized B H →
    (Hᵀ * A * H).det ≤ ∏ j, lambda j

/-- Product lower-bound form of the generalized-eigenvalue determinant
min-max theorem. -/
def generalizedEigenDetProductLowerBound
    (A B : Matrix k k ℝ) (lambda : r → ℝ) : Prop :=
  ∀ H : Matrix k r ℝ, generalizedEigenvectorBNormalized B H →
    ∏ j, lambda j ≤ (Hᵀ * A * H).det

/-- Scalar Rayleigh upper bound for a generalized pencil, normalized by its
denominator quadratic form. This is strictly weaker than the multi-column
determinant maximum and is supplied by the top ordered eigenvalue after
whitening. -/
def generalizedEigenRayleighUpperBound
    (A B : Matrix k k ℝ) (alpha : ℝ) : Prop :=
  ∀ v : k → ℝ, v ⬝ᵥ (B *ᵥ v) = 1 → v ⬝ᵥ (A *ᵥ v) ≤ alpha

omit [DecidableEq r] in
private theorem compression_quadratic_eq_image_quadratic
    (A : Matrix k k ℝ) (H : Matrix k r ℝ) (x : r → ℝ) :
    x ⬝ᵥ ((Hᵀ * A * H) *ᵥ x) =
      (H *ᵥ x) ⬝ᵥ (A *ᵥ (H *ᵥ x)) := by
  calc
    x ⬝ᵥ ((Hᵀ * A * H) *ᵥ x) =
        x ⬝ᵥ (Hᵀ *ᵥ (A *ᵥ (H *ᵥ x))) := by
          simp [Matrix.mulVec_mulVec, Matrix.mul_assoc]
    _ = (x ᵥ* Hᵀ) ⬝ᵥ (A *ᵥ (H *ᵥ x)) :=
      Matrix.dotProduct_mulVec x Hᵀ (A *ᵥ (H *ᵥ x))
    _ = (H *ᵥ x) ⬝ᵥ (A *ᵥ (H *ᵥ x)) := by
      rw [Matrix.vecMul_transpose]

/-- Multiplicative Ritz bound for a positive-semidefinite matrix.

For every orthonormal `r`-column block, the determinant of the compression is
at most the product of the leading `r` ordered eigenvalues of the ambient
matrix.  This is the general multi-column determinant theorem used by Hansen's
two reduced-rank pencils after positive-definite whitening. -/
theorem generalizedEigenDetProductUpperBound_identity_of_posSemidef_ordered
    [DecidableEq k]
    (M : Matrix k k ℝ) (hM : M.PosSemidef)
    (hcard : Fintype.card r ≤ Fintype.card k) :
    generalizedEigenDetProductUpperBound M (1 : Matrix k k ℝ)
      (fun j : r => hM.1.eigenvalues₀
        (Fin.castLE hcard ((Fintype.equivFin r) j))) := by
  classical
  intro H hHNorm
  have hHTH : Hᵀ * H = 1 := by
    simpa [generalizedEigenvectorBNormalized, Matrix.mul_assoc] using hHNorm
  let C : Matrix r r ℝ := Hᵀ * M * H
  have hC : C.PosSemidef := by
    have hcomp := hM.conjTranspose_mul_mul_same H
    simpa [C, Matrix.conjTranspose, Matrix.star_apply] using hcomp
  have hEigLe : ∀ j : Fin (Fintype.card r),
      hC.1.eigenvalues₀ j ≤ hM.1.eigenvalues₀ (Fin.castLE hcard j) := by
    intro j
    simpa [C] using
      (hermitian_compression_ordered_eigenvalue_le hM.1 H hHTH hcard j)
  have hCProd : (∏ i : r, hC.1.eigenvalues i) =
      ∏ j : Fin (Fintype.card r), hC.1.eigenvalues₀ j := by
    calc
      (∏ i : r, hC.1.eigenvalues i) =
          ∏ j : Fin (Fintype.card r),
            hC.1.eigenvalues
              ((Fintype.equivOfCardEq
                (Fintype.card_fin (Fintype.card r))) j) := by
            exact (Equiv.prod_comp
              (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card r)))
              hC.1.eigenvalues).symm
      _ = ∏ j : Fin (Fintype.card r), hC.1.eigenvalues₀ j := by
            apply Finset.prod_congr rfl
            intro j _
            simp [Matrix.IsHermitian.eigenvalues]
  calc
    (Hᵀ * M * H).det = ∏ i, hC.1.eigenvalues i := by
      simpa [C] using hC.1.det_eq_prod_eigenvalues
    _ = ∏ j : Fin (Fintype.card r), hC.1.eigenvalues₀ j := hCProd
    _ ≤ ∏ j : Fin (Fintype.card r),
        hM.1.eigenvalues₀ (Fin.castLE hcard j) := by
      exact Finset.prod_le_prod
        (fun j _ => by
          let e : Fin (Fintype.card r) ≃ r :=
            Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card r))
          have hnonneg := hC.eigenvalues_nonneg (e j)
          simpa [Matrix.IsHermitian.eigenvalues, e] using hnonneg)
        (fun j _ => hEigLe j)
    _ = ∏ i : r, hM.1.eigenvalues₀
        (Fin.castLE hcard ((Fintype.equivFin r) i)) := by
      exact (Equiv.prod_comp (Fintype.equivFin r)
        (fun j : Fin (Fintype.card r) =>
          hM.1.eigenvalues₀ (Fin.castLE hcard j))).symm

/-- Complement-product lower bound transported from an ordinary whitened
matrix to a generalized pencil.

When the whitened numerator satisfies `0 <= M <= I`, every B-normalized
competitor `H` satisfies that the product of one minus the leading ordered
eigenvalues is at most `det (I - H' A H)`. This is the determinant direction
needed by equation (11.20); it is stronger than, and is not inferred from, a
maximum of `det (H' A H)`. -/
theorem generalizedEigenComplementDetLowerBound_of_whitening
    [DecidableEq k]
    (A B M T : Matrix k k ℝ)
    (hA : A = Tᵀ * M * T) (hB : B = Tᵀ * T)
    (hM : M.PosSemidef) (hIM : (1 - M).PosSemidef)
    (hcard : Fintype.card r ≤ Fintype.card k) :
    ∀ H : Matrix k r ℝ, generalizedEigenvectorBNormalized B H →
      ∏ j : r,
          (1 - hM.1.eigenvalues₀
            (Fin.castLE hcard ((Fintype.equivFin r) j))) ≤
        (1 - Hᵀ * A * H).det := by
  intro H hH
  change Hᵀ * B * H = 1 at hH
  have hTH : (T * H)ᵀ * (T * H) = (1 : Matrix r r ℝ) := by
    calc
      (T * H)ᵀ * (T * H) = Hᵀ * Tᵀ * (T * H) := by
        rw [Matrix.transpose_mul]
      _ = Hᵀ * (Tᵀ * T) * H := by simp [Matrix.mul_assoc]
      _ = Hᵀ * B * H := by rw [← hB]
      _ = 1 := hH
  have hBound :=
    prod_one_sub_ordered_eigenvalues_le_det_one_sub_compression_reindex
      hM hIM (T * H) hTH hcard
  have hCompression :
      (T * H)ᵀ * M * (T * H) = Hᵀ * A * H := by
    calc
      (T * H)ᵀ * M * (T * H) = Hᵀ * (Tᵀ * M * T) * H := by
        rw [Matrix.transpose_mul]
        simp [Matrix.mul_assoc]
      _ = Hᵀ * A * H := by rw [← hA]
  rw [hCompression] at hBound
  exact hBound

/-- A normalized leading generalized-eigenblock minimizes the complement
determinant used by Hansen's profiled equation (11.20).

The leading-root formula is retained explicitly in the hypotheses instead of
being projected to a bare determinant-max certificate. Together with
`0 <= M <= I`, this proves the correct `det (I - compression)` comparison over
every B-normalized competitor, including multi-column blocks. -/
theorem generalizedEigenLeadingComplementDetMinimal_of_whitening
    [DecidableEq k]
    (A B M T : Matrix k k ℝ)
    (hA : A = Tᵀ * M * T) (hB : B = Tᵀ * T)
    (hM : M.PosSemidef) (hIM : (1 - M).PosSemidef)
    (hcard : Fintype.card r ≤ Fintype.card k)
    (G : Matrix k r ℝ)
    (hEig : generalizedEigenvectorColumns A B
      (fun j : r => hM.1.eigenvalues₀
        (Fin.castLE hcard ((Fintype.equivFin r) j))) G)
    (hNorm : generalizedEigenvectorBNormalized B G) :
    ∀ H : Matrix k r ℝ, generalizedEigenvectorBNormalized B H →
      (1 - Gᵀ * A * G).det ≤ (1 - Hᵀ * A * H).det := by
  let lambda : r → ℝ := fun j => hM.1.eigenvalues₀
    (Fin.castLE hcard ((Fintype.equivFin r) j))
  have hGCompression : Gᵀ * A * G = Matrix.diagonal lambda := by
    calc
      Gᵀ * A * G = (Gᵀ * B * G) * Matrix.diagonal lambda :=
        generalizedEigenvectorColumns_crossGram_eq_mul_diagonal
          A B lambda G hEig
      _ = Matrix.diagonal lambda := by
        change Gᵀ * B * G = 1 at hNorm
        rw [hNorm]
        simp
  have hGDet :
      (1 - Gᵀ * A * G).det = ∏ j : r, (1 - lambda j) := by
    rw [hGCompression]
    rw [show (1 : Matrix r r ℝ) - Matrix.diagonal lambda =
      Matrix.diagonal (fun j => 1 - lambda j) by
        ext i j
        by_cases hij : i = j
        · subst j
          simp
        · simp [hij]]
    rw [Matrix.det_diagonal]
  intro H hH
  rw [hGDet]
  exact generalizedEigenComplementDetLowerBound_of_whitening
    A B M T hA hB hM hIM hcard H hH

/-- Multi-column determinant variational theorem in the top-eigenvalue
plateau case.

For a positive-semidefinite numerator, every eigenvalue of a normalized
compression is nonnegative. Applying the scalar top-Rayleigh bound to each
normalized compression eigenvector bounds every one by `alpha`; hence the
compressed determinant is at most `alpha ^ card r`. When all selected roots
equal `alpha`, this is exactly their product. No determinant maximum is assumed. -/
theorem generalizedEigenDetProductUpperBound_of_posSemidef_tied_rayleigh
    (A B : Matrix k k ℝ) (hA : A.PosSemidef)
    (lambda : r → ℝ) (alpha : ℝ)
    (hTie : ∀ j, lambda j = alpha)
    (hRayleigh : generalizedEigenRayleighUpperBound A B alpha) :
    generalizedEigenDetProductUpperBound A B lambda := by
  classical
  intro H hHNorm
  let C : Matrix r r ℝ := Hᵀ * A * H
  have hC : C.PosSemidef := by
    have hcomp := hA.conjTranspose_mul_mul_same H
    simpa [C, Matrix.conjTranspose, Matrix.star_apply] using hcomp
  have hEigLe : ∀ i : r, hC.1.eigenvalues i ≤ alpha := by
    intro i
    let xE : EuclideanSpace ℝ r := hC.1.eigenvectorBasis i
    let x : r → ℝ := ⇑xE
    have hnorm : x ⬝ᵥ x = 1 := by
      have hnorm1 : ‖xE‖ = 1 := hC.1.eigenvectorBasis.orthonormal.1 i
      have hnormsq : ‖xE‖ ^ 2 = (1 : ℝ) := by rw [hnorm1]; norm_num
      have hsum := (EuclideanSpace.real_norm_sq_eq xE).symm
      calc
        x ⬝ᵥ x = ∑ j : r, xE j ^ 2 := by
          simp [x, dotProduct, pow_two]
        _ = ‖xE‖ ^ 2 := hsum
        _ = 1 := hnormsq
    let v : k → ℝ := H *ᵥ x
    have hBunit : v ⬝ᵥ (B *ᵥ v) = 1 := by
      calc
        v ⬝ᵥ (B *ᵥ v) = x ⬝ᵥ ((Hᵀ * B * H) *ᵥ x) := by
          exact (compression_quadratic_eq_image_quadratic B H x).symm
        _ = x ⬝ᵥ x := by rw [hHNorm]; simp
        _ = 1 := hnorm
    have heig : C *ᵥ x = hC.1.eigenvalues i • x := by
      simpa [x, xE] using hC.1.mulVec_eigenvectorBasis i
    have hquad : v ⬝ᵥ (A *ᵥ v) = hC.1.eigenvalues i := by
      calc
        v ⬝ᵥ (A *ᵥ v) = x ⬝ᵥ (C *ᵥ x) := by
          exact (compression_quadratic_eq_image_quadratic A H x).symm
        _ = x ⬝ᵥ (hC.1.eigenvalues i • x) := by rw [heig]
        _ = hC.1.eigenvalues i := by
          simp [dotProduct_smul, hnorm]
    rw [← hquad]
    exact hRayleigh v hBunit
  calc
    (Hᵀ * A * H).det = ∏ i, hC.1.eigenvalues i := by
      simpa [C] using hC.1.det_eq_prod_eigenvalues
    _ ≤ ∏ _i : r, alpha := by
      exact Finset.prod_le_prod
        (fun i _ => hC.eigenvalues_nonneg i) (fun i _ => hEigLe i)
    _ = ∏ j, lambda j := by
      apply Finset.prod_congr rfl
      intro j _
      exact (hTie j).symm

/-- A tied normalized generalized-eigenblock at a scalar Rayleigh upper bound
is the independently attained determinant-objective maximizer.

This identifies the spectral and compact-attainment witnesses in the plateau
case without taking objective maximality as a premise. -/
theorem generalizedEigenDetObjectiveMaximizer_of_posSemidef_tied_rayleigh
    (A B : Matrix k k ℝ) (hA : A.PosSemidef)
    (lambda : r → ℝ) (alpha : ℝ) (G : Matrix k r ℝ)
    (hEig : generalizedEigenvectorColumns A B lambda G)
    (hNorm : generalizedEigenvectorBNormalized B G)
    (hTie : ∀ j, lambda j = alpha)
    (hRayleigh : generalizedEigenRayleighUpperBound A B alpha) :
    generalizedEigenDetObjectiveMaximizer A B G := by
  refine ⟨hNorm, ?_⟩
  intro H hHNorm
  rw [generalizedEigenDetObjective_eq_compressed_det_of_normalized A B H hHNorm,
    generalizedEigenDetObjective_eq_prod_eigenvalues_of_normalized
      A B lambda G hEig hNorm]
  exact generalizedEigenDetProductUpperBound_of_posSemidef_tied_rayleigh
    A B hA lambda alpha hTie hRayleigh H hHNorm

/-- Whitening transports Mathlib's largest ordered Hermitian eigenvalue into
a scalar generalized Rayleigh upper bound.

The factor `T` may be rectangular. Thus the theorem applies directly to the
canonical Hansen factorizations `A = X̃' M X̃`, `B = X̃'X̃` and
`A = Ỹ' M Ỹ`, `B = Ỹ'Ỹ`. -/
theorem generalizedEigenRayleighUpperBound_of_whitened_top
    {q : Type*} [Fintype q] [DecidableEq q] [Nonempty q]
    (A B : Matrix k k ℝ) (M : Matrix q q ℝ) (T : Matrix q k ℝ)
    (hA : A = Tᵀ * M * T) (hB : B = Tᵀ * T)
    (hM : M.IsHermitian) :
    generalizedEigenRayleighUpperBound A B
      (hM.eigenvalues₀ ⟨0, Fintype.card_pos⟩) := by
  classical
  intro v hBunit
  let z : EuclideanSpace ℝ q := WithLp.toLp 2 (T *ᵥ v)
  have hunit : (z : q → ℝ) ⬝ᵥ (z : q → ℝ) = 1 := by
    calc
      (z : q → ℝ) ⬝ᵥ (z : q → ℝ) =
          (T *ᵥ v) ⬝ᵥ ((1 : Matrix q q ℝ) *ᵥ (T *ᵥ v)) := by
            simp [z]
      _ = v ⬝ᵥ ((Tᵀ * (1 : Matrix q q ℝ) * T) *ᵥ v) := by
        exact (compression_quadratic_eq_image_quadratic
          (1 : Matrix q q ℝ) T v).symm
      _ = v ⬝ᵥ (B *ᵥ v) := by simp [hB, Matrix.mul_assoc]
      _ = 1 := hBunit
  have hzero :
      ∀ i : Fin (Fintype.card q), i < ⟨0, Fintype.card_pos⟩ →
        hM.eigenvectorBasis.repr z
          ((Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card q))) i) = 0 := by
    intro i hi
    simp at hi
  have htop :=
    quadForm_le_ordered_eigenvalue_of_unit_of_zero_before
      (M := M) hM ⟨0, Fintype.card_pos⟩ z hunit hzero
  calc
    v ⬝ᵥ (A *ᵥ v) = v ⬝ᵥ ((Tᵀ * M * T) *ᵥ v) := by rw [hA]
    _ = (T *ᵥ v) ⬝ᵥ (M *ᵥ (T *ᵥ v)) :=
      compression_quadratic_eq_image_quadratic M T v
    _ ≤ hM.eigenvalues₀ ⟨0, Fintype.card_pos⟩ := by
      simpa [z] using htop

/-- Ordered spectral block equals the determinant-objective maximizer in the
top plateau case after whitening.

This is the exact multi-column spectral/attainment identification available
without a general multiplicative interlacing theorem: the selected roots are
required only to equal the largest ordered eigenvalue of the whitened PSD
matrix, rather than assuming the determinant objective itself is maximal. -/
theorem
    generalizedEigenDetObjectiveMaximizer_of_whitened_posSemidef_tied_top
    {q : Type*} [Fintype q] [DecidableEq q] [Nonempty q]
    (A B : Matrix k k ℝ) (M : Matrix q q ℝ) (T : Matrix q k ℝ)
    (lambda : r → ℝ) (G : Matrix k r ℝ)
    (hA : A = Tᵀ * M * T) (hB : B = Tᵀ * T)
    (hM : M.PosSemidef)
    (hEig : generalizedEigenvectorColumns A B lambda G)
    (hNorm : generalizedEigenvectorBNormalized B G)
    (hTie : ∀ j, lambda j =
      hM.1.eigenvalues₀ ⟨0, Fintype.card_pos⟩) :
    generalizedEigenDetObjectiveMaximizer A B G := by
  have hApsd : A.PosSemidef := by
    rw [hA]
    have hcomp := hM.conjTranspose_mul_mul_same T
    simpa [Matrix.conjTranspose, Matrix.star_apply] using hcomp
  exact generalizedEigenDetObjectiveMaximizer_of_posSemidef_tied_rayleigh
    A B hApsd lambda (hM.1.eigenvalues₀ ⟨0, Fintype.card_pos⟩) G
      hEig hNorm hTie
      (generalizedEigenRayleighUpperBound_of_whitened_top
        A B M T hA hB hM.1)

omit [Fintype r] [DecidableEq r] in
private theorem rankOne_compression_entry_eq_dot
    [Unique r] (A : Matrix k k ℝ) (H : Matrix k r ℝ) :
    (Hᵀ * A * H) default default =
      (fun i => H i default) ⬝ᵥ (A *ᵥ fun i => H i default) := by
  calc
    (Hᵀ * A * H) default default =
        ∑ x, (∑ y, H y default * A y x) * H x default := by
      simp [Matrix.mul_apply, Matrix.transpose_apply]
    _ = ∑ y, H y default * ∑ x, A y x * H x default := by
      calc
        ∑ x, (∑ y, H y default * A y x) * H x default =
            ∑ x, ∑ y, (H y default * A y x) * H x default := by
          simp [Finset.sum_mul]
        _ = ∑ y, ∑ x, (H y default * A y x) * H x default := by
          rw [Finset.sum_comm]
        _ = ∑ y, H y default * ∑ x, A y x * H x default := by
          refine Finset.sum_congr rfl ?_
          intro y _
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro x _
          ring
    _ = (fun i => H i default) ⬝ᵥ (A *ᵥ fun i => H i default) := by
      simp [Matrix.mulVec, dotProduct]

omit [Fintype r] in
/-- In a one-column block, the `B`-normalization `H'BH = 1` is exactly the
scalar quadratic normalization for the unique column of `H`.

This is the rank-one bridge from Hansen's determinant/product generalized
pencil notation to the ordinary Rayleigh-quotient surface. -/
theorem generalizedEigenvectorBNormalized_rankOne_dot
    [Unique r] (B : Matrix k k ℝ) (H : Matrix k r ℝ)
    (hNorm : generalizedEigenvectorBNormalized B H) :
    (fun i => H i default) ⬝ᵥ (B *ᵥ fun i => H i default) = 1 := by
  have hentry := congrFun (congrFun hNorm default) default
  rw [← rankOne_compression_entry_eq_dot B H]
  simpa [generalizedEigenvectorBNormalized] using hentry

/-- A one-column compressed determinant is the scalar quadratic form of the
unique column.

This removes the determinant bookkeeping from the rank-one case of the
generalized-pencil variational theorem needed by Hansen Theorem 11.7. -/
theorem generalizedEigen_rankOne_compressed_det_eq_dot
    [Unique r] (A : Matrix k k ℝ) (H : Matrix k r ℝ) :
    (Hᵀ * A * H).det =
      (fun i => H i default) ⬝ᵥ (A *ᵥ fun i => H i default) := by
  rw [Matrix.det_unique]
  exact rankOne_compression_entry_eq_dot A H

/-- Rank-one generalized-pencil product upper bound from a scalar Rayleigh
upper bound.

For one selected column, Hansen's product determinant inequality is exactly the
Rayleigh inequality for vectors normalized by `v'Bv = 1`. -/
theorem generalizedEigenDetProductUpperBound_rankOne_of_rayleigh_bound
    [Unique r] (A B : Matrix k k ℝ) (lambda : r → ℝ)
    (hBound : ∀ v : k → ℝ, v ⬝ᵥ (B *ᵥ v) = 1 →
      v ⬝ᵥ (A *ᵥ v) ≤ lambda default) :
    generalizedEigenDetProductUpperBound A B lambda := by
  intro H hHNorm
  calc
    (Hᵀ * A * H).det =
        (fun i => H i default) ⬝ᵥ (A *ᵥ fun i => H i default) := by
      exact generalizedEigen_rankOne_compressed_det_eq_dot A H
    _ ≤ lambda default :=
      hBound (fun i => H i default)
        (generalizedEigenvectorBNormalized_rankOne_dot B H hHNorm)
    _ = ∏ j, lambda j := by
      simp

/-- Rank-one generalized-pencil product lower bound from a scalar Rayleigh
lower bound.

This is the `A⊥`-side counterpart of
`generalizedEigenDetProductUpperBound_rankOne_of_rayleigh_bound`. -/
theorem generalizedEigenDetProductLowerBound_rankOne_of_rayleigh_bound
    [Unique r] (A B : Matrix k k ℝ) (lambda : r → ℝ)
    (hBound : ∀ v : k → ℝ, v ⬝ᵥ (B *ᵥ v) = 1 →
      lambda default ≤ v ⬝ᵥ (A *ᵥ v)) :
    generalizedEigenDetProductLowerBound A B lambda := by
  intro H hHNorm
  calc
    ∏ j, lambda j = lambda default := by
      simp
    _ ≤ (fun i => H i default) ⬝ᵥ (A *ᵥ fun i => H i default) :=
      hBound (fun i => H i default)
        (generalizedEigenvectorBNormalized_rankOne_dot B H hHNorm)
    _ = (Hᵀ * A * H).det := by
      exact (generalizedEigen_rankOne_compressed_det_eq_dot A H).symm

/-- Rank-one ordinary Hermitian determinant/product upper bound for an
identity denominator.

This is the one-column case of the determinant variational theorem when the
generalized pencil has already been whitened to denominator `I`: it reuses the
repo's ordered-Hermitian Rayleigh bound. -/
theorem generalizedEigenDetProductUpperBound_rankOne_identity_of_isHermitian_top
    [Unique r] [DecidableEq k] [Nonempty k]
    (A : Matrix k k ℝ) (hA : A.IsHermitian)
    (lambda : r → ℝ)
    (hLambda : lambda default =
      hA.eigenvalues₀ ⟨0, Fintype.card_pos⟩) :
    generalizedEigenDetProductUpperBound A 1 lambda :=
  generalizedEigenDetProductUpperBound_rankOne_of_rayleigh_bound A 1 lambda <| by
    intro v hunit
    have hunit' :
        ((WithLp.toLp 2 v : EuclideanSpace ℝ k) : k → ℝ) ⬝ᵥ
          ((WithLp.toLp 2 v : EuclideanSpace ℝ k) : k → ℝ) = 1 := by
      simpa using hunit
    have hzero :
        ∀ i : Fin (Fintype.card k), i < ⟨0, Fintype.card_pos⟩ →
          hA.eigenvectorBasis.repr (WithLp.toLp 2 v : EuclideanSpace ℝ k)
            ((Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card k))) i) = 0 := by
      intro i hi
      simp at hi
    have hle :=
      quadForm_le_ordered_eigenvalue_of_unit_of_zero_before
        (M := A) hA ⟨0, Fintype.card_pos⟩
        (WithLp.toLp 2 v : EuclideanSpace ℝ k) hunit' hzero
    simpa [hLambda] using hle

/-- Rank-one ordinary Hermitian determinant/product lower bound for an
identity denominator, expressed as the negative top eigenvalue of `-A`.

This is the dual Rayleigh bridge used for one-column lower-bound surfaces such
as Hansen's `A⊥` side after whitening. -/
theorem generalizedEigenDetProductLowerBound_rankOne_identity_of_isHermitian_neg_top
    [Unique r] [DecidableEq k] [Nonempty k]
    (A : Matrix k k ℝ) (hA : A.IsHermitian)
    (lambda : r → ℝ)
    (hLambda : lambda default =
      -((hA.neg).eigenvalues₀ ⟨0, Fintype.card_pos⟩)) :
    generalizedEigenDetProductLowerBound A 1 lambda :=
  generalizedEigenDetProductLowerBound_rankOne_of_rayleigh_bound A 1 lambda <| by
    intro v hunit
    have hunit' :
        ((WithLp.toLp 2 v : EuclideanSpace ℝ k) : k → ℝ) ⬝ᵥ
          ((WithLp.toLp 2 v : EuclideanSpace ℝ k) : k → ℝ) = 1 := by
      simpa using hunit
    have hzero :
        ∀ i : Fin (Fintype.card k), i < ⟨0, Fintype.card_pos⟩ →
          (hA.neg).eigenvectorBasis.repr (WithLp.toLp 2 v : EuclideanSpace ℝ k)
            ((Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card k))) i) = 0 := by
      intro i hi
      simp at hi
    have hle :=
      quadForm_le_ordered_eigenvalue_of_unit_of_zero_before
        (M := -A) hA.neg ⟨0, Fintype.card_pos⟩
        (WithLp.toLp 2 v : EuclideanSpace ℝ k) hunit' hzero
    have hle' :
        -(v ⬝ᵥ (A *ᵥ v)) ≤ (hA.neg).eigenvalues₀ ⟨0, Fintype.card_pos⟩ := by
      simpa [Matrix.mulVec, dotProduct, Finset.sum_neg_distrib] using hle
    have hlower : -((hA.neg).eigenvalues₀ ⟨0, Fintype.card_pos⟩) ≤
        v ⬝ᵥ (A *ᵥ v) := neg_le.mp hle'
    simpa [hLambda] using hlower

/-- A generalized-eigenvector block satisfying the compressed determinant
maximum gives the product upper-bound min-max theorem. -/
theorem generalizedEigenDetProductUpperBound_of_selected_compressedDet_maximal
    (A B : Matrix k k ℝ) (lambda : r → ℝ) (G : Matrix k r ℝ)
    (h : generalizedEigenvectorColumns A B lambda G)
    (hNorm : generalizedEigenvectorBNormalized B G)
    (hMax : generalizedEigenSelectedCompressedDetMaximal A B G) :
    generalizedEigenDetProductUpperBound A B lambda := by
  intro H hHNorm
  calc
    (Hᵀ * A * H).det ≤ (Gᵀ * A * G).det := hMax H hHNorm
    _ = ∏ j, lambda j :=
      generalizedEigenvectorColumns_compressed_det_eq_prod_of_normalized
        A B lambda G h hNorm

/-- A generalized-eigenvector block satisfying the compressed determinant
minimum gives the product lower-bound min-max theorem. -/
theorem generalizedEigenDetProductLowerBound_of_selected_compressedDet_minimal
    (A B : Matrix k k ℝ) (lambda : r → ℝ) (G : Matrix k r ℝ)
    (h : generalizedEigenvectorColumns A B lambda G)
    (hNorm : generalizedEigenvectorBNormalized B G)
    (hMin : generalizedEigenSelectedCompressedDetMinimal A B G) :
    generalizedEigenDetProductLowerBound A B lambda := by
  intro H hHNorm
  calc
    ∏ j, lambda j = (Gᵀ * A * G).det := by
      exact (generalizedEigenvectorColumns_compressed_det_eq_prod_of_normalized
        A B lambda G h hNorm).symm
    _ ≤ (Hᵀ * A * H).det := hMin H hHNorm

/-- Generalized-eigenvalue determinant/product min-max theorem from a
determinant-objective maximizer. The selected generalized eigenvectors identify
the maximizer's compressed determinant with the product of selected roots. -/
theorem generalizedEigenDetProductUpperBound_of_detObjectiveMaximizer
    (A B : Matrix k k ℝ) (lambda : r → ℝ) (G : Matrix k r ℝ)
    (h : generalizedEigenvectorColumns A B lambda G)
    (hOpt : generalizedEigenDetObjectiveMaximizer A B G) :
    generalizedEigenDetProductUpperBound A B lambda :=
  generalizedEigenDetProductUpperBound_of_selected_compressedDet_maximal
    A B lambda G h hOpt.1
    (generalizedEigenSelectedCompressedDetMaximal_of_detObjectiveMaximizer
      A B G hOpt)

/-- Dual generalized-eigenvalue determinant/product min-max theorem from a
determinant-objective minimizer. -/
theorem generalizedEigenDetProductLowerBound_of_detObjectiveMinimizer
    (A B : Matrix k k ℝ) (lambda : r → ℝ) (G : Matrix k r ℝ)
    (h : generalizedEigenvectorColumns A B lambda G)
    (hOpt : generalizedEigenDetObjectiveMinimizer A B G) :
    generalizedEigenDetProductLowerBound A B lambda :=
  generalizedEigenDetProductLowerBound_of_selected_compressedDet_minimal
    A B lambda G h hOpt.1
    (generalizedEigenSelectedCompressedDetMinimal_of_detObjectiveMinimizer
      A B G hOpt)

/-- Compression-form route to the generalized-pencil product upper bound.

This isolates a useful intermediate target for a raw variational theorem:
every normalized competitor may be compared through an invariant compression
matrix whose determinant is bounded by the selected root product. -/
theorem generalizedEigenDetProductUpperBound_of_compression_det_bound
    (A B : Matrix k k ℝ) (lambda : r → ℝ)
    (hBound : ∀ H : Matrix k r ℝ, generalizedEigenvectorBNormalized B H →
      ∃ C : Matrix r r ℝ, generalizedEigenCompression A B H C ∧
        C.det ≤ ∏ j, lambda j) :
    generalizedEigenDetProductUpperBound A B lambda := by
  intro H hHNorm
  rcases hBound H hHNorm with ⟨C, hComp, hCdet⟩
  calc
    (Hᵀ * A * H).det = generalizedEigenDetObjective A B H := by
      exact (generalizedEigenDetObjective_eq_compressed_det_of_normalized
        A B H hHNorm).symm
    _ = C.det :=
      generalizedEigenDetObjective_eq_det_compression_of_normalized
        A B H C hComp hHNorm
    _ ≤ ∏ j, lambda j := hCdet

/-- Compression-form route to the generalized-pencil product lower bound.

This is the dual counterpart of
`generalizedEigenDetProductUpperBound_of_compression_det_bound`. -/
theorem generalizedEigenDetProductLowerBound_of_compression_det_bound
    (A B : Matrix k k ℝ) (lambda : r → ℝ)
    (hBound : ∀ H : Matrix k r ℝ, generalizedEigenvectorBNormalized B H →
      ∃ C : Matrix r r ℝ, generalizedEigenCompression A B H C ∧
        ∏ j, lambda j ≤ C.det) :
    generalizedEigenDetProductLowerBound A B lambda := by
  intro H hHNorm
  rcases hBound H hHNorm with ⟨C, hComp, hCdet⟩
  calc
    ∏ j, lambda j ≤ C.det := hCdet
    _ = generalizedEigenDetObjective A B H := by
      exact (generalizedEigenDetObjective_eq_det_compression_of_normalized
        A B H C hComp hHNorm).symm
    _ = (Hᵀ * A * H).det :=
      generalizedEigenDetObjective_eq_compressed_det_of_normalized A B H hHNorm

variable {q : Type*}

/-- Whitening route to the generalized-pencil product upper bound.

If a generalized pencil can be written as `A = T' M T` and `B = T' T`, then
every `B`-normalized competitor `H` is sent to an ordinary orthonormal
competitor `T H` for the identity-denominator pencil `(M, I)`. Thus the raw
generalized product theorem reduces to the standard identity-denominator
determinant product theorem. -/
theorem generalizedEigenDetProductUpperBound_of_whitened_identity
    [Fintype q] [DecidableEq q]
    (A B : Matrix k k ℝ) (M : Matrix q q ℝ) (T : Matrix q k ℝ)
    (lambda : r → ℝ)
    (hA : A = Tᵀ * M * T)
    (hB : B = Tᵀ * T)
    (hBound : generalizedEigenDetProductUpperBound M 1 lambda) :
    generalizedEigenDetProductUpperBound A B lambda := by
  intro H hHNorm
  have hKNorm : generalizedEigenvectorBNormalized (1 : Matrix q q ℝ) (T * H) := by
    calc
      (T * H)ᵀ * (1 : Matrix q q ℝ) * (T * H)
          = Hᵀ * Tᵀ * T * H := by
            simp [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = Hᵀ * B * H := by
            simp [hB, Matrix.mul_assoc]
      _ = 1 := hHNorm
  have hdet :
      (Hᵀ * A * H).det = ((T * H)ᵀ * M * (T * H)).det := by
    congr 1
    calc
      Hᵀ * A * H = Hᵀ * (Tᵀ * M * T) * H := by rw [hA]
      _ = (T * H)ᵀ * M * (T * H) := by
            simp [Matrix.transpose_mul, Matrix.mul_assoc]
  rw [hdet]
  exact hBound (T * H) hKNorm

/-- Whitening route to the generalized-pencil product lower bound.

This is the dual counterpart of
`generalizedEigenDetProductUpperBound_of_whitened_identity`: after the
factorization `A = T' M T`, `B = T' T`, the generalized lower-bound problem is
reduced to the ordinary identity-denominator lower-bound problem for `M`. -/
theorem generalizedEigenDetProductLowerBound_of_whitened_identity
    [Fintype q] [DecidableEq q]
    (A B : Matrix k k ℝ) (M : Matrix q q ℝ) (T : Matrix q k ℝ)
    (lambda : r → ℝ)
    (hA : A = Tᵀ * M * T)
    (hB : B = Tᵀ * T)
    (hBound : generalizedEigenDetProductLowerBound M 1 lambda) :
    generalizedEigenDetProductLowerBound A B lambda := by
  intro H hHNorm
  have hKNorm : generalizedEigenvectorBNormalized (1 : Matrix q q ℝ) (T * H) := by
    calc
      (T * H)ᵀ * (1 : Matrix q q ℝ) * (T * H)
          = Hᵀ * Tᵀ * T * H := by
            simp [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = Hᵀ * B * H := by
            simp [hB, Matrix.mul_assoc]
      _ = 1 := hHNorm
  have hdet :
      (Hᵀ * A * H).det = ((T * H)ᵀ * M * (T * H)).det := by
    congr 1
    calc
      Hᵀ * A * H = Hᵀ * (Tᵀ * M * T) * H := by rw [hA]
      _ = (T * H)ᵀ * M * (T * H) := by
            simp [Matrix.transpose_mul, Matrix.mul_assoc]
  rw [hdet]
  exact hBound (T * H) hKNorm

/-- Ordinary identity-denominator determinant/product upper bound from a
selected compressed-determinant maximum.

This is the multi-column bridge needed after whitening a generalized pencil:
once the denominator is `I`, the product bound follows from the ordinary
orthonormal-column compressed determinant maximum and the selected eigenvector
equations. -/
theorem generalizedEigenDetProductUpperBound_identity_of_selected_compressedDet_maximal
    [DecidableEq k]
    (A : Matrix k k ℝ) (lambda : r → ℝ) (G : Matrix k r ℝ)
    (h : generalizedEigenvectorColumns A (1 : Matrix k k ℝ) lambda G)
    (hNorm : Gᵀ * G = 1)
    (hMax : ∀ H : Matrix k r ℝ, Hᵀ * H = 1 →
      (Hᵀ * A * H).det ≤ (Gᵀ * A * G).det) :
    generalizedEigenDetProductUpperBound A (1 : Matrix k k ℝ) lambda := by
  refine generalizedEigenDetProductUpperBound_of_selected_compressedDet_maximal
    A (1 : Matrix k k ℝ) lambda G h ?_ ?_
  · simpa [generalizedEigenvectorBNormalized, Matrix.mul_assoc] using hNorm
  · intro H hHNorm
    exact hMax H (by
      simpa [generalizedEigenvectorBNormalized, Matrix.mul_assoc] using hHNorm)

/-- Ordinary identity-denominator determinant/product lower bound from a
selected compressed-determinant minimum.

This is the dual ordinary bridge for Hansen's `A⊥` side after whitening. -/
theorem generalizedEigenDetProductLowerBound_identity_of_selected_compressedDet_minimal
    [DecidableEq k]
    (A : Matrix k k ℝ) (lambda : r → ℝ) (G : Matrix k r ℝ)
    (h : generalizedEigenvectorColumns A (1 : Matrix k k ℝ) lambda G)
    (hNorm : Gᵀ * G = 1)
    (hMin : ∀ H : Matrix k r ℝ, Hᵀ * H = 1 →
      (Gᵀ * A * G).det ≤ (Hᵀ * A * H).det) :
    generalizedEigenDetProductLowerBound A (1 : Matrix k k ℝ) lambda := by
  refine generalizedEigenDetProductLowerBound_of_selected_compressedDet_minimal
    A (1 : Matrix k k ℝ) lambda G h ?_ ?_
  · simpa [generalizedEigenvectorBNormalized, Matrix.mul_assoc] using hNorm
  · intro H hHNorm
    exact hMin H (by
      simpa [generalizedEigenvectorBNormalized, Matrix.mul_assoc] using hHNorm)

private theorem det_orthonormal_conj_eq_det
    [DecidableEq k] (A : Matrix k k ℝ) (H : Matrix k k ℝ)
    (hH : Hᵀ * H = 1) :
    (Hᵀ * A * H).det = A.det := by
  have hdetH : H.det * H.det = (1 : ℝ) := by
    have hdet := congrArg Matrix.det hH
    simpa [Matrix.det_mul, Matrix.det_transpose] using hdet
  calc
    (Hᵀ * A * H).det = H.det * A.det * H.det := by
      rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
    _ = H.det * H.det * A.det := by ring
    _ = A.det := by
      rw [hdetH]
      ring

private theorem generalizedEigenSelectedRootProduct_eq_det_of_square_orthonormal
    [DecidableEq k] (A : Matrix k k ℝ) (lambda : k → ℝ) (G : Matrix k k ℝ)
    (h : generalizedEigenvectorColumns A (1 : Matrix k k ℝ) lambda G)
    (hNorm : Gᵀ * G = 1) :
    ∏ j, lambda j = A.det := by
  have hNorm' : generalizedEigenvectorBNormalized (1 : Matrix k k ℝ) G := by
    simpa [generalizedEigenvectorBNormalized, Matrix.mul_assoc] using hNorm
  calc
    ∏ j, lambda j = (Gᵀ * A * G).det := by
      exact (generalizedEigenvectorColumns_compressed_det_eq_prod_of_normalized
        A (1 : Matrix k k ℝ) lambda G h hNorm').symm
    _ = A.det := det_orthonormal_conj_eq_det A G hNorm

omit [Fintype r] [DecidableEq r] in
private theorem transpose_mul_columnReindex_eq_one
    [DecidableEq k] [DecidableEq r] (e : k ≃ r)
    (G : Matrix k r ℝ) (hG : Gᵀ * G = 1) :
    (G.submatrix id e)ᵀ * (G.submatrix id e) = 1 := by
  ext i j
  calc
    ((G.submatrix id e)ᵀ * (G.submatrix id e)) i j =
        (Gᵀ * G) (e i) (e j) := by
          simp [Matrix.mul_apply, Matrix.transpose_apply]
    _ = (1 : Matrix r r ℝ) (e i) (e j) := by rw [hG]
    _ = (1 : Matrix k k ℝ) i j := by
          by_cases hij : i = j
          · subst j
            simp
          · have heij : e i ≠ e j := fun h => hij (e.injective h)
            simp [hij, heij]

omit [DecidableEq r] in
private theorem det_columnReindex_compression_eq
    [DecidableEq k] [DecidableEq r] (e : k ≃ r)
    (A : Matrix k k ℝ) (H : Matrix k r ℝ) :
    ((H.submatrix id e)ᵀ * A * (H.submatrix id e)).det =
      (Hᵀ * A * H).det := by
  have hmat :
      (H.submatrix id e)ᵀ * A * (H.submatrix id e) =
        (Hᵀ * A * H).submatrix e e := by
    ext i j
    simp [Matrix.mul_apply, Matrix.transpose_apply]
  rw [hmat]
  exact Matrix.det_submatrix_equiv_self e (Hᵀ * A * H)

/-- Ordinary full-basis identity-denominator determinant/product upper bound.

When the selected ordinary eigenvector block is square and orthonormal, every
orthonormal competitor is an orthogonal change of coordinates. The compressed
determinant is therefore exactly `det A`, and the selected eigenvector equations
identify `det A` with `∏ λ_j`. This proves the multi-column product bound
without an external selected-compressed-determinant maximality premise in the
full selected-basis case. -/
theorem generalizedEigenDetProductUpperBound_identity_of_square_orthonormal_eigenbasis
    [DecidableEq k]
    (A : Matrix k k ℝ) (lambda : k → ℝ) (G : Matrix k k ℝ)
    (h : generalizedEigenvectorColumns A (1 : Matrix k k ℝ) lambda G)
    (hNorm : Gᵀ * G = 1) :
    generalizedEigenDetProductUpperBound A (1 : Matrix k k ℝ) lambda := by
  intro H hHNorm
  have hHNorm' : Hᵀ * H = 1 := by
    simpa [generalizedEigenvectorBNormalized, Matrix.mul_assoc] using hHNorm
  have hProd := generalizedEigenSelectedRootProduct_eq_det_of_square_orthonormal
    A lambda G h hNorm
  calc
    (Hᵀ * A * H).det = A.det := det_orthonormal_conj_eq_det A H hHNorm'
    _ = ∏ j, lambda j := hProd.symm
    _ ≤ ∏ j, lambda j := le_rfl

/-- Ordinary full-basis identity-denominator determinant/product lower bound.

This is the lower-bound counterpart of
`generalizedEigenDetProductUpperBound_identity_of_square_orthonormal_eigenbasis`.
In the square orthonormal case the compressed determinant is invariant under
orthogonal coordinate changes, so the upper and lower product inequalities both
hold as equalities. -/
theorem generalizedEigenDetProductLowerBound_identity_of_square_orthonormal_eigenbasis
    [DecidableEq k]
    (A : Matrix k k ℝ) (lambda : k → ℝ) (G : Matrix k k ℝ)
    (h : generalizedEigenvectorColumns A (1 : Matrix k k ℝ) lambda G)
    (hNorm : Gᵀ * G = 1) :
    generalizedEigenDetProductLowerBound A (1 : Matrix k k ℝ) lambda := by
  intro H hHNorm
  have hHNorm' : Hᵀ * H = 1 := by
    simpa [generalizedEigenvectorBNormalized, Matrix.mul_assoc] using hHNorm
  have hProd := generalizedEigenSelectedRootProduct_eq_det_of_square_orthonormal
    A lambda G h hNorm
  calc
    ∏ j, lambda j = A.det := hProd
    _ = (Hᵀ * A * H).det := (det_orthonormal_conj_eq_det A H hHNorm').symm
    _ ≤ (Hᵀ * A * H).det := le_rfl

/-- Ordinary full-basis identity-denominator determinant/product upper bound,
with the selected full basis indexed by any type equivalent to the ambient
index type.

This is the same mathematical statement as
`generalizedEigenDetProductUpperBound_identity_of_square_orthonormal_eigenbasis`,
but it reindexes the selected columns before applying the square theorem. It is
useful for theorem surfaces that keep Hansen's selected-root index type separate
from the matrix row/column type. -/
theorem generalizedEigenDetProductUpperBound_identity_of_equiv_orthonormal_eigenbasis
    [DecidableEq k] [DecidableEq r] (e : k ≃ r)
    (A : Matrix k k ℝ) (lambda : r → ℝ) (G : Matrix k r ℝ)
    (h : generalizedEigenvectorColumns A (1 : Matrix k k ℝ) lambda G)
    (hNorm : Gᵀ * G = 1) :
    generalizedEigenDetProductUpperBound A (1 : Matrix k k ℝ) lambda := by
  let lambdaSq : k → ℝ := fun i => lambda (e i)
  let Gsq : Matrix k k ℝ := G.submatrix id e
  have hSq : generalizedEigenvectorColumns A (1 : Matrix k k ℝ) lambdaSq Gsq := by
    intro i
    simpa [lambdaSq, Gsq] using h (e i)
  have hSqNorm : Gsqᵀ * Gsq = 1 := by
    simpa [Gsq] using transpose_mul_columnReindex_eq_one e G hNorm
  have hBound :=
    generalizedEigenDetProductUpperBound_identity_of_square_orthonormal_eigenbasis
      A lambdaSq Gsq hSq hSqNorm
  intro H hHNorm
  have hHNorm' : Hᵀ * H = 1 := by
    simpa [generalizedEigenvectorBNormalized, Matrix.mul_assoc] using hHNorm
  have hHSqNorm : (H.submatrix id e)ᵀ * (H.submatrix id e) = 1 :=
    transpose_mul_columnReindex_eq_one e H hHNorm'
  have hHSqNorm' :
      generalizedEigenvectorBNormalized (1 : Matrix k k ℝ) (H.submatrix id e) := by
    simpa [generalizedEigenvectorBNormalized, Matrix.mul_assoc] using hHSqNorm
  calc
    (Hᵀ * A * H).det =
        ((H.submatrix id e)ᵀ * A * (H.submatrix id e)).det := by
          exact (det_columnReindex_compression_eq e A H).symm
    _ ≤ ∏ i : k, lambdaSq i := hBound (H.submatrix id e) hHSqNorm'
    _ = ∏ j : r, lambda j := by
      simpa [lambdaSq] using Equiv.prod_comp e lambda

/-- Ordinary full-basis identity-denominator determinant/product lower bound,
with the selected full basis indexed by any type equivalent to the ambient
index type. -/
theorem generalizedEigenDetProductLowerBound_identity_of_equiv_orthonormal_eigenbasis
    [DecidableEq k] [DecidableEq r] (e : k ≃ r)
    (A : Matrix k k ℝ) (lambda : r → ℝ) (G : Matrix k r ℝ)
    (h : generalizedEigenvectorColumns A (1 : Matrix k k ℝ) lambda G)
    (hNorm : Gᵀ * G = 1) :
    generalizedEigenDetProductLowerBound A (1 : Matrix k k ℝ) lambda := by
  let lambdaSq : k → ℝ := fun i => lambda (e i)
  let Gsq : Matrix k k ℝ := G.submatrix id e
  have hSq : generalizedEigenvectorColumns A (1 : Matrix k k ℝ) lambdaSq Gsq := by
    intro i
    simpa [lambdaSq, Gsq] using h (e i)
  have hSqNorm : Gsqᵀ * Gsq = 1 := by
    simpa [Gsq] using transpose_mul_columnReindex_eq_one e G hNorm
  have hBound :=
    generalizedEigenDetProductLowerBound_identity_of_square_orthonormal_eigenbasis
      A lambdaSq Gsq hSq hSqNorm
  intro H hHNorm
  have hHNorm' : Hᵀ * H = 1 := by
    simpa [generalizedEigenvectorBNormalized, Matrix.mul_assoc] using hHNorm
  have hHSqNorm : (H.submatrix id e)ᵀ * (H.submatrix id e) = 1 :=
    transpose_mul_columnReindex_eq_one e H hHNorm'
  have hHSqNorm' :
      generalizedEigenvectorBNormalized (1 : Matrix k k ℝ) (H.submatrix id e) := by
    simpa [generalizedEigenvectorBNormalized, Matrix.mul_assoc] using hHSqNorm
  calc
    ∏ j : r, lambda j = ∏ i : k, lambdaSq i := by
      have hProdReindex : (∏ i : k, lambdaSq i) = ∏ j : r, lambda j := by
        simpa [lambdaSq] using Equiv.prod_comp e lambda
      exact hProdReindex.symm
    _ ≤ ((H.submatrix id e)ᵀ * A * (H.submatrix id e)).det :=
      hBound (H.submatrix id e) hHSqNorm'
    _ = (Hᵀ * A * H).det := det_columnReindex_compression_eq e A H

/-- Ordinary full-basis identity-denominator selected compressed-determinant
maximum.

This is the determinant-extrema form of
`generalizedEigenDetProductUpperBound_identity_of_equiv_orthonormal_eigenbasis`:
when the selected orthonormal eigenvectors span the ambient whitened space, the
selected compressed determinant is maximal over all orthonormal competitors. -/
theorem generalizedEigenSelectedCompressedDetMaximal_identity_of_equiv_orthonormal_eigenbasis
    [DecidableEq k] [DecidableEq r] (e : k ≃ r)
    (A : Matrix k k ℝ) (lambda : r → ℝ) (G : Matrix k r ℝ)
    (h : generalizedEigenvectorColumns A (1 : Matrix k k ℝ) lambda G)
    (hNorm : Gᵀ * G = 1) :
    generalizedEigenSelectedCompressedDetMaximal A (1 : Matrix k k ℝ) G := by
  have hNorm' : generalizedEigenvectorBNormalized (1 : Matrix k k ℝ) G := by
    simpa [generalizedEigenvectorBNormalized, Matrix.mul_assoc] using hNorm
  have hBound :=
    generalizedEigenDetProductUpperBound_identity_of_equiv_orthonormal_eigenbasis
      e A lambda G h hNorm
  intro H hHNorm
  calc
    (Hᵀ * A * H).det ≤ ∏ j, lambda j := hBound H hHNorm
    _ = (Gᵀ * A * G).det := by
      exact (generalizedEigenvectorColumns_compressed_det_eq_prod_of_normalized
        A (1 : Matrix k k ℝ) lambda G h hNorm').symm

/-- Ordinary full-basis identity-denominator selected compressed-determinant
minimum.

This is the determinant-extrema counterpart of
`generalizedEigenDetProductLowerBound_identity_of_equiv_orthonormal_eigenbasis`;
it is useful for the trailing/full-basis side of whitened reduced-rank
pencils. -/
theorem generalizedEigenSelectedCompressedDetMinimal_identity_of_equiv_orthonormal_eigenbasis
    [DecidableEq k] [DecidableEq r] (e : k ≃ r)
    (A : Matrix k k ℝ) (lambda : r → ℝ) (G : Matrix k r ℝ)
    (h : generalizedEigenvectorColumns A (1 : Matrix k k ℝ) lambda G)
    (hNorm : Gᵀ * G = 1) :
    generalizedEigenSelectedCompressedDetMinimal A (1 : Matrix k k ℝ) G := by
  have hNorm' : generalizedEigenvectorBNormalized (1 : Matrix k k ℝ) G := by
    simpa [generalizedEigenvectorBNormalized, Matrix.mul_assoc] using hNorm
  have hBound :=
    generalizedEigenDetProductLowerBound_identity_of_equiv_orthonormal_eigenbasis
      e A lambda G h hNorm
  intro H hHNorm
  calc
    (Gᵀ * A * G).det = ∏ j, lambda j :=
      generalizedEigenvectorColumns_compressed_det_eq_prod_of_normalized
        A (1 : Matrix k k ℝ) lambda G h hNorm'
    _ ≤ (Hᵀ * A * H).det := hBound H hHNorm

omit [Fintype r] [DecidableEq r] in
private theorem posSemidef_of_transpose_eq_self_idempotent
    (P : Matrix k k ℝ) (hPt : Pᵀ = P) (hPid : P * P = P) :
    P.PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · exact (Matrix.conjTranspose_eq_transpose_of_trivial P).trans hPt
  · intro x
    have hquad := quadratic_form_eq_dotProduct_of_symm_idempotent P hPt hPid x
    have hnonneg : 0 ≤ (P *ᵥ x) ⬝ᵥ (P *ᵥ x) := by
      simpa using dotProduct_star_self_nonneg (P *ᵥ x)
    simpa using hquad.symm ▸ hnonneg

omit [Fintype k] [Fintype r] [DecidableEq r] in
private theorem one_sub_transpose_eq_self_of_transpose_eq_self
    [DecidableEq k] (P : Matrix k k ℝ) (hPt : Pᵀ = P) :
    ((1 : Matrix k k ℝ) - P)ᵀ = (1 : Matrix k k ℝ) - P := by
  rw [Matrix.transpose_sub, Matrix.transpose_one, hPt]

omit [Fintype r] [DecidableEq r] in
private theorem one_sub_idempotent_of_idempotent
    [DecidableEq k] (P : Matrix k k ℝ) (hPid : P * P = P) :
    ((1 : Matrix k k ℝ) - P) * ((1 : Matrix k k ℝ) - P) =
      (1 : Matrix k k ℝ) - P := by
  calc
    ((1 : Matrix k k ℝ) - P) * ((1 : Matrix k k ℝ) - P) =
        ((1 : Matrix k k ℝ) - P) * 1 - ((1 : Matrix k k ℝ) - P) * P := by
      rw [Matrix.mul_sub]
    _ = ((1 : Matrix k k ℝ) - P) - (P - P * P) := by
      rw [Matrix.mul_one, Matrix.sub_mul, Matrix.one_mul]
    _ = (1 : Matrix k k ℝ) - P := by rw [hPid]; simp

omit [Fintype r] in
private theorem compression_eq_one_sub_compression
    [DecidableEq k] (P : Matrix k k ℝ) (H : Matrix k r ℝ)
    (hH : Hᵀ * H = 1) :
    Hᵀ * ((1 : Matrix k k ℝ) - P) * H =
      (1 : Matrix r r ℝ) - Hᵀ * P * H := by
  calc
    Hᵀ * ((1 : Matrix k k ℝ) - P) * H =
        (Hᵀ * (1 : Matrix k k ℝ) - Hᵀ * P) * H := by
      rw [Matrix.mul_sub]
    _ = Hᵀ * (1 : Matrix k k ℝ) * H - Hᵀ * P * H := by
      rw [Matrix.sub_mul]
    _ = Hᵀ * H - Hᵀ * P * H := by simp [Matrix.mul_assoc]
    _ = (1 : Matrix r r ℝ) - Hᵀ * P * H := by rw [hH]

omit [Fintype r] in
private theorem compressed_projection_one_sub_posSemidef
    [Finite r]
    (P : Matrix k k ℝ) (H : Matrix k r ℝ)
    (hPt : Pᵀ = P) (hPid : P * P = P) (hH : Hᵀ * H = 1) :
    ((1 : Matrix r r ℝ) - Hᵀ * P * H).PosSemidef := by
  classical
  haveI := Fintype.ofFinite r
  have hPcomp : ((1 : Matrix k k ℝ) - P).PosSemidef :=
    posSemidef_of_transpose_eq_self_idempotent ((1 : Matrix k k ℝ) - P)
      (one_sub_transpose_eq_self_of_transpose_eq_self P hPt)
      (one_sub_idempotent_of_idempotent P hPid)
  have h := hPcomp.conjTranspose_mul_mul_same H
  have hEq := compression_eq_one_sub_compression P H hH
  rw [← hEq]
  simpa [Matrix.conjTranspose, Matrix.star_apply] using h

private theorem posSemidef_eigenvalues_le_one_of_one_sub_posSemidef
    (C : Matrix r r ℝ) (hC : C.PosSemidef)
    (hOne : ((1 : Matrix r r ℝ) - C).PosSemidef) :
    ∀ i : r, hC.1.eigenvalues i ≤ 1 := by
  intro i
  let xE : EuclideanSpace ℝ r := hC.1.eigenvectorBasis i
  let x : r → ℝ := ⇑xE
  have hnonneg := hOne.dotProduct_mulVec_nonneg x
  have heig : C *ᵥ x = hC.1.eigenvalues i • x := by
    simpa [x, xE] using hC.1.mulVec_eigenvectorBasis i
  have hnorm : x ⬝ᵥ x = 1 := by
    have hnorm1 : ‖xE‖ = 1 := hC.1.eigenvectorBasis.orthonormal.1 i
    have hnormsq : ‖xE‖ ^ 2 = (1 : ℝ) := by rw [hnorm1]; norm_num
    have hsum := (EuclideanSpace.real_norm_sq_eq xE).symm
    calc
      x ⬝ᵥ x = ∑ i : r, xE i ^ 2 := by
        simp [x, dotProduct, pow_two]
      _ = ‖xE‖ ^ 2 := hsum
      _ = 1 := hnormsq
  have hquad :
      star x ⬝ᵥ (((1 : Matrix r r ℝ) - C) *ᵥ x) =
        1 - hC.1.eigenvalues i := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, heig]
    simp [dotProduct_sub, dotProduct_smul, hnorm]
  rw [hquad] at hnonneg
  linarith

/-- Partial-column determinant bound for an ordinary orthogonal projection.

If `P` is symmetric and idempotent, every orthonormal column block `H` has
compressed determinant at most `1`. This is the projection-specific partial
leading-block determinant fact needed by Hansen Theorem 11.7 after the G-side
whitening identifies `Ỹ(Ỹ'Ỹ)⁻¹Ỹ'` with the Chapter 3 hat matrix. -/
theorem orthogonalProjection_compressed_det_le_one
    (P : Matrix k k ℝ) (H : Matrix k r ℝ)
    (hPt : Pᵀ = P) (hPid : P * P = P) (hH : Hᵀ * H = 1) :
    (Hᵀ * P * H).det ≤ 1 := by
  classical
  let C : Matrix r r ℝ := Hᵀ * P * H
  have hPpsd : P.PosSemidef :=
    posSemidef_of_transpose_eq_self_idempotent P hPt hPid
  have hC : C.PosSemidef := by
    have h := hPpsd.conjTranspose_mul_mul_same H
    simpa [C, Matrix.conjTranspose, Matrix.star_apply] using h
  have hOne : ((1 : Matrix r r ℝ) - C).PosSemidef := by
    simpa [C] using compressed_projection_one_sub_posSemidef P H hPt hPid hH
  have hEigLe := posSemidef_eigenvalues_le_one_of_one_sub_posSemidef C hC hOne
  calc
    (Hᵀ * P * H).det = ∏ i, hC.1.eigenvalues i := by
      simpa [C] using hC.1.det_eq_prod_eigenvalues
    _ ≤ ∏ _i : r, (1 : ℝ) := by
      exact Finset.prod_le_prod
        (fun i _ => hC.eigenvalues_nonneg i) (fun i _ => hEigLe i)
    _ = 1 := by simp

omit [Fintype r] in
/-- A normalized ordinary generalized-eigenvector block contained in the range
of a projection has displayed roots equal to `1`.

This is the deterministic root-identification bridge for the residualized
projection route in Hansen Theorem 11.7: once the selected whitened columns are
fixed by `P`, the separate assumption `λ_j = 1` is not needed. -/
theorem generalizedEigenProjection_top_roots_of_range
    [DecidableEq k] [Finite r]
    (P : Matrix k k ℝ) (lambda : r → ℝ) (G : Matrix k r ℝ)
    (h : generalizedEigenvectorColumns P (1 : Matrix k k ℝ) lambda G)
    (hNorm : Gᵀ * G = 1)
    (hRange : P * G = G) :
    ∀ j : r, lambda j = 1 := by
  classical
  haveI := Fintype.ofFinite r
  intro j
  let v : k → ℝ := fun i => G i j
  have hEig : P *ᵥ v = lambda j • v := by
    simpa [v, Matrix.one_mulVec] using (h j).2
  have hFixed : P *ᵥ v = v := by
    funext i
    have hEntry := congrArg (fun M : Matrix k r ℝ => M i j) hRange
    simpa [v, Matrix.mul_apply, Matrix.mulVec, dotProduct] using hEntry
  have hScalarVec : lambda j • v = v := by
    rw [hFixed] at hEig
    exact hEig.symm
  have hColNorm : v ⬝ᵥ v = 1 := by
    have hEntry := congrArg (fun M : Matrix r r ℝ => M j j) hNorm
    simpa [v, Matrix.mul_apply, dotProduct, Matrix.one_apply] using hEntry
  have hDot := congrArg (fun w : k → ℝ => v ⬝ᵥ w) hScalarVec
  have hScalar : lambda j * (v ⬝ᵥ v) = v ⬝ᵥ v := by
    simpa [dotProduct_smul, mul_comm, mul_left_comm, mul_assoc] using hDot
  simpa [hColNorm] using hScalar

omit [Fintype r] in
/-- A normalized ordinary generalized-eigenvector block in the nullspace has all
displayed roots equal to zero.

This is the deterministic nullspace bridge for the residual `A⊥` side of
Hansen Theorem 11.7: once the selected whitened columns are killed by the PSD
residual matrix, the separate pointwise zero-root assumption is not needed. -/
theorem generalizedEigenNull_roots_zero
    [DecidableEq k] [Finite r]
    (M : Matrix k k ℝ) (lambda : r → ℝ) (G : Matrix k r ℝ)
    (h : generalizedEigenvectorColumns M (1 : Matrix k k ℝ) lambda G)
    (hNorm : Gᵀ * G = 1)
    (hNull : M * G = 0) :
    ∀ j : r, lambda j = 0 := by
  classical
  haveI := Fintype.ofFinite r
  intro j
  let v : k → ℝ := fun i => G i j
  have hEig : M *ᵥ v = lambda j • v := by
    simpa [v, Matrix.one_mulVec] using (h j).2
  have hZero : M *ᵥ v = 0 := by
    funext i
    have hEntry := congrArg (fun N : Matrix k r ℝ => N i j) hNull
    simpa [v, Matrix.mul_apply, Matrix.mulVec, dotProduct] using hEntry
  have hScalarVec : lambda j • v = 0 := by
    rw [← hEig]
    exact hZero
  have hColNorm : v ⬝ᵥ v = 1 := by
    have hEntry := congrArg (fun N : Matrix r r ℝ => N j j) hNorm
    simpa [v, Matrix.mul_apply, dotProduct, Matrix.one_apply] using hEntry
  have hDot := congrArg (fun w : k → ℝ => v ⬝ᵥ w) hScalarVec
  have hScalar : lambda j * (v ⬝ᵥ v) = 0 := by
    simpa [dotProduct_smul, mul_comm, mul_left_comm, mul_assoc] using hDot
  simpa [hColNorm] using hScalar

/-- A nonempty normalized ordinary generalized-eigenvector block in the nullspace
has zero selected-root product.

This packages `generalizedEigenNull_roots_zero` in the product form consumed by
the existing PSD trailing-block determinant minimum. -/
theorem generalizedEigenNull_rootProduct_eq_zero
    [DecidableEq k] [Nonempty r]
    (M : Matrix k k ℝ) (lambda : r → ℝ) (G : Matrix k r ℝ)
    (h : generalizedEigenvectorColumns M (1 : Matrix k k ℝ) lambda G)
    (hNorm : Gᵀ * G = 1)
    (hNull : M * G = 0) :
    (∏ j, lambda j) = 0 := by
  classical
  rcases (inferInstance : Nonempty r) with ⟨j⟩
  exact Finset.prod_eq_zero (Finset.mem_univ j)
    (generalizedEigenNull_roots_zero M lambda G h hNorm hNull j)

omit [Fintype r] in
private theorem column_ne_zero_of_orthonormal
    (G : Matrix k r ℝ) (hNorm : Gᵀ * G = 1) (j : r) :
    (fun i => G i j) ≠ 0 := by
  intro hzero
  have hEntry := congrArg (fun M : Matrix r r ℝ => M j j) hNorm
  have hColZero : ∀ i, G i j = 0 := by
    intro i
    exact congrFun hzero i
  have hDiag : (∑ i, G i j * G i j) = 1 := by
    simpa [Matrix.mul_apply, dotProduct, Matrix.one_apply] using hEntry
  have hDiagZero : (∑ i, G i j * G i j) = 0 := by
    simp [hColZero]
  rw [hDiagZero] at hDiag
  norm_num at hDiag

set_option linter.unusedSectionVars false in
set_option linter.unusedFintypeInType false in
/-- Orthonormal columns fixed by an ordinary projection are generalized
eigenvector columns with all displayed roots equal to one.

This is a raw ordinary-block constructor for Hansen Theorem 11.7: once the
selected whitened block is known to lie in the projection range, callers no
longer have to separately package the same fact as generalized eigenvectors. -/
theorem generalizedEigenvectorColumns_one_of_range
    [DecidableEq k] (P : Matrix k k ℝ) (G : Matrix k r ℝ)
    (hNorm : Gᵀ * G = 1) (hRange : P * G = G) :
    generalizedEigenvectorColumns P (1 : Matrix k k ℝ) (fun _ : r => (1 : ℝ)) G := by
  intro j
  refine ⟨column_ne_zero_of_orthonormal G hNorm j, ?_⟩
  ext i
  have hEntry := congrArg (fun M : Matrix k r ℝ => M i j) hRange
  simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using hEntry

set_option linter.unusedSectionVars false in
set_option linter.unusedFintypeInType false in
/-- Orthonormal columns killed by an ordinary matrix are generalized eigenvector
columns with all displayed roots equal to zero. -/
theorem generalizedEigenvectorColumns_zero_of_null
    [DecidableEq k] (M : Matrix k k ℝ) (G : Matrix k r ℝ)
    (hNorm : Gᵀ * G = 1) (hNull : M * G = 0) :
    generalizedEigenvectorColumns M (1 : Matrix k k ℝ) (fun _ : r => (0 : ℝ)) G := by
  intro j
  refine ⟨column_ne_zero_of_orthonormal G hNorm j, ?_⟩
  ext i
  have hEntry := congrArg (fun N : Matrix k r ℝ => N i j) hNull
  simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using hEntry

omit [Fintype r] [DecidableEq r] in
/-- Ordinary identity-denominator eigenvector columns with root `1` are fixed
by the numerator matrix. -/
theorem generalizedEigenvectorColumns_range_of_one
    [DecidableEq k] (P : Matrix k k ℝ) (G : Matrix k r ℝ)
    (h : generalizedEigenvectorColumns P (1 : Matrix k k ℝ) (fun _ : r => (1 : ℝ)) G) :
    P * G = G := by
  ext i j
  let v : k → ℝ := fun a => G a j
  have hj : P *ᵥ v = v := by
    simpa [v, Matrix.one_mulVec] using (h j).2
  simpa [v, Matrix.mul_apply, Matrix.mulVec, dotProduct] using congrFun hj i

omit [Fintype r] [DecidableEq r] in
/-- Ordinary identity-denominator eigenvector columns with root `0` are killed
by the numerator matrix. -/
theorem generalizedEigenvectorColumns_null_of_zero
    [DecidableEq k] (M : Matrix k k ℝ) (G : Matrix k r ℝ)
    (h : generalizedEigenvectorColumns M (1 : Matrix k k ℝ) (fun _ : r => (0 : ℝ)) G) :
    M * G = 0 := by
  ext i j
  let v : k → ℝ := fun a => G a j
  have hj : M *ᵥ v = 0 := by
    simpa [v, Matrix.one_mulVec] using (h j).2
  simpa [v, Matrix.mul_apply, Matrix.mulVec, dotProduct] using congrFun hj i

/-- Selected-compressed determinant maximum for a partial block of top
projection eigenvectors.

The selected block is required to be a normalized ordinary eigenvector block
with all displayed roots equal to `1`, the leading eigenvalue of an orthogonal
projection. This avoids the invalid arbitrary-Hermitian selected-eigenspace
claim while proving a genuine multi-column partial-block theorem. -/
theorem generalizedEigenSelectedCompressedDetMaximal_identity_of_projection_top
    [DecidableEq k] (P : Matrix k k ℝ) (lambda : r → ℝ) (G : Matrix k r ℝ)
    (hPt : Pᵀ = P) (hPid : P * P = P)
    (h : generalizedEigenvectorColumns P (1 : Matrix k k ℝ) lambda G)
    (hNorm : Gᵀ * G = 1)
    (hTop : ∀ j : r, lambda j = 1) :
    generalizedEigenSelectedCompressedDetMaximal P (1 : Matrix k k ℝ) G := by
  have hNorm' : generalizedEigenvectorBNormalized (1 : Matrix k k ℝ) G := by
    simpa [generalizedEigenvectorBNormalized, Matrix.mul_assoc] using hNorm
  have hGdet : (Gᵀ * P * G).det = 1 := by
    calc
      (Gᵀ * P * G).det = ∏ j, lambda j :=
        generalizedEigenvectorColumns_compressed_det_eq_prod_of_normalized
          P (1 : Matrix k k ℝ) lambda G h hNorm'
      _ = 1 := by simp [hTop]
  intro H hHNorm
  have hHNorm' : Hᵀ * H = 1 := by
    simpa [generalizedEigenvectorBNormalized, Matrix.mul_assoc] using hHNorm
  calc
    (Hᵀ * P * H).det ≤ 1 :=
      orthogonalProjection_compressed_det_le_one P H hPt hPid hHNorm'
    _ = (Gᵀ * P * G).det := hGdet.symm

/-- Projection-range version of
`generalizedEigenSelectedCompressedDetMaximal_identity_of_projection_top`.

The roots equal to one are derived from `P * G = G`, which is closer to the raw
residualized projection construction than supplying them separately. -/
theorem generalizedEigenSelectedCompressedDetMaximal_identity_of_projection_range
    [DecidableEq k] (P : Matrix k k ℝ) (lambda : r → ℝ) (G : Matrix k r ℝ)
    (hPt : Pᵀ = P) (hPid : P * P = P)
    (h : generalizedEigenvectorColumns P (1 : Matrix k k ℝ) lambda G)
    (hNorm : Gᵀ * G = 1)
    (hRange : P * G = G) :
    generalizedEigenSelectedCompressedDetMaximal P (1 : Matrix k k ℝ) G :=
  generalizedEigenSelectedCompressedDetMaximal_identity_of_projection_top
    P lambda G hPt hPid h hNorm
    (generalizedEigenProjection_top_roots_of_range P lambda G h hNorm hRange)

/-- Selected-compressed determinant minimum for a zero-product block of a
positive semidefinite ordinary matrix.

For Hansen's residual-maker `A⊥` side this is the trailing-zero-eigenspace
route: once the selected ordinary block has zero displayed eigenvalue product,
every orthonormal competitor has nonnegative compressed determinant. -/
theorem generalizedEigenSelectedCompressedDetMinimal_identity_of_posSemidef_zero
    [DecidableEq k] (M : Matrix k k ℝ) (lambda : r → ℝ) (G : Matrix k r ℝ)
    (hM : M.PosSemidef)
    (h : generalizedEigenvectorColumns M (1 : Matrix k k ℝ) lambda G)
    (hNorm : Gᵀ * G = 1)
    (hZeroProduct : (∏ j, lambda j) = 0) :
    generalizedEigenSelectedCompressedDetMinimal M (1 : Matrix k k ℝ) G := by
  have hNorm' : generalizedEigenvectorBNormalized (1 : Matrix k k ℝ) G := by
    simpa [generalizedEigenvectorBNormalized, Matrix.mul_assoc] using hNorm
  have hGdet : (Gᵀ * M * G).det = 0 := by
    calc
      (Gᵀ * M * G).det = ∏ j, lambda j :=
        generalizedEigenvectorColumns_compressed_det_eq_prod_of_normalized
          M (1 : Matrix k k ℝ) lambda G h hNorm'
      _ = 0 := hZeroProduct
  intro H _hHNorm
  have hComp : (Hᵀ * M * H).PosSemidef := by
    have h := hM.conjTranspose_mul_mul_same H
    simpa [Matrix.conjTranspose, Matrix.star_apply] using h
  calc
    (Gᵀ * M * G).det = 0 := hGdet
    _ ≤ (Hᵀ * M * H).det := hComp.det_nonneg

/-- Selected-compressed determinant minimum for a nonempty nullspace block of a
positive semidefinite ordinary matrix.

Compared with `generalizedEigenSelectedCompressedDetMinimal_identity_of_posSemidef_zero`,
this derives the zero selected-root product from the concrete nullspace identity
`M * G = 0`. -/
theorem generalizedEigenSelectedCompressedDetMinimal_identity_of_posSemidef_null
    [DecidableEq k] [Nonempty r]
    (M : Matrix k k ℝ) (lambda : r → ℝ) (G : Matrix k r ℝ)
    (hM : M.PosSemidef)
    (h : generalizedEigenvectorColumns M (1 : Matrix k k ℝ) lambda G)
    (hNorm : Gᵀ * G = 1)
    (hNull : M * G = 0) :
    generalizedEigenSelectedCompressedDetMinimal M (1 : Matrix k k ℝ) G :=
  generalizedEigenSelectedCompressedDetMinimal_identity_of_posSemidef_zero
    M lambda G hM h hNorm
    (generalizedEigenNull_rootProduct_eq_zero M lambda G h hNorm hNull)

/-- Whitening route to the generalized-pencil product upper bound, with the
ordinary identity-denominator theorem supplied as a selected compressed-
determinant maximum. -/
theorem generalizedEigenDetProductUpperBound_of_whitened_identity_selected_compressedDet_maximal
    [Fintype q] [DecidableEq q]
    (A B : Matrix k k ℝ) (M : Matrix q q ℝ) (T : Matrix q k ℝ)
    (lambda : r → ℝ) (G0 : Matrix q r ℝ)
    (hA : A = Tᵀ * M * T)
    (hB : B = Tᵀ * T)
    (hG0 : generalizedEigenvectorColumns M (1 : Matrix q q ℝ) lambda G0)
    (hG0Norm : G0ᵀ * G0 = 1)
    (hG0Max : ∀ H : Matrix q r ℝ, Hᵀ * H = 1 →
      (Hᵀ * M * H).det ≤ (G0ᵀ * M * G0).det) :
    generalizedEigenDetProductUpperBound A B lambda :=
  generalizedEigenDetProductUpperBound_of_whitened_identity
    A B M T lambda hA hB
    (generalizedEigenDetProductUpperBound_identity_of_selected_compressedDet_maximal
      M lambda G0 hG0 hG0Norm hG0Max)

/-- Whitening route to the generalized-pencil product lower bound, with the
ordinary identity-denominator theorem supplied as a selected compressed-
determinant minimum. -/
theorem generalizedEigenDetProductLowerBound_of_whitened_identity_selected_compressedDet_minimal
    [Fintype q] [DecidableEq q]
    (A B : Matrix k k ℝ) (M : Matrix q q ℝ) (T : Matrix q k ℝ)
    (lambda : r → ℝ) (G0 : Matrix q r ℝ)
    (hA : A = Tᵀ * M * T)
    (hB : B = Tᵀ * T)
    (hG0 : generalizedEigenvectorColumns M (1 : Matrix q q ℝ) lambda G0)
    (hG0Norm : G0ᵀ * G0 = 1)
    (hG0Min : ∀ H : Matrix q r ℝ, Hᵀ * H = 1 →
      (G0ᵀ * M * G0).det ≤ (Hᵀ * M * H).det) :
    generalizedEigenDetProductLowerBound A B lambda :=
  generalizedEigenDetProductLowerBound_of_whitened_identity
    A B M T lambda hA hB
    (generalizedEigenDetProductLowerBound_identity_of_selected_compressedDet_minimal
      M lambda G0 hG0 hG0Norm hG0Min)

/-- The literal product upper bound for a selected generalized-eigenvector
block supplies its compressed-determinant maximality. This is the bridge from
an ordered generalized-eigenvalue determinant/product theorem to the certificate
shape used by Hansen Theorem 11.7. -/
theorem generalizedEigenSelectedCompressedDetMaximal_of_productUpperBound
    (A B : Matrix k k ℝ) (lambda : r → ℝ) (G : Matrix k r ℝ)
    (h : generalizedEigenvectorColumns A B lambda G)
    (hNorm : generalizedEigenvectorBNormalized B G)
    (hBound : generalizedEigenDetProductUpperBound A B lambda) :
    generalizedEigenSelectedCompressedDetMaximal A B G := by
  intro H hHNorm
  calc
    (Hᵀ * A * H).det ≤ ∏ j, lambda j := hBound H hHNorm
    _ = (Gᵀ * A * G).det := by
      exact (generalizedEigenvectorColumns_compressed_det_eq_prod_of_normalized
        A B lambda G h hNorm).symm

/-- The literal product lower bound for a selected generalized-eigenvector
block supplies its compressed-determinant minimality. This is the dual bridge
from the ordered generalized-eigenvalue theorem to the Hansen certificate
shape. -/
theorem generalizedEigenSelectedCompressedDetMinimal_of_productLowerBound
    (A B : Matrix k k ℝ) (lambda : r → ℝ) (G : Matrix k r ℝ)
    (h : generalizedEigenvectorColumns A B lambda G)
    (hNorm : generalizedEigenvectorBNormalized B G)
    (hBound : generalizedEigenDetProductLowerBound A B lambda) :
    generalizedEigenSelectedCompressedDetMinimal A B G := by
  intro H hHNorm
  calc
    (Gᵀ * A * G).det = ∏ j, lambda j :=
      generalizedEigenvectorColumns_compressed_det_eq_prod_of_normalized
        A B lambda G h hNorm
    _ ≤ (Hᵀ * A * H).det := hBound H hHNorm

/-- For a normalized selected generalized-eigenvector block, the product upper
bound is equivalent to selected compressed-determinant maximality. -/
theorem generalizedEigenDetProductUpperBound_iff_selected_compressedDet_maximal
    (A B : Matrix k k ℝ) (lambda : r → ℝ) (G : Matrix k r ℝ)
    (h : generalizedEigenvectorColumns A B lambda G)
    (hNorm : generalizedEigenvectorBNormalized B G) :
    generalizedEigenDetProductUpperBound A B lambda ↔
      generalizedEigenSelectedCompressedDetMaximal A B G := by
  constructor
  · exact generalizedEigenSelectedCompressedDetMaximal_of_productUpperBound
      A B lambda G h hNorm
  · exact generalizedEigenDetProductUpperBound_of_selected_compressedDet_maximal
      A B lambda G h hNorm

/-- For a normalized selected generalized-eigenvector block, the product lower
bound is equivalent to selected compressed-determinant minimality. -/
theorem generalizedEigenDetProductLowerBound_iff_selected_compressedDet_minimal
    (A B : Matrix k k ℝ) (lambda : r → ℝ) (G : Matrix k r ℝ)
    (h : generalizedEigenvectorColumns A B lambda G)
    (hNorm : generalizedEigenvectorBNormalized B G) :
    generalizedEigenDetProductLowerBound A B lambda ↔
      generalizedEigenSelectedCompressedDetMinimal A B G := by
  constructor
  · exact generalizedEigenSelectedCompressedDetMinimal_of_productLowerBound
      A B lambda G h hNorm
  · exact generalizedEigenDetProductLowerBound_of_selected_compressedDet_minimal
      A B lambda G h hNorm

/-- For a normalized selected generalized-eigenvector block, the product upper
bound is equivalent to global determinant-objective maximality. -/
theorem generalizedEigenDetProductUpperBound_iff_detObjectiveMaximizer
    (A B : Matrix k k ℝ) (lambda : r → ℝ) (G : Matrix k r ℝ)
    (h : generalizedEigenvectorColumns A B lambda G)
    (hNorm : generalizedEigenvectorBNormalized B G) :
    generalizedEigenDetProductUpperBound A B lambda ↔
      generalizedEigenDetObjectiveMaximizer A B G := by
  constructor
  · intro hBound
    constructor
    · exact hNorm
    · intro H hHNorm
      calc
        generalizedEigenDetObjective A B H = (Hᵀ * A * H).det :=
          generalizedEigenDetObjective_eq_compressed_det_of_normalized A B H hHNorm
        _ ≤ ∏ j, lambda j := hBound H hHNorm
        _ = (Gᵀ * A * G).det := by
          exact (generalizedEigenvectorColumns_compressed_det_eq_prod_of_normalized
            A B lambda G h hNorm).symm
        _ = generalizedEigenDetObjective A B G := by
          exact (generalizedEigenDetObjective_eq_compressed_det_of_normalized
            A B G hNorm).symm
  · intro hOpt
    exact generalizedEigenDetProductUpperBound_of_detObjectiveMaximizer
      A B lambda G h hOpt

/-- For a normalized selected generalized-eigenvector block, the product lower
bound is equivalent to global determinant-objective minimality. -/
theorem generalizedEigenDetProductLowerBound_iff_detObjectiveMinimizer
    (A B : Matrix k k ℝ) (lambda : r → ℝ) (G : Matrix k r ℝ)
    (h : generalizedEigenvectorColumns A B lambda G)
    (hNorm : generalizedEigenvectorBNormalized B G) :
    generalizedEigenDetProductLowerBound A B lambda ↔
      generalizedEigenDetObjectiveMinimizer A B G := by
  constructor
  · intro hBound
    constructor
    · exact hNorm
    · intro H hHNorm
      calc
        generalizedEigenDetObjective A B G = (Gᵀ * A * G).det :=
          generalizedEigenDetObjective_eq_compressed_det_of_normalized A B G hNorm
        _ = ∏ j, lambda j :=
          generalizedEigenvectorColumns_compressed_det_eq_prod_of_normalized
            A B lambda G h hNorm
        _ ≤ (Hᵀ * A * H).det := hBound H hHNorm
        _ = generalizedEigenDetObjective A B H := by
          exact (generalizedEigenDetObjective_eq_compressed_det_of_normalized
            A B H hHNorm).symm
  · intro hOpt
    exact generalizedEigenDetProductLowerBound_of_detObjectiveMinimizer
      A B lambda G h hOpt

/-- The enforceable G-side certificate for a generalized pencil: selected
generalized eigenvectors, Hansen normalization, and the compressed determinant
maximum. The product bound is derived, not assumed. -/
structure GeneralizedEigenDetProductMaxCertificate
    (A B : Matrix k k ℝ) (G : Matrix k r ℝ) (lambda : r → ℝ) : Prop where
  eigenvectors : generalizedEigenvectorColumns A B lambda G
  normalized : generalizedEigenvectorBNormalized B G
  selected_compressedDet_maximal : generalizedEigenSelectedCompressedDetMaximal A B G

/-- The enforceable dual-side certificate for a generalized pencil: selected
generalized eigenvectors, Hansen normalization, and the compressed determinant
minimum. The product lower bound is derived, not assumed. -/
structure GeneralizedEigenDetProductMinCertificate
    (A B : Matrix k k ℝ) (G : Matrix k r ℝ) (lambda : r → ℝ) : Prop where
  eigenvectors : generalizedEigenvectorColumns A B lambda G
  normalized : generalizedEigenvectorBNormalized B G
  selected_compressedDet_minimal : generalizedEigenSelectedCompressedDetMinimal A B G

/-- Raw ordered-product surface for the G-side generalized-pencil theorem.

Compared with `GeneralizedEigenDetProductMaxCertificate`, this stores the
literal ordered generalized-eigenvalue product inequality as the primitive
field. The selected compressed-determinant maximum is derived from the product
bound and the normalized generalized-eigenvector equations. -/
structure GeneralizedEigenOrderedProductMaxCertificate
    (A B : Matrix k k ℝ) (G : Matrix k r ℝ) (lambda : r → ℝ) : Prop where
  eigenvectors : generalizedEigenvectorColumns A B lambda G
  normalized : generalizedEigenvectorBNormalized B G
  product_upper_bound : generalizedEigenDetProductUpperBound A B lambda

/-- Raw ordered-product surface for the dual generalized-pencil theorem.

This is the `A⊥` counterpart of
`GeneralizedEigenOrderedProductMaxCertificate`: the primitive field is the
literal product lower bound, from which the selected compressed-determinant
minimum follows. -/
structure GeneralizedEigenOrderedProductMinCertificate
    (A B : Matrix k k ℝ) (G : Matrix k r ℝ) (lambda : r → ℝ) : Prop where
  eigenvectors : generalizedEigenvectorColumns A B lambda G
  normalized : generalizedEigenvectorBNormalized B G
  product_lower_bound : generalizedEigenDetProductLowerBound A B lambda

/-- The ordered-product G-side surface implies the selected compressed-
determinant maximum. -/
theorem GeneralizedEigenOrderedProductMaxCertificate.selected_compressedDet_maximal
    {A B : Matrix k k ℝ} {G : Matrix k r ℝ} {lambda : r → ℝ}
    (h : GeneralizedEigenOrderedProductMaxCertificate A B G lambda) :
    generalizedEigenSelectedCompressedDetMaximal A B G :=
  generalizedEigenSelectedCompressedDetMaximal_of_productUpperBound
    A B lambda G h.eigenvectors h.normalized h.product_upper_bound

/-- A raw ordered-product G-side certificate turns nonsingularity of the
selected compressed determinant into nonsingularity of the selected root
product. -/
theorem GeneralizedEigenOrderedProductMaxCertificate.rootProduct_ne_zero_of_compressedDet_ne_zero
    {A B : Matrix k k ℝ} {G : Matrix k r ℝ} {lambda : r → ℝ}
    (h : GeneralizedEigenOrderedProductMaxCertificate A B G lambda)
    (hdet : (Gᵀ * A * G).det ≠ 0) :
    (∏ j, lambda j) ≠ 0 :=
  generalizedEigenSelectedRootProduct_ne_zero_of_compressedDet_ne_zero
    A B lambda G h.eigenvectors h.normalized hdet

/-- A raw ordered-product G-side certificate turns positive selected roots
into nonsingularity of the selected compressed determinant. -/
theorem GeneralizedEigenOrderedProductMaxCertificate.compressedDet_ne_zero_of_pos
    {A B : Matrix k k ℝ} {G : Matrix k r ℝ} {lambda : r → ℝ}
    (h : GeneralizedEigenOrderedProductMaxCertificate A B G lambda)
    (hLambda : ∀ j, 0 < lambda j) :
    (Gᵀ * A * G).det ≠ 0 :=
  generalizedEigenSelectedCompressedDet_ne_zero_of_pos
    A B lambda G h.eigenvectors h.normalized hLambda

/-- The ordered-product dual surface implies the selected compressed-
determinant minimum. -/
theorem GeneralizedEigenOrderedProductMinCertificate.selected_compressedDet_minimal
    {A B : Matrix k k ℝ} {G : Matrix k r ℝ} {lambda : r → ℝ}
    (h : GeneralizedEigenOrderedProductMinCertificate A B G lambda) :
    generalizedEigenSelectedCompressedDetMinimal A B G :=
  generalizedEigenSelectedCompressedDetMinimal_of_productLowerBound
    A B lambda G h.eigenvectors h.normalized h.product_lower_bound

/-- Convert the raw ordered-product G-side surface into the reusable determinant
product max certificate. -/
theorem GeneralizedEigenOrderedProductMaxCertificate.to_detProductMaxCertificate
    {A B : Matrix k k ℝ} {G : Matrix k r ℝ} {lambda : r → ℝ}
    (h : GeneralizedEigenOrderedProductMaxCertificate A B G lambda) :
    GeneralizedEigenDetProductMaxCertificate A B G lambda where
  eigenvectors := h.eigenvectors
  normalized := h.normalized
  selected_compressedDet_maximal := h.selected_compressedDet_maximal

/-- Convert the raw ordered-product dual surface into the reusable determinant
product min certificate. -/
theorem GeneralizedEigenOrderedProductMinCertificate.to_detProductMinCertificate
    {A B : Matrix k k ℝ} {G : Matrix k r ℝ} {lambda : r → ℝ}
    (h : GeneralizedEigenOrderedProductMinCertificate A B G lambda) :
    GeneralizedEigenDetProductMinCertificate A B G lambda where
  eigenvectors := h.eigenvectors
  normalized := h.normalized
  selected_compressedDet_minimal := h.selected_compressedDet_minimal

/-- Product upper-bound theorem extracted from a generalized-pencil max
certificate. -/
theorem GeneralizedEigenDetProductMaxCertificate.upperBound
    {A B : Matrix k k ℝ} {G : Matrix k r ℝ} {lambda : r → ℝ}
    (h : GeneralizedEigenDetProductMaxCertificate A B G lambda) :
    generalizedEigenDetProductUpperBound A B lambda :=
  generalizedEigenDetProductUpperBound_of_selected_compressedDet_maximal
    A B lambda G h.eigenvectors h.normalized h.selected_compressedDet_maximal

/-- Product lower-bound theorem extracted from a generalized-pencil min
certificate. -/
theorem GeneralizedEigenDetProductMinCertificate.lowerBound
    {A B : Matrix k k ℝ} {G : Matrix k r ℝ} {lambda : r → ℝ}
    (h : GeneralizedEigenDetProductMinCertificate A B G lambda) :
    generalizedEigenDetProductLowerBound A B lambda :=
  generalizedEigenDetProductLowerBound_of_selected_compressedDet_minimal
    A B lambda G h.eigenvectors h.normalized h.selected_compressedDet_minimal

/-- A G-side determinant/product min-max certificate gives the corresponding
global determinant-objective maximum. This is the objective-extrema bridge for
an ordered generalized-eigenvalue min-max theorem: the certificate's selected
compressed-determinant maximum is over all `B`-normalized competitors, and the
objective ratio is just that compressed determinant under normalization. -/
theorem GeneralizedEigenDetProductMaxCertificate.detObjectiveMaximizer
    {A B : Matrix k k ℝ} {G : Matrix k r ℝ} {lambda : r → ℝ}
    (h : GeneralizedEigenDetProductMaxCertificate A B G lambda) :
    generalizedEigenDetObjectiveMaximizer A B G := by
  constructor
  · exact h.normalized
  · intro H hHNorm
    calc
      generalizedEigenDetObjective A B H = (Hᵀ * A * H).det :=
        generalizedEigenDetObjective_eq_compressed_det_of_normalized A B H hHNorm
      _ ≤ (Gᵀ * A * G).det := h.selected_compressedDet_maximal H hHNorm
      _ = generalizedEigenDetObjective A B G :=
        (generalizedEigenDetObjective_eq_compressed_det_of_normalized
          A B G h.normalized).symm

/-- A dual determinant/product min-max certificate gives the corresponding
global determinant-objective minimum. This is the `A⊥` objective-extrema bridge
for the ordered generalized-eigenvalue min-max route. -/
theorem GeneralizedEigenDetProductMinCertificate.detObjectiveMinimizer
    {A B : Matrix k k ℝ} {G : Matrix k r ℝ} {lambda : r → ℝ}
    (h : GeneralizedEigenDetProductMinCertificate A B G lambda) :
    generalizedEigenDetObjectiveMinimizer A B G := by
  constructor
  · exact h.normalized
  · intro H hHNorm
    calc
      generalizedEigenDetObjective A B G = (Gᵀ * A * G).det :=
        generalizedEigenDetObjective_eq_compressed_det_of_normalized A B G h.normalized
      _ ≤ (Hᵀ * A * H).det := h.selected_compressedDet_minimal H hHNorm
      _ = generalizedEigenDetObjective A B H :=
        (generalizedEigenDetObjective_eq_compressed_det_of_normalized
          A B H hHNorm).symm

/-- Build the G-side determinant/product certificate from the literal product
variational upper bound. -/
theorem GeneralizedEigenDetProductMaxCertificate.of_productUpperBound
    (A B : Matrix k k ℝ) (G : Matrix k r ℝ) (lambda : r → ℝ)
    (h : generalizedEigenvectorColumns A B lambda G)
    (hNorm : generalizedEigenvectorBNormalized B G)
    (hBound : generalizedEigenDetProductUpperBound A B lambda) :
    GeneralizedEigenDetProductMaxCertificate A B G lambda where
  eigenvectors := h
  normalized := hNorm
  selected_compressedDet_maximal :=
    generalizedEigenSelectedCompressedDetMaximal_of_productUpperBound
      A B lambda G h hNorm hBound

/-- Build the dual determinant/product certificate from the literal product
variational lower bound. -/
theorem GeneralizedEigenDetProductMinCertificate.of_productLowerBound
    (A B : Matrix k k ℝ) (G : Matrix k r ℝ) (lambda : r → ℝ)
    (h : generalizedEigenvectorColumns A B lambda G)
    (hNorm : generalizedEigenvectorBNormalized B G)
    (hBound : generalizedEigenDetProductLowerBound A B lambda) :
    GeneralizedEigenDetProductMinCertificate A B G lambda where
  eigenvectors := h
  normalized := hNorm
  selected_compressedDet_minimal :=
    generalizedEigenSelectedCompressedDetMinimal_of_productLowerBound
      A B lambda G h hNorm hBound

/-- Build the G-side determinant/product certificate from a normal-likelihood
determinant-objective maximizer. -/
theorem GeneralizedEigenDetProductMaxCertificate.of_detObjectiveMaximizer
    (A B : Matrix k k ℝ) (G : Matrix k r ℝ) (lambda : r → ℝ)
    (h : generalizedEigenvectorColumns A B lambda G)
    (hOpt : generalizedEigenDetObjectiveMaximizer A B G) :
    GeneralizedEigenDetProductMaxCertificate A B G lambda where
  eigenvectors := h
  normalized := hOpt.1
  selected_compressedDet_maximal :=
    generalizedEigenSelectedCompressedDetMaximal_of_detObjectiveMaximizer A B G hOpt

/-- Build the dual determinant/product certificate from a normal-likelihood
determinant-objective minimizer. -/
theorem GeneralizedEigenDetProductMinCertificate.of_detObjectiveMinimizer
    (A B : Matrix k k ℝ) (G : Matrix k r ℝ) (lambda : r → ℝ)
    (h : generalizedEigenvectorColumns A B lambda G)
    (hOpt : generalizedEigenDetObjectiveMinimizer A B G) :
    GeneralizedEigenDetProductMinCertificate A B G lambda where
  eigenvectors := h
  normalized := hOpt.1
  selected_compressedDet_minimal :=
    generalizedEigenSelectedCompressedDetMinimal_of_detObjectiveMinimizer A B G hOpt

/-- Explicit-whitening existence for the generalized-pencil determinant max
certificate.

The selected roots are exactly the leading `card r` ordered eigenvalues of the
positive-semidefinite whitened numerator `M = S' A S`. Thus the spectral block
and the global determinant maximizer are the same constructed witness. -/
theorem generalizedEigenDetProductMaxCertificate_exists_of_whitening
    [DecidableEq k]
    (A B T S M : Matrix k k ℝ)
    (hB : B = Tᵀ * T) (hM : M = Sᵀ * A * S)
    (hST : S * T = 1) (hTS : T * S = 1)
    (hMPos : M.PosSemidef)
    (hcard : Fintype.card r ≤ Fintype.card k) :
    ∃ G : Matrix k r ℝ,
      GeneralizedEigenDetProductMaxCertificate A B G
        (fun j : r => hMPos.1.eigenvalues₀
          (Fin.castLE hcard ((Fintype.equivFin r) j))) := by
  classical
  let lambda : r → ℝ := fun j => hMPos.1.eigenvalues₀
    (Fin.castLE hcard ((Fintype.equivFin r) j))
  obtain ⟨G, hGEig, hGNorm⟩ :=
    generalizedEigenvectorColumns_normalized_leading_exists_of_whitening
      A B T S M hB hM hST hTS hMPos.1 hcard
  have hAFactor : A = Tᵀ * M * T := by
    calc
      A = (S * T)ᵀ * A * (S * T) := by rw [hST]; simp
      _ = Tᵀ * (Sᵀ * A * S) * T := by
        simp [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = Tᵀ * M * T := by rw [← hM]
  have hBound : generalizedEigenDetProductUpperBound A B lambda :=
    generalizedEigenDetProductUpperBound_of_whitened_identity
      A B M T lambda hAFactor hB
      (generalizedEigenDetProductUpperBound_identity_of_posSemidef_ordered
        M hMPos hcard)
  exact ⟨G,
    GeneralizedEigenDetProductMaxCertificate.of_productUpperBound
      A B G lambda hGEig hGNorm hBound⟩

open scoped MatrixOrder

/-- A positive-semidefinite generalized-pencil numerator and positive-definite
denominator admit a normalized leading generalized-eigenvector block that
globally maximizes the compressed determinant.

The returned whitening data records that the roots in the max certificate are
exactly the leading `card r` ordered eigenvalues of the whitened numerator. -/
theorem generalizedEigenLeadingDetProductMaxCertificate_exists_of_posSemidef_posDef
    [DecidableEq k]
    (A B : Matrix k k ℝ) (hA : A.PosSemidef) (hB : B.PosDef)
    (hcard : Fintype.card r ≤ Fintype.card k) :
    ∃ (T S M : Matrix k k ℝ) (hMPos : M.PosSemidef)
        (G : Matrix k r ℝ),
      B = Tᵀ * T ∧
        M = Sᵀ * A * S ∧
        S * T = 1 ∧
        T * S = 1 ∧
        GeneralizedEigenDetProductMaxCertificate A B G
          (fun j : r => hMPos.1.eigenvalues₀
            (Fin.castLE hcard ((Fintype.equivFin r) j))) := by
  classical
  have hFactor :
      ∃ T : Matrix k k ℝ, IsUnit T ∧ B = star T * T :=
    (CStarAlgebra.isStrictlyPositive_iff_eq_star_mul_self
      (A := Matrix k k ℝ)).mp
      (show IsStrictlyPositive B from hB.isStrictlyPositive)
  obtain ⟨T, hTunit, hBT⟩ := hFactor
  have hBT' : B = Tᵀ * T := by
    simpa [star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
      using hBT
  have hTdet : IsUnit T.det := (Matrix.isUnit_iff_isUnit_det T).mp hTunit
  let S : Matrix k k ℝ := T⁻¹
  have hST : S * T = 1 := Matrix.nonsing_inv_mul T hTdet
  have hTS : T * S = 1 := Matrix.mul_nonsing_inv T hTdet
  let M : Matrix k k ℝ := Sᵀ * A * S
  have hMPos : M.PosSemidef := by
    have hconj := hA.conjTranspose_mul_mul_same S
    simpa [M, Matrix.conjTranspose, Matrix.star_apply] using hconj
  obtain ⟨G, hG⟩ :=
    generalizedEigenDetProductMaxCertificate_exists_of_whitening
      A B T S M hBT' rfl hST hTS hMPos hcard
  exact ⟨T, S, M, hMPos, G, hBT', rfl, hST, hTS, hG⟩

/-- A positive-semidefinite/positive-definite pencil with `A <= B` admits one
leading block carrying both spectral objective certificates needed by Hansen's
G-side analysis.

The returned G is the same leading ordered generalized-eigenblock in the
determinant-max certificate and in the universal
`det (I - G' A G) <= det (I - H' A H)` comparison. The whitening data and exact
ordered-root formula are retained, so no complement extremum is inferred from
the bare determinant maximum. -/
theorem generalizedEigenLeadingComplementDetMinimal_exists_of_posSemidef_posDef
    [DecidableEq k]
    (A B : Matrix k k ℝ) (hA : A.PosSemidef) (hB : B.PosDef)
    (hAB : A ≤ B)
    (hcard : Fintype.card r ≤ Fintype.card k) :
    ∃ (T S M : Matrix k k ℝ) (hMPos : M.PosSemidef)
        (G : Matrix k r ℝ),
      B = Tᵀ * T ∧
        M = Sᵀ * A * S ∧
        S * T = 1 ∧
        T * S = 1 ∧
        (1 - M).PosSemidef ∧
        GeneralizedEigenDetProductMaxCertificate A B G
          (fun j : r => hMPos.1.eigenvalues₀
            (Fin.castLE hcard ((Fintype.equivFin r) j))) ∧
        (∀ H : Matrix k r ℝ, generalizedEigenvectorBNormalized B H →
          (1 - Gᵀ * A * G).det ≤ (1 - Hᵀ * A * H).det) := by
  obtain ⟨T, S, M, hMPos, G, hBT, hMA, hST, hTS, hG⟩ :=
    generalizedEigenLeadingDetProductMaxCertificate_exists_of_posSemidef_posDef
      (r := r) A B hA hB hcard
  have hSBS : Sᵀ * B * S = (1 : Matrix k k ℝ) := by
    rw [hBT]
    calc
      Sᵀ * (Tᵀ * T) * S = (T * S)ᵀ * (T * S) := by
        simp [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = 1 := by rw [hTS]; simp
  have hSIM : Sᵀ * (B - A) * S = (1 : Matrix k k ℝ) - M := by
    calc
      Sᵀ * (B - A) * S = Sᵀ * B * S - Sᵀ * A * S := by
        rw [Matrix.mul_sub, Matrix.sub_mul]
      _ = 1 - M := by rw [hSBS, ← hMA]
  have hIM : ((1 : Matrix k k ℝ) - M).PosSemidef := by
    have hcong := (Matrix.le_iff.mp hAB).conjTranspose_mul_mul_same S
    rw [Matrix.conjTranspose_eq_transpose_of_trivial, hSIM] at hcong
    exact hcong
  have hAFactor : A = Tᵀ * M * T := by
    calc
      A = (S * T)ᵀ * A * (S * T) := by rw [hST]; simp
      _ = Tᵀ * (Sᵀ * A * S) * T := by
        simp [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = Tᵀ * M * T := by rw [← hMA]
  have hMinimal :=
    generalizedEigenLeadingComplementDetMinimal_of_whitening
      A B M T hAFactor hBT hMPos hIM hcard G
        hG.eigenvectors hG.normalized
  exact ⟨T, S, M, hMPos, G, hBT, hMA, hST, hTS, hIM, hG, hMinimal⟩

/-- Compatibility projection of
`generalizedEigenLeadingDetProductMaxCertificate_exists_of_posSemidef_posDef`.

This shorter surface returns a normalized generalized-eigenvector block and
its global determinant-max certificate, but deliberately forgets the
whitening data that identifies its roots as the leading ordered roots. -/
theorem generalizedEigenDetProductMaxCertificate_exists_of_posSemidef_posDef
    (A B : Matrix k k ℝ) (hA : A.PosSemidef) (hB : B.PosDef)
    (hcard : Fintype.card r ≤ Fintype.card k) :
    ∃ (G : Matrix k r ℝ) (lambda : r → ℝ),
      GeneralizedEigenDetProductMaxCertificate A B G lambda := by
  classical
  obtain ⟨T, S, M, hMPos, G, hBT, hMA, hST, hTS, hG⟩ :=
    generalizedEigenLeadingDetProductMaxCertificate_exists_of_posSemidef_posDef
      (r := r) A B hA hB hcard
  exact ⟨G,
    (fun j : r => hMPos.1.eigenvalues₀
      (Fin.castLE hcard ((Fintype.equivFin r) j))),
    hG⟩

end GeneralizedEigenvectors

section HansenPencil

variable {n : Type*}
variable [Fintype n] [DecidableEq n]
variable [Fintype k] [Fintype m] [Fintype ell]
variable [DecidableEq m] [DecidableEq ell]

/-- Residualized outcome matrix `Ỹ` from regressing `Y` on controls `Z`. -/
noncomputable def reducedRankTildeY
    (Z : Matrix n ell ℝ) (Y : Matrix n m ℝ)
    [Invertible (Zᵀ * Z)] : Matrix n m ℝ :=
  residualizedRegressors Z Y

/-- Residualized regressor matrix `X̃` from regressing `X` on controls `Z`. -/
noncomputable def reducedRankTildeX
    (Z : Matrix n ell ℝ) (X : Matrix n k ℝ)
    [Invertible (Zᵀ * Z)] : Matrix n k ℝ :=
  residualizedRegressors Z X

/-- Residual matrix `Ẽ = M_{X,Z}Y` from the unrestricted multivariate
regression of `Y` on `(X,Z)`, used in Hansen's `A⊥` representation. -/
noncomputable def reducedRankTildeE
    (X : Matrix n k ℝ) (Z : Matrix n ell ℝ) (Y : Matrix n m ℝ)
    [DecidableEq k]
    [Invertible ((Matrix.fromCols X Z)ᵀ * Matrix.fromCols X Z)] :
    Matrix n m ℝ :=
  residualizedRegressors (Matrix.fromCols X Z) Y

/-- Full-rank `[X,Z]` and full-rank controls imply that the FWL-residualized
design Gram `X̃'X̃` is positive definite.

The proof identifies `X̃'X̃` with the Schur complement of `Z'Z` in the full
design Gram, uses Mathlib's block-invertibility equivalence, and combines the
resulting unit condition with Gram positive semidefiniteness. -/
theorem reducedRankTildeX_gram_posDef
    (Z : Matrix n ell ℝ) (X : Matrix n k ℝ)
    [DecidableEq k]
    [Invertible (Zᵀ * Z)]
    [Invertible ((Matrix.fromCols X Z)ᵀ * Matrix.fromCols X Z)] :
    ((reducedRankTildeX Z X)ᵀ * reducedRankTildeX Z X).PosDef := by
  change ((residualizedRegressors Z X)ᵀ * residualizedRegressors Z X).PosDef
  have hblock :
      (Matrix.fromCols X Z)ᵀ * Matrix.fromCols X Z =
        Matrix.fromBlocks (Xᵀ * X) (Xᵀ * Z) (Zᵀ * X) (Zᵀ * Z) := by
    rw [Matrix.transpose_fromCols, Matrix.fromRows_mul_fromCols]
  have hfull : IsUnit ((Matrix.fromCols X Z)ᵀ * Matrix.fromCols X Z) :=
    isUnit_of_invertible _
  have hblockUnit :
      IsUnit (Matrix.fromBlocks (Xᵀ * X) (Xᵀ * Z) (Zᵀ * X) (Zᵀ * Z)) := by
    rwa [← hblock]
  have hschurUnit :
      IsUnit (Xᵀ * X - (Xᵀ * Z) * ⅟(Zᵀ * Z) * (Zᵀ * X)) :=
    Matrix.isUnit_fromBlocks_iff_of_invertible₂₂.mp hblockUnit
  have hschur :
      Xᵀ * X - (Xᵀ * Z) * ⅟(Zᵀ * Z) * (Zᵀ * X) =
        (residualizedRegressors Z X)ᵀ * residualizedRegressors Z X := by
    rw [residualizedRegressors_gram_eq]
    simp [annihilatorMatrix, hatMatrix, Matrix.mul_sub, Matrix.sub_mul,
      Matrix.mul_assoc]
  have hunit :
      IsUnit ((residualizedRegressors Z X)ᵀ * residualizedRegressors Z X) := by
    rwa [hschur] at hschurUnit
  have hpsd :
      ((residualizedRegressors Z X)ᵀ *
        residualizedRegressors Z X).PosSemidef := by
    simpa [Matrix.conjTranspose, Matrix.star_apply] using
      (posSemidef_conjTranspose_mul_self (residualizedRegressors Z X))
  exact hpsd.posDef_iff_isUnit.mpr hunit

/-- Full-rank `[Y,Z]` and full-rank controls imply that the residualized
outcome Gram `Ỹ'Ỹ` is positive definite.

This is the outcome-index specialization of
`reducedRankTildeX_gram_posDef`; it turns a raw full-Gram assumption into the
regular denominator condition used by both Hansen pencils. -/
theorem reducedRankTildeY_gram_posDef
    (Z : Matrix n ell ℝ) (Y : Matrix n m ℝ)
    [Invertible (Zᵀ * Z)]
    [Invertible ((Matrix.fromCols Y Z)ᵀ * Matrix.fromCols Y Z)] :
    ((reducedRankTildeY Z Y)ᵀ * reducedRankTildeY Z Y).PosDef := by
  simpa [reducedRankTildeY, reducedRankTildeX] using
    (reducedRankTildeX_gram_posDef (k := m) Z Y)

/-- Hansen Theorem 11.7 generalized-eigenvalue pencil numerator
`X̃'Ỹ(Ỹ'Ỹ)⁻¹Ỹ'X̃`. -/
noncomputable def reducedRankGPencilA
    (Xtilde : Matrix n k ℝ) (Ytilde : Matrix n m ℝ) : Matrix k k ℝ :=
  Xtildeᵀ * Ytilde * (Ytildeᵀ * Ytilde)⁻¹ * Ytildeᵀ * Xtilde

/-- Hansen Theorem 11.7 generalized-eigenvalue pencil denominator `X̃'X̃`. -/
noncomputable def reducedRankGPencilB
    (Xtilde : Matrix n k ℝ) : Matrix k k ℝ :=
  Xtildeᵀ * Xtilde

/-- Hansen Theorem 11.7 `A⊥` generalized-eigenvalue pencil numerator
`Ẽ'Ẽ`, where `Ẽ = M_{X,Z}Y` is the unrestricted residual matrix. -/
noncomputable def reducedRankAperpPencilA
    (Etilde : Matrix n m ℝ) : Matrix m m ℝ :=
  Etildeᵀ * Etilde

/-- Hansen Theorem 11.7 `A⊥` generalized-eigenvalue pencil denominator
`Ỹ'Ỹ`. -/
noncomputable def reducedRankAperpPencilB
    (Ytilde : Matrix n m ℝ) : Matrix m m ℝ :=
  Ytildeᵀ * Ytilde

/-- Ordinary identity-denominator matrix obtained by whitening Hansen's
G-side pencil with `T = X̃`.

The full multi-column 11.7 determinant theorem should be proved for this
positive semidefinite ordinary matrix, selecting its leading eigenspace, before
transporting the result back to the generalized pencil. -/
noncomputable def reducedRankGWhitenedProjection
    (Ytilde : Matrix n m ℝ) : Matrix n n ℝ :=
  Ytilde * (Ytildeᵀ * Ytilde)⁻¹ * Ytildeᵀ

/-- Ordinary identity-denominator matrix obtained from a residual factor
`Ẽ = R Ỹ` on Hansen's `A⊥` side. -/
noncomputable def reducedRankAperpResidualWhitenedMatrix
    (R : Matrix n n ℝ) : Matrix n n ℝ :=
  Rᵀ * R

/-- Concrete residual-maker factor for Hansen's residualized `A⊥` side.

For the actual reduced-rank data matrices, this is the unrestricted residual
maker from regressing on both `X` and `Z`. The theorem
`reducedRankTildeE_eq_residualFactor_mul_tildeY` proves that it factors the
unrestricted residual block through the `Z`-residualized outcome block:
`Ẽ = R Ỹ`. -/
noncomputable def reducedRankAperpResidualFactor
    (X : Matrix n k ℝ) (Z : Matrix n ell ℝ)
    [DecidableEq k]
    [Invertible ((Matrix.fromCols X Z)ᵀ * Matrix.fromCols X Z)] :
    Matrix n n ℝ :=
  annihilatorMatrix (Matrix.fromCols X Z)

omit [DecidableEq n] in
/-- Hansen's canonical G-side whitened matrix is positive semidefinite. -/
theorem reducedRankGWhitenedProjection_posSemidef
    (Ytilde : Matrix n m ℝ) :
    (reducedRankGWhitenedProjection Ytilde).PosSemidef := by
  have hGram : (Ytildeᵀ * Ytilde).PosSemidef := by
    simpa [Matrix.conjTranspose, Matrix.star_apply] using
      (posSemidef_conjTranspose_mul_self Ytilde)
  have hInv : ((Ytildeᵀ * Ytilde)⁻¹).PosSemidef := hGram.inv
  simpa [reducedRankGWhitenedProjection, Matrix.conjTranspose, Matrix.star_apply] using
    (Matrix.PosSemidef.mul_mul_conjTranspose_same hInv Ytilde)

omit [DecidableEq n] [Fintype k] in
/-- Hansen's G-pencil numerator is positive semidefinite for every pair of
residualized data matrices, including when `Ỹ'Ỹ` is singular and the total
matrix inverse is used. -/
theorem reducedRankGPencilA_posSemidef
    [Finite k]
    (Xtilde : Matrix n k ℝ) (Ytilde : Matrix n m ℝ) :
    (reducedRankGPencilA Xtilde Ytilde).PosSemidef := by
  letI := Fintype.ofFinite k
  have hP := reducedRankGWhitenedProjection_posSemidef Ytilde
  have h := hP.conjTranspose_mul_mul_same Xtilde
  simpa [reducedRankGPencilA, reducedRankGWhitenedProjection,
    Matrix.conjTranspose, Matrix.star_apply, Matrix.mul_assoc] using h

omit [DecidableEq n] [Fintype k] in
open scoped MatrixOrder in
/-- Hansen's G-pencil numerator is bounded above by its denominator when the
outcome Gram is positive definite.

The difference is the congruence `Xtilde' M_Y Xtilde` of the orthogonal
annihilator for `Ytilde`, hence is positive semidefinite. This supplies the
literal `0 <= M <= I` order input after whitening; it does not by itself turn a
compressed-determinant maximum into an extremum of `det (I - compression)`. -/
theorem reducedRankGPencilA_le_pencilB_of_yGram_posDef
    [Finite k]
    (Xtilde : Matrix n k ℝ) (Ytilde : Matrix n m ℝ)
    (hYGram : (Ytildeᵀ * Ytilde).PosDef) :
    reducedRankGPencilA Xtilde Ytilde ≤ reducedRankGPencilB Xtilde := by
  classical
  letI := Fintype.ofFinite k
  have hYdet : IsUnit (Ytildeᵀ * Ytilde).det :=
    (Matrix.isUnit_iff_isUnit_det (Ytildeᵀ * Ytilde)).mp hYGram.isUnit
  letI : Invertible (Ytildeᵀ * Ytilde) :=
    Matrix.invertibleOfIsUnitDet (A := Ytildeᵀ * Ytilde) hYdet
  let M : Matrix n n ℝ := annihilatorMatrix Ytilde
  have hMPos : M.PosSemidef :=
    posSemidef_of_transpose_eq_self_idempotent M
      (by simpa [M] using annihilatorMatrix_transpose Ytilde)
      (by simpa [M] using annihilatorMatrix_idempotent Ytilde)
  have hCongr : (Xtildeᵀ * M * Xtilde).PosSemidef := by
    have h := hMPos.conjTranspose_mul_mul_same Xtilde
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using h
  rw [Matrix.le_iff]
  have hDiff :
      reducedRankGPencilB Xtilde - reducedRankGPencilA Xtilde Ytilde =
        Xtildeᵀ * M * Xtilde := by
    simp only [reducedRankGPencilA, reducedRankGPencilB, M,
      annihilatorMatrix, hatMatrix, Matrix.invOf_eq_nonsing_inv]
    rw [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul]
    simp [Matrix.mul_assoc]
  rw [hDiff]
  exact hCongr

omit [DecidableEq n] [Fintype m] [DecidableEq m] in
/-- Hansen's residual-pencil numerator `Ẽ'Ẽ` is positive semidefinite. -/
theorem reducedRankAperpPencilA_posSemidef
    [Finite m]
    (Etilde : Matrix n m ℝ) :
    (reducedRankAperpPencilA Etilde).PosSemidef := by
  letI := Fintype.ofFinite m
  simpa [reducedRankAperpPencilA, Matrix.conjTranspose, Matrix.star_apply] using
    (posSemidef_conjTranspose_mul_self Etilde)

omit [DecidableEq n] in
/-- Under the usual full-column-rank condition for `Ỹ`, the G-side whitened
matrix is exactly the Chapter 3 OLS projection matrix for design `Ỹ`.

This bridge reuses the existing projection algebra instead of reproving
symmetry and idempotence for Hansen's whitened notation. -/
theorem reducedRankGWhitenedProjection_eq_hatMatrix
    (Ytilde : Matrix n m ℝ) [Invertible (Ytildeᵀ * Ytilde)] :
    reducedRankGWhitenedProjection Ytilde = hatMatrix Ytilde := by
  simp [reducedRankGWhitenedProjection, hatMatrix, Matrix.invOf_eq_nonsing_inv]

omit [DecidableEq n] in
/-- Columns represented as `Ỹ C` are fixed by Hansen's G-side whitened
projection.

This is the Chapter 3 projection range fact in reduced-rank notation and is the
ordinary `P G₀ = G₀` block used by the 11.7 projection route. -/
theorem reducedRankGWhitenedProjection_mul_range
    (Ytilde : Matrix n m ℝ) (C : Matrix m r ℝ) [Invertible (Ytildeᵀ * Ytilde)] :
    reducedRankGWhitenedProjection Ytilde * (Ytilde * C) = Ytilde * C := by
  rw [reducedRankGWhitenedProjection_eq_hatMatrix]
  exact hat_mul_range Ytilde C

omit [DecidableEq n] in
/-- A Hansen-native span certificate `X̃G = ỸC` gives the G-side projection
fixed-point equation used by the projection-specialized Theorem 11.7 route. -/
theorem reducedRankGWhitenedProjection_image_range_of_span
    (Xtilde : Matrix n k ℝ) (Ytilde : Matrix n m ℝ)
    (G : Matrix k r ℝ) (C : Matrix m r ℝ)
    [Invertible (Ytildeᵀ * Ytilde)]
    (hSpan : Xtilde * G = Ytilde * C) :
    reducedRankGWhitenedProjection Ytilde * (Xtilde * G) = Xtilde * G := by
  calc
    reducedRankGWhitenedProjection Ytilde * (Xtilde * G) =
        reducedRankGWhitenedProjection Ytilde * (Ytilde * C) := by
          rw [hSpan]
    _ = Ytilde * C := reducedRankGWhitenedProjection_mul_range Ytilde C
    _ = Xtilde * G := hSpan.symm

omit [DecidableEq n] in
/-- The G-side whitened projection is symmetric when `Ỹ'Ỹ` is invertible. -/
theorem reducedRankGWhitenedProjection_transpose
    (Ytilde : Matrix n m ℝ) [Invertible (Ytildeᵀ * Ytilde)] :
    (reducedRankGWhitenedProjection Ytilde)ᵀ =
      reducedRankGWhitenedProjection Ytilde := by
  rw [reducedRankGWhitenedProjection_eq_hatMatrix, hatMatrix_transpose]

omit [DecidableEq n] in
/-- The G-side whitened projection is idempotent when `Ỹ'Ỹ` is invertible. -/
theorem reducedRankGWhitenedProjection_idempotent
    (Ytilde : Matrix n m ℝ) [Invertible (Ytildeᵀ * Ytilde)] :
    reducedRankGWhitenedProjection Ytilde *
        reducedRankGWhitenedProjection Ytilde =
      reducedRankGWhitenedProjection Ytilde := by
  rw [reducedRankGWhitenedProjection_eq_hatMatrix]
  exact hatMatrix_idempotent Ytilde

omit [DecidableEq n] in
/-- The G-side whitened projection is Hermitian when `Ỹ'Ỹ` is invertible. -/
theorem reducedRankGWhitenedProjection_isHermitian
    (Ytilde : Matrix n m ℝ) [Invertible (Ytildeᵀ * Ytilde)] :
    (reducedRankGWhitenedProjection Ytilde).IsHermitian :=
  (Matrix.conjTranspose_eq_transpose_of_trivial _).trans
    (reducedRankGWhitenedProjection_transpose Ytilde)

/-- The ordinary G-side whitened projection has only `0` and `1` eigenvalues
under the usual full-column-rank condition for `Ỹ`. -/
theorem reducedRankGWhitenedProjection_eigenvalues_zero_or_one
    (Ytilde : Matrix n m ℝ) [Invertible (Ytildeᵀ * Ytilde)] :
    ∀ i : n,
      (reducedRankGWhitenedProjection_isHermitian Ytilde).eigenvalues i = 0 ∨
        (reducedRankGWhitenedProjection_isHermitian Ytilde).eigenvalues i = 1 :=
  eigenvalues_zero_or_one_of_isHermitian_idempotent
    (reducedRankGWhitenedProjection_isHermitian Ytilde)
    (reducedRankGWhitenedProjection_idempotent Ytilde)

omit [DecidableEq n] in
/-- A residual-factor whitened `A⊥` matrix is positive semidefinite. -/
theorem reducedRankAperpResidualWhitenedMatrix_posSemidef
    (R : Matrix n n ℝ) :
    (reducedRankAperpResidualWhitenedMatrix R).PosSemidef := by
  simpa [reducedRankAperpResidualWhitenedMatrix, Matrix.conjTranspose,
    Matrix.star_apply] using (posSemidef_conjTranspose_mul_self R)

omit [DecidableEq n] in
/-- A block in the nullspace of the residual factor is killed by the residual
whitened matrix `R'R`.

This is the direct algebra bridge from a raw residual nullspace certificate
`R A₀ = 0` to the ordinary `R'R A₀ = 0` block used on Hansen's `A⊥` side. -/
theorem reducedRankAperpResidualWhitenedMatrix_mul_eq_zero_of_factor_null
    (R : Matrix n n ℝ) (A0 : Matrix n r ℝ) (hNull : R * A0 = 0) :
    reducedRankAperpResidualWhitenedMatrix R * A0 = 0 := by
  simp [reducedRankAperpResidualWhitenedMatrix, Matrix.mul_assoc, hNull]

omit [DecidableEq m] in
private theorem reducedRankAperpResidualFactor_mul_Z
    (X : Matrix n k ℝ) (Z : Matrix n ell ℝ)
    [DecidableEq k]
    [Invertible ((Matrix.fromCols X Z)ᵀ * Matrix.fromCols X Z)] :
    reducedRankAperpResidualFactor X Z * Z = 0 := by
  have h := annihilator_mul_X (Matrix.fromCols X Z)
  ext i j
  simpa [reducedRankAperpResidualFactor, Matrix.mul_fromCols] using
    congrFun (congrFun h i) (Sum.inr j)

omit [DecidableEq m] in
private theorem reducedRankAperpResidualFactor_mul_hatMatrix_Z
    (X : Matrix n k ℝ) (Z : Matrix n ell ℝ)
    [DecidableEq k] [Invertible (Zᵀ * Z)]
    [Invertible ((Matrix.fromCols X Z)ᵀ * Matrix.fromCols X Z)] :
    reducedRankAperpResidualFactor X Z * hatMatrix Z = 0 := by
  calc
    reducedRankAperpResidualFactor X Z * hatMatrix Z =
        (reducedRankAperpResidualFactor X Z * Z) * ⅟ (Zᵀ * Z) * Zᵀ := by
          simp [hatMatrix, Matrix.mul_assoc]
    _ = 0 := by
      rw [reducedRankAperpResidualFactor_mul_Z X Z]
      simp

omit [Fintype m] [DecidableEq m] in
/-- Concrete residual-factor identity for Hansen Theorem 11.7.

With `Ỹ = M_Z Y` and `Ẽ = M_[X,Z]Y`, the unrestricted residual maker
`R = M_[X,Z]` satisfies `Ẽ = R Ỹ`. This closes the algebraic residual-factor
premise used by the whitened `A⊥` determinant route; the remaining open input
is only the ordinary multi-column determinant min-max theorem for the whitened
positive semidefinite matrices. -/
theorem reducedRankTildeE_eq_residualFactor_mul_tildeY
    (Z : Matrix n ell ℝ) (X : Matrix n k ℝ) (Y : Matrix n m ℝ)
    [DecidableEq k] [Invertible (Zᵀ * Z)]
    [Invertible ((Matrix.fromCols X Z)ᵀ * Matrix.fromCols X Z)] :
    reducedRankTildeE X Z Y =
      reducedRankAperpResidualFactor X Z * reducedRankTildeY Z Y := by
  have hM :
      reducedRankAperpResidualFactor X Z * annihilatorMatrix Z =
        reducedRankAperpResidualFactor X Z := by
    unfold annihilatorMatrix
    calc
      reducedRankAperpResidualFactor X Z * ((1 : Matrix n n ℝ) - hatMatrix Z)
          = reducedRankAperpResidualFactor X Z * (1 : Matrix n n ℝ) -
              reducedRankAperpResidualFactor X Z * hatMatrix Z := by
            rw [Matrix.mul_sub]
      _ = reducedRankAperpResidualFactor X Z := by
            rw [Matrix.mul_one, reducedRankAperpResidualFactor_mul_hatMatrix_Z X Z]
            simp
  simp only [reducedRankTildeE, reducedRankTildeY, residualizedRegressors]
  change reducedRankAperpResidualFactor X Z * Y =
    reducedRankAperpResidualFactor X Z * (annihilatorMatrix Z * Y)
  calc
    reducedRankAperpResidualFactor X Z * Y =
        (reducedRankAperpResidualFactor X Z * annihilatorMatrix Z) * Y := by
          rw [hM]
    _ = reducedRankAperpResidualFactor X Z * (annihilatorMatrix Z * Y) := by
          rw [Matrix.mul_assoc]

omit [DecidableEq m] in
/-- Hansen-native residual null certificate for the `A⊥` block.

If the unrestricted residualized outcome satisfies `Ẽ A⊥ = 0`, then the
concrete residual factor `R = M_[X,Z]` kills the residualized outcome image
`Ỹ A⊥`.  This is just the existing factorization `Ẽ = RỸ`. -/
theorem reducedRankAperpResidualFactor_image_null_of_tildeE_null
    (Z : Matrix n ell ℝ) (X : Matrix n k ℝ) (Y : Matrix n m ℝ)
    (Aperp : Matrix m s ℝ)
    [DecidableEq k] [Invertible (Zᵀ * Z)]
    [Invertible ((Matrix.fromCols X Z)ᵀ * Matrix.fromCols X Z)]
    (hNull : reducedRankTildeE X Z Y * Aperp = 0) :
    reducedRankAperpResidualFactor X Z *
        (reducedRankTildeY Z Y * Aperp) = 0 := by
  calc
    reducedRankAperpResidualFactor X Z *
        (reducedRankTildeY Z Y * Aperp) =
        (reducedRankAperpResidualFactor X Z * reducedRankTildeY Z Y) * Aperp := by
          rw [Matrix.mul_assoc]
    _ = reducedRankTildeE X Z Y * Aperp := by
          rw [← reducedRankTildeE_eq_residualFactor_mul_tildeY Z X Y]
    _ = 0 := hNull

/-- Hansen's residualized generalized-eigenvector package for the `G` block in
Theorem 11.7. This is still a support predicate: it does not assert that the
selected eigenvalues are the largest `r` values. -/
def reducedRankHansenGEigenvectors
    (Xtilde : Matrix n k ℝ) (Ytilde : Matrix n m ℝ)
    (lambda : r → ℝ) (G : Matrix k r ℝ) : Prop :=
  generalizedEigenvectorColumns
    (reducedRankGPencilA Xtilde Ytilde) (reducedRankGPencilB Xtilde) lambda G

/-- Hansen's generalized-eigenvector package for the `A⊥` block in Theorem
11.7, using the unrestricted residual pencil `Ẽ'Ẽ` with respect to `Ỹ'Ỹ`.

This is still a support predicate: it records the eigenvector equations, while
the ordering condition selecting the theorem's extremal eigenvectors remains
separate. -/
def reducedRankHansenAperpEigenvectors
    (Etilde : Matrix n m ℝ) (Ytilde : Matrix n m ℝ)
    (lambda : s → ℝ) (Aperp : Matrix m s ℝ) : Prop :=
  generalizedEigenvectorColumns
    (reducedRankAperpPencilA Etilde) (reducedRankAperpPencilB Ytilde) lambda Aperp

/-- Hansen's spectral-duality subspace identification in normalized coordinates:
`A⊥'Ỹ'X̃G = 0`. -/
def reducedRankAperpCrossOrthogonal
    (Xtilde : Matrix n k ℝ) (Ytilde : Matrix n m ℝ)
    (G : Matrix k r ℝ) (Aperp : Matrix m s ℝ) : Prop :=
  Aperpᵀ * (Ytildeᵀ * Xtilde * G) = 0

section Objective

variable [Fintype r] [DecidableEq r]

/-- Hansen normalization for Theorem 11.7's `G` block:
`G' X̃'X̃ G = I_r`. -/
def reducedRankGNormalized
    (Xtilde : Matrix n k ℝ) (G : Matrix k r ℝ) : Prop :=
  generalizedEigenvectorBNormalized (reducedRankGPencilB Xtilde) G

omit [DecidableEq n] [Fintype ell] [DecidableEq ell] in
/-- Hansen's G pencil admits a normalized leading block that minimizes the
complement determinant in equation (11.20).

This is the chapter-facing specialization of
`generalizedEigenLeadingComplementDetMinimal_exists_of_posSemidef_posDef`.
The returned roots are exactly the leading ordered roots of the whitened
positive-semidefinite numerator; the same `G` carries both their generalized
eigenvector equations and the universal `det (I - compression)` comparison. -/
theorem reducedRankGLeadingComplementDetMinimal_exists
    (Xtilde : Matrix n k ℝ) (Ytilde : Matrix n m ℝ)
    (hXGram : (Xtildeᵀ * Xtilde).PosDef)
    (hYGram : (Ytildeᵀ * Ytilde).PosDef)
    (hcard : Fintype.card r ≤ Fintype.card k) :
    ∃ (G : Matrix k r ℝ) (lambda : r → ℝ),
      reducedRankHansenGEigenvectors Xtilde Ytilde lambda G ∧
        reducedRankGNormalized Xtilde G ∧
        (∀ H : Matrix k r ℝ, reducedRankGNormalized Xtilde H →
          (1 - Gᵀ * reducedRankGPencilA Xtilde Ytilde * G).det ≤
            (1 - Hᵀ * reducedRankGPencilA Xtilde Ytilde * H).det) := by
  classical
  have hA : (reducedRankGPencilA Xtilde Ytilde).PosSemidef :=
    reducedRankGPencilA_posSemidef Xtilde Ytilde
  have hB : (reducedRankGPencilB Xtilde).PosDef := by
    simpa [reducedRankGPencilB] using hXGram
  have hAB :=
    reducedRankGPencilA_le_pencilB_of_yGram_posDef Xtilde Ytilde hYGram
  obtain ⟨T, S, M, hMPos, G, hBT, hMA, hST, hTS, hIM, hG, hMinimal⟩ :=
    generalizedEigenLeadingComplementDetMinimal_exists_of_posSemidef_posDef
      (r := r) (reducedRankGPencilA Xtilde Ytilde)
        (reducedRankGPencilB Xtilde) hA hB hAB hcard
  let lambda : r → ℝ := fun j =>
    hMPos.1.eigenvalues₀ (Fin.castLE hcard ((Fintype.equivFin r) j))
  exact ⟨G, lambda, hG.eigenvectors, hG.normalized, hMinimal⟩

omit [DecidableEq n] [Fintype r] in
/-- Hansen normalization of `G` says that the image block `X̃G` is ordinary
orthonormal. -/
theorem reducedRankG_image_orthonormal_of_normalized
    (Xtilde : Matrix n k ℝ) (G : Matrix k r ℝ)
    (hNorm : reducedRankGNormalized Xtilde G) :
    (Xtilde * G)ᵀ * (Xtilde * G) = (1 : Matrix r r ℝ) := by
  change Gᵀ * (Xtildeᵀ * Xtilde) * G = 1 at hNorm
  simpa [Matrix.transpose_mul, Matrix.mul_assoc] using hNorm

omit [DecidableEq n] [Fintype r] in
/-- If the Hansen-normalized image block `X̃G` is fixed by the whitened
projection `Ỹ(Ỹ'Ỹ)⁻¹Ỹ'`, then `G` solves Hansen's original G-side
generalized-eigenvector equations with displayed roots all equal to `1`.

This is a bridge from the ordinary whitened projection route back to the
textbook generalized pencil; it is intentionally projection-specialized. -/
theorem reducedRankHansenGEigenvectors_one_of_whitened_projection_image_range
    (Xtilde : Matrix n k ℝ) (Ytilde : Matrix n m ℝ) (G : Matrix k r ℝ)
    (hNorm : reducedRankGNormalized Xtilde G)
    (hRange : reducedRankGWhitenedProjection Ytilde * (Xtilde * G) = Xtilde * G) :
    reducedRankHansenGEigenvectors Xtilde Ytilde (fun _ : r => (1 : ℝ)) G := by
  intro j
  refine ⟨?_, ?_⟩
  · intro hzero
    have hXGNorm := reducedRankG_image_orthonormal_of_normalized Xtilde G hNorm
    have hXGzero : (fun i : n => (Xtilde * G) i j) = 0 := by
      funext i
      have hcol : ∀ a : k, G a j = 0 := fun a => congrFun hzero a
      simp [Matrix.mul_apply, hcol]
    exact column_ne_zero_of_orthonormal (Xtilde * G) hXGNorm j hXGzero
  · have hMat :
        reducedRankGPencilA Xtilde Ytilde * G =
          reducedRankGPencilB Xtilde * G := by
      calc
        reducedRankGPencilA Xtilde Ytilde * G =
            (Xtildeᵀ * reducedRankGWhitenedProjection Ytilde * Xtilde) * G := by
              simp [reducedRankGPencilA, reducedRankGWhitenedProjection, Matrix.mul_assoc]
        _ = Xtildeᵀ * (reducedRankGWhitenedProjection Ytilde * (Xtilde * G)) := by
              simp [Matrix.mul_assoc]
        _ = Xtildeᵀ * (Xtilde * G) := by rw [hRange]
        _ = reducedRankGPencilB Xtilde * G := by
              simp [reducedRankGPencilB, Matrix.mul_assoc]
    ext i
    have hEntry := congrArg (fun M : Matrix k r ℝ => M i j) hMat
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using hEntry

/-- Hansen's concentrated determinant objective in equation (11.20), written
for the `argmax` form using the residualized pencil numerator. -/
noncomputable def reducedRankConcentratedEigenObjective
    (Xtilde : Matrix n k ℝ) (Ytilde : Matrix n m ℝ) (G : Matrix k r ℝ) : ℝ :=
  generalizedEigenDetObjective (reducedRankGPencilA Xtilde Ytilde)
    (reducedRankGPencilB Xtilde) G

/-- Reciprocal form of Hansen's concentrated reduced-rank objective. -/
noncomputable def reducedRankConcentratedReciprocalEigenObjective
    (Xtilde : Matrix n k ℝ) (Ytilde : Matrix n m ℝ) (G : Matrix k r ℝ) : ℝ :=
  generalizedEigenDetReciprocalObjective (reducedRankGPencilA Xtilde Ytilde)
    (reducedRankGPencilB Xtilde) G

/-- Exact G-side determinant variational inequality in Hansen Theorem 11.7.

For every competitor normalized by `H' X̃'X̃ H = I`, the compressed determinant
is bounded by the product of the selected generalized roots. This is the
missing product min-max theorem as a reusable target, not an optimizer wrapper. -/
def reducedRankGDetVariationalBound
    (Xtilde : Matrix n k ℝ) (Ytilde : Matrix n m ℝ) (lambda : r → ℝ) : Prop :=
  ∀ H : Matrix k r ℝ, reducedRankGNormalized Xtilde H →
    (Hᵀ * reducedRankGPencilA Xtilde Ytilde * H).det ≤ ∏ j, lambda j

omit [DecidableEq n] [Fintype k] in
/-- Canonical whitening factorization of Hansen's residualized G-pencil
numerator.

With `T = X̃` and
`M = Ỹ(Ỹ'Ỹ)⁻¹Ỹ'`, the numerator is exactly `T' M T`. This is the
factorization identity needed to route the G-side generalized pencil through an
ordinary identity-denominator determinant/product theorem. -/
theorem reducedRankGPencilA_eq_canonical_whitened_identity_factor
    (Xtilde : Matrix n k ℝ) (Ytilde : Matrix n m ℝ) :
    reducedRankGPencilA Xtilde Ytilde =
      Xtildeᵀ * (Ytilde * (Ytildeᵀ * Ytilde)⁻¹ * Ytildeᵀ) * Xtilde := by
  unfold reducedRankGPencilA
  simp [Matrix.mul_assoc]

omit [DecidableEq n] [Fintype k] in
/-- Canonical G-side whitening factorization using
`reducedRankGWhitenedProjection`. -/
theorem reducedRankGPencilA_eq_whitenedProjection_factor
    (Xtilde : Matrix n k ℝ) (Ytilde : Matrix n m ℝ) :
    reducedRankGPencilA Xtilde Ytilde =
      Xtildeᵀ * reducedRankGWhitenedProjection Ytilde * Xtilde := by
  simpa [reducedRankGWhitenedProjection] using
    reducedRankGPencilA_eq_canonical_whitened_identity_factor Xtilde Ytilde

omit [DecidableEq n] [Fintype k] in
/-- Canonical whitening factorization of Hansen's residualized G-pencil
denominator with `T = X̃`. -/
theorem reducedRankGPencilB_eq_canonical_whitened_identity_factor
    (Xtilde : Matrix n k ℝ) :
    reducedRankGPencilB Xtilde = Xtildeᵀ * Xtilde := rfl

omit [DecidableEq n] in
/-- Specialize a generic generalized-pencil determinant/product upper bound to
Hansen's G-side product variational inequality.

This is the theorem-facing bridge for the remaining raw min-max theorem: the
spectral result can be stated once for an arbitrary pencil `(A, B)`, then
instantiated here at Hansen's residualized pencil without restating the matrix
surface. -/
theorem reducedRankGDetVariationalBound_of_generalized_productUpperBound
    (Xtilde : Matrix n k ℝ) (Ytilde : Matrix n m ℝ) (lambda : r → ℝ)
    (hBound : generalizedEigenDetProductUpperBound
      (reducedRankGPencilA Xtilde Ytilde) (reducedRankGPencilB Xtilde) lambda) :
    reducedRankGDetVariationalBound Xtilde Ytilde lambda :=
  hBound

omit [DecidableEq n] in
/-- Hansen G-side whitening bridge for the determinant/product variational
bound.

If the residualized G pencil is factored as
`A_G = T' M T`, `B_G = T' T`, then the remaining G-side product theorem can be
proved for the ordinary identity-denominator pencil `(M, I)` over orthonormal
columns. This is the concrete reduction from Hansen's generalized pencil to the
standard whitened determinant product problem. -/
theorem reducedRankGDetVariationalBound_of_whitened_identity_productUpperBound
    {q : Type*} [Fintype q] [DecidableEq q]
    (Xtilde : Matrix n k ℝ) (Ytilde : Matrix n m ℝ)
    (M : Matrix q q ℝ) (T : Matrix q k ℝ) (lambda : r → ℝ)
    (hA : reducedRankGPencilA Xtilde Ytilde = Tᵀ * M * T)
    (hB : reducedRankGPencilB Xtilde = Tᵀ * T)
    (hBound : generalizedEigenDetProductUpperBound M 1 lambda) :
    reducedRankGDetVariationalBound Xtilde Ytilde lambda :=
  reducedRankGDetVariationalBound_of_generalized_productUpperBound
    Xtilde Ytilde lambda
    (generalizedEigenDetProductUpperBound_of_whitened_identity
      (reducedRankGPencilA Xtilde Ytilde) (reducedRankGPencilB Xtilde)
      M T lambda hA hB hBound)

/-- Hansen G-side determinant/product bound from the canonical identity-
denominator whitening `T = X̃`.

This removes the G-side pencil factorization from the remaining spectral
theorem: it is enough to prove the ordinary product bound for
`Ỹ(Ỹ'Ỹ)⁻¹Ỹ'` over orthonormal columns. -/
theorem reducedRankGDetVariationalBound_of_canonical_whitened_identity_productUpperBound
    (Xtilde : Matrix n k ℝ) (Ytilde : Matrix n m ℝ) (lambda : r → ℝ)
    (hBound : generalizedEigenDetProductUpperBound
      (Ytilde * (Ytildeᵀ * Ytilde)⁻¹ * Ytildeᵀ) (1 : Matrix n n ℝ) lambda) :
    reducedRankGDetVariationalBound Xtilde Ytilde lambda :=
  reducedRankGDetVariationalBound_of_whitened_identity_productUpperBound
    Xtilde Ytilde (Ytilde * (Ytildeᵀ * Ytilde)⁻¹ * Ytildeᵀ) Xtilde lambda
    (reducedRankGPencilA_eq_canonical_whitened_identity_factor Xtilde Ytilde)
    (reducedRankGPencilB_eq_canonical_whitened_identity_factor Xtilde)
    hBound

/-- Hansen G-side determinant/product bound from the canonical whitening plus
an ordinary identity-denominator selected compressed-determinant maximum. -/
theorem
    reducedRankGDetVariationalBound_of_canonical_whitened_identity_selected_compressedDet_maximal
    (Xtilde : Matrix n k ℝ) (Ytilde : Matrix n m ℝ)
    (lambda : r → ℝ) (G0 : Matrix n r ℝ)
    (hG0 : generalizedEigenvectorColumns
      (Ytilde * (Ytildeᵀ * Ytilde)⁻¹ * Ytildeᵀ)
      (1 : Matrix n n ℝ) lambda G0)
    (hG0Norm : G0ᵀ * G0 = 1)
    (hG0Max : ∀ H : Matrix n r ℝ, Hᵀ * H = 1 →
      (Hᵀ * (Ytilde * (Ytildeᵀ * Ytilde)⁻¹ * Ytildeᵀ) * H).det ≤
        (G0ᵀ * (Ytilde * (Ytildeᵀ * Ytilde)⁻¹ * Ytildeᵀ) * G0).det) :
    reducedRankGDetVariationalBound Xtilde Ytilde lambda :=
  reducedRankGDetVariationalBound_of_canonical_whitened_identity_productUpperBound
    Xtilde Ytilde lambda
    (generalizedEigenDetProductUpperBound_identity_of_selected_compressedDet_maximal
      (Ytilde * (Ytildeᵀ * Ytilde)⁻¹ * Ytildeᵀ) lambda G0
      hG0 hG0Norm hG0Max)

/-- Hansen G-side determinant/product bound from the canonical whitening when
the selected ordinary eigenvectors form a full orthonormal basis of the
whitened ambient space.

This is a proved multi-column ordinary determinant route. It does not replace
the partial leading-eigenspace theorem needed for the general `r < n` Hansen
case, but it removes all remaining determinant-extrema premises in the
full-basis case. -/
theorem reducedRankGDetVariationalBound_of_canonical_whitened_equiv_orthonormal_eigenbasis
    [DecidableEq r] (e : n ≃ r)
    (Xtilde : Matrix n k ℝ) (Ytilde : Matrix n m ℝ)
    (lambda : r → ℝ) (G0 : Matrix n r ℝ)
    (hG0 : generalizedEigenvectorColumns
      (reducedRankGWhitenedProjection Ytilde) (1 : Matrix n n ℝ) lambda G0)
    (hG0Norm : G0ᵀ * G0 = 1) :
    reducedRankGDetVariationalBound Xtilde Ytilde lambda := by
  have hBound :
      generalizedEigenDetProductUpperBound
        (reducedRankGWhitenedProjection Ytilde) (1 : Matrix n n ℝ) lambda :=
    generalizedEigenDetProductUpperBound_identity_of_equiv_orthonormal_eigenbasis
      e (reducedRankGWhitenedProjection Ytilde) lambda G0 hG0 hG0Norm
  exact reducedRankGDetVariationalBound_of_canonical_whitened_identity_productUpperBound
    Xtilde Ytilde lambda (by
      simpa [reducedRankGWhitenedProjection] using hBound)

omit [DecidableEq n] in
/-- Rank-one Hansen G-side determinant/product bound from the scalar
generalized Rayleigh inequality.

When the selected reduced-rank block has one column, the determinant in
Hansen's G-side variational inequality is a scalar quadratic form. This lemma
reduces the remaining raw generalized-pencil product theorem to the exact
one-dimensional Rayleigh bound normalized by `v'X̃'X̃v = 1`. -/
theorem reducedRankGDetVariationalBound_rankOne_of_rayleigh_bound
    [Unique r] (Xtilde : Matrix n k ℝ) (Ytilde : Matrix n m ℝ)
    (lambda : r → ℝ)
    (hBound : ∀ v : k → ℝ,
      v ⬝ᵥ (reducedRankGPencilB Xtilde *ᵥ v) = 1 →
        v ⬝ᵥ (reducedRankGPencilA Xtilde Ytilde *ᵥ v) ≤ lambda default) :
    reducedRankGDetVariationalBound Xtilde Ytilde lambda :=
  generalizedEigenDetProductUpperBound_rankOne_of_rayleigh_bound
    (reducedRankGPencilA Xtilde Ytilde) (reducedRankGPencilB Xtilde)
    lambda hBound

/-- Global maximizer predicate for Hansen's concentrated determinant objective
over normalized `G` matrices. -/
def reducedRankConcentratedObjectiveMaximizer
    (Xtilde : Matrix n k ℝ) (Ytilde : Matrix n m ℝ) (G : Matrix k r ℝ) : Prop :=
  reducedRankGNormalized Xtilde G ∧
    ∀ H : Matrix k r ℝ, reducedRankGNormalized Xtilde H →
      reducedRankConcentratedEigenObjective Xtilde Ytilde H ≤
        reducedRankConcentratedEigenObjective Xtilde Ytilde G

omit [DecidableEq n] in
/-- Specialize a generic generalized-pencil determinant-objective maximizer to
Hansen's concentrated G-side objective. -/
theorem reducedRankConcentratedObjectiveMaximizer_of_generalized_detObjectiveMaximizer
    (Xtilde : Matrix n k ℝ) (Ytilde : Matrix n m ℝ) (G : Matrix k r ℝ)
    (hOpt : generalizedEigenDetObjectiveMaximizer
      (reducedRankGPencilA Xtilde Ytilde) (reducedRankGPencilB Xtilde) G) :
    reducedRankConcentratedObjectiveMaximizer Xtilde Ytilde G :=
  hOpt

omit [DecidableEq n] in
/-- Hansen's direct G-side determinant objective attains a global maximum
under the regular residualized-design condition `X̃'X̃ ≻ 0` and the natural
dimension bound `r ≤ k`.

No generalized-eigenvector equation or objective maximum is assumed. The
remaining Theorem 11.7 work is to identify the ordered generalized eigenspace
with one such maximizer and coordinate it with the `A⊥` block. -/
theorem reducedRankConcentratedObjectiveMaximizer_exists_of_gram_posDef
    (Xtilde : Matrix n k ℝ) (Ytilde : Matrix n m ℝ)
    (hXGram : (Xtildeᵀ * Xtilde).PosDef)
    (hcard : Fintype.card r ≤ Fintype.card k) :
    ∃ G : Matrix k r ℝ,
      reducedRankConcentratedObjectiveMaximizer Xtilde Ytilde G := by
  have hB : (reducedRankGPencilB Xtilde).PosDef := by
    simpa [reducedRankGPencilB] using hXGram
  obtain ⟨G, hG⟩ :=
    generalizedEigenDetObjectiveMaximizer_exists_of_posDef
      (r := r) (reducedRankGPencilA Xtilde Ytilde)
        (reducedRankGPencilB Xtilde) hB hcard
  exact ⟨G,
    reducedRankConcentratedObjectiveMaximizer_of_generalized_detObjectiveMaximizer
      Xtilde Ytilde G hG⟩

omit [DecidableEq n] in
/-- Hansen's G pencil has normalized generalized-eigenvector columns in every
admissible reduced-rank dimension when `X̃'X̃` is positive definite.

This compatibility theorem exposes only spectral existence. The stronger
`reducedRankGDetProductMaxCertificate_exists_of_gram_posDef` below adds global
determinant maximality; the generic
`generalizedEigenLeadingDetProductMaxCertificate_exists_of_posSemidef_posDef`
retains the explicit leading-root formula. -/
theorem reducedRankHansenGEigenvectors_normalized_exists_of_gram_posDef
    (Xtilde : Matrix n k ℝ) (Ytilde : Matrix n m ℝ)
    (hXGram : (Xtildeᵀ * Xtilde).PosDef)
    (hcard : Fintype.card r ≤ Fintype.card k) :
    ∃ (G : Matrix k r ℝ) (lambda : r → ℝ),
      reducedRankHansenGEigenvectors Xtilde Ytilde lambda G ∧
        reducedRankGNormalized Xtilde G := by
  have hA : (reducedRankGPencilA Xtilde Ytilde).IsHermitian :=
    (reducedRankGPencilA_posSemidef Xtilde Ytilde).isHermitian
  have hB : (reducedRankGPencilB Xtilde).PosDef := by
    simpa [reducedRankGPencilB] using hXGram
  exact generalizedEigenvectorColumns_normalized_exists_of_isHermitian_posDef
    (r := r) (reducedRankGPencilA Xtilde Ytilde)
      (reducedRankGPencilB Xtilde) hA hB hcard

omit [DecidableEq n] in
/-- Hansen's G pencil admits a normalized generalized-eigenvector block that
is also a global determinant-product max certificate.

This compatibility projection does not retain the whitening data that
identifies the returned roots as leading ordered roots. -/
theorem reducedRankGDetProductMaxCertificate_exists_of_gram_posDef
    (Xtilde : Matrix n k ℝ) (Ytilde : Matrix n m ℝ)
    (hXGram : (Xtildeᵀ * Xtilde).PosDef)
    (hcard : Fintype.card r ≤ Fintype.card k) :
    ∃ (G : Matrix k r ℝ) (lambda : r → ℝ),
      GeneralizedEigenDetProductMaxCertificate
        (reducedRankGPencilA Xtilde Ytilde) (reducedRankGPencilB Xtilde)
        G lambda := by
  classical
  have hB : (reducedRankGPencilB Xtilde).PosDef := by
    simpa [reducedRankGPencilB] using hXGram
  exact generalizedEigenDetProductMaxCertificate_exists_of_posSemidef_posDef
    (r := r) (reducedRankGPencilA Xtilde Ytilde)
      (reducedRankGPencilB Xtilde)
      (reducedRankGPencilA_posSemidef Xtilde Ytilde) hB hcard

/-- Global minimizer predicate for Hansen's reciprocal concentrated objective
over normalized `G` matrices. -/
def reducedRankConcentratedReciprocalObjectiveMinimizer
    (Xtilde : Matrix n k ℝ) (Ytilde : Matrix n m ℝ) (G : Matrix k r ℝ) : Prop :=
  reducedRankGNormalized Xtilde G ∧
    ∀ H : Matrix k r ℝ, reducedRankGNormalized Xtilde H →
      reducedRankConcentratedReciprocalEigenObjective Xtilde Ytilde G ≤
        reducedRankConcentratedReciprocalEigenObjective Xtilde Ytilde H

/-- The weaker comparison obtained after restricting competitors to normalized
generalized-eigenvector candidates. This is useful proof infrastructure for
the leading-eigenvalue route without claiming the full determinant optimizer. -/
def reducedRankGEigenObjectiveMaximizerOnEigenvectors
    (Xtilde : Matrix n k ℝ) (Ytilde : Matrix n m ℝ)
    (G : Matrix k r ℝ) : Prop :=
  ∀ (H : Matrix k r ℝ) (mu : r → ℝ),
    reducedRankHansenGEigenvectors Xtilde Ytilde mu H →
      reducedRankGNormalized Xtilde H →
        reducedRankConcentratedEigenObjective Xtilde Ytilde H ≤
          reducedRankConcentratedEigenObjective Xtilde Ytilde G

/-- Reciprocal-objective comparison restricted to normalized generalized
eigenvector candidates. -/
def reducedRankGReciprocalObjectiveMinimizerOnEigenvectors
    (Xtilde : Matrix n k ℝ) (Ytilde : Matrix n m ℝ)
    (G : Matrix k r ℝ) : Prop :=
  ∀ (H : Matrix k r ℝ) (mu : r → ℝ),
    reducedRankHansenGEigenvectors Xtilde Ytilde mu H →
      reducedRankGNormalized Xtilde H →
        reducedRankConcentratedReciprocalEigenObjective Xtilde Ytilde G ≤
          reducedRankConcentratedReciprocalEigenObjective Xtilde Ytilde H

omit [DecidableEq n] in
/-- In Hansen's residualized pencil, normalized generalized eigenvectors make
the concentrated determinant objective equal to the product of the selected
generalized eigenvalues. -/
theorem reducedRankConcentratedObjective_eq_prod_eigenvalues_of_normalized
    (Xtilde : Matrix n k ℝ) (Ytilde : Matrix n m ℝ)
    (lambda : r → ℝ) (G : Matrix k r ℝ)
    (h : reducedRankHansenGEigenvectors Xtilde Ytilde lambda G)
    (hNorm : reducedRankGNormalized Xtilde G) :
    reducedRankConcentratedEigenObjective Xtilde Ytilde G = ∏ j, lambda j :=
  generalizedEigenDetObjective_eq_prod_eigenvalues_of_normalized
    (reducedRankGPencilA Xtilde Ytilde) (reducedRankGPencilB Xtilde) lambda G h hNorm

omit [DecidableEq n] in
/-- For Hansen's residualized `G` pencil, the selected compressed determinant
equals the product of the selected generalized roots under Hansen's
normalization. This is the determinant/product bridge used to turn a
compressed-determinant max theorem into the literal bound in Theorem 11.7. -/
theorem reducedRankGCompressedDet_eq_prod_of_normalized
    (Xtilde : Matrix n k ℝ) (Ytilde : Matrix n m ℝ)
    (lambda : r → ℝ) (G : Matrix k r ℝ)
    (h : reducedRankHansenGEigenvectors Xtilde Ytilde lambda G)
    (hNorm : reducedRankGNormalized Xtilde G) :
    (Gᵀ * reducedRankGPencilA Xtilde Ytilde * G).det = ∏ j, lambda j :=
  generalizedEigenvectorColumns_compressed_det_eq_prod_of_normalized
    (reducedRankGPencilA Xtilde Ytilde) (reducedRankGPencilB Xtilde) lambda G h hNorm

omit [DecidableEq n] in
/-- Positive selected G-side roots make Hansen's selected compressed
determinant nonsingular. -/
theorem reducedRankGCompressedDet_ne_zero_of_pos
    (Xtilde : Matrix n k ℝ) (Ytilde : Matrix n m ℝ)
    (lambda : r → ℝ) (G : Matrix k r ℝ)
    (h : reducedRankHansenGEigenvectors Xtilde Ytilde lambda G)
    (hNorm : reducedRankGNormalized Xtilde G)
    (hLambda : ∀ j, 0 < lambda j) :
    (Gᵀ * reducedRankGPencilA Xtilde Ytilde * G).det ≠ 0 :=
  generalizedEigenSelectedCompressedDet_ne_zero_of_pos
    (reducedRankGPencilA Xtilde Ytilde) (reducedRankGPencilB Xtilde)
    lambda G h hNorm hLambda

omit [DecidableEq n] in
/-- In Hansen's residualized pencil, normalized generalized eigenvectors make
the reciprocal concentrated objective equal to the reciprocal product of the
selected generalized eigenvalues. -/
theorem reducedRankConcentratedReciprocalObjective_eq_inv_prod_eigenvalues_of_normalized
    (Xtilde : Matrix n k ℝ) (Ytilde : Matrix n m ℝ)
    (lambda : r → ℝ) (G : Matrix k r ℝ)
    (h : reducedRankHansenGEigenvectors Xtilde Ytilde lambda G)
    (hNorm : reducedRankGNormalized Xtilde G) :
    reducedRankConcentratedReciprocalEigenObjective Xtilde Ytilde G =
      (∏ j, lambda j)⁻¹ :=
  generalizedEigenDetReciprocalObjective_eq_inv_prod_eigenvalues_of_normalized
    (reducedRankGPencilA Xtilde Ytilde) (reducedRankGPencilB Xtilde) lambda G h hNorm

omit [DecidableEq n] in
/-- Compression-bound route to Hansen's global reduced-rank determinant
optimizer.

The remaining spectral theorem for Hansen Theorem 11.7 should provide the
`hBound` premise: every normalized competitor admits an invariant compression
whose determinant is bounded by the determinant of the selected leading
generalized-eigenvalue block. This lemma then turns that variational statement
into the concrete optimizer predicate used by the MLE endpoint. -/
theorem reducedRankConcentratedObjectiveMaximizer_of_compression_det_bound
    (Xtilde : Matrix n k ℝ) (Ytilde : Matrix n m ℝ)
    (lambda : r → ℝ) (G : Matrix k r ℝ)
    (h : reducedRankHansenGEigenvectors Xtilde Ytilde lambda G)
    (hNorm : reducedRankGNormalized Xtilde G)
    (hBound : ∀ H : Matrix k r ℝ, reducedRankGNormalized Xtilde H →
      ∃ C : Matrix r r ℝ,
        generalizedEigenCompression
          (reducedRankGPencilA Xtilde Ytilde) (reducedRankGPencilB Xtilde) H C ∧
          C.det ≤ ∏ j, lambda j) :
    reducedRankConcentratedObjectiveMaximizer Xtilde Ytilde G := by
  constructor
  · exact hNorm
  · intro H hHNorm
    rcases hBound H hHNorm with ⟨C, hComp, hCdet⟩
    calc
      reducedRankConcentratedEigenObjective Xtilde Ytilde H = C.det :=
        generalizedEigenDetObjective_eq_det_compression_of_normalized
          (reducedRankGPencilA Xtilde Ytilde) (reducedRankGPencilB Xtilde)
          H C hComp hHNorm
      _ ≤ ∏ j, lambda j := hCdet
      _ = reducedRankConcentratedEigenObjective Xtilde Ytilde G := by
        rw [reducedRankConcentratedObjective_eq_prod_eigenvalues_of_normalized
          Xtilde Ytilde lambda G h hNorm]

omit [DecidableEq n] in
/-- Compressed-determinant route to Hansen's global reduced-rank determinant
optimizer.

This is the theorem-shaped bridge for the missing generalized-eigenvalue
determinant variational theorem: every `X̃'X̃`-normalized competitor only needs
the compressed determinant bound
`det(H' X̃'Ỹ(Ỹ'Ỹ)⁻¹Ỹ'X̃ H) ≤ ∏ λ_j`. No invariant-subspace assumption is made
on the competitor. -/
theorem reducedRankConcentratedObjectiveMaximizer_of_compressed_det_bound
    (Xtilde : Matrix n k ℝ) (Ytilde : Matrix n m ℝ)
    (lambda : r → ℝ) (G : Matrix k r ℝ)
    (h : reducedRankHansenGEigenvectors Xtilde Ytilde lambda G)
    (hNorm : reducedRankGNormalized Xtilde G)
    (hBound : ∀ H : Matrix k r ℝ, reducedRankGNormalized Xtilde H →
      (Hᵀ * reducedRankGPencilA Xtilde Ytilde * H).det ≤ ∏ j, lambda j) :
    reducedRankConcentratedObjectiveMaximizer Xtilde Ytilde G := by
  constructor
  · exact hNorm
  · intro H hHNorm
    calc
      reducedRankConcentratedEigenObjective Xtilde Ytilde H =
          (Hᵀ * reducedRankGPencilA Xtilde Ytilde * H).det := by
        exact generalizedEigenDetObjective_eq_compressed_det_of_normalized
          (reducedRankGPencilA Xtilde Ytilde) (reducedRankGPencilB Xtilde)
          H hHNorm
      _ ≤ ∏ j, lambda j := hBound H hHNorm
      _ = reducedRankConcentratedEigenObjective Xtilde Ytilde G := by
        rw [reducedRankConcentratedObjective_eq_prod_eigenvalues_of_normalized
          Xtilde Ytilde lambda G h hNorm]

omit [DecidableEq n] in
/-- The exact G-side determinant variational inequality is equivalent to
Hansen's concentrated determinant optimizer once the selected columns are
normalized generalized eigenvectors.

This keeps the remaining generalized-eigenvalue theorem focused on the literal
Hansen inequality
`det(H'X̃'Ỹ(Ỹ'Ỹ)⁻¹Ỹ'X̃H) ≤ ∏ λ_j`, while retaining compatibility with the
existing optimizer-based MLE route. -/
theorem reducedRankGDetVariationalBound_iff_objectiveMaximizer
    (Xtilde : Matrix n k ℝ) (Ytilde : Matrix n m ℝ)
    (lambda : r → ℝ) (G : Matrix k r ℝ)
    (h : reducedRankHansenGEigenvectors Xtilde Ytilde lambda G)
    (hNorm : reducedRankGNormalized Xtilde G) :
    reducedRankGDetVariationalBound Xtilde Ytilde lambda ↔
      reducedRankConcentratedObjectiveMaximizer Xtilde Ytilde G := by
  constructor
  · intro hBound
    exact reducedRankConcentratedObjectiveMaximizer_of_compressed_det_bound
      Xtilde Ytilde lambda G h hNorm hBound
  · intro hOpt H hHNorm
    calc
      (Hᵀ * reducedRankGPencilA Xtilde Ytilde * H).det =
          reducedRankConcentratedEigenObjective Xtilde Ytilde H := by
        exact (generalizedEigenDetObjective_eq_compressed_det_of_normalized
          (reducedRankGPencilA Xtilde Ytilde) (reducedRankGPencilB Xtilde)
          H hHNorm).symm
      _ ≤ reducedRankConcentratedEigenObjective Xtilde Ytilde G := hOpt.2 H hHNorm
      _ = ∏ j, lambda j := by
        exact reducedRankConcentratedObjective_eq_prod_eigenvalues_of_normalized
          Xtilde Ytilde lambda G h hNorm

omit [DecidableEq n] in
/-- Hansen G-side selected compressed-determinant maximum derived from the
normal-likelihood concentrated determinant objective. -/
theorem reducedRankGSelectedCompressedDetMaximal_of_objectiveMaximizer
    (Xtilde : Matrix n k ℝ) (Ytilde : Matrix n m ℝ) (G : Matrix k r ℝ)
    (hOpt : reducedRankConcentratedObjectiveMaximizer Xtilde Ytilde G) :
    generalizedEigenSelectedCompressedDetMaximal
      (reducedRankGPencilA Xtilde Ytilde) (reducedRankGPencilB Xtilde) G :=
  generalizedEigenSelectedCompressedDetMaximal_of_detObjectiveMaximizer
    (reducedRankGPencilA Xtilde Ytilde) (reducedRankGPencilB Xtilde) G
    ⟨hOpt.1, hOpt.2⟩

omit [DecidableEq n] in
/-- Hansen G-side determinant/product min-max theorem derived from the
normal-likelihood concentrated determinant objective. -/
theorem reducedRankGDetVariationalBound_of_objectiveMaximizer
    (Xtilde : Matrix n k ℝ) (Ytilde : Matrix n m ℝ)
    (lambda : r → ℝ) (G : Matrix k r ℝ)
    (h : reducedRankHansenGEigenvectors Xtilde Ytilde lambda G)
    (hOpt : reducedRankConcentratedObjectiveMaximizer Xtilde Ytilde G) :
    reducedRankGDetVariationalBound Xtilde Ytilde lambda :=
  (reducedRankGDetVariationalBound_iff_objectiveMaximizer
    Xtilde Ytilde lambda G h hOpt.1).mpr hOpt

omit [DecidableEq n] in
/-- Hansen G-side determinant/product certificate derived from the
normal-likelihood concentrated determinant objective. -/
theorem reducedRankGDetProductMaxCertificate_of_objectiveMaximizer
    (Xtilde : Matrix n k ℝ) (Ytilde : Matrix n m ℝ)
    (lambda : r → ℝ) (G : Matrix k r ℝ)
    (h : reducedRankHansenGEigenvectors Xtilde Ytilde lambda G)
    (hOpt : reducedRankConcentratedObjectiveMaximizer Xtilde Ytilde G) :
    GeneralizedEigenDetProductMaxCertificate
      (reducedRankGPencilA Xtilde Ytilde) (reducedRankGPencilB Xtilde) G lambda :=
  GeneralizedEigenDetProductMaxCertificate.of_detObjectiveMaximizer
    (reducedRankGPencilA Xtilde Ytilde) (reducedRankGPencilB Xtilde)
    G lambda h ⟨hOpt.1, hOpt.2⟩

omit [DecidableEq n] in
/-- A compressed-determinant maximum of the selected `G` columns supplies
Hansen's literal G-side product variational bound.

The remaining spectral min-max theorem may now prove the natural determinant
comparison against the selected subspace; this lemma performs the exact
product conversion using the generalized-eigenvector equations and Hansen
normalization. -/
theorem reducedRankGDetVariationalBound_of_selected_compressedDet_maximal
    (Xtilde : Matrix n k ℝ) (Ytilde : Matrix n m ℝ)
    (lambda : r → ℝ) (G : Matrix k r ℝ)
    (h : reducedRankHansenGEigenvectors Xtilde Ytilde lambda G)
    (hNorm : reducedRankGNormalized Xtilde G)
    (hMax : ∀ H : Matrix k r ℝ, reducedRankGNormalized Xtilde H →
      (Hᵀ * reducedRankGPencilA Xtilde Ytilde * H).det ≤
        (Gᵀ * reducedRankGPencilA Xtilde Ytilde * G).det) :
    reducedRankGDetVariationalBound Xtilde Ytilde lambda := by
  intro H hHNorm
  calc
    (Hᵀ * reducedRankGPencilA Xtilde Ytilde * H).det
        ≤ (Gᵀ * reducedRankGPencilA Xtilde Ytilde * G).det := hMax H hHNorm
    _ = ∏ j, lambda j := reducedRankGCompressedDet_eq_prod_of_normalized
      Xtilde Ytilde lambda G h hNorm

omit [DecidableEq n] in
/-- If the selected generalized eigenvalues dominate the eigenvalue products
of all normalized generalized-eigenvector competitors, then the corresponding
columns maximize Hansen's determinant objective on that generalized-eigenvector
candidate class. -/
theorem reducedRankGEigenObjectiveMaximizerOnEigenvectors_of_eigenvalueProduct_maximal
    (Xtilde : Matrix n k ℝ) (Ytilde : Matrix n m ℝ)
    (lambda : r → ℝ) (G : Matrix k r ℝ)
    (h : reducedRankHansenGEigenvectors Xtilde Ytilde lambda G)
    (hNorm : reducedRankGNormalized Xtilde G)
    (hlead : ∀ (H : Matrix k r ℝ) (mu : r → ℝ),
      reducedRankHansenGEigenvectors Xtilde Ytilde mu H →
        reducedRankGNormalized Xtilde H → ∏ j, mu j ≤ ∏ j, lambda j) :
    reducedRankGEigenObjectiveMaximizerOnEigenvectors Xtilde Ytilde G := by
  intro H mu hH hHNorm
  rw [reducedRankConcentratedObjective_eq_prod_eigenvalues_of_normalized
        Xtilde Ytilde mu H hH hHNorm,
      reducedRankConcentratedObjective_eq_prod_eigenvalues_of_normalized
        Xtilde Ytilde lambda G h hNorm]
  exact hlead H mu hH hHNorm

omit [DecidableEq n] in
/-- If the reciprocal selected-eigenvalue product is minimal over normalized
generalized-eigenvector competitors, then the corresponding columns minimize
Hansen's reciprocal determinant objective on that candidate class. -/
theorem reducedRankGReciprocalObjectiveMinimizerOnEigenvectors_of_invEigenvalueProduct_minimal
    (Xtilde : Matrix n k ℝ) (Ytilde : Matrix n m ℝ)
    (lambda : r → ℝ) (G : Matrix k r ℝ)
    (h : reducedRankHansenGEigenvectors Xtilde Ytilde lambda G)
    (hNorm : reducedRankGNormalized Xtilde G)
    (hlead : ∀ (H : Matrix k r ℝ) (mu : r → ℝ),
      reducedRankHansenGEigenvectors Xtilde Ytilde mu H →
        reducedRankGNormalized Xtilde H →
          (∏ j, lambda j)⁻¹ ≤ (∏ j, mu j)⁻¹) :
    reducedRankGReciprocalObjectiveMinimizerOnEigenvectors Xtilde Ytilde G := by
  intro H mu hH hHNorm
  rw [reducedRankConcentratedReciprocalObjective_eq_inv_prod_eigenvalues_of_normalized
        Xtilde Ytilde lambda G h hNorm,
      reducedRankConcentratedReciprocalObjective_eq_inv_prod_eigenvalues_of_normalized
        Xtilde Ytilde mu H hH hHNorm]
  exact hlead H mu hH hHNorm

end Objective

section AperpObjective

variable [Fintype s] [DecidableEq s]

/-- Hansen normalization for Theorem 11.7's `A⊥` block:
`A⊥' Ỹ'Ỹ A⊥ = I`. -/
def reducedRankAperpNormalized
    (Ytilde : Matrix n m ℝ) (Aperp : Matrix m s ℝ) : Prop :=
  generalizedEigenvectorBNormalized (reducedRankAperpPencilB Ytilde) Aperp

omit [DecidableEq n] [DecidableEq m] [Fintype s] in
/-- Hansen normalization of `A⊥` says that the image block `ỸA⊥` is ordinary
orthonormal. -/
theorem reducedRankAperp_image_orthonormal_of_normalized
    (Ytilde : Matrix n m ℝ) (Aperp : Matrix m s ℝ)
    (hNorm : reducedRankAperpNormalized Ytilde Aperp) :
    (Ytilde * Aperp)ᵀ * (Ytilde * Aperp) = (1 : Matrix s s ℝ) := by
  change Aperpᵀ * (Ytildeᵀ * Ytilde) * Aperp = 1 at hNorm
  simpa [Matrix.transpose_mul, Matrix.mul_assoc] using hNorm

/-- Hansen's determinant objective for the `A⊥` representation (11.21). -/
noncomputable def reducedRankAperpEigenObjective
    (Etilde : Matrix n m ℝ) (Ytilde : Matrix n m ℝ)
    (Aperp : Matrix m s ℝ) : ℝ :=
  generalizedEigenDetObjective (reducedRankAperpPencilA Etilde)
    (reducedRankAperpPencilB Ytilde) Aperp

/-- Reciprocal form of Hansen's `A⊥` objective, matching the equivalent
`argmin` display following equation (11.21). -/
noncomputable def reducedRankAperpReciprocalEigenObjective
    (Etilde : Matrix n m ℝ) (Ytilde : Matrix n m ℝ)
    (Aperp : Matrix m s ℝ) : ℝ :=
  generalizedEigenDetReciprocalObjective (reducedRankAperpPencilA Etilde)
    (reducedRankAperpPencilB Ytilde) Aperp

/-- Exact `A⊥`-side determinant variational inequality in Hansen Theorem 11.7.

For every competitor normalized by `H' Ỹ'Ỹ H = I`, the product of the selected
dual generalized roots is bounded by the compressed residual determinant. This
is the literal lower-bound target
`∏ η_j ≤ det(H'Ẽ'ẼH)`. -/
def reducedRankAperpDetVariationalBound
    (Etilde : Matrix n m ℝ) (Ytilde : Matrix n m ℝ) (eta : s → ℝ) : Prop :=
  ∀ H : Matrix m s ℝ, reducedRankAperpNormalized Ytilde H →
    ∏ j, eta j ≤ (Hᵀ * reducedRankAperpPencilA Etilde * H).det

omit [DecidableEq n] [DecidableEq m] in
/-- Specialize a generic generalized-pencil determinant/product lower bound to
Hansen's `A⊥`-side product variational inequality. -/
theorem reducedRankAperpDetVariationalBound_of_generalized_productLowerBound
    (Etilde : Matrix n m ℝ) (Ytilde : Matrix n m ℝ) (eta : s → ℝ)
    (hBound : generalizedEigenDetProductLowerBound
      (reducedRankAperpPencilA Etilde) (reducedRankAperpPencilB Ytilde) eta) :
    reducedRankAperpDetVariationalBound Etilde Ytilde eta :=
  hBound

omit [DecidableEq n] [DecidableEq m] [Fintype m] in
/-- Residual-factor whitening identity for Hansen's `A⊥` numerator.

If the unrestricted residual block factors as `Ẽ = R Ỹ`, then
`Ẽ'Ẽ = Ỹ' (R'R) Ỹ`. This is the algebraic bridge needed to reduce the
`A⊥` generalized pencil to an ordinary identity-denominator problem once the
residual-maker factorization has been proved. -/
theorem reducedRankAperpPencilA_eq_whitened_identity_factor_of_left_factor
    (Etilde : Matrix n m ℝ) (Ytilde : Matrix n m ℝ)
    (R M : Matrix n n ℝ)
    (hE : Etilde = R * Ytilde)
    (hM : M = Rᵀ * R) :
    reducedRankAperpPencilA Etilde = Ytildeᵀ * M * Ytilde := by
  unfold reducedRankAperpPencilA
  calc
    Etildeᵀ * Etilde = (R * Ytilde)ᵀ * (R * Ytilde) := by rw [hE]
    _ = Ytildeᵀ * (Rᵀ * R) * Ytilde := by
      simp [Matrix.transpose_mul, Matrix.mul_assoc]
    _ = Ytildeᵀ * M * Ytilde := by rw [← hM]

omit [DecidableEq n] [DecidableEq m] [Fintype m] in
/-- Residual-factor whitening identity using
`reducedRankAperpResidualWhitenedMatrix`. -/
theorem reducedRankAperpPencilA_eq_residualWhitened_factor_of_left_factor
    (Etilde : Matrix n m ℝ) (Ytilde : Matrix n m ℝ)
    (R : Matrix n n ℝ)
    (hE : Etilde = R * Ytilde) :
    reducedRankAperpPencilA Etilde =
      Ytildeᵀ * reducedRankAperpResidualWhitenedMatrix R * Ytilde :=
  reducedRankAperpPencilA_eq_whitened_identity_factor_of_left_factor
    Etilde Ytilde R (reducedRankAperpResidualWhitenedMatrix R) hE rfl

omit [Fintype m] [DecidableEq m] in
/-- Concrete residualized `A⊥` numerator factorization for Hansen Theorem 11.7.

This specializes `Ẽ'Ẽ = Ỹ'(R'R)Ỹ` to the actual residualized matrices
`Ỹ = M_ZY`, `Ẽ = M_[X,Z]Y`, and
`R = reducedRankAperpResidualFactor X Z`. -/
theorem reducedRankAperpPencilA_eq_residualized_residualWhitened_factor
    (Z : Matrix n ell ℝ) (X : Matrix n k ℝ) (Y : Matrix n m ℝ)
    [DecidableEq k] [Invertible (Zᵀ * Z)]
    [Invertible ((Matrix.fromCols X Z)ᵀ * Matrix.fromCols X Z)] :
    reducedRankAperpPencilA (reducedRankTildeE X Z Y) =
      (reducedRankTildeY Z Y)ᵀ *
        reducedRankAperpResidualWhitenedMatrix (reducedRankAperpResidualFactor X Z) *
          reducedRankTildeY Z Y :=
  reducedRankAperpPencilA_eq_residualWhitened_factor_of_left_factor
    (reducedRankTildeE X Z Y) (reducedRankTildeY Z Y)
    (reducedRankAperpResidualFactor X Z)
    (reducedRankTildeE_eq_residualFactor_mul_tildeY Z X Y)

omit [DecidableEq n] [DecidableEq m] [Fintype s] in
/-- If `Ẽ = RỸ` and the Hansen-normalized image block `ỸA⊥` is killed by
the residual factor `R`, then `A⊥` solves Hansen's original dual generalized
eigenvector equations with displayed roots all equal to `0`.

This is the dual image-space bridge used by the projection/residual-null route
for Theorem 11.7. -/
theorem reducedRankHansenAperpEigenvectors_zero_of_residual_factor_image_null
    (Etilde Ytilde : Matrix n m ℝ) (R : Matrix n n ℝ)
    (Aperp : Matrix m s ℝ)
    (hE : Etilde = R * Ytilde)
    (hNorm : reducedRankAperpNormalized Ytilde Aperp)
    (hNull : R * (Ytilde * Aperp) = 0) :
    reducedRankHansenAperpEigenvectors Etilde Ytilde (fun _ : s => (0 : ℝ)) Aperp := by
  intro j
  refine ⟨?_, ?_⟩
  · intro hzero
    have hYANorm := reducedRankAperp_image_orthonormal_of_normalized Ytilde Aperp hNorm
    have hYAzero : (fun i : n => (Ytilde * Aperp) i j) = 0 := by
      funext i
      have hcol : ∀ a : m, Aperp a j = 0 := fun a => congrFun hzero a
      simp [Matrix.mul_apply, hcol]
    exact column_ne_zero_of_orthonormal (Ytilde * Aperp) hYANorm j hYAzero
  · have hWhiteNull :
        reducedRankAperpResidualWhitenedMatrix R * (Ytilde * Aperp) = 0 :=
      reducedRankAperpResidualWhitenedMatrix_mul_eq_zero_of_factor_null
        R (Ytilde * Aperp) hNull
    have hFactor :
        reducedRankAperpPencilA Etilde =
          Ytildeᵀ * reducedRankAperpResidualWhitenedMatrix R * Ytilde :=
      reducedRankAperpPencilA_eq_residualWhitened_factor_of_left_factor
        Etilde Ytilde R hE
    have hMat : reducedRankAperpPencilA Etilde * Aperp = 0 := by
      calc
        reducedRankAperpPencilA Etilde * Aperp =
            (Ytildeᵀ * reducedRankAperpResidualWhitenedMatrix R * Ytilde) * Aperp := by
              rw [hFactor]
        _ = Ytildeᵀ * (reducedRankAperpResidualWhitenedMatrix R * (Ytilde * Aperp)) := by
              simp [Matrix.mul_assoc]
        _ = 0 := by rw [hWhiteNull]; simp
    ext i
    have hEntry := congrArg (fun M : Matrix m s ℝ => M i j) hMat
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using hEntry

omit [DecidableEq m] [Fintype s] in
/-- Residualized version of
`reducedRankHansenAperpEigenvectors_zero_of_residual_factor_image_null` for
Hansen's concrete unrestricted residual maker `M_[X,Z]`. -/
theorem reducedRankHansenAperpEigenvectors_zero_of_residualized_image_null
    (Z : Matrix n ell ℝ) (X : Matrix n k ℝ) (Y : Matrix n m ℝ)
    (Aperp : Matrix m s ℝ)
    [DecidableEq k] [Invertible (Zᵀ * Z)]
    [Invertible ((Matrix.fromCols X Z)ᵀ * Matrix.fromCols X Z)]
    (hNorm : reducedRankAperpNormalized (reducedRankTildeY Z Y) Aperp)
    (hNull :
      reducedRankAperpResidualFactor X Z * (reducedRankTildeY Z Y * Aperp) = 0) :
    reducedRankHansenAperpEigenvectors
      (reducedRankTildeE X Z Y) (reducedRankTildeY Z Y)
      (fun _ : s => (0 : ℝ)) Aperp :=
  reducedRankHansenAperpEigenvectors_zero_of_residual_factor_image_null
    (reducedRankTildeE X Z Y) (reducedRankTildeY Z Y)
    (reducedRankAperpResidualFactor X Z) Aperp
    (reducedRankTildeE_eq_residualFactor_mul_tildeY Z X Y) hNorm hNull

omit [DecidableEq n] [DecidableEq m] [Fintype m] in
/-- Canonical factorization of Hansen's `A⊥` denominator with `T = Ỹ`. -/
theorem reducedRankAperpPencilB_eq_canonical_whitened_identity_factor
    (Ytilde : Matrix n m ℝ) :
    reducedRankAperpPencilB Ytilde = Ytildeᵀ * Ytilde := rfl

omit [DecidableEq n] [DecidableEq m] in
/-- Hansen `A⊥`-side whitening bridge for the determinant/product variational
bound.

Once the residual `A⊥` pencil is represented as
`A_⊥ = T' M T`, `B_⊥ = T' T`, the remaining lower-bound theorem is the ordinary
identity-denominator determinant product theorem for `M` on orthonormal
columns. -/
theorem reducedRankAperpDetVariationalBound_of_whitened_identity_productLowerBound
    {q : Type*} [Fintype q] [DecidableEq q]
    (Etilde : Matrix n m ℝ) (Ytilde : Matrix n m ℝ)
    (M : Matrix q q ℝ) (T : Matrix q m ℝ) (eta : s → ℝ)
    (hA : reducedRankAperpPencilA Etilde = Tᵀ * M * T)
    (hB : reducedRankAperpPencilB Ytilde = Tᵀ * T)
    (hBound : generalizedEigenDetProductLowerBound M 1 eta) :
    reducedRankAperpDetVariationalBound Etilde Ytilde eta :=
  reducedRankAperpDetVariationalBound_of_generalized_productLowerBound
    Etilde Ytilde eta
    (generalizedEigenDetProductLowerBound_of_whitened_identity
      (reducedRankAperpPencilA Etilde) (reducedRankAperpPencilB Ytilde)
      M T eta hA hB hBound)

omit [DecidableEq m] in
/-- Hansen `A⊥` determinant/product lower bound from a residual-factor
identity `Ẽ = R Ỹ`.

After this factorization, the remaining lower-bound theorem is the ordinary
identity-denominator product theorem for `M = R'R` over orthonormal columns. -/
theorem reducedRankAperpDetVariationalBound_of_residual_factor_identity_productLowerBound
    (Etilde : Matrix n m ℝ) (Ytilde : Matrix n m ℝ)
    (R M : Matrix n n ℝ) (eta : s → ℝ)
    (hE : Etilde = R * Ytilde)
    (hM : M = Rᵀ * R)
    (hBound : generalizedEigenDetProductLowerBound M (1 : Matrix n n ℝ) eta) :
    reducedRankAperpDetVariationalBound Etilde Ytilde eta :=
  reducedRankAperpDetVariationalBound_of_whitened_identity_productLowerBound
    Etilde Ytilde M Ytilde eta
    (reducedRankAperpPencilA_eq_whitened_identity_factor_of_left_factor
      Etilde Ytilde R M hE hM)
    (reducedRankAperpPencilB_eq_canonical_whitened_identity_factor Ytilde)
    hBound

omit [DecidableEq m] in
/-- Hansen `A⊥` determinant/product lower bound from a residual-factor
identity and an ordinary identity-denominator selected compressed-determinant
minimum. -/
theorem
    reducedRankAperpDetVariationalBound_of_residual_factor_identity_selected_compressedDet_minimal
    (Etilde : Matrix n m ℝ) (Ytilde : Matrix n m ℝ)
    (R M : Matrix n n ℝ) (eta : s → ℝ) (A0 : Matrix n s ℝ)
    (hE : Etilde = R * Ytilde)
    (hM : M = Rᵀ * R)
    (hA0 : generalizedEigenvectorColumns M (1 : Matrix n n ℝ) eta A0)
    (hA0Norm : A0ᵀ * A0 = 1)
    (hA0Min : ∀ H : Matrix n s ℝ, Hᵀ * H = 1 →
      (A0ᵀ * M * A0).det ≤ (Hᵀ * M * H).det) :
    reducedRankAperpDetVariationalBound Etilde Ytilde eta :=
  reducedRankAperpDetVariationalBound_of_residual_factor_identity_productLowerBound
    Etilde Ytilde R M eta hE hM
    (generalizedEigenDetProductLowerBound_identity_of_selected_compressedDet_minimal
      M eta A0 hA0 hA0Norm hA0Min)

omit [DecidableEq m] in
/-- Hansen `A⊥` determinant/product lower bound from a residual-factor
identity when the selected ordinary residual-factor eigenvectors form a full
orthonormal basis of the whitened ambient space.

This is the full-basis multi-column ordinary determinant route for the dual
side. The general Hansen theorem still needs the partial trailing-eigenspace
determinant theorem when the selected `A⊥` block is not ambient-square. -/
theorem reducedRankAperpDetVariationalBound_of_residual_factor_identity_equiv_orthonormal_eigenbasis
    [DecidableEq s] (e : n ≃ s)
    (Etilde : Matrix n m ℝ) (Ytilde : Matrix n m ℝ)
    (R : Matrix n n ℝ) (eta : s → ℝ) (A0 : Matrix n s ℝ)
    (hE : Etilde = R * Ytilde)
    (hA0 : generalizedEigenvectorColumns
      (reducedRankAperpResidualWhitenedMatrix R) (1 : Matrix n n ℝ) eta A0)
    (hA0Norm : A0ᵀ * A0 = 1) :
    reducedRankAperpDetVariationalBound Etilde Ytilde eta :=
  reducedRankAperpDetVariationalBound_of_residual_factor_identity_productLowerBound
    Etilde Ytilde R (reducedRankAperpResidualWhitenedMatrix R) eta hE rfl
    (generalizedEigenDetProductLowerBound_identity_of_equiv_orthonormal_eigenbasis
      e (reducedRankAperpResidualWhitenedMatrix R) eta A0 hA0 hA0Norm)

omit [DecidableEq m] in
/-- Residualized Hansen `A⊥` determinant/product lower bound from the ordinary
identity-denominator product theorem for the concrete residual-factor matrix
`R'R`, where `R = M_[X,Z]`. -/
theorem reducedRankAperpDetVariationalBound_of_residualized_productLowerBound
    (Z : Matrix n ell ℝ) (X : Matrix n k ℝ) (Y : Matrix n m ℝ)
    (eta : s → ℝ)
    [DecidableEq k] [Invertible (Zᵀ * Z)]
    [Invertible ((Matrix.fromCols X Z)ᵀ * Matrix.fromCols X Z)]
    (hBound : generalizedEigenDetProductLowerBound
      (reducedRankAperpResidualWhitenedMatrix (reducedRankAperpResidualFactor X Z))
      (1 : Matrix n n ℝ) eta) :
    reducedRankAperpDetVariationalBound
      (reducedRankTildeE X Z Y) (reducedRankTildeY Z Y) eta :=
  reducedRankAperpDetVariationalBound_of_residual_factor_identity_productLowerBound
    (reducedRankTildeE X Z Y) (reducedRankTildeY Z Y)
    (reducedRankAperpResidualFactor X Z)
    (reducedRankAperpResidualWhitenedMatrix (reducedRankAperpResidualFactor X Z))
    eta (reducedRankTildeE_eq_residualFactor_mul_tildeY Z X Y) rfl hBound

omit [DecidableEq m] in
/-- Residualized Hansen `A⊥` determinant/product lower bound from the ordinary
selected-compressed-determinant minimum for the concrete residual-factor
matrix `R'R`, where `R = M_[X,Z]`. -/
theorem
    reducedRankAperpDetVariationalBound_of_residualized_selected_compressedDet_minimal
    (Z : Matrix n ell ℝ) (X : Matrix n k ℝ) (Y : Matrix n m ℝ)
    (eta : s → ℝ) (A0 : Matrix n s ℝ)
    [DecidableEq k] [Invertible (Zᵀ * Z)]
    [Invertible ((Matrix.fromCols X Z)ᵀ * Matrix.fromCols X Z)]
    (hA0 : generalizedEigenvectorColumns
      (reducedRankAperpResidualWhitenedMatrix (reducedRankAperpResidualFactor X Z))
      (1 : Matrix n n ℝ) eta A0)
    (hA0Norm : A0ᵀ * A0 = 1)
    (hA0Min : ∀ H : Matrix n s ℝ, Hᵀ * H = 1 →
      (A0ᵀ * reducedRankAperpResidualWhitenedMatrix
          (reducedRankAperpResidualFactor X Z) * A0).det ≤
        (Hᵀ * reducedRankAperpResidualWhitenedMatrix
          (reducedRankAperpResidualFactor X Z) * H).det) :
    reducedRankAperpDetVariationalBound
      (reducedRankTildeE X Z Y) (reducedRankTildeY Z Y) eta :=
  reducedRankAperpDetVariationalBound_of_residualized_productLowerBound
    Z X Y eta
    (generalizedEigenDetProductLowerBound_identity_of_selected_compressedDet_minimal
      (reducedRankAperpResidualWhitenedMatrix (reducedRankAperpResidualFactor X Z))
      eta A0 hA0 hA0Norm hA0Min)

omit [DecidableEq m] in
/-- Residualized Hansen `A⊥` determinant/product lower bound from a full
ordinary orthonormal eigenbasis of the concrete residual-factor matrix
`R'R`, where `R = M_[X,Z]`. -/
theorem reducedRankAperpDetVariationalBound_of_residualized_equiv_orthonormal_eigenbasis
    [DecidableEq s] (e : n ≃ s)
    (Z : Matrix n ell ℝ) (X : Matrix n k ℝ) (Y : Matrix n m ℝ)
    (eta : s → ℝ) (A0 : Matrix n s ℝ)
    [DecidableEq k] [Invertible (Zᵀ * Z)]
    [Invertible ((Matrix.fromCols X Z)ᵀ * Matrix.fromCols X Z)]
    (hA0 : generalizedEigenvectorColumns
      (reducedRankAperpResidualWhitenedMatrix (reducedRankAperpResidualFactor X Z))
      (1 : Matrix n n ℝ) eta A0)
    (hA0Norm : A0ᵀ * A0 = 1) :
    reducedRankAperpDetVariationalBound
      (reducedRankTildeE X Z Y) (reducedRankTildeY Z Y) eta :=
  reducedRankAperpDetVariationalBound_of_residual_factor_identity_equiv_orthonormal_eigenbasis
    e (reducedRankTildeE X Z Y) (reducedRankTildeY Z Y)
    (reducedRankAperpResidualFactor X Z) eta A0
    (reducedRankTildeE_eq_residualFactor_mul_tildeY Z X Y) hA0 hA0Norm

omit [DecidableEq n] [DecidableEq m] in
/-- Rank-one Hansen `A⊥`-side determinant/product bound from the scalar
generalized Rayleigh lower bound.

This is the dual one-column bridge for Hansen Theorem 11.7: it reduces
`∏ η_j ≤ det(H'Ẽ'ẼH)` to the scalar inequality for vectors normalized by
`v'Ỹ'Ỹv = 1`. -/
theorem reducedRankAperpDetVariationalBound_rankOne_of_rayleigh_bound
    [Unique s] (Etilde : Matrix n m ℝ) (Ytilde : Matrix n m ℝ)
    (eta : s → ℝ)
    (hBound : ∀ v : m → ℝ,
      v ⬝ᵥ (reducedRankAperpPencilB Ytilde *ᵥ v) = 1 →
        eta default ≤ v ⬝ᵥ (reducedRankAperpPencilA Etilde *ᵥ v)) :
    reducedRankAperpDetVariationalBound Etilde Ytilde eta :=
  generalizedEigenDetProductLowerBound_rankOne_of_rayleigh_bound
    (reducedRankAperpPencilA Etilde) (reducedRankAperpPencilB Ytilde)
    eta hBound

/-- Global maximizer predicate for Hansen's `A⊥` determinant objective over
`Ỹ'Ỹ`-normalized matrices. -/
def reducedRankAperpObjectiveMaximizer
    (Etilde : Matrix n m ℝ) (Ytilde : Matrix n m ℝ)
    (Aperp : Matrix m s ℝ) : Prop :=
  reducedRankAperpNormalized Ytilde Aperp ∧
    ∀ H : Matrix m s ℝ, reducedRankAperpNormalized Ytilde H →
          reducedRankAperpEigenObjective Etilde Ytilde H ≤
          reducedRankAperpEigenObjective Etilde Ytilde Aperp

omit [DecidableEq n] [DecidableEq m] in
/-- Specialize a generic generalized-pencil determinant-objective maximizer to
Hansen's direct `A⊥` determinant objective (11.21). -/
theorem reducedRankAperpObjectiveMaximizer_of_generalized_detObjectiveMaximizer
    (Etilde : Matrix n m ℝ) (Ytilde : Matrix n m ℝ) (Aperp : Matrix m s ℝ)
    (hOpt : generalizedEigenDetObjectiveMaximizer
      (reducedRankAperpPencilA Etilde) (reducedRankAperpPencilB Ytilde) Aperp) :
    reducedRankAperpObjectiveMaximizer Etilde Ytilde Aperp :=
  hOpt

omit [DecidableEq n] [DecidableEq m] in
/-- Hansen's direct equation (11.21) `A⊥` determinant objective attains a
global maximum under `Ỹ'Ỹ ≻ 0` and the natural dimension bound `s ≤ m`.

This is a compactness consequence, not an assumption of the selected residual
roots or of cross orthogonality with a G-side maximizer. -/
theorem reducedRankAperpObjectiveMaximizer_exists_of_gram_posDef
    (Etilde : Matrix n m ℝ) (Ytilde : Matrix n m ℝ)
    (hYGram : (Ytildeᵀ * Ytilde).PosDef)
    (hcard : Fintype.card s ≤ Fintype.card m) :
    ∃ Aperp : Matrix m s ℝ,
      reducedRankAperpObjectiveMaximizer Etilde Ytilde Aperp := by
  have hB : (reducedRankAperpPencilB Ytilde).PosDef := by
    simpa [reducedRankAperpPencilB] using hYGram
  obtain ⟨Aperp, hAperp⟩ :=
    generalizedEigenDetObjectiveMaximizer_exists_of_posDef
      (r := s) (reducedRankAperpPencilA Etilde)
        (reducedRankAperpPencilB Ytilde) hB hcard
  exact ⟨Aperp,
    reducedRankAperpObjectiveMaximizer_of_generalized_detObjectiveMaximizer
      Etilde Ytilde Aperp hAperp⟩

omit [DecidableEq n] [DecidableEq m] in
/-- Hansen's residual `A⊥` pencil has normalized generalized-eigenvector
columns in every admissible complement dimension when `Ỹ'Ỹ` is positive
definite.

This compatibility theorem exposes only spectral existence. The stronger
`reducedRankAperpDetProductMaxCertificate_exists_of_gram_posDef` below adds
global maximality for equation (11.21); the generic
`generalizedEigenLeadingDetProductMaxCertificate_exists_of_posSemidef_posDef`
retains the explicit leading-root formula. -/
theorem reducedRankHansenAperpEigenvectors_normalized_exists_of_gram_posDef
    (Etilde : Matrix n m ℝ) (Ytilde : Matrix n m ℝ)
    (hYGram : (Ytildeᵀ * Ytilde).PosDef)
    (hcard : Fintype.card s ≤ Fintype.card m) :
    ∃ (Aperp : Matrix m s ℝ) (eta : s → ℝ),
      reducedRankHansenAperpEigenvectors Etilde Ytilde eta Aperp ∧
        reducedRankAperpNormalized Ytilde Aperp := by
  have hA : (reducedRankAperpPencilA Etilde).IsHermitian :=
    (reducedRankAperpPencilA_posSemidef Etilde).isHermitian
  have hB : (reducedRankAperpPencilB Ytilde).PosDef := by
    simpa [reducedRankAperpPencilB] using hYGram
  exact generalizedEigenvectorColumns_normalized_exists_of_isHermitian_posDef
    (r := s) (reducedRankAperpPencilA Etilde)
      (reducedRankAperpPencilB Ytilde) hA hB hcard

omit [DecidableEq n] [DecidableEq m] in
/-- Hansen's direct equation (11.21) residual pencil admits a normalized
generalized-eigenvector block that is also a global determinant-product max
certificate.

This compatibility projection does not retain the whitening data that
identifies the returned roots as leading ordered roots. -/
theorem reducedRankAperpDetProductMaxCertificate_exists_of_gram_posDef
    (Etilde : Matrix n m ℝ) (Ytilde : Matrix n m ℝ)
    (hYGram : (Ytildeᵀ * Ytilde).PosDef)
    (hcard : Fintype.card s ≤ Fintype.card m) :
    ∃ (Aperp : Matrix m s ℝ) (eta : s → ℝ),
      GeneralizedEigenDetProductMaxCertificate
        (reducedRankAperpPencilA Etilde) (reducedRankAperpPencilB Ytilde)
        Aperp eta := by
  classical
  have hB : (reducedRankAperpPencilB Ytilde).PosDef := by
    simpa [reducedRankAperpPencilB] using hYGram
  exact generalizedEigenDetProductMaxCertificate_exists_of_posSemidef_posDef
    (r := s) (reducedRankAperpPencilA Etilde)
      (reducedRankAperpPencilB Ytilde)
      (reducedRankAperpPencilA_posSemidef Etilde) hB hcard

/-- Global minimizer predicate for Hansen's `A⊥` determinant objective over
`Ỹ'Ỹ`-normalized matrices.

This is compatibility with the isolated "smallest eigenvalues" sentence in
Hansen's final Theorem 11.7 summary. It conflicts with equation (11.21), the
preceding derivation, and the equivalent residual-pencil display, all of which
use `argmax` and the largest roots. Consequently this minimum is not the MLE
`A⊥` complement; canonical theorem-facing declarations use
`reducedRankAperpObjectiveMaximizer`. -/
def reducedRankAperpObjectiveMinimizer
    (Etilde : Matrix n m ℝ) (Ytilde : Matrix n m ℝ)
    (Aperp : Matrix m s ℝ) : Prop :=
  reducedRankAperpNormalized Ytilde Aperp ∧
    ∀ H : Matrix m s ℝ, reducedRankAperpNormalized Ytilde H →
      reducedRankAperpEigenObjective Etilde Ytilde Aperp ≤
        reducedRankAperpEigenObjective Etilde Ytilde H

omit [DecidableEq n] [DecidableEq m] in
/-- Specialize a generic generalized-pencil determinant-objective minimizer to
Hansen's direct `A⊥` determinant objective. -/
theorem reducedRankAperpObjectiveMinimizer_of_generalized_detObjectiveMinimizer
    (Etilde : Matrix n m ℝ) (Ytilde : Matrix n m ℝ) (Aperp : Matrix m s ℝ)
    (hOpt : generalizedEigenDetObjectiveMinimizer
      (reducedRankAperpPencilA Etilde) (reducedRankAperpPencilB Ytilde) Aperp) :
    reducedRankAperpObjectiveMinimizer Etilde Ytilde Aperp :=
  hOpt

/-- Global minimizer predicate for Hansen's reciprocal `A⊥` determinant
objective over `Ỹ'Ỹ`-normalized matrices. -/
def reducedRankAperpReciprocalObjectiveMinimizer
    (Etilde : Matrix n m ℝ) (Ytilde : Matrix n m ℝ)
    (Aperp : Matrix m s ℝ) : Prop :=
  reducedRankAperpNormalized Ytilde Aperp ∧
    ∀ H : Matrix m s ℝ, reducedRankAperpNormalized Ytilde H →
      reducedRankAperpReciprocalEigenObjective Etilde Ytilde Aperp ≤
        reducedRankAperpReciprocalEigenObjective Etilde Ytilde H

/-- The weaker comparison obtained after restricting competitors to normalized
`A⊥` generalized-eigenvector candidates. -/
def reducedRankAperpGEigenObjectiveMaximizerOnEigenvectors
    (Etilde : Matrix n m ℝ) (Ytilde : Matrix n m ℝ)
    (Aperp : Matrix m s ℝ) : Prop :=
  ∀ (H : Matrix m s ℝ) (mu : s → ℝ),
    reducedRankHansenAperpEigenvectors Etilde Ytilde mu H →
      reducedRankAperpNormalized Ytilde H →
        reducedRankAperpEigenObjective Etilde Ytilde H ≤
          reducedRankAperpEigenObjective Etilde Ytilde Aperp

/-- The direct determinant-objective comparison after restricting competitors
to normalized `A⊥` generalized-eigenvector candidates. -/
def reducedRankAperpGEigenObjectiveMinimizerOnEigenvectors
    (Etilde : Matrix n m ℝ) (Ytilde : Matrix n m ℝ)
    (Aperp : Matrix m s ℝ) : Prop :=
  ∀ (H : Matrix m s ℝ) (mu : s → ℝ),
    reducedRankHansenAperpEigenvectors Etilde Ytilde mu H →
      reducedRankAperpNormalized Ytilde H →
        reducedRankAperpEigenObjective Etilde Ytilde Aperp ≤
          reducedRankAperpEigenObjective Etilde Ytilde H

/-- The reciprocal-objective comparison after restricting competitors to
normalized `A⊥` generalized-eigenvector candidates. -/
def reducedRankAperpReciprocalObjectiveMinimizerOnEigenvectors
    (Etilde : Matrix n m ℝ) (Ytilde : Matrix n m ℝ)
    (Aperp : Matrix m s ℝ) : Prop :=
  ∀ (H : Matrix m s ℝ) (mu : s → ℝ),
    reducedRankHansenAperpEigenvectors Etilde Ytilde mu H →
      reducedRankAperpNormalized Ytilde H →
        reducedRankAperpReciprocalEigenObjective Etilde Ytilde Aperp ≤
          reducedRankAperpReciprocalEigenObjective Etilde Ytilde H

omit [DecidableEq n] [DecidableEq m] in
/-- In Hansen's `A⊥` residualized pencil, normalized generalized eigenvectors
make the determinant objective equal to the product of selected generalized
eigenvalues. -/
theorem reducedRankAperpObjective_eq_prod_eigenvalues_of_normalized
    (Etilde : Matrix n m ℝ) (Ytilde : Matrix n m ℝ)
    (lambda : s → ℝ) (Aperp : Matrix m s ℝ)
    (h : reducedRankHansenAperpEigenvectors Etilde Ytilde lambda Aperp)
    (hNorm : reducedRankAperpNormalized Ytilde Aperp) :
    reducedRankAperpEigenObjective Etilde Ytilde Aperp = ∏ j, lambda j :=
  generalizedEigenDetObjective_eq_prod_eigenvalues_of_normalized
    (reducedRankAperpPencilA Etilde) (reducedRankAperpPencilB Ytilde)
    lambda Aperp h hNorm

omit [DecidableEq n] [DecidableEq m] in
/-- For Hansen's `A⊥` residual pencil, the selected compressed determinant
equals the product of selected dual generalized roots under Hansen's
normalization. This is the dual determinant/product bridge behind Theorem
11.7's `∏ η_j ≤ det(H'Ẽ'ẼH)` inequality. -/
theorem reducedRankAperpCompressedDet_eq_prod_of_normalized
    (Etilde : Matrix n m ℝ) (Ytilde : Matrix n m ℝ)
    (lambda : s → ℝ) (Aperp : Matrix m s ℝ)
    (h : reducedRankHansenAperpEigenvectors Etilde Ytilde lambda Aperp)
    (hNorm : reducedRankAperpNormalized Ytilde Aperp) :
    (Aperpᵀ * reducedRankAperpPencilA Etilde * Aperp).det = ∏ j, lambda j :=
  generalizedEigenvectorColumns_compressed_det_eq_prod_of_normalized
    (reducedRankAperpPencilA Etilde) (reducedRankAperpPencilB Ytilde)
    lambda Aperp h hNorm

omit [DecidableEq n] [DecidableEq m] in
/-- In Hansen's reciprocal `A⊥` objective, normalized generalized eigenvectors
make the determinant ratio equal to the reciprocal product of selected
generalized eigenvalues. -/
theorem reducedRankAperpReciprocalObjective_eq_inv_prod_eigenvalues_of_normalized
    (Etilde : Matrix n m ℝ) (Ytilde : Matrix n m ℝ)
    (lambda : s → ℝ) (Aperp : Matrix m s ℝ)
    (h : reducedRankHansenAperpEigenvectors Etilde Ytilde lambda Aperp)
    (hNorm : reducedRankAperpNormalized Ytilde Aperp) :
    reducedRankAperpReciprocalEigenObjective Etilde Ytilde Aperp =
      (∏ j, lambda j)⁻¹ :=
  generalizedEigenDetReciprocalObjective_eq_inv_prod_eigenvalues_of_normalized
    (reducedRankAperpPencilA Etilde) (reducedRankAperpPencilB Ytilde)
    lambda Aperp h hNorm

omit [DecidableEq n] [DecidableEq m] in
/-- Compressed-determinant route to the global maximizer in Hansen's direct
`A⊥` objective (11.21).

The selected normalized generalized-eigenvector block has objective
`∏ eta_j`; an upper bound on every normalized competitor therefore proves that
the selected residual-pencil roots are product-maximal. -/
theorem reducedRankAperpObjectiveMaximizer_of_compressed_det_bound
    (Etilde : Matrix n m ℝ) (Ytilde : Matrix n m ℝ)
    (eta : s → ℝ) (Aperp : Matrix m s ℝ)
    (h : reducedRankHansenAperpEigenvectors Etilde Ytilde eta Aperp)
    (hNorm : reducedRankAperpNormalized Ytilde Aperp)
    (hBound : ∀ H : Matrix m s ℝ, reducedRankAperpNormalized Ytilde H →
      (Hᵀ * reducedRankAperpPencilA Etilde * H).det ≤ ∏ j, eta j) :
    reducedRankAperpObjectiveMaximizer Etilde Ytilde Aperp := by
  constructor
  · exact hNorm
  · intro H hHNorm
    calc
      reducedRankAperpEigenObjective Etilde Ytilde H =
          (Hᵀ * reducedRankAperpPencilA Etilde * H).det :=
        generalizedEigenDetObjective_eq_compressed_det_of_normalized
          (reducedRankAperpPencilA Etilde) (reducedRankAperpPencilB Ytilde)
          H hHNorm
      _ ≤ ∏ j, eta j := hBound H hHNorm
      _ = reducedRankAperpEigenObjective Etilde Ytilde Aperp :=
        (reducedRankAperpObjective_eq_prod_eigenvalues_of_normalized
          Etilde Ytilde eta Aperp h hNorm).symm

omit [DecidableEq n] [DecidableEq m] in
/-- A direct `A⊥` objective maximizer supplies the selected compressed-
determinant maximum used by the maximizer-oriented spectral certificate. -/
theorem reducedRankAperpSelectedCompressedDetMaximal_of_objectiveMaximizer
    (Etilde : Matrix n m ℝ) (Ytilde : Matrix n m ℝ)
    (Aperp : Matrix m s ℝ)
    (hOpt : reducedRankAperpObjectiveMaximizer Etilde Ytilde Aperp) :
    generalizedEigenSelectedCompressedDetMaximal
      (reducedRankAperpPencilA Etilde) (reducedRankAperpPencilB Ytilde) Aperp :=
  generalizedEigenSelectedCompressedDetMaximal_of_detObjectiveMaximizer
    (reducedRankAperpPencilA Etilde) (reducedRankAperpPencilB Ytilde) Aperp
    hOpt

omit [DecidableEq n] [DecidableEq m] in
/-- Compression-bound route to Hansen's global `A⊥` determinant minimizer.

This is the dual-side analogue of
`reducedRankConcentratedObjectiveMaximizer_of_compression_det_bound`: once the
spectral theorem proves that every normalized competitor has compressed
determinant at least the selected `A⊥` block determinant, the determinant
objective minimizer follows. -/
theorem reducedRankAperpObjectiveMinimizer_of_compression_det_bound
    (Etilde : Matrix n m ℝ) (Ytilde : Matrix n m ℝ)
    (lambda : s → ℝ) (Aperp : Matrix m s ℝ)
    (h : reducedRankHansenAperpEigenvectors Etilde Ytilde lambda Aperp)
    (hNorm : reducedRankAperpNormalized Ytilde Aperp)
    (hBound : ∀ H : Matrix m s ℝ, reducedRankAperpNormalized Ytilde H →
      ∃ C : Matrix s s ℝ,
        generalizedEigenCompression
          (reducedRankAperpPencilA Etilde) (reducedRankAperpPencilB Ytilde) H C ∧
          ∏ j, lambda j ≤ C.det) :
    reducedRankAperpObjectiveMinimizer Etilde Ytilde Aperp := by
  constructor
  · exact hNorm
  · intro H hHNorm
    rcases hBound H hHNorm with ⟨C, hComp, hCdet⟩
    calc
      reducedRankAperpEigenObjective Etilde Ytilde Aperp = ∏ j, lambda j := by
        rw [reducedRankAperpObjective_eq_prod_eigenvalues_of_normalized
          Etilde Ytilde lambda Aperp h hNorm]
      _ ≤ C.det := hCdet
      _ = reducedRankAperpEigenObjective Etilde Ytilde H := by
        exact (generalizedEigenDetObjective_eq_det_compression_of_normalized
          (reducedRankAperpPencilA Etilde) (reducedRankAperpPencilB Ytilde)
          H C hComp hHNorm).symm

omit [DecidableEq n] [DecidableEq m] in
/-- Compressed-determinant route to Hansen's global `A⊥` determinant
minimizer.

This is the `A⊥` side of the theorem-shaped bridge for the missing
generalized-eigenvalue determinant variational theorem: every `Ỹ'Ỹ`-normalized
competitor only needs the compressed determinant lower bound
`∏ η_j ≤ det(H' Ẽ'Ẽ H)`. No invariant-subspace assumption is made on the
competitor. -/
theorem reducedRankAperpObjectiveMinimizer_of_compressed_det_bound
    (Etilde : Matrix n m ℝ) (Ytilde : Matrix n m ℝ)
    (lambda : s → ℝ) (Aperp : Matrix m s ℝ)
    (h : reducedRankHansenAperpEigenvectors Etilde Ytilde lambda Aperp)
    (hNorm : reducedRankAperpNormalized Ytilde Aperp)
    (hBound : ∀ H : Matrix m s ℝ, reducedRankAperpNormalized Ytilde H →
      ∏ j, lambda j ≤ (Hᵀ * reducedRankAperpPencilA Etilde * H).det) :
    reducedRankAperpObjectiveMinimizer Etilde Ytilde Aperp := by
  constructor
  · exact hNorm
  · intro H hHNorm
    calc
      reducedRankAperpEigenObjective Etilde Ytilde Aperp = ∏ j, lambda j := by
        rw [reducedRankAperpObjective_eq_prod_eigenvalues_of_normalized
          Etilde Ytilde lambda Aperp h hNorm]
      _ ≤ (Hᵀ * reducedRankAperpPencilA Etilde * H).det := hBound H hHNorm
      _ = reducedRankAperpEigenObjective Etilde Ytilde H := by
        exact (generalizedEigenDetObjective_eq_compressed_det_of_normalized
          (reducedRankAperpPencilA Etilde) (reducedRankAperpPencilB Ytilde)
          H hHNorm).symm

omit [DecidableEq n] [DecidableEq m] in
/-- The exact `A⊥` determinant variational inequality is equivalent to Hansen's
dual determinant minimizer once the selected columns are normalized generalized
eigenvectors.

This isolates the remaining product min-max theorem on the literal Hansen
surface `∏ η_j ≤ det(H'Ẽ'ẼH)`. -/
theorem reducedRankAperpDetVariationalBound_iff_objectiveMinimizer
    (Etilde : Matrix n m ℝ) (Ytilde : Matrix n m ℝ)
    (eta : s → ℝ) (Aperp : Matrix m s ℝ)
    (h : reducedRankHansenAperpEigenvectors Etilde Ytilde eta Aperp)
    (hNorm : reducedRankAperpNormalized Ytilde Aperp) :
    reducedRankAperpDetVariationalBound Etilde Ytilde eta ↔
      reducedRankAperpObjectiveMinimizer Etilde Ytilde Aperp := by
  constructor
  · intro hBound
    exact reducedRankAperpObjectiveMinimizer_of_compressed_det_bound
      Etilde Ytilde eta Aperp h hNorm hBound
  · intro hOpt H hHNorm
    calc
      ∏ j, eta j = reducedRankAperpEigenObjective Etilde Ytilde Aperp := by
        exact (reducedRankAperpObjective_eq_prod_eigenvalues_of_normalized
          Etilde Ytilde eta Aperp h hNorm).symm
      _ ≤ reducedRankAperpEigenObjective Etilde Ytilde H := hOpt.2 H hHNorm
      _ = (Hᵀ * reducedRankAperpPencilA Etilde * H).det := by
        exact generalizedEigenDetObjective_eq_compressed_det_of_normalized
          (reducedRankAperpPencilA Etilde) (reducedRankAperpPencilB Ytilde)
          H hHNorm

omit [DecidableEq n] [DecidableEq m] in
/-- Hansen `A⊥`-side selected compressed-determinant minimum derived from the
dual normal-likelihood determinant objective. -/
theorem reducedRankAperpSelectedCompressedDetMinimal_of_objectiveMinimizer
    (Etilde : Matrix n m ℝ) (Ytilde : Matrix n m ℝ)
    (Aperp : Matrix m s ℝ)
    (hOpt : reducedRankAperpObjectiveMinimizer Etilde Ytilde Aperp) :
    generalizedEigenSelectedCompressedDetMinimal
      (reducedRankAperpPencilA Etilde) (reducedRankAperpPencilB Ytilde) Aperp :=
  generalizedEigenSelectedCompressedDetMinimal_of_detObjectiveMinimizer
    (reducedRankAperpPencilA Etilde) (reducedRankAperpPencilB Ytilde) Aperp
    ⟨hOpt.1, hOpt.2⟩

omit [DecidableEq n] [DecidableEq m] in
/-- Hansen `A⊥`-side determinant/product min-max theorem derived from the
dual normal-likelihood determinant objective. -/
theorem reducedRankAperpDetVariationalBound_of_objectiveMinimizer
    (Etilde : Matrix n m ℝ) (Ytilde : Matrix n m ℝ)
    (eta : s → ℝ) (Aperp : Matrix m s ℝ)
    (h : reducedRankHansenAperpEigenvectors Etilde Ytilde eta Aperp)
    (hOpt : reducedRankAperpObjectiveMinimizer Etilde Ytilde Aperp) :
    reducedRankAperpDetVariationalBound Etilde Ytilde eta :=
  (reducedRankAperpDetVariationalBound_iff_objectiveMinimizer
    Etilde Ytilde eta Aperp h hOpt.1).mpr hOpt

omit [DecidableEq n] [DecidableEq m] in
/-- Hansen `A⊥`-side determinant/product certificate derived from the
dual normal-likelihood determinant objective. -/
theorem reducedRankAperpDetProductMinCertificate_of_objectiveMinimizer
    (Etilde : Matrix n m ℝ) (Ytilde : Matrix n m ℝ)
    (eta : s → ℝ) (Aperp : Matrix m s ℝ)
    (h : reducedRankHansenAperpEigenvectors Etilde Ytilde eta Aperp)
    (hOpt : reducedRankAperpObjectiveMinimizer Etilde Ytilde Aperp) :
    GeneralizedEigenDetProductMinCertificate
      (reducedRankAperpPencilA Etilde) (reducedRankAperpPencilB Ytilde) Aperp eta :=
  GeneralizedEigenDetProductMinCertificate.of_detObjectiveMinimizer
    (reducedRankAperpPencilA Etilde) (reducedRankAperpPencilB Ytilde)
    Aperp eta h ⟨hOpt.1, hOpt.2⟩

omit [DecidableEq n] [DecidableEq m] in
/-- A compressed-determinant minimum of the selected `A⊥` columns supplies
Hansen's literal dual product variational bound.

This separates the spectral min-max work from the product conversion: prove the
selected `A⊥` subspace minimizes the residual compressed determinant, and this
lemma derives `∏ η_j ≤ det(H'Ẽ'ẼH)` for every normalized competitor. -/
theorem reducedRankAperpDetVariationalBound_of_selected_compressedDet_minimal
    (Etilde : Matrix n m ℝ) (Ytilde : Matrix n m ℝ)
    (eta : s → ℝ) (Aperp : Matrix m s ℝ)
    (h : reducedRankHansenAperpEigenvectors Etilde Ytilde eta Aperp)
    (hNorm : reducedRankAperpNormalized Ytilde Aperp)
    (hMin : ∀ H : Matrix m s ℝ, reducedRankAperpNormalized Ytilde H →
      (Aperpᵀ * reducedRankAperpPencilA Etilde * Aperp).det ≤
        (Hᵀ * reducedRankAperpPencilA Etilde * H).det) :
    reducedRankAperpDetVariationalBound Etilde Ytilde eta := by
  intro H hHNorm
  calc
    ∏ j, eta j
        = (Aperpᵀ * reducedRankAperpPencilA Etilde * Aperp).det := by
          exact (reducedRankAperpCompressedDet_eq_prod_of_normalized
            Etilde Ytilde eta Aperp h hNorm).symm
    _ ≤ (Hᵀ * reducedRankAperpPencilA Etilde * H).det := hMin H hHNorm

omit [DecidableEq n] [DecidableEq m] in
/-- If the selected `A⊥` generalized eigenvalues dominate the eigenvalue
products of all normalized generalized-eigenvector competitors, then the
corresponding columns maximize Hansen's `A⊥` determinant objective on that
candidate class. -/
theorem reducedRankAperpGEigenObjectiveMaximizerOnEigenvectors_of_eigenvalueProduct_maximal
    (Etilde : Matrix n m ℝ) (Ytilde : Matrix n m ℝ)
    (lambda : s → ℝ) (Aperp : Matrix m s ℝ)
    (h : reducedRankHansenAperpEigenvectors Etilde Ytilde lambda Aperp)
    (hNorm : reducedRankAperpNormalized Ytilde Aperp)
    (hlead : ∀ (H : Matrix m s ℝ) (mu : s → ℝ),
      reducedRankHansenAperpEigenvectors Etilde Ytilde mu H →
        reducedRankAperpNormalized Ytilde H → ∏ j, mu j ≤ ∏ j, lambda j) :
    reducedRankAperpGEigenObjectiveMaximizerOnEigenvectors Etilde Ytilde Aperp := by
  intro H mu hH hHNorm
  rw [reducedRankAperpObjective_eq_prod_eigenvalues_of_normalized
        Etilde Ytilde mu H hH hHNorm,
      reducedRankAperpObjective_eq_prod_eigenvalues_of_normalized
        Etilde Ytilde lambda Aperp h hNorm]
  exact hlead H mu hH hHNorm

omit [DecidableEq n] [DecidableEq m] in
/-- If the selected `A⊥` generalized eigenvalues are product-minimal among
normalized generalized-eigenvector competitors, then the corresponding columns
minimize Hansen's direct `A⊥` determinant objective on that candidate class. -/
theorem reducedRankAperpGEigenObjectiveMinimizerOnEigenvectors_of_eigenvalueProduct_minimal
    (Etilde : Matrix n m ℝ) (Ytilde : Matrix n m ℝ)
    (lambda : s → ℝ) (Aperp : Matrix m s ℝ)
    (h : reducedRankHansenAperpEigenvectors Etilde Ytilde lambda Aperp)
    (hNorm : reducedRankAperpNormalized Ytilde Aperp)
    (hlead : ∀ (H : Matrix m s ℝ) (mu : s → ℝ),
      reducedRankHansenAperpEigenvectors Etilde Ytilde mu H →
        reducedRankAperpNormalized Ytilde H → ∏ j, lambda j ≤ ∏ j, mu j) :
    reducedRankAperpGEigenObjectiveMinimizerOnEigenvectors Etilde Ytilde Aperp := by
  intro H mu hH hHNorm
  rw [reducedRankAperpObjective_eq_prod_eigenvalues_of_normalized
        Etilde Ytilde lambda Aperp h hNorm,
      reducedRankAperpObjective_eq_prod_eigenvalues_of_normalized
        Etilde Ytilde mu H hH hHNorm]
  exact hlead H mu hH hHNorm

omit [DecidableEq n] [DecidableEq m] in
/-- If the reciprocal selected-eigenvalue product is minimal over normalized
`A⊥` generalized-eigenvector competitors, then the corresponding columns
minimize Hansen's reciprocal determinant objective on that candidate class. -/
theorem reducedRankAperpReciprocalObjectiveMinimizerOnEigenvectors_of_invEigenvalueProduct_minimal
    (Etilde : Matrix n m ℝ) (Ytilde : Matrix n m ℝ)
    (lambda : s → ℝ) (Aperp : Matrix m s ℝ)
    (h : reducedRankHansenAperpEigenvectors Etilde Ytilde lambda Aperp)
    (hNorm : reducedRankAperpNormalized Ytilde Aperp)
    (hlead : ∀ (H : Matrix m s ℝ) (mu : s → ℝ),
      reducedRankHansenAperpEigenvectors Etilde Ytilde mu H →
        reducedRankAperpNormalized Ytilde H →
          (∏ j, lambda j)⁻¹ ≤ (∏ j, mu j)⁻¹) :
    reducedRankAperpReciprocalObjectiveMinimizerOnEigenvectors
      Etilde Ytilde Aperp := by
  intro H mu hH hHNorm
  rw [reducedRankAperpReciprocalObjective_eq_inv_prod_eigenvalues_of_normalized
        Etilde Ytilde lambda Aperp h hNorm,
      reducedRankAperpReciprocalObjective_eq_inv_prod_eigenvalues_of_normalized
        Etilde Ytilde mu H hH hHNorm]
  exact hlead H mu hH hHNorm

end AperpObjective

section ObjectiveExistence

variable [Fintype r] [DecidableEq r] [Fintype s] [DecidableEq s]

omit [DecidableEq n] in
/-- Under positive-definite residualized X and Y Gram matrices, both direct
determinant objectives in Hansen's reduced-rank derivation attain maxima.

The witnesses are deliberately existential and independent: this theorem does
not assume or claim the still-missing simultaneous generalized-eigenspace and
cross-orthogonality selection. -/
theorem reducedRankHansenObjectiveMaximizers_exist_of_gram_posDef
    (Xtilde : Matrix n k ℝ) (Ytilde Etilde : Matrix n m ℝ)
    (hXGram : (Xtildeᵀ * Xtilde).PosDef)
    (hYGram : (Ytildeᵀ * Ytilde).PosDef)
    (hrk : Fintype.card r ≤ Fintype.card k)
    (hsm : Fintype.card s ≤ Fintype.card m) :
    ∃ (G : Matrix k r ℝ) (Aperp : Matrix m s ℝ),
      reducedRankConcentratedObjectiveMaximizer Xtilde Ytilde G ∧
        reducedRankAperpObjectiveMaximizer Etilde Ytilde Aperp := by
  obtain ⟨G, hG⟩ :=
    reducedRankConcentratedObjectiveMaximizer_exists_of_gram_posDef
      Xtilde Ytilde hXGram hrk
  obtain ⟨Aperp, hAperp⟩ :=
    reducedRankAperpObjectiveMaximizer_exists_of_gram_posDef
      Etilde Ytilde hYGram hsm
  exact ⟨G, Aperp, hG, hAperp⟩

/-- Residualized-data specialization of
`reducedRankHansenObjectiveMaximizers_exist_of_gram_posDef`.

Full column rank of `[X,Z]` and of `Z` imply the `X̃'X̃` denominator condition;
`Ỹ'Ỹ ≻ 0` is the only additional realized-sample Gram premise. The theorem
derives both objective-maximizer witnesses without taking either maximum or
cross orthogonality as an input. It does not assert that the same witnesses are
the ordered generalized-eigenvector blocks or form the simultaneous
cross-orthogonal pair required by Hansen's certificate. -/
theorem reducedRankHansenResidualizedObjectiveMaximizers_exist_of_gram_posDef
    (Z : Matrix n ell ℝ) (X : Matrix n k ℝ) (Y : Matrix n m ℝ)
    [DecidableEq k]
    [Invertible (Zᵀ * Z)]
    [Invertible ((Matrix.fromCols X Z)ᵀ * Matrix.fromCols X Z)]
    (hYGram :
      ((reducedRankTildeY Z Y)ᵀ * reducedRankTildeY Z Y).PosDef)
    (hrk : Fintype.card r ≤ Fintype.card k)
    (hsm : Fintype.card s ≤ Fintype.card m) :
    ∃ (G : Matrix k r ℝ) (Aperp : Matrix m s ℝ),
      reducedRankConcentratedObjectiveMaximizer
          (reducedRankTildeX Z X) (reducedRankTildeY Z Y) G ∧
        reducedRankAperpObjectiveMaximizer
          (reducedRankTildeE X Z Y) (reducedRankTildeY Z Y) Aperp :=
  reducedRankHansenObjectiveMaximizers_exist_of_gram_posDef
    (r := r) (s := s)
    (reducedRankTildeX Z X) (reducedRankTildeY Z Y)
      (reducedRankTildeE X Z Y)
      (reducedRankTildeX_gram_posDef Z X) hYGram hrk hsm

/-- Raw full-Gram specialization of
`reducedRankHansenResidualizedObjectiveMaximizers_exist_of_gram_posDef`.

Full column rank of `[X,Z]`, `[Y,Z]`, and `Z` now supplies both positive-
definite pencil denominators. The resulting direct-objective maximizers remain
independent witnesses; no spectral identification or cross orthogonality is
assumed. -/
theorem reducedRankHansenResidualizedObjectiveMaximizers_exist_of_full_grams
    (Z : Matrix n ell ℝ) (X : Matrix n k ℝ) (Y : Matrix n m ℝ)
    [DecidableEq k]
    [Invertible (Zᵀ * Z)]
    [Invertible ((Matrix.fromCols X Z)ᵀ * Matrix.fromCols X Z)]
    [Invertible ((Matrix.fromCols Y Z)ᵀ * Matrix.fromCols Y Z)]
    (hrk : Fintype.card r ≤ Fintype.card k)
    (hsm : Fintype.card s ≤ Fintype.card m) :
    ∃ (G : Matrix k r ℝ) (Aperp : Matrix m s ℝ),
      reducedRankConcentratedObjectiveMaximizer
          (reducedRankTildeX Z X) (reducedRankTildeY Z Y) G ∧
        reducedRankAperpObjectiveMaximizer
          (reducedRankTildeE X Z Y) (reducedRankTildeY Z Y) Aperp :=
  reducedRankHansenResidualizedObjectiveMaximizers_exist_of_gram_posDef
    (r := r) (s := s) Z X Y (reducedRankTildeY_gram_posDef Z Y) hrk hsm

/-- The two residualized Hansen pencils each admit normalized generalized-
eigenvector blocks under the same regular sample assumptions used by the
objective-existence theorem.

The G-side denominator condition is derived from full `[X,Z]` rank by
`reducedRankTildeX_gram_posDef`; only `Ỹ'Ỹ ≻ 0` is an additional realized-
sample premise. The two existential witnesses are not yet asserted to be the
simultaneous objective maximizers or cross-orthogonal pair required by the
identified Theorem 11.7 certificate. -/
theorem reducedRankHansenResidualizedNormalizedEigenblocks_exist_of_yGram_posDef
    (Z : Matrix n ell ℝ) (X : Matrix n k ℝ) (Y : Matrix n m ℝ)
    [DecidableEq k]
    [Invertible (Zᵀ * Z)]
    [Invertible ((Matrix.fromCols X Z)ᵀ * Matrix.fromCols X Z)]
    (hYGram :
      ((reducedRankTildeY Z Y)ᵀ * reducedRankTildeY Z Y).PosDef)
    (hrk : Fintype.card r ≤ Fintype.card k)
    (hsm : Fintype.card s ≤ Fintype.card m) :
    (∃ (G : Matrix k r ℝ) (lambda : r → ℝ),
      reducedRankHansenGEigenvectors
          (reducedRankTildeX Z X) (reducedRankTildeY Z Y) lambda G ∧
        reducedRankGNormalized (reducedRankTildeX Z X) G) ∧
      ∃ (Aperp : Matrix m s ℝ) (eta : s → ℝ),
        reducedRankHansenAperpEigenvectors
            (reducedRankTildeE X Z Y) (reducedRankTildeY Z Y) eta Aperp ∧
          reducedRankAperpNormalized (reducedRankTildeY Z Y) Aperp := by
  constructor
  · exact reducedRankHansenGEigenvectors_normalized_exists_of_gram_posDef
      (r := r) (reducedRankTildeX Z X) (reducedRankTildeY Z Y)
        (reducedRankTildeX_gram_posDef Z X) hrk
  · exact reducedRankHansenAperpEigenvectors_normalized_exists_of_gram_posDef
      (s := s) (reducedRankTildeE X Z Y) (reducedRankTildeY Z Y) hYGram hsm

/-- Raw full-Gram specialization of
`reducedRankHansenResidualizedNormalizedEigenblocks_exist_of_yGram_posDef`.

It constructs normalized generalized-eigenvector blocks for both residualized
pencils from full column rank of `[X,Z]`, `[Y,Z]`, and `Z`. This compatibility
surface does not return the available max certificates and still does not
construct a simultaneous cross-orthogonal Hansen pair. -/
theorem reducedRankHansenResidualizedNormalizedEigenblocks_exist_of_full_grams
    (Z : Matrix n ell ℝ) (X : Matrix n k ℝ) (Y : Matrix n m ℝ)
    [DecidableEq k]
    [Invertible (Zᵀ * Z)]
    [Invertible ((Matrix.fromCols X Z)ᵀ * Matrix.fromCols X Z)]
    [Invertible ((Matrix.fromCols Y Z)ᵀ * Matrix.fromCols Y Z)]
    (hrk : Fintype.card r ≤ Fintype.card k)
    (hsm : Fintype.card s ≤ Fintype.card m) :
    (∃ (G : Matrix k r ℝ) (lambda : r → ℝ),
      reducedRankHansenGEigenvectors
          (reducedRankTildeX Z X) (reducedRankTildeY Z Y) lambda G ∧
        reducedRankGNormalized (reducedRankTildeX Z X) G) ∧
      ∃ (Aperp : Matrix m s ℝ) (eta : s → ℝ),
        reducedRankHansenAperpEigenvectors
            (reducedRankTildeE X Z Y) (reducedRankTildeY Z Y) eta Aperp ∧
          reducedRankAperpNormalized (reducedRankTildeY Z Y) Aperp :=
  reducedRankHansenResidualizedNormalizedEigenblocks_exist_of_yGram_posDef
    (r := r) (s := s) Z X Y (reducedRankTildeY_gram_posDef Z Y) hrk hsm

end ObjectiveExistence

section SpectralDualityCertificate

variable [Fintype r] [DecidableEq r] [Fintype s] [DecidableEq s]

/-- Compatibility certificate for the isolated smallest-root sentence in the
final summary of Hansen Theorem 11.7, stated at the spectral level.

The G side supplies a selected compressed-determinant maximum for the residualized
G pencil. The `A⊥` side supplies the dual selected compressed-determinant
minimum for the residual pencil. That minimum conflicts with equation (11.21)
and its derivation, so this certificate is not an MLE-complement certificate.
It remains available only to preserve the literal smallest-root summary and
the algebraic singular-boundary constructions built on it. -/
structure ReducedRankHansenDetProductMinMaxCertificate
    (Xtilde : Matrix n k ℝ) (Ytilde Etilde : Matrix n m ℝ)
    (G : Matrix k r ℝ) (lambda : r → ℝ)
    (Aperp : Matrix m s ℝ) (eta : s → ℝ) : Prop where
  g_max :
    GeneralizedEigenDetProductMaxCertificate
      (reducedRankGPencilA Xtilde Ytilde) (reducedRankGPencilB Xtilde) G lambda
  aperp_min :
    GeneralizedEigenDetProductMinCertificate
      (reducedRankAperpPencilA Etilde) (reducedRankAperpPencilB Ytilde) Aperp eta

/-- Canonical maximizer-oriented spectral input for Hansen Theorem 11.7.

Both selected blocks maximize their direct determinant objectives. In
particular, the `A⊥` field is the selected compressed-determinant maximum for
the residual pencil in equation (11.21), hence represents the largest
residual-pencil roots rather than the inconsistent smallest-root summary. -/
structure ReducedRankHansenDetProductMaxMaxCertificate
    (Xtilde : Matrix n k ℝ) (Ytilde Etilde : Matrix n m ℝ)
    (G : Matrix k r ℝ) (lambda : r → ℝ)
    (Aperp : Matrix m s ℝ) (eta : s → ℝ) : Prop where
  g_max :
    GeneralizedEigenDetProductMaxCertificate
      (reducedRankGPencilA Xtilde Ytilde) (reducedRankGPencilB Xtilde) G lambda
  aperp_max :
    GeneralizedEigenDetProductMaxCertificate
      (reducedRankAperpPencilA Etilde) (reducedRankAperpPencilB Ytilde) Aperp eta

omit [DecidableEq n] in
/-- Positive-definite residualized design and outcome Grams construct both
global determinant-max blocks in Hansen's canonical max/max spectral
certificate.

No objective maximizer or spectral witness is assumed: both are supplied by
the positive-semidefinite/positive-definite generalized-pencil theorem. This
projected certificate does not retain either block's ordered-root formula. -/
theorem ReducedRankHansenDetProductMaxMaxCertificate.exists_of_gram_posDef
    (Xtilde : Matrix n k ℝ) (Ytilde Etilde : Matrix n m ℝ)
    (hXGram : (Xtildeᵀ * Xtilde).PosDef)
    (hYGram : (Ytildeᵀ * Ytilde).PosDef)
    (hrk : Fintype.card r ≤ Fintype.card k)
    (hsm : Fintype.card s ≤ Fintype.card m) :
    ∃ (G : Matrix k r ℝ) (lambda : r → ℝ)
        (Aperp : Matrix m s ℝ) (eta : s → ℝ),
      ReducedRankHansenDetProductMaxMaxCertificate
        Xtilde Ytilde Etilde G lambda Aperp eta := by
  obtain ⟨G, lambda, hG⟩ :=
    reducedRankGDetProductMaxCertificate_exists_of_gram_posDef
      (r := r) Xtilde Ytilde hXGram hrk
  obtain ⟨Aperp, eta, hAperp⟩ :=
    reducedRankAperpDetProductMaxCertificate_exists_of_gram_posDef
      (s := s) Etilde Ytilde hYGram hsm
  exact ⟨G, lambda, Aperp, eta, ⟨hG, hAperp⟩⟩

/-- Full-Gram specialization constructing Hansen's canonical max/max spectral
certificate for the actual residualized sample matrices. -/
theorem ReducedRankHansenDetProductMaxMaxCertificate.exists_residualized_of_full_grams
    (Z : Matrix n ell ℝ) (X : Matrix n k ℝ) (Y : Matrix n m ℝ)
    [DecidableEq k]
    [Invertible (Zᵀ * Z)]
    [Invertible ((Matrix.fromCols X Z)ᵀ * Matrix.fromCols X Z)]
    [Invertible ((Matrix.fromCols Y Z)ᵀ * Matrix.fromCols Y Z)]
    (hrk : Fintype.card r ≤ Fintype.card k)
    (hsm : Fintype.card s ≤ Fintype.card m) :
    ∃ (G : Matrix k r ℝ) (lambda : r → ℝ)
        (Aperp : Matrix m s ℝ) (eta : s → ℝ),
      ReducedRankHansenDetProductMaxMaxCertificate
        (reducedRankTildeX Z X) (reducedRankTildeY Z Y)
        (reducedRankTildeE X Z Y) G lambda Aperp eta :=
  ReducedRankHansenDetProductMaxMaxCertificate.exists_of_gram_posDef
    (reducedRankTildeX Z X) (reducedRankTildeY Z Y)
    (reducedRankTildeE X Z Y)
    (reducedRankTildeX_gram_posDef Z X)
    (reducedRankTildeY_gram_posDef Z Y) hrk hsm

omit [DecidableEq n] in
/-- Build the canonical max/max spectral certificate from the two direct
determinant-objective maximizers. -/
theorem ReducedRankHansenDetProductMaxMaxCertificate.of_objective_maximizers
    (Xtilde : Matrix n k ℝ) (Ytilde Etilde : Matrix n m ℝ)
    (G : Matrix k r ℝ) (lambda : r → ℝ)
    (Aperp : Matrix m s ℝ) (eta : s → ℝ)
    (hG : reducedRankHansenGEigenvectors Xtilde Ytilde lambda G)
    (hGOpt : reducedRankConcentratedObjectiveMaximizer Xtilde Ytilde G)
    (hAperp : reducedRankHansenAperpEigenvectors Etilde Ytilde eta Aperp)
    (hAperpOpt : reducedRankAperpObjectiveMaximizer Etilde Ytilde Aperp) :
    ReducedRankHansenDetProductMaxMaxCertificate
      Xtilde Ytilde Etilde G lambda Aperp eta where
  g_max :=
    GeneralizedEigenDetProductMaxCertificate.of_detObjectiveMaximizer
      (reducedRankGPencilA Xtilde Ytilde) (reducedRankGPencilB Xtilde)
      G lambda hG hGOpt
  aperp_max :=
    GeneralizedEigenDetProductMaxCertificate.of_detObjectiveMaximizer
      (reducedRankAperpPencilA Etilde) (reducedRankAperpPencilB Ytilde)
      Aperp eta hAperp hAperpOpt

omit [DecidableEq n] in
/-- Build the canonical max/max spectral certificate from selected compressed-
determinant maxima for the two Hansen pencils. -/
theorem
    ReducedRankHansenDetProductMaxMaxCertificate.of_selected_compressedDet_maxima
    (Xtilde : Matrix n k ℝ) (Ytilde Etilde : Matrix n m ℝ)
    (G : Matrix k r ℝ) (lambda : r → ℝ)
    (Aperp : Matrix m s ℝ) (eta : s → ℝ)
    (hG : reducedRankHansenGEigenvectors Xtilde Ytilde lambda G)
    (hGNorm : reducedRankGNormalized Xtilde G)
    (hGMax : generalizedEigenSelectedCompressedDetMaximal
      (reducedRankGPencilA Xtilde Ytilde) (reducedRankGPencilB Xtilde) G)
    (hAperp : reducedRankHansenAperpEigenvectors Etilde Ytilde eta Aperp)
    (hAperpNorm : reducedRankAperpNormalized Ytilde Aperp)
    (hAperpMax : generalizedEigenSelectedCompressedDetMaximal
      (reducedRankAperpPencilA Etilde) (reducedRankAperpPencilB Ytilde) Aperp) :
    ReducedRankHansenDetProductMaxMaxCertificate
      Xtilde Ytilde Etilde G lambda Aperp eta where
  g_max := ⟨hG, hGNorm, hGMax⟩
  aperp_max := ⟨hAperp, hAperpNorm, hAperpMax⟩

omit [DecidableEq n] in
/-- The G-side objective maximizer extracted from the canonical max/max
certificate. -/
theorem ReducedRankHansenDetProductMaxMaxCertificate.g_objectiveMaximizer
    {Xtilde : Matrix n k ℝ} {Ytilde Etilde : Matrix n m ℝ}
    {G : Matrix k r ℝ} {lambda : r → ℝ}
    {Aperp : Matrix m s ℝ} {eta : s → ℝ}
    (h : ReducedRankHansenDetProductMaxMaxCertificate
      Xtilde Ytilde Etilde G lambda Aperp eta) :
    reducedRankConcentratedObjectiveMaximizer Xtilde Ytilde G := by
  change generalizedEigenDetObjectiveMaximizer
    (reducedRankGPencilA Xtilde Ytilde) (reducedRankGPencilB Xtilde) G
  exact h.g_max.detObjectiveMaximizer

omit [DecidableEq n] in
/-- The equation (11.21) `A⊥` objective maximizer extracted from the canonical
max/max certificate. -/
theorem ReducedRankHansenDetProductMaxMaxCertificate.aperp_objectiveMaximizer
    {Xtilde : Matrix n k ℝ} {Ytilde Etilde : Matrix n m ℝ}
    {G : Matrix k r ℝ} {lambda : r → ℝ}
    {Aperp : Matrix m s ℝ} {eta : s → ℝ}
    (h : ReducedRankHansenDetProductMaxMaxCertificate
      Xtilde Ytilde Etilde G lambda Aperp eta) :
    reducedRankAperpObjectiveMaximizer Etilde Ytilde Aperp :=
  reducedRankAperpObjectiveMaximizer_of_generalized_detObjectiveMaximizer
    Etilde Ytilde Aperp h.aperp_max.detObjectiveMaximizer

/-- Canonical identified spectral certificate for Hansen Theorem 11.7.

It combines the two direct objective maxima with Hansen's identifying
orthogonality `A⊥'Ỹ'X̃G = 0` (equivalently `A⊥' Ahat = 0` under the normalized
coefficient formula). -/
structure ReducedRankHansenIdentifiedSpectralMaximizerCertificate
    (Xtilde : Matrix n k ℝ) (Ytilde Etilde : Matrix n m ℝ)
    (G : Matrix k r ℝ) (lambda : r → ℝ)
    (Aperp : Matrix m s ℝ) (eta : s → ℝ) : Prop where
  spectral_maximizers :
    ReducedRankHansenDetProductMaxMaxCertificate
      Xtilde Ytilde Etilde G lambda Aperp eta
  aperp_cross_orthogonal : reducedRankAperpCrossOrthogonal Xtilde Ytilde G Aperp

omit [DecidableEq n] in
/-- Build the canonical identified spectral certificate directly from the two
objective maxima and cross orthogonality. -/
theorem
    ReducedRankHansenIdentifiedSpectralMaximizerCertificate.of_objective_maximizers_and_cross
    (Xtilde : Matrix n k ℝ) (Ytilde Etilde : Matrix n m ℝ)
    (G : Matrix k r ℝ) (lambda : r → ℝ)
    (Aperp : Matrix m s ℝ) (eta : s → ℝ)
    (hG : reducedRankHansenGEigenvectors Xtilde Ytilde lambda G)
    (hGOpt : reducedRankConcentratedObjectiveMaximizer Xtilde Ytilde G)
    (hAperp : reducedRankHansenAperpEigenvectors Etilde Ytilde eta Aperp)
    (hAperpOpt : reducedRankAperpObjectiveMaximizer Etilde Ytilde Aperp)
    (hCross : reducedRankAperpCrossOrthogonal Xtilde Ytilde G Aperp) :
    ReducedRankHansenIdentifiedSpectralMaximizerCertificate
      Xtilde Ytilde Etilde G lambda Aperp eta where
  spectral_maximizers :=
    ReducedRankHansenDetProductMaxMaxCertificate.of_objective_maximizers
      Xtilde Ytilde Etilde G lambda Aperp eta hG hGOpt hAperp hAperpOpt
  aperp_cross_orthogonal := hCross

omit [DecidableEq n] in
/-- Add cross orthogonality to an existing max/max spectral certificate. -/
theorem
    ReducedRankHansenIdentifiedSpectralMaximizerCertificate.of_maxMax_and_cross
    {Xtilde : Matrix n k ℝ} {Ytilde Etilde : Matrix n m ℝ}
    {G : Matrix k r ℝ} {lambda : r → ℝ}
    {Aperp : Matrix m s ℝ} {eta : s → ℝ}
    (hMax : ReducedRankHansenDetProductMaxMaxCertificate
      Xtilde Ytilde Etilde G lambda Aperp eta)
    (hCross : reducedRankAperpCrossOrthogonal Xtilde Ytilde G Aperp) :
    ReducedRankHansenIdentifiedSpectralMaximizerCertificate
      Xtilde Ytilde Etilde G lambda Aperp eta :=
  ⟨hMax, hCross⟩

/-- Raw ordered max/min surface for Hansen's inconsistent smallest-root
summary compatibility.

The primitive spectral inputs are the selected generalized-eigenvector equations,
Hansen normalizations, and the two literal ordered product inequalities for the
G and `A⊥` pencils. The `A⊥` lower bound is not equation (11.21) and is not an
MLE-complement condition. -/
structure ReducedRankHansenOrderedGeneralizedEigenMinMaxCertificate
    (Xtilde : Matrix n k ℝ) (Ytilde Etilde : Matrix n m ℝ)
    (G : Matrix k r ℝ) (lambda : r → ℝ)
    (Aperp : Matrix m s ℝ) (eta : s → ℝ) : Prop where
  g_ordered :
    GeneralizedEigenOrderedProductMaxCertificate
      (reducedRankGPencilA Xtilde Ytilde) (reducedRankGPencilB Xtilde) G lambda
  aperp_ordered :
    GeneralizedEigenOrderedProductMinCertificate
      (reducedRankAperpPencilA Etilde) (reducedRankAperpPencilB Ytilde) Aperp eta

/-- Ordinary PSD leading/trailing determinant-extrema surface for Hansen
Theorem 11.7 after whitening.

This is the precise remaining spectral primitive for the multi-column case.
The G side is the leading-eigenspace maximum for the positive semidefinite
ordinary matrix `Ỹ(Ỹ'Ỹ)⁻¹Ỹ'`. The `A⊥` side first factors
`Ẽ = R Ỹ`, then asks for the trailing-eigenspace minimum for the positive
semidefinite ordinary matrix `R'R`. These are ordinary identity-denominator
determinant statements; the constructors below transport them to Hansen's two
generalized pencils. -/
structure ReducedRankHansenWhitenedPSDLeadingTrailingCertificate
    (Ytilde Etilde : Matrix n m ℝ)
    (lambda : r → ℝ) (eta : s → ℝ)
    (R : Matrix n n ℝ) (G0 : Matrix n r ℝ) (A0 : Matrix n s ℝ) : Prop where
  g_eigenvectors :
    generalizedEigenvectorColumns
      (reducedRankGWhitenedProjection Ytilde) (1 : Matrix n n ℝ) lambda G0
  g_orthonormal : G0ᵀ * G0 = 1
  g_leading_compressedDet_maximal :
    ∀ H : Matrix n r ℝ, Hᵀ * H = 1 →
      (Hᵀ * reducedRankGWhitenedProjection Ytilde * H).det ≤
        (G0ᵀ * reducedRankGWhitenedProjection Ytilde * G0).det
  aperp_residual_factor : Etilde = R * Ytilde
  aperp_eigenvectors :
    generalizedEigenvectorColumns
      (reducedRankAperpResidualWhitenedMatrix R) (1 : Matrix n n ℝ) eta A0
  aperp_orthonormal : A0ᵀ * A0 = 1
  aperp_trailing_compressedDet_minimal :
    ∀ H : Matrix n s ℝ, Hᵀ * H = 1 →
      (A0ᵀ * reducedRankAperpResidualWhitenedMatrix R * A0).det ≤
        (Hᵀ * reducedRankAperpResidualWhitenedMatrix R * H).det

namespace ReducedRankHansenWhitenedPSDLeadingTrailingCertificate

/-- The G-side ordinary whitened matrix in the leading/trailing certificate is
positive semidefinite. -/
theorem g_posSemidef
    {Ytilde Etilde : Matrix n m ℝ}
    {lambda : r → ℝ} {eta : s → ℝ}
    {R : Matrix n n ℝ} {G0 : Matrix n r ℝ} {A0 : Matrix n s ℝ}
    (_h : ReducedRankHansenWhitenedPSDLeadingTrailingCertificate
      Ytilde Etilde lambda eta R G0 A0) :
    (reducedRankGWhitenedProjection Ytilde).PosSemidef :=
  reducedRankGWhitenedProjection_posSemidef Ytilde

/-- The `A⊥` ordinary whitened matrix in the leading/trailing certificate is
positive semidefinite. -/
theorem aperp_posSemidef
    {Ytilde Etilde : Matrix n m ℝ}
    {lambda : r → ℝ} {eta : s → ℝ}
    {R : Matrix n n ℝ} {G0 : Matrix n r ℝ} {A0 : Matrix n s ℝ}
    (_h : ReducedRankHansenWhitenedPSDLeadingTrailingCertificate
      Ytilde Etilde lambda eta R G0 A0) :
    (reducedRankAperpResidualWhitenedMatrix R).PosSemidef :=
  reducedRankAperpResidualWhitenedMatrix_posSemidef R

/-- The leading ordinary PSD determinant-extremum gives the identity-
denominator G-side product bound. -/
theorem g_identity_productUpperBound
    {Ytilde Etilde : Matrix n m ℝ}
    {lambda : r → ℝ} {eta : s → ℝ}
    {R : Matrix n n ℝ} {G0 : Matrix n r ℝ} {A0 : Matrix n s ℝ}
    (h : ReducedRankHansenWhitenedPSDLeadingTrailingCertificate
      Ytilde Etilde lambda eta R G0 A0) :
    generalizedEigenDetProductUpperBound
      (reducedRankGWhitenedProjection Ytilde) (1 : Matrix n n ℝ) lambda :=
  generalizedEigenDetProductUpperBound_identity_of_selected_compressedDet_maximal
    (reducedRankGWhitenedProjection Ytilde) lambda G0
    h.g_eigenvectors h.g_orthonormal h.g_leading_compressedDet_maximal

/-- The trailing ordinary PSD determinant-extremum gives the identity-
denominator `A⊥` product lower bound. -/
theorem aperp_identity_productLowerBound
    {Ytilde Etilde : Matrix n m ℝ}
    {lambda : r → ℝ} {eta : s → ℝ}
    {R : Matrix n n ℝ} {G0 : Matrix n r ℝ} {A0 : Matrix n s ℝ}
    (h : ReducedRankHansenWhitenedPSDLeadingTrailingCertificate
      Ytilde Etilde lambda eta R G0 A0) :
    generalizedEigenDetProductLowerBound
      (reducedRankAperpResidualWhitenedMatrix R) (1 : Matrix n n ℝ) eta :=
  generalizedEigenDetProductLowerBound_identity_of_selected_compressedDet_minimal
    (reducedRankAperpResidualWhitenedMatrix R) eta A0
    h.aperp_eigenvectors h.aperp_orthonormal h.aperp_trailing_compressedDet_minimal

/-- Transport the leading ordinary PSD G-side determinant theorem to Hansen's
residualized generalized G pencil. -/
theorem g_detVariationalBound
    {Ytilde Etilde : Matrix n m ℝ}
    {lambda : r → ℝ} {eta : s → ℝ}
    {R : Matrix n n ℝ} {G0 : Matrix n r ℝ} {A0 : Matrix n s ℝ}
    (h : ReducedRankHansenWhitenedPSDLeadingTrailingCertificate
      Ytilde Etilde lambda eta R G0 A0)
    (Xtilde : Matrix n k ℝ) :
    reducedRankGDetVariationalBound Xtilde Ytilde lambda := by
  have hBound :
      generalizedEigenDetProductUpperBound
        (Ytilde * (Ytildeᵀ * Ytilde)⁻¹ * Ytildeᵀ)
        (1 : Matrix n n ℝ) lambda := by
    simpa [reducedRankGWhitenedProjection] using h.g_identity_productUpperBound
  exact reducedRankGDetVariationalBound_of_canonical_whitened_identity_productUpperBound
    Xtilde Ytilde lambda hBound

/-- Transport the trailing ordinary PSD `A⊥` determinant theorem through the
residual-factor identity `Ẽ = RỸ`. -/
theorem aperp_detVariationalBound
    {Ytilde Etilde : Matrix n m ℝ}
    {lambda : r → ℝ} {eta : s → ℝ}
    {R : Matrix n n ℝ} {G0 : Matrix n r ℝ} {A0 : Matrix n s ℝ}
    (h : ReducedRankHansenWhitenedPSDLeadingTrailingCertificate
      Ytilde Etilde lambda eta R G0 A0) :
    reducedRankAperpDetVariationalBound Etilde Ytilde eta :=
  reducedRankAperpDetVariationalBound_of_residual_factor_identity_productLowerBound
    Etilde Ytilde R (reducedRankAperpResidualWhitenedMatrix R) eta
    h.aperp_residual_factor rfl h.aperp_identity_productLowerBound

/-- Build the faithful whitened PSD leading/trailing certificate for the
actual residualized Hansen matrices.

The residual-factor field is discharged by
`reducedRankTildeE_eq_residualFactor_mul_tildeY`, so callers only supply the
ordinary identity-denominator leading/trailing eigenspace data. -/
theorem of_residualized
    (Z : Matrix n ell ℝ) (X : Matrix n k ℝ) (Y : Matrix n m ℝ)
    (lambda : r → ℝ) (eta : s → ℝ)
    (G0 : Matrix n r ℝ) (A0 : Matrix n s ℝ)
    [DecidableEq k] [Invertible (Zᵀ * Z)]
    [Invertible ((Matrix.fromCols X Z)ᵀ * Matrix.fromCols X Z)]
    (hG0 : generalizedEigenvectorColumns
      (reducedRankGWhitenedProjection (reducedRankTildeY Z Y))
      (1 : Matrix n n ℝ) lambda G0)
    (hG0Norm : G0ᵀ * G0 = 1)
    (hG0Max : ∀ H : Matrix n r ℝ, Hᵀ * H = 1 →
      (Hᵀ * reducedRankGWhitenedProjection (reducedRankTildeY Z Y) * H).det ≤
        (G0ᵀ * reducedRankGWhitenedProjection (reducedRankTildeY Z Y) * G0).det)
    (hA0 : generalizedEigenvectorColumns
      (reducedRankAperpResidualWhitenedMatrix (reducedRankAperpResidualFactor X Z))
      (1 : Matrix n n ℝ) eta A0)
    (hA0Norm : A0ᵀ * A0 = 1)
    (hA0Min : ∀ H : Matrix n s ℝ, Hᵀ * H = 1 →
      (A0ᵀ * reducedRankAperpResidualWhitenedMatrix
          (reducedRankAperpResidualFactor X Z) * A0).det ≤
        (Hᵀ * reducedRankAperpResidualWhitenedMatrix
          (reducedRankAperpResidualFactor X Z) * H).det) :
    ReducedRankHansenWhitenedPSDLeadingTrailingCertificate
      (reducedRankTildeY Z Y) (reducedRankTildeE X Z Y) lambda eta
      (reducedRankAperpResidualFactor X Z) G0 A0 where
  g_eigenvectors := hG0
  g_orthonormal := hG0Norm
  g_leading_compressedDet_maximal := hG0Max
  aperp_residual_factor := reducedRankTildeE_eq_residualFactor_mul_tildeY Z X Y
  aperp_eigenvectors := hA0
  aperp_orthonormal := hA0Norm
  aperp_trailing_compressedDet_minimal := hA0Min

/-- Build the residualized whitened PSD leading/trailing certificate from the
projection-specific partial determinant theorem.

On the G side, the usual nonsingularity of `Ỹ'Ỹ` identifies
`Ỹ(Ỹ'Ỹ)⁻¹Ỹ'` with the Chapter 3 orthogonal projection, so a normalized block
with displayed roots all equal to `1` is determinant-maximal among partial
orthonormal blocks. On the `A⊥` side, positive semidefiniteness of the concrete
residual-factor matrix `R'R` makes a selected zero-product block
determinant-minimal. This is still a partial-block theorem for Hansen's
whitened projection surface, not the general exterior-power PSD min-max theorem. -/
theorem of_residualized_projection_top_zero
    (Z : Matrix n ell ℝ) (X : Matrix n k ℝ) (Y : Matrix n m ℝ)
    (lambda : r → ℝ) (eta : s → ℝ)
    (G0 : Matrix n r ℝ) (A0 : Matrix n s ℝ)
    [DecidableEq k] [Invertible (Zᵀ * Z)]
    [Invertible ((Matrix.fromCols X Z)ᵀ * Matrix.fromCols X Z)]
    [Invertible ((reducedRankTildeY Z Y)ᵀ * reducedRankTildeY Z Y)]
    (hG0 : generalizedEigenvectorColumns
      (reducedRankGWhitenedProjection (reducedRankTildeY Z Y))
      (1 : Matrix n n ℝ) lambda G0)
    (hG0Norm : G0ᵀ * G0 = 1)
    (hG0Top : ∀ j : r, lambda j = 1)
    (hA0 : generalizedEigenvectorColumns
      (reducedRankAperpResidualWhitenedMatrix (reducedRankAperpResidualFactor X Z))
      (1 : Matrix n n ℝ) eta A0)
    (hA0Norm : A0ᵀ * A0 = 1)
    (hA0ZeroProduct : (∏ j, eta j) = 0) :
    ReducedRankHansenWhitenedPSDLeadingTrailingCertificate
      (reducedRankTildeY Z Y) (reducedRankTildeE X Z Y) lambda eta
      (reducedRankAperpResidualFactor X Z) G0 A0 := by
  refine of_residualized Z X Y lambda eta G0 A0 hG0 hG0Norm ?_ hA0 hA0Norm ?_
  · have hG0Max :
        generalizedEigenSelectedCompressedDetMaximal
          (reducedRankGWhitenedProjection (reducedRankTildeY Z Y))
          (1 : Matrix n n ℝ) G0 :=
      generalizedEigenSelectedCompressedDetMaximal_identity_of_projection_top
        (reducedRankGWhitenedProjection (reducedRankTildeY Z Y)) lambda G0
        (reducedRankGWhitenedProjection_transpose (reducedRankTildeY Z Y))
        (reducedRankGWhitenedProjection_idempotent (reducedRankTildeY Z Y))
        hG0 hG0Norm hG0Top
    intro H hHNorm
    have hHNorm' :
        generalizedEigenvectorBNormalized (1 : Matrix n n ℝ) H := by
      simpa [generalizedEigenvectorBNormalized, Matrix.mul_assoc] using hHNorm
    exact hG0Max H hHNorm'
  · have hA0Min :
        generalizedEigenSelectedCompressedDetMinimal
          (reducedRankAperpResidualWhitenedMatrix (reducedRankAperpResidualFactor X Z))
          (1 : Matrix n n ℝ) A0 :=
      generalizedEigenSelectedCompressedDetMinimal_identity_of_posSemidef_zero
        (reducedRankAperpResidualWhitenedMatrix (reducedRankAperpResidualFactor X Z))
        eta A0
        (reducedRankAperpResidualWhitenedMatrix_posSemidef (reducedRankAperpResidualFactor X Z))
        hA0 hA0Norm hA0ZeroProduct
    intro H hHNorm
    have hHNorm' :
        generalizedEigenvectorBNormalized (1 : Matrix n n ℝ) H := by
      simpa [generalizedEigenvectorBNormalized, Matrix.mul_assoc] using hHNorm
    exact hA0Min H hHNorm'

/-- Residualized projection constructor with the top-root condition derived
from the range identity `P G₀ = G₀`.

This is the tighter Hansen-facing version of
`of_residualized_projection_top_zero`: the projection-side selected roots equal
one because the whitened selected block lies in the projection range. -/
theorem of_residualized_projection_range_zero
    (Z : Matrix n ell ℝ) (X : Matrix n k ℝ) (Y : Matrix n m ℝ)
    (lambda : r → ℝ) (eta : s → ℝ)
    (G0 : Matrix n r ℝ) (A0 : Matrix n s ℝ)
    [DecidableEq k] [Invertible (Zᵀ * Z)]
    [Invertible ((Matrix.fromCols X Z)ᵀ * Matrix.fromCols X Z)]
    [Invertible ((reducedRankTildeY Z Y)ᵀ * reducedRankTildeY Z Y)]
    (hG0 : generalizedEigenvectorColumns
      (reducedRankGWhitenedProjection (reducedRankTildeY Z Y))
      (1 : Matrix n n ℝ) lambda G0)
    (hG0Norm : G0ᵀ * G0 = 1)
    (hG0Range :
      reducedRankGWhitenedProjection (reducedRankTildeY Z Y) * G0 = G0)
    (hA0 : generalizedEigenvectorColumns
      (reducedRankAperpResidualWhitenedMatrix (reducedRankAperpResidualFactor X Z))
      (1 : Matrix n n ℝ) eta A0)
    (hA0Norm : A0ᵀ * A0 = 1)
    (hA0ZeroProduct : (∏ j, eta j) = 0) :
    ReducedRankHansenWhitenedPSDLeadingTrailingCertificate
      (reducedRankTildeY Z Y) (reducedRankTildeE X Z Y) lambda eta
      (reducedRankAperpResidualFactor X Z) G0 A0 :=
  of_residualized_projection_top_zero Z X Y lambda eta G0 A0
    hG0 hG0Norm
    (generalizedEigenProjection_top_roots_of_range
      (reducedRankGWhitenedProjection (reducedRankTildeY Z Y))
      lambda G0 hG0 hG0Norm hG0Range)
    hA0 hA0Norm hA0ZeroProduct

/-- Residualized projection constructor with the `A⊥` zero-product condition
derived from the nullspace identity for the residual whitened matrix.

This tightens `of_residualized_projection_range_zero` on the trailing side:
callers provide `R'R A₀ = 0`, which is the deterministic nullspace condition
produced by a residualized spectral construction, and the selected-root product
is derived internally. -/
theorem of_residualized_projection_range_null
    (Z : Matrix n ell ℝ) (X : Matrix n k ℝ) (Y : Matrix n m ℝ)
    (lambda : r → ℝ) (eta : s → ℝ)
    (G0 : Matrix n r ℝ) (A0 : Matrix n s ℝ)
    [Nonempty s]
    [DecidableEq k] [Invertible (Zᵀ * Z)]
    [Invertible ((Matrix.fromCols X Z)ᵀ * Matrix.fromCols X Z)]
    [Invertible ((reducedRankTildeY Z Y)ᵀ * reducedRankTildeY Z Y)]
    (hG0 : generalizedEigenvectorColumns
      (reducedRankGWhitenedProjection (reducedRankTildeY Z Y))
      (1 : Matrix n n ℝ) lambda G0)
    (hG0Norm : G0ᵀ * G0 = 1)
    (hG0Range :
      reducedRankGWhitenedProjection (reducedRankTildeY Z Y) * G0 = G0)
    (hA0 : generalizedEigenvectorColumns
      (reducedRankAperpResidualWhitenedMatrix (reducedRankAperpResidualFactor X Z))
      (1 : Matrix n n ℝ) eta A0)
    (hA0Norm : A0ᵀ * A0 = 1)
    (hA0Null :
      reducedRankAperpResidualWhitenedMatrix (reducedRankAperpResidualFactor X Z) *
        A0 = 0) :
    ReducedRankHansenWhitenedPSDLeadingTrailingCertificate
      (reducedRankTildeY Z Y) (reducedRankTildeE X Z Y) lambda eta
      (reducedRankAperpResidualFactor X Z) G0 A0 :=
  of_residualized_projection_range_zero Z X Y lambda eta G0 A0
    hG0 hG0Norm hG0Range hA0 hA0Norm
    (generalizedEigenNull_rootProduct_eq_zero
      (reducedRankAperpResidualWhitenedMatrix (reducedRankAperpResidualFactor X Z))
      eta A0 hA0 hA0Norm hA0Null)

/-- Residualized projection constructor from ordinary fixed-root eigenvector
packages.

This route is between `of_residualized_projection_range_null` and
`of_residualized_projection_span_residual_null`: callers supply ordinary
identity-denominator eigenvector blocks with displayed roots `1` and `0`, and
the projection-range and residual-nullspace equations are derived internally. -/
theorem of_residualized_projection_fixed_roots
    (Z : Matrix n ell ℝ) (X : Matrix n k ℝ) (Y : Matrix n m ℝ)
    (G0 : Matrix n r ℝ) (A0 : Matrix n s ℝ)
    [Nonempty s]
    [DecidableEq k] [Invertible (Zᵀ * Z)]
    [Invertible ((Matrix.fromCols X Z)ᵀ * Matrix.fromCols X Z)]
    [Invertible ((reducedRankTildeY Z Y)ᵀ * reducedRankTildeY Z Y)]
    (hG0 : generalizedEigenvectorColumns
      (reducedRankGWhitenedProjection (reducedRankTildeY Z Y))
      (1 : Matrix n n ℝ) (fun _ : r => (1 : ℝ)) G0)
    (hG0Norm : G0ᵀ * G0 = 1)
    (hA0 : generalizedEigenvectorColumns
      (reducedRankAperpResidualWhitenedMatrix (reducedRankAperpResidualFactor X Z))
      (1 : Matrix n n ℝ) (fun _ : s => (0 : ℝ)) A0)
    (hA0Norm : A0ᵀ * A0 = 1) :
    ReducedRankHansenWhitenedPSDLeadingTrailingCertificate
      (reducedRankTildeY Z Y) (reducedRankTildeE X Z Y)
      (fun _ : r => (1 : ℝ)) (fun _ : s => (0 : ℝ))
      (reducedRankAperpResidualFactor X Z) G0 A0 :=
  of_residualized_projection_range_null Z X Y
    (fun _ : r => (1 : ℝ)) (fun _ : s => (0 : ℝ)) G0 A0
    hG0 hG0Norm
    (generalizedEigenvectorColumns_range_of_one
      (reducedRankGWhitenedProjection (reducedRankTildeY Z Y)) G0 hG0)
    hA0 hA0Norm
    (generalizedEigenvectorColumns_null_of_zero
      (reducedRankAperpResidualWhitenedMatrix (reducedRankAperpResidualFactor X Z))
      A0 hA0)

/-- Residualized projection constructor from ordinary span and residual
nullspace witnesses.

This is the closest ordinary-matrix surface for the current Hansen 11.7
projection route. A selected block written as `G₀ = Ỹ C` is fixed by the
whitened projection, and a selected residual block with `R A₀ = 0` is killed by
`R'R`. The ordinary generalized-eigenvector packages with displayed roots
`1` and `0` are derived internally. -/
theorem of_residualized_projection_span_residual_null
    (Z : Matrix n ell ℝ) (X : Matrix n k ℝ) (Y : Matrix n m ℝ)
    (G0 : Matrix n r ℝ) (A0 : Matrix n s ℝ) (C : Matrix m r ℝ)
    [Nonempty s]
    [DecidableEq k] [Invertible (Zᵀ * Z)]
    [Invertible ((Matrix.fromCols X Z)ᵀ * Matrix.fromCols X Z)]
    [Invertible ((reducedRankTildeY Z Y)ᵀ * reducedRankTildeY Z Y)]
    (hG0Span : G0 = reducedRankTildeY Z Y * C)
    (hG0Norm : G0ᵀ * G0 = 1)
    (hA0Norm : A0ᵀ * A0 = 1)
    (hA0ResidualNull : reducedRankAperpResidualFactor X Z * A0 = 0) :
    ReducedRankHansenWhitenedPSDLeadingTrailingCertificate
      (reducedRankTildeY Z Y) (reducedRankTildeE X Z Y)
      (fun _ : r => (1 : ℝ)) (fun _ : s => (0 : ℝ))
      (reducedRankAperpResidualFactor X Z) G0 A0 := by
  have hG0Range :
      reducedRankGWhitenedProjection (reducedRankTildeY Z Y) * G0 = G0 := by
    calc
      reducedRankGWhitenedProjection (reducedRankTildeY Z Y) * G0 =
          reducedRankGWhitenedProjection (reducedRankTildeY Z Y) *
            (reducedRankTildeY Z Y * C) := by
            rw [hG0Span]
      _ = reducedRankTildeY Z Y * C :=
            reducedRankGWhitenedProjection_mul_range (reducedRankTildeY Z Y) C
      _ = G0 := hG0Span.symm
  have hA0Null :
      reducedRankAperpResidualWhitenedMatrix (reducedRankAperpResidualFactor X Z) *
        A0 = 0 :=
    reducedRankAperpResidualWhitenedMatrix_mul_eq_zero_of_factor_null
      (reducedRankAperpResidualFactor X Z) A0 hA0ResidualNull
  exact of_residualized_projection_range_null Z X Y
    (fun _ : r => (1 : ℝ)) (fun _ : s => (0 : ℝ)) G0 A0
    (generalizedEigenvectorColumns_one_of_range
      (reducedRankGWhitenedProjection (reducedRankTildeY Z Y)) G0 hG0Norm hG0Range)
    hG0Norm hG0Range
    (generalizedEigenvectorColumns_zero_of_null
      (reducedRankAperpResidualWhitenedMatrix (reducedRankAperpResidualFactor X Z))
      A0 hA0Norm hA0Null)
    hA0Norm hA0Null

end ReducedRankHansenWhitenedPSDLeadingTrailingCertificate

omit [DecidableEq n] in
/-- Build the raw Hansen ordered min-max surface from generic product bounds
for the two generalized pencils. -/
theorem ReducedRankHansenOrderedGeneralizedEigenMinMaxCertificate.of_generalized_product_bounds
    (Xtilde : Matrix n k ℝ) (Ytilde Etilde : Matrix n m ℝ)
    (G : Matrix k r ℝ) (lambda : r → ℝ)
    (Aperp : Matrix m s ℝ) (eta : s → ℝ)
    (hG : reducedRankHansenGEigenvectors Xtilde Ytilde lambda G)
    (hGNorm : reducedRankGNormalized Xtilde G)
    (hGBound : generalizedEigenDetProductUpperBound
      (reducedRankGPencilA Xtilde Ytilde) (reducedRankGPencilB Xtilde) lambda)
    (hAperp : reducedRankHansenAperpEigenvectors Etilde Ytilde eta Aperp)
    (hAperpNorm : reducedRankAperpNormalized Ytilde Aperp)
    (hAperpBound : generalizedEigenDetProductLowerBound
      (reducedRankAperpPencilA Etilde) (reducedRankAperpPencilB Ytilde) eta) :
    ReducedRankHansenOrderedGeneralizedEigenMinMaxCertificate
      Xtilde Ytilde Etilde G lambda Aperp eta where
  g_ordered :=
    { eigenvectors := hG
      normalized := hGNorm
      product_upper_bound := hGBound }
  aperp_ordered :=
    { eigenvectors := hAperp
      normalized := hAperpNorm
      product_lower_bound := hAperpBound }

omit [DecidableEq n] in
/-- Convert the raw Hansen ordered min-max surface into the existing reusable
determinant/product min-max certificate. -/
theorem ReducedRankHansenOrderedGeneralizedEigenMinMaxCertificate.to_detProductMinMaxCertificate
    {Xtilde : Matrix n k ℝ} {Ytilde Etilde : Matrix n m ℝ}
    {G : Matrix k r ℝ} {lambda : r → ℝ}
    {Aperp : Matrix m s ℝ} {eta : s → ℝ}
    (h : ReducedRankHansenOrderedGeneralizedEigenMinMaxCertificate
      Xtilde Ytilde Etilde G lambda Aperp eta) :
    ReducedRankHansenDetProductMinMaxCertificate
      Xtilde Ytilde Etilde G lambda Aperp eta where
  g_max := h.g_ordered.to_detProductMaxCertificate
  aperp_min := h.aperp_ordered.to_detProductMinCertificate

omit [DecidableEq n] in
/-- Build the determinant/product min-max certificate from the natural selected
compressed determinant extrema for the two Hansen pencils. -/
theorem ReducedRankHansenDetProductMinMaxCertificate.of_selected_compressedDet_extrema
    (Xtilde : Matrix n k ℝ) (Ytilde Etilde : Matrix n m ℝ)
    (G : Matrix k r ℝ) (lambda : r → ℝ)
    (Aperp : Matrix m s ℝ) (eta : s → ℝ)
    (hG : reducedRankHansenGEigenvectors Xtilde Ytilde lambda G)
    (hGNorm : reducedRankGNormalized Xtilde G)
    (hGMax :
      generalizedEigenSelectedCompressedDetMaximal
        (reducedRankGPencilA Xtilde Ytilde) (reducedRankGPencilB Xtilde) G)
    (hAperp : reducedRankHansenAperpEigenvectors Etilde Ytilde eta Aperp)
    (hAperpNorm : reducedRankAperpNormalized Ytilde Aperp)
    (hAperpMin :
      generalizedEigenSelectedCompressedDetMinimal
        (reducedRankAperpPencilA Etilde) (reducedRankAperpPencilB Ytilde) Aperp) :
    ReducedRankHansenDetProductMinMaxCertificate
      Xtilde Ytilde Etilde G lambda Aperp eta where
  g_max :=
    { eigenvectors := hG
      normalized := hGNorm
      selected_compressedDet_maximal := hGMax }
  aperp_min :=
    { eigenvectors := hAperp
      normalized := hAperpNorm
      selected_compressedDet_minimal := hAperpMin }

omit [DecidableEq n] in
/-- Build Hansen's determinant/product min-max certificate from the literal
product variational bounds for the two residualized pencils.

This is the direct input surface for a raw ordered generalized-eigenvalue
determinant theorem: it only has to provide Hansen's displayed inequalities
`det(H'X̃'Ỹ(Ỹ'Ỹ)⁻¹Ỹ'X̃H) ≤ ∏ λ_j` and
`∏ η_j ≤ det(H'Ẽ'ẼH)`. The selected compressed-determinant extrema required
by the reusable certificate are derived internally. -/
theorem ReducedRankHansenDetProductMinMaxCertificate.of_product_variational_bounds
    (Xtilde : Matrix n k ℝ) (Ytilde Etilde : Matrix n m ℝ)
    (G : Matrix k r ℝ) (lambda : r → ℝ)
    (Aperp : Matrix m s ℝ) (eta : s → ℝ)
    (hG : reducedRankHansenGEigenvectors Xtilde Ytilde lambda G)
    (hGNorm : reducedRankGNormalized Xtilde G)
    (hGBound : reducedRankGDetVariationalBound Xtilde Ytilde lambda)
    (hAperp : reducedRankHansenAperpEigenvectors Etilde Ytilde eta Aperp)
    (hAperpNorm : reducedRankAperpNormalized Ytilde Aperp)
    (hAperpBound : reducedRankAperpDetVariationalBound Etilde Ytilde eta) :
    ReducedRankHansenDetProductMinMaxCertificate
      Xtilde Ytilde Etilde G lambda Aperp eta where
  g_max :=
    GeneralizedEigenDetProductMaxCertificate.of_productUpperBound
      (reducedRankGPencilA Xtilde Ytilde) (reducedRankGPencilB Xtilde)
      G lambda hG hGNorm hGBound
  aperp_min :=
    GeneralizedEigenDetProductMinCertificate.of_productLowerBound
      (reducedRankAperpPencilA Etilde) (reducedRankAperpPencilB Ytilde)
      Aperp eta hAperp hAperpNorm hAperpBound

/-- Build Hansen's determinant/product min-max certificate from the ordinary
PSD leading/trailing determinant-extrema theorem after whitening.

This is the faithful multi-column bridge for Theorem 11.7: the remaining
primitive is exactly the ordinary determinant theorem for the leading
eigenspace of `Ỹ(Ỹ'Ỹ)⁻¹Ỹ'` and the trailing eigenspace of `R'R`, together
with the residual-factor identity `Ẽ = RỸ`. -/
theorem ReducedRankHansenDetProductMinMaxCertificate.of_whitened_psd_leading_trailing
    (Xtilde : Matrix n k ℝ) (Ytilde Etilde : Matrix n m ℝ)
    (G : Matrix k r ℝ) (lambda : r → ℝ)
    (Aperp : Matrix m s ℝ) (eta : s → ℝ)
    (R : Matrix n n ℝ) (G0 : Matrix n r ℝ) (A0 : Matrix n s ℝ)
    (hG : reducedRankHansenGEigenvectors Xtilde Ytilde lambda G)
    (hGNorm : reducedRankGNormalized Xtilde G)
    (hAperp : reducedRankHansenAperpEigenvectors Etilde Ytilde eta Aperp)
    (hAperpNorm : reducedRankAperpNormalized Ytilde Aperp)
    (hWhite : ReducedRankHansenWhitenedPSDLeadingTrailingCertificate
      Ytilde Etilde lambda eta R G0 A0) :
    ReducedRankHansenDetProductMinMaxCertificate
      Xtilde Ytilde Etilde G lambda Aperp eta :=
  ReducedRankHansenDetProductMinMaxCertificate.of_product_variational_bounds
    Xtilde Ytilde Etilde G lambda Aperp eta hG hGNorm
    (hWhite.g_detVariationalBound Xtilde)
    hAperp hAperpNorm hWhite.aperp_detVariationalBound

/-- Build Hansen's determinant/product min-max certificate for the actual
residualized Theorem 11.7 matrices from the ordinary whitened PSD
leading/trailing determinant-extrema inputs.

Compared with `of_whitened_psd_leading_trailing`, this constructor discharges
the concrete residual-factor identity internally using
`reducedRankTildeE_eq_residualFactor_mul_tildeY`. -/
theorem ReducedRankHansenDetProductMinMaxCertificate.of_residualized_whitened_psd_leading_trailing
    (Z : Matrix n ell ℝ) (X : Matrix n k ℝ) (Y : Matrix n m ℝ)
    (G : Matrix k r ℝ) (lambda : r → ℝ)
    (Aperp : Matrix m s ℝ) (eta : s → ℝ)
    (G0 : Matrix n r ℝ) (A0 : Matrix n s ℝ)
    [DecidableEq k] [Invertible (Zᵀ * Z)]
    [Invertible ((Matrix.fromCols X Z)ᵀ * Matrix.fromCols X Z)]
    (hG : reducedRankHansenGEigenvectors
      (reducedRankTildeX Z X) (reducedRankTildeY Z Y) lambda G)
    (hGNorm : reducedRankGNormalized (reducedRankTildeX Z X) G)
    (hAperp : reducedRankHansenAperpEigenvectors
      (reducedRankTildeE X Z Y) (reducedRankTildeY Z Y) eta Aperp)
    (hAperpNorm : reducedRankAperpNormalized (reducedRankTildeY Z Y) Aperp)
    (hG0 : generalizedEigenvectorColumns
      (reducedRankGWhitenedProjection (reducedRankTildeY Z Y))
      (1 : Matrix n n ℝ) lambda G0)
    (hG0Norm : G0ᵀ * G0 = 1)
    (hG0Max : ∀ H : Matrix n r ℝ, Hᵀ * H = 1 →
      (Hᵀ * reducedRankGWhitenedProjection (reducedRankTildeY Z Y) * H).det ≤
        (G0ᵀ * reducedRankGWhitenedProjection (reducedRankTildeY Z Y) * G0).det)
    (hA0 : generalizedEigenvectorColumns
      (reducedRankAperpResidualWhitenedMatrix (reducedRankAperpResidualFactor X Z))
      (1 : Matrix n n ℝ) eta A0)
    (hA0Norm : A0ᵀ * A0 = 1)
    (hA0Min : ∀ H : Matrix n s ℝ, Hᵀ * H = 1 →
      (A0ᵀ * reducedRankAperpResidualWhitenedMatrix
          (reducedRankAperpResidualFactor X Z) * A0).det ≤
        (Hᵀ * reducedRankAperpResidualWhitenedMatrix
          (reducedRankAperpResidualFactor X Z) * H).det) :
    ReducedRankHansenDetProductMinMaxCertificate
      (reducedRankTildeX Z X) (reducedRankTildeY Z Y) (reducedRankTildeE X Z Y)
      G lambda Aperp eta :=
  ReducedRankHansenDetProductMinMaxCertificate.of_whitened_psd_leading_trailing
    (reducedRankTildeX Z X) (reducedRankTildeY Z Y) (reducedRankTildeE X Z Y)
    G lambda Aperp eta (reducedRankAperpResidualFactor X Z) G0 A0
    hG hGNorm hAperp hAperpNorm
    (ReducedRankHansenWhitenedPSDLeadingTrailingCertificate.of_residualized
      Z X Y lambda eta G0 A0 hG0 hG0Norm hG0Max hA0 hA0Norm hA0Min)

/-- Build Hansen's determinant/product min-max certificate for the actual
residualized Theorem 11.7 matrices from the projection-specific partial
determinant route.

Compared with `of_residualized_whitened_psd_leading_trailing`, the two
ordinary determinant-extrema premises are discharged from the proved partial
projection determinant bound on the G side and the zero-product PSD determinant
minimum on the `A⊥` side. -/
theorem ReducedRankHansenDetProductMinMaxCertificate.of_residualized_projection_top_zero
    (Z : Matrix n ell ℝ) (X : Matrix n k ℝ) (Y : Matrix n m ℝ)
    (G : Matrix k r ℝ) (lambda : r → ℝ)
    (Aperp : Matrix m s ℝ) (eta : s → ℝ)
    (G0 : Matrix n r ℝ) (A0 : Matrix n s ℝ)
    [DecidableEq k] [Invertible (Zᵀ * Z)]
    [Invertible ((Matrix.fromCols X Z)ᵀ * Matrix.fromCols X Z)]
    [Invertible ((reducedRankTildeY Z Y)ᵀ * reducedRankTildeY Z Y)]
    (hG : reducedRankHansenGEigenvectors
      (reducedRankTildeX Z X) (reducedRankTildeY Z Y) lambda G)
    (hGNorm : reducedRankGNormalized (reducedRankTildeX Z X) G)
    (hAperp : reducedRankHansenAperpEigenvectors
      (reducedRankTildeE X Z Y) (reducedRankTildeY Z Y) eta Aperp)
    (hAperpNorm : reducedRankAperpNormalized (reducedRankTildeY Z Y) Aperp)
    (hG0 : generalizedEigenvectorColumns
      (reducedRankGWhitenedProjection (reducedRankTildeY Z Y))
      (1 : Matrix n n ℝ) lambda G0)
    (hG0Norm : G0ᵀ * G0 = 1)
    (hG0Top : ∀ j : r, lambda j = 1)
    (hA0 : generalizedEigenvectorColumns
      (reducedRankAperpResidualWhitenedMatrix (reducedRankAperpResidualFactor X Z))
      (1 : Matrix n n ℝ) eta A0)
    (hA0Norm : A0ᵀ * A0 = 1)
    (hA0ZeroProduct : (∏ j, eta j) = 0) :
    ReducedRankHansenDetProductMinMaxCertificate
      (reducedRankTildeX Z X) (reducedRankTildeY Z Y) (reducedRankTildeE X Z Y)
      G lambda Aperp eta :=
  ReducedRankHansenDetProductMinMaxCertificate.of_whitened_psd_leading_trailing
    (reducedRankTildeX Z X) (reducedRankTildeY Z Y) (reducedRankTildeE X Z Y)
    G lambda Aperp eta (reducedRankAperpResidualFactor X Z) G0 A0
    hG hGNorm hAperp hAperpNorm
    (ReducedRankHansenWhitenedPSDLeadingTrailingCertificate.of_residualized_projection_top_zero
      Z X Y lambda eta G0 A0 hG0 hG0Norm hG0Top hA0 hA0Norm hA0ZeroProduct)

/-- Determinant/product min-max certificate for the actual residualized
Theorem 11.7 matrices from the projection-range route.

Compared with `of_residualized_projection_top_zero`, this constructor derives
the `λ_j = 1` projection roots from `P G₀ = G₀`. -/
theorem ReducedRankHansenDetProductMinMaxCertificate.of_residualized_projection_range_zero
    (Z : Matrix n ell ℝ) (X : Matrix n k ℝ) (Y : Matrix n m ℝ)
    (G : Matrix k r ℝ) (lambda : r → ℝ)
    (Aperp : Matrix m s ℝ) (eta : s → ℝ)
    (G0 : Matrix n r ℝ) (A0 : Matrix n s ℝ)
    [DecidableEq k] [Invertible (Zᵀ * Z)]
    [Invertible ((Matrix.fromCols X Z)ᵀ * Matrix.fromCols X Z)]
    [Invertible ((reducedRankTildeY Z Y)ᵀ * reducedRankTildeY Z Y)]
    (hG : reducedRankHansenGEigenvectors
      (reducedRankTildeX Z X) (reducedRankTildeY Z Y) lambda G)
    (hGNorm : reducedRankGNormalized (reducedRankTildeX Z X) G)
    (hAperp : reducedRankHansenAperpEigenvectors
      (reducedRankTildeE X Z Y) (reducedRankTildeY Z Y) eta Aperp)
    (hAperpNorm : reducedRankAperpNormalized (reducedRankTildeY Z Y) Aperp)
    (hG0 : generalizedEigenvectorColumns
      (reducedRankGWhitenedProjection (reducedRankTildeY Z Y))
      (1 : Matrix n n ℝ) lambda G0)
    (hG0Norm : G0ᵀ * G0 = 1)
    (hG0Range :
      reducedRankGWhitenedProjection (reducedRankTildeY Z Y) * G0 = G0)
    (hA0 : generalizedEigenvectorColumns
      (reducedRankAperpResidualWhitenedMatrix (reducedRankAperpResidualFactor X Z))
      (1 : Matrix n n ℝ) eta A0)
    (hA0Norm : A0ᵀ * A0 = 1)
    (hA0ZeroProduct : (∏ j, eta j) = 0) :
    ReducedRankHansenDetProductMinMaxCertificate
      (reducedRankTildeX Z X) (reducedRankTildeY Z Y) (reducedRankTildeE X Z Y)
      G lambda Aperp eta :=
  ReducedRankHansenDetProductMinMaxCertificate.of_whitened_psd_leading_trailing
    (reducedRankTildeX Z X) (reducedRankTildeY Z Y) (reducedRankTildeE X Z Y)
    G lambda Aperp eta (reducedRankAperpResidualFactor X Z) G0 A0
    hG hGNorm hAperp hAperpNorm
    (ReducedRankHansenWhitenedPSDLeadingTrailingCertificate.of_residualized_projection_range_zero
      Z X Y lambda eta G0 A0 hG0 hG0Norm hG0Range hA0 hA0Norm hA0ZeroProduct)

/-- Determinant/product min-max certificate for the actual residualized
Theorem 11.7 matrices from the projection-range/nullspace route.

Compared with `of_residualized_projection_range_zero`, this constructor derives
the trailing selected-root product `∏ η_j = 0` from the ordinary nullspace
identity `R'R A₀ = 0`. -/
theorem ReducedRankHansenDetProductMinMaxCertificate.of_residualized_projection_range_null
    (Z : Matrix n ell ℝ) (X : Matrix n k ℝ) (Y : Matrix n m ℝ)
    (G : Matrix k r ℝ) (lambda : r → ℝ)
    (Aperp : Matrix m s ℝ) (eta : s → ℝ)
    (G0 : Matrix n r ℝ) (A0 : Matrix n s ℝ)
    [Nonempty s]
    [DecidableEq k] [Invertible (Zᵀ * Z)]
    [Invertible ((Matrix.fromCols X Z)ᵀ * Matrix.fromCols X Z)]
    [Invertible ((reducedRankTildeY Z Y)ᵀ * reducedRankTildeY Z Y)]
    (hG : reducedRankHansenGEigenvectors
      (reducedRankTildeX Z X) (reducedRankTildeY Z Y) lambda G)
    (hGNorm : reducedRankGNormalized (reducedRankTildeX Z X) G)
    (hAperp : reducedRankHansenAperpEigenvectors
      (reducedRankTildeE X Z Y) (reducedRankTildeY Z Y) eta Aperp)
    (hAperpNorm : reducedRankAperpNormalized (reducedRankTildeY Z Y) Aperp)
    (hG0 : generalizedEigenvectorColumns
      (reducedRankGWhitenedProjection (reducedRankTildeY Z Y))
      (1 : Matrix n n ℝ) lambda G0)
    (hG0Norm : G0ᵀ * G0 = 1)
    (hG0Range :
      reducedRankGWhitenedProjection (reducedRankTildeY Z Y) * G0 = G0)
    (hA0 : generalizedEigenvectorColumns
      (reducedRankAperpResidualWhitenedMatrix (reducedRankAperpResidualFactor X Z))
      (1 : Matrix n n ℝ) eta A0)
    (hA0Norm : A0ᵀ * A0 = 1)
    (hA0Null :
      reducedRankAperpResidualWhitenedMatrix (reducedRankAperpResidualFactor X Z) *
        A0 = 0) :
    ReducedRankHansenDetProductMinMaxCertificate
      (reducedRankTildeX Z X) (reducedRankTildeY Z Y) (reducedRankTildeE X Z Y)
      G lambda Aperp eta :=
  ReducedRankHansenDetProductMinMaxCertificate.of_whitened_psd_leading_trailing
    (reducedRankTildeX Z X) (reducedRankTildeY Z Y) (reducedRankTildeE X Z Y)
    G lambda Aperp eta (reducedRankAperpResidualFactor X Z) G0 A0
    hG hGNorm hAperp hAperpNorm
    (ReducedRankHansenWhitenedPSDLeadingTrailingCertificate.of_residualized_projection_range_null
      Z X Y lambda eta G0 A0 hG0 hG0Norm hG0Range hA0 hA0Norm hA0Null)

/-- Determinant/product min-max certificate for the actual residualized
Theorem 11.7 matrices from ordinary fixed-root eigenvector packages.

The ordinary whitened G block has root `1`, and the ordinary residual block has
root `0`; the projection-range and residual-nullspace equations are derived by
`generalizedEigenvectorColumns_range_of_one` and
`generalizedEigenvectorColumns_null_of_zero`. -/
theorem ReducedRankHansenDetProductMinMaxCertificate.of_residualized_projection_fixed_roots
    (Z : Matrix n ell ℝ) (X : Matrix n k ℝ) (Y : Matrix n m ℝ)
    (G : Matrix k r ℝ)
    (Aperp : Matrix m s ℝ)
    (G0 : Matrix n r ℝ) (A0 : Matrix n s ℝ)
    [Nonempty s]
    [DecidableEq k] [Invertible (Zᵀ * Z)]
    [Invertible ((Matrix.fromCols X Z)ᵀ * Matrix.fromCols X Z)]
    [Invertible ((reducedRankTildeY Z Y)ᵀ * reducedRankTildeY Z Y)]
    (hG : reducedRankHansenGEigenvectors
      (reducedRankTildeX Z X) (reducedRankTildeY Z Y) (fun _ : r => (1 : ℝ)) G)
    (hGNorm : reducedRankGNormalized (reducedRankTildeX Z X) G)
    (hAperp : reducedRankHansenAperpEigenvectors
      (reducedRankTildeE X Z Y) (reducedRankTildeY Z Y)
      (fun _ : s => (0 : ℝ)) Aperp)
    (hAperpNorm : reducedRankAperpNormalized (reducedRankTildeY Z Y) Aperp)
    (hG0 : generalizedEigenvectorColumns
      (reducedRankGWhitenedProjection (reducedRankTildeY Z Y))
      (1 : Matrix n n ℝ) (fun _ : r => (1 : ℝ)) G0)
    (hG0Norm : G0ᵀ * G0 = 1)
    (hA0 : generalizedEigenvectorColumns
      (reducedRankAperpResidualWhitenedMatrix (reducedRankAperpResidualFactor X Z))
      (1 : Matrix n n ℝ) (fun _ : s => (0 : ℝ)) A0)
    (hA0Norm : A0ᵀ * A0 = 1) :
    ReducedRankHansenDetProductMinMaxCertificate
      (reducedRankTildeX Z X) (reducedRankTildeY Z Y) (reducedRankTildeE X Z Y)
      G (fun _ : r => (1 : ℝ)) Aperp (fun _ : s => (0 : ℝ)) :=
  ReducedRankHansenDetProductMinMaxCertificate.of_whitened_psd_leading_trailing
    (reducedRankTildeX Z X) (reducedRankTildeY Z Y) (reducedRankTildeE X Z Y)
    G (fun _ : r => (1 : ℝ)) Aperp (fun _ : s => (0 : ℝ))
    (reducedRankAperpResidualFactor X Z) G0 A0
    hG hGNorm hAperp hAperpNorm
    (ReducedRankHansenWhitenedPSDLeadingTrailingCertificate.of_residualized_projection_fixed_roots
      Z X Y G0 A0 hG0 hG0Norm hA0 hA0Norm)

set_option linter.style.longLine false in
/-- Determinant/product min-max certificate for the actual residualized
Theorem 11.7 matrices from ordinary span and residual-nullspace witnesses.

The selected ordinary G block is supplied as `G₀ = Ỹ C`, and the selected
ordinary `A⊥` block is supplied by the raw residual nullspace equation
`R A₀ = 0`. This derives the projection-range and `R'R A₀ = 0` certificates
before entering the existing projection-range/nullspace route. -/
theorem ReducedRankHansenDetProductMinMaxCertificate.of_residualized_projection_span_residual_null
    (Z : Matrix n ell ℝ) (X : Matrix n k ℝ) (Y : Matrix n m ℝ)
    (G : Matrix k r ℝ)
    (Aperp : Matrix m s ℝ)
    (G0 : Matrix n r ℝ) (A0 : Matrix n s ℝ) (C : Matrix m r ℝ)
    [Nonempty s]
    [DecidableEq k] [Invertible (Zᵀ * Z)]
    [Invertible ((Matrix.fromCols X Z)ᵀ * Matrix.fromCols X Z)]
    [Invertible ((reducedRankTildeY Z Y)ᵀ * reducedRankTildeY Z Y)]
    (hG : reducedRankHansenGEigenvectors
      (reducedRankTildeX Z X) (reducedRankTildeY Z Y) (fun _ : r => (1 : ℝ)) G)
    (hGNorm : reducedRankGNormalized (reducedRankTildeX Z X) G)
    (hAperp : reducedRankHansenAperpEigenvectors
      (reducedRankTildeE X Z Y) (reducedRankTildeY Z Y)
      (fun _ : s => (0 : ℝ)) Aperp)
    (hAperpNorm : reducedRankAperpNormalized (reducedRankTildeY Z Y) Aperp)
    (hG0Span : G0 = reducedRankTildeY Z Y * C)
    (hG0Norm : G0ᵀ * G0 = 1)
    (hA0Norm : A0ᵀ * A0 = 1)
    (hA0ResidualNull : reducedRankAperpResidualFactor X Z * A0 = 0) :
    ReducedRankHansenDetProductMinMaxCertificate
      (reducedRankTildeX Z X) (reducedRankTildeY Z Y) (reducedRankTildeE X Z Y)
      G (fun _ : r => (1 : ℝ)) Aperp (fun _ : s => (0 : ℝ)) :=
  ReducedRankHansenDetProductMinMaxCertificate.of_whitened_psd_leading_trailing
    (reducedRankTildeX Z X) (reducedRankTildeY Z Y) (reducedRankTildeE X Z Y)
    G (fun _ : r => (1 : ℝ)) Aperp (fun _ : s => (0 : ℝ))
    (reducedRankAperpResidualFactor X Z) G0 A0
    hG hGNorm hAperp hAperpNorm
    (ReducedRankHansenWhitenedPSDLeadingTrailingCertificate.of_residualized_projection_span_residual_null
      Z X Y G0 A0 C hG0Span hG0Norm hA0Norm hA0ResidualNull)

/-- Build Hansen's determinant/product min-max certificate for the actual
residualized Theorem 11.7 matrices from full ordinary orthonormal eigenbases
of the two whitened identity-denominator matrices.

This is a proved multi-column full-basis route through the same certificate
surface as the partial leading/trailing theorem. It intentionally does not
claim Hansen's general partial-block determinant min-max theorem; that remains
the ordinary leading/trailing PSD result when `r` and `s` do not span the
ambient whitened index type. -/
theorem ReducedRankHansenDetProductMinMaxCertificate.of_residualized_whitened_full_eigenbases
    (eG : n ≃ r) (eA : n ≃ s)
    (Z : Matrix n ell ℝ) (X : Matrix n k ℝ) (Y : Matrix n m ℝ)
    (G : Matrix k r ℝ) (lambda : r → ℝ)
    (Aperp : Matrix m s ℝ) (eta : s → ℝ)
    (G0 : Matrix n r ℝ) (A0 : Matrix n s ℝ)
    [DecidableEq k] [Invertible (Zᵀ * Z)]
    [Invertible ((Matrix.fromCols X Z)ᵀ * Matrix.fromCols X Z)]
    (hG : reducedRankHansenGEigenvectors
      (reducedRankTildeX Z X) (reducedRankTildeY Z Y) lambda G)
    (hGNorm : reducedRankGNormalized (reducedRankTildeX Z X) G)
    (hAperp : reducedRankHansenAperpEigenvectors
      (reducedRankTildeE X Z Y) (reducedRankTildeY Z Y) eta Aperp)
    (hAperpNorm : reducedRankAperpNormalized (reducedRankTildeY Z Y) Aperp)
    (hG0 : generalizedEigenvectorColumns
      (reducedRankGWhitenedProjection (reducedRankTildeY Z Y))
      (1 : Matrix n n ℝ) lambda G0)
    (hG0Norm : G0ᵀ * G0 = 1)
    (hA0 : generalizedEigenvectorColumns
      (reducedRankAperpResidualWhitenedMatrix (reducedRankAperpResidualFactor X Z))
      (1 : Matrix n n ℝ) eta A0)
    (hA0Norm : A0ᵀ * A0 = 1) :
    ReducedRankHansenDetProductMinMaxCertificate
      (reducedRankTildeX Z X) (reducedRankTildeY Z Y) (reducedRankTildeE X Z Y)
      G lambda Aperp eta :=
  ReducedRankHansenDetProductMinMaxCertificate.of_product_variational_bounds
    (reducedRankTildeX Z X) (reducedRankTildeY Z Y) (reducedRankTildeE X Z Y)
    G lambda Aperp eta hG hGNorm
    (reducedRankGDetVariationalBound_of_canonical_whitened_equiv_orthonormal_eigenbasis
      eG (reducedRankTildeX Z X) (reducedRankTildeY Z Y) lambda G0 hG0 hG0Norm)
    hAperp hAperpNorm
    (reducedRankAperpDetVariationalBound_of_residualized_equiv_orthonormal_eigenbasis
      eA Z X Y eta A0 hA0 hA0Norm)

omit [DecidableEq n] in
/-- Build Hansen's determinant/product min-max certificate from generic
generalized-pencil product bounds.

This is the narrow interface a raw generalized-pencil determinant/product
theorem should target: prove the upper-bound theorem for Hansen's `G` pencil and
the lower-bound theorem for the residual `A⊥` pencil, while this constructor
performs the Hansen-specific translation. -/
theorem ReducedRankHansenDetProductMinMaxCertificate.of_generalized_product_bounds
    (Xtilde : Matrix n k ℝ) (Ytilde Etilde : Matrix n m ℝ)
    (G : Matrix k r ℝ) (lambda : r → ℝ)
    (Aperp : Matrix m s ℝ) (eta : s → ℝ)
    (hG : reducedRankHansenGEigenvectors Xtilde Ytilde lambda G)
    (hGNorm : reducedRankGNormalized Xtilde G)
    (hGBound : generalizedEigenDetProductUpperBound
      (reducedRankGPencilA Xtilde Ytilde) (reducedRankGPencilB Xtilde) lambda)
    (hAperp : reducedRankHansenAperpEigenvectors Etilde Ytilde eta Aperp)
    (hAperpNorm : reducedRankAperpNormalized Ytilde Aperp)
    (hAperpBound : generalizedEigenDetProductLowerBound
      (reducedRankAperpPencilA Etilde) (reducedRankAperpPencilB Ytilde) eta) :
    ReducedRankHansenDetProductMinMaxCertificate
      Xtilde Ytilde Etilde G lambda Aperp eta :=
  ReducedRankHansenDetProductMinMaxCertificate.of_product_variational_bounds
    Xtilde Ytilde Etilde G lambda Aperp eta
    hG hGNorm
    (reducedRankGDetVariationalBound_of_generalized_productUpperBound
      Xtilde Ytilde lambda hGBound)
    hAperp hAperpNorm
    (reducedRankAperpDetVariationalBound_of_generalized_productLowerBound
      Etilde Ytilde eta hAperpBound)

omit [DecidableEq n] in
/-- Build Hansen's determinant/product min-max certificate from whitened
identity-denominator product bounds for the two residualized pencils.

This is the reduced raw target for Hansen Theorem 11.7: after factoring each
generalized pencil as `A = T' M T`, `B = T' T`, it is enough to prove the
ordinary orthonormal-column determinant product upper/lower bounds for the two
identity-denominator matrices. -/
theorem ReducedRankHansenDetProductMinMaxCertificate.of_whitened_identity_product_bounds
    {qG qA : Type*} [Fintype qG] [DecidableEq qG] [Fintype qA] [DecidableEq qA]
    (Xtilde : Matrix n k ℝ) (Ytilde Etilde : Matrix n m ℝ)
    (G : Matrix k r ℝ) (lambda : r → ℝ)
    (Aperp : Matrix m s ℝ) (eta : s → ℝ)
    (MG : Matrix qG qG ℝ) (TG : Matrix qG k ℝ)
    (MA : Matrix qA qA ℝ) (TA : Matrix qA m ℝ)
    (hG : reducedRankHansenGEigenvectors Xtilde Ytilde lambda G)
    (hGNorm : reducedRankGNormalized Xtilde G)
    (hGA : reducedRankGPencilA Xtilde Ytilde = TGᵀ * MG * TG)
    (hGB : reducedRankGPencilB Xtilde = TGᵀ * TG)
    (hGBound : generalizedEigenDetProductUpperBound MG 1 lambda)
    (hAperp : reducedRankHansenAperpEigenvectors Etilde Ytilde eta Aperp)
    (hAperpNorm : reducedRankAperpNormalized Ytilde Aperp)
    (hAperpA : reducedRankAperpPencilA Etilde = TAᵀ * MA * TA)
    (hAperpB : reducedRankAperpPencilB Ytilde = TAᵀ * TA)
    (hAperpBound : generalizedEigenDetProductLowerBound MA 1 eta) :
    ReducedRankHansenDetProductMinMaxCertificate
      Xtilde Ytilde Etilde G lambda Aperp eta :=
  ReducedRankHansenDetProductMinMaxCertificate.of_product_variational_bounds
    Xtilde Ytilde Etilde G lambda Aperp eta
    hG hGNorm
    (reducedRankGDetVariationalBound_of_whitened_identity_productUpperBound
      Xtilde Ytilde MG TG lambda hGA hGB hGBound)
    hAperp hAperpNorm
    (reducedRankAperpDetVariationalBound_of_whitened_identity_productLowerBound
      Etilde Ytilde MA TA eta hAperpA hAperpB hAperpBound)

omit [DecidableEq n] in
/-- Build Hansen's determinant/product min-max certificate from scalar
Rayleigh bounds in the rank-one/rank-one case.

This is not the full generalized-pencil determinant theorem. It is the exact
one-column bridge for both sides of Hansen Theorem 11.7: the G-side determinant
inequality reduces to a scalar upper Rayleigh bound, and the `A⊥` determinant
inequality reduces to a scalar lower Rayleigh bound. The existing theorem-facing
endpoints can then consume the resulting min-max certificate unchanged. -/
theorem ReducedRankHansenDetProductMinMaxCertificate.of_rankOne_rayleigh_bounds
    [Unique r] [Unique s]
    (Xtilde : Matrix n k ℝ) (Ytilde Etilde : Matrix n m ℝ)
    (G : Matrix k r ℝ) (lambda : r → ℝ)
    (Aperp : Matrix m s ℝ) (eta : s → ℝ)
    (hG : reducedRankHansenGEigenvectors Xtilde Ytilde lambda G)
    (hGNorm : reducedRankGNormalized Xtilde G)
    (hGBound : ∀ v : k → ℝ,
      v ⬝ᵥ (reducedRankGPencilB Xtilde *ᵥ v) = 1 →
        v ⬝ᵥ (reducedRankGPencilA Xtilde Ytilde *ᵥ v) ≤ lambda default)
    (hAperp : reducedRankHansenAperpEigenvectors Etilde Ytilde eta Aperp)
    (hAperpNorm : reducedRankAperpNormalized Ytilde Aperp)
    (hAperpBound : ∀ v : m → ℝ,
      v ⬝ᵥ (reducedRankAperpPencilB Ytilde *ᵥ v) = 1 →
        eta default ≤ v ⬝ᵥ (reducedRankAperpPencilA Etilde *ᵥ v)) :
    ReducedRankHansenDetProductMinMaxCertificate
      Xtilde Ytilde Etilde G lambda Aperp eta :=
  ReducedRankHansenDetProductMinMaxCertificate.of_product_variational_bounds
    Xtilde Ytilde Etilde G lambda Aperp eta
    hG hGNorm
    (reducedRankGDetVariationalBound_rankOne_of_rayleigh_bound
      Xtilde Ytilde lambda hGBound)
    hAperp hAperpNorm
    (reducedRankAperpDetVariationalBound_rankOne_of_rayleigh_bound
      Etilde Ytilde eta hAperpBound)

omit [DecidableEq n] in
/-- Build Hansen's determinant/product min-max certificate from the
normal-likelihood objective extrema for the two residualized determinant
surfaces. The selected compressed-determinant extrema are derived internally. -/
theorem ReducedRankHansenDetProductMinMaxCertificate.of_objective_extrema
    (Xtilde : Matrix n k ℝ) (Ytilde Etilde : Matrix n m ℝ)
    (G : Matrix k r ℝ) (lambda : r → ℝ)
    (Aperp : Matrix m s ℝ) (eta : s → ℝ)
    (hG : reducedRankHansenGEigenvectors Xtilde Ytilde lambda G)
    (hGOpt : reducedRankConcentratedObjectiveMaximizer Xtilde Ytilde G)
    (hAperp : reducedRankHansenAperpEigenvectors Etilde Ytilde eta Aperp)
    (hAperpOpt : reducedRankAperpObjectiveMinimizer Etilde Ytilde Aperp) :
    ReducedRankHansenDetProductMinMaxCertificate
      Xtilde Ytilde Etilde G lambda Aperp eta where
  g_max :=
    reducedRankGDetProductMaxCertificate_of_objectiveMaximizer
      Xtilde Ytilde lambda G hG hGOpt
  aperp_min :=
    reducedRankAperpDetProductMinCertificate_of_objectiveMinimizer
      Etilde Ytilde eta Aperp hAperp hAperpOpt

omit [DecidableEq n] in
/-- Build Hansen's determinant/product min-max certificate from generic
generalized-pencil determinant-objective extrema specialized to the two Hansen
pencils. -/
theorem ReducedRankHansenDetProductMinMaxCertificate.of_generalized_objective_extrema
    (Xtilde : Matrix n k ℝ) (Ytilde Etilde : Matrix n m ℝ)
    (G : Matrix k r ℝ) (lambda : r → ℝ)
    (Aperp : Matrix m s ℝ) (eta : s → ℝ)
    (hG : reducedRankHansenGEigenvectors Xtilde Ytilde lambda G)
    (hGOpt : generalizedEigenDetObjectiveMaximizer
      (reducedRankGPencilA Xtilde Ytilde) (reducedRankGPencilB Xtilde) G)
    (hAperp : reducedRankHansenAperpEigenvectors Etilde Ytilde eta Aperp)
    (hAperpOpt : generalizedEigenDetObjectiveMinimizer
      (reducedRankAperpPencilA Etilde) (reducedRankAperpPencilB Ytilde) Aperp) :
    ReducedRankHansenDetProductMinMaxCertificate
      Xtilde Ytilde Etilde G lambda Aperp eta :=
  ReducedRankHansenDetProductMinMaxCertificate.of_objective_extrema
    Xtilde Ytilde Etilde G lambda Aperp eta
    hG
    (reducedRankConcentratedObjectiveMaximizer_of_generalized_detObjectiveMaximizer
      Xtilde Ytilde G hGOpt)
    hAperp
    (reducedRankAperpObjectiveMinimizer_of_generalized_detObjectiveMinimizer
      Etilde Ytilde Aperp hAperpOpt)

omit [DecidableEq n] in
/-- The G-side objective maximum derived from Hansen's determinant/product
min-max certificate. This is the ordered generalized-eigenvalue route to the
normal-likelihood objective extremum used by Theorem 11.7. -/
theorem ReducedRankHansenDetProductMinMaxCertificate.g_objectiveMaximizer
    {Xtilde : Matrix n k ℝ} {Ytilde Etilde : Matrix n m ℝ}
    {G : Matrix k r ℝ} {lambda : r → ℝ}
    {Aperp : Matrix m s ℝ} {eta : s → ℝ}
    (h : ReducedRankHansenDetProductMinMaxCertificate
      Xtilde Ytilde Etilde G lambda Aperp eta) :
    reducedRankConcentratedObjectiveMaximizer Xtilde Ytilde G := by
  change generalizedEigenDetObjectiveMaximizer
    (reducedRankGPencilA Xtilde Ytilde) (reducedRankGPencilB Xtilde) G
  exact h.g_max.detObjectiveMaximizer

omit [DecidableEq n] in
/-- The `A⊥` objective minimum derived from Hansen's determinant/product
min-max certificate. -/
theorem ReducedRankHansenDetProductMinMaxCertificate.aperp_objectiveMinimizer
    {Xtilde : Matrix n k ℝ} {Ytilde Etilde : Matrix n m ℝ}
    {G : Matrix k r ℝ} {lambda : r → ℝ}
    {Aperp : Matrix m s ℝ} {eta : s → ℝ}
    (h : ReducedRankHansenDetProductMinMaxCertificate
      Xtilde Ytilde Etilde G lambda Aperp eta) :
    reducedRankAperpObjectiveMinimizer Etilde Ytilde Aperp := by
  change generalizedEigenDetObjectiveMinimizer
    (reducedRankAperpPencilA Etilde) (reducedRankAperpPencilB Ytilde) Aperp
  exact h.aperp_min.detObjectiveMinimizer

omit [DecidableEq n] in
/-- The G-side product variational bound derived from the min-max certificate. -/
theorem ReducedRankHansenDetProductMinMaxCertificate.g_det_bound
    {Xtilde : Matrix n k ℝ} {Ytilde Etilde : Matrix n m ℝ}
    {G : Matrix k r ℝ} {lambda : r → ℝ}
    {Aperp : Matrix m s ℝ} {eta : s → ℝ}
    (h : ReducedRankHansenDetProductMinMaxCertificate
      Xtilde Ytilde Etilde G lambda Aperp eta) :
    reducedRankGDetVariationalBound Xtilde Ytilde lambda := by
  intro H hHNorm
  exact (GeneralizedEigenDetProductMaxCertificate.upperBound h.g_max) H hHNorm

omit [DecidableEq n] in
/-- The `A⊥`-side product variational bound derived from the min-max
certificate. -/
theorem ReducedRankHansenDetProductMinMaxCertificate.aperp_det_bound
    {Xtilde : Matrix n k ℝ} {Ytilde Etilde : Matrix n m ℝ}
    {G : Matrix k r ℝ} {lambda : r → ℝ}
    {Aperp : Matrix m s ℝ} {eta : s → ℝ}
    (h : ReducedRankHansenDetProductMinMaxCertificate
      Xtilde Ytilde Etilde G lambda Aperp eta) :
    reducedRankAperpDetVariationalBound Etilde Ytilde eta := by
  intro H hHNorm
  exact (GeneralizedEigenDetProductMinCertificate.lowerBound h.aperp_min) H hHNorm

/-- Deterministic spectral certificate for the literal smallest-root summary
compatibility route.

The fields are the two residualized generalized-eigenvector equations, the two
Hansen normalizations, and the two literal determinant/product variational
inequalities. Its `A⊥` lower bound follows the inconsistent final summary, not
equation (11.21); it must not be used as an MLE-complement certificate. -/
structure ReducedRankHansenSpectralDualityCertificate
    (Xtilde : Matrix n k ℝ) (Ytilde Etilde : Matrix n m ℝ)
    (G : Matrix k r ℝ) (lambda : r → ℝ)
    (Aperp : Matrix m s ℝ) (eta : s → ℝ) : Prop where
  g_eigenvectors : reducedRankHansenGEigenvectors Xtilde Ytilde lambda G
  g_normalized : reducedRankGNormalized Xtilde G
  g_det_bound : reducedRankGDetVariationalBound Xtilde Ytilde lambda
  aperp_eigenvectors : reducedRankHansenAperpEigenvectors Etilde Ytilde eta Aperp
  aperp_normalized : reducedRankAperpNormalized Ytilde Aperp
  aperp_det_bound : reducedRankAperpDetVariationalBound Etilde Ytilde eta

/-- Identified compatibility certificate that keeps Hansen's explicit
subspace equation `A⊥'Ỹ'X̃G = 0` alongside the old max/min bounds.

For the canonical max/max theorem surface use
`ReducedRankHansenIdentifiedSpectralMaximizerCertificate`. -/
structure ReducedRankHansenIdentifiedSpectralDualityCertificate
    (Xtilde : Matrix n k ℝ) (Ytilde Etilde : Matrix n m ℝ)
    (G : Matrix k r ℝ) (lambda : r → ℝ)
    (Aperp : Matrix m s ℝ) (eta : s → ℝ) : Prop where
  spectral_duality :
    ReducedRankHansenSpectralDualityCertificate Xtilde Ytilde Etilde G lambda Aperp eta
  aperp_cross_orthogonal : reducedRankAperpCrossOrthogonal Xtilde Ytilde G Aperp

omit [DecidableEq n] in
/-- Forget the explicit subspace-identification field from the strengthened
certificate. -/
theorem ReducedRankHansenIdentifiedSpectralDualityCertificate.to_spectralDualityCertificate
    {Xtilde : Matrix n k ℝ} {Ytilde Etilde : Matrix n m ℝ}
    {G : Matrix k r ℝ} {lambda : r → ℝ}
    {Aperp : Matrix m s ℝ} {eta : s → ℝ}
    (h : ReducedRankHansenIdentifiedSpectralDualityCertificate
      Xtilde Ytilde Etilde G lambda Aperp eta) :
    ReducedRankHansenSpectralDualityCertificate
      Xtilde Ytilde Etilde G lambda Aperp eta :=
  h.spectral_duality

omit [DecidableEq n] in
/-- Convert the stronger determinant/product min-max certificate into the
existing Hansen spectral-duality certificate consumed by the MLE endpoints. -/
theorem ReducedRankHansenDetProductMinMaxCertificate.to_spectralDualityCertificate
    {Xtilde : Matrix n k ℝ} {Ytilde Etilde : Matrix n m ℝ}
    {G : Matrix k r ℝ} {lambda : r → ℝ}
    {Aperp : Matrix m s ℝ} {eta : s → ℝ}
    (h : ReducedRankHansenDetProductMinMaxCertificate
      Xtilde Ytilde Etilde G lambda Aperp eta) :
    ReducedRankHansenSpectralDualityCertificate
      Xtilde Ytilde Etilde G lambda Aperp eta where
  g_eigenvectors := h.g_max.eigenvectors
  g_normalized := h.g_max.normalized
  g_det_bound := h.g_det_bound
  aperp_eigenvectors := h.aperp_min.eigenvectors
  aperp_normalized := h.aperp_min.normalized
  aperp_det_bound := h.aperp_det_bound

omit [DecidableEq n] in
/-- A spectral-duality certificate also supplies the stronger reusable
determinant/product min-max certificate. The literal product variational bounds
are converted back into selected compressed-determinant extrema using the
selected generalized-eigenvector product identities. -/
theorem ReducedRankHansenSpectralDualityCertificate.to_detProductMinMaxCertificate
    {Xtilde : Matrix n k ℝ} {Ytilde Etilde : Matrix n m ℝ}
    {G : Matrix k r ℝ} {lambda : r → ℝ}
    {Aperp : Matrix m s ℝ} {eta : s → ℝ}
    (h : ReducedRankHansenSpectralDualityCertificate
      Xtilde Ytilde Etilde G lambda Aperp eta) :
    ReducedRankHansenDetProductMinMaxCertificate
      Xtilde Ytilde Etilde G lambda Aperp eta :=
  ReducedRankHansenDetProductMinMaxCertificate.of_product_variational_bounds
    Xtilde Ytilde Etilde G lambda Aperp eta
    h.g_eigenvectors h.g_normalized h.g_det_bound
    h.aperp_eigenvectors h.aperp_normalized h.aperp_det_bound

omit [DecidableEq n] in
/-- Build the strengthened spectral-duality certificate from determinant/product
min-max plus the explicit `A⊥'Ỹ'X̃G = 0` subspace identification. -/
theorem ReducedRankHansenIdentifiedSpectralDualityCertificate.of_detProductMinMax_and_cross
    {Xtilde : Matrix n k ℝ} {Ytilde Etilde : Matrix n m ℝ}
    {G : Matrix k r ℝ} {lambda : r → ℝ}
    {Aperp : Matrix m s ℝ} {eta : s → ℝ}
    (hMinMax : ReducedRankHansenDetProductMinMaxCertificate
      Xtilde Ytilde Etilde G lambda Aperp eta)
    (hCross : reducedRankAperpCrossOrthogonal Xtilde Ytilde G Aperp) :
    ReducedRankHansenIdentifiedSpectralDualityCertificate
      Xtilde Ytilde Etilde G lambda Aperp eta where
  spectral_duality :=
    ReducedRankHansenDetProductMinMaxCertificate.to_spectralDualityCertificate hMinMax
  aperp_cross_orthogonal := hCross

omit [DecidableEq n] in
/-- Build the strengthened spectral-duality certificate directly from the two
normal-likelihood objective extrema and the explicit subspace identification. -/
theorem ReducedRankHansenIdentifiedSpectralDualityCertificate.of_objective_extrema_and_cross
    (Xtilde : Matrix n k ℝ) (Ytilde Etilde : Matrix n m ℝ)
    (G : Matrix k r ℝ) (lambda : r → ℝ)
    (Aperp : Matrix m s ℝ) (eta : s → ℝ)
    (hG : reducedRankHansenGEigenvectors Xtilde Ytilde lambda G)
    (hGOpt : reducedRankConcentratedObjectiveMaximizer Xtilde Ytilde G)
    (hAperp : reducedRankHansenAperpEigenvectors Etilde Ytilde eta Aperp)
    (hAperpOpt : reducedRankAperpObjectiveMinimizer Etilde Ytilde Aperp)
    (hCross : reducedRankAperpCrossOrthogonal Xtilde Ytilde G Aperp) :
    ReducedRankHansenIdentifiedSpectralDualityCertificate
      Xtilde Ytilde Etilde G lambda Aperp eta :=
  ReducedRankHansenIdentifiedSpectralDualityCertificate.of_detProductMinMax_and_cross
    (ReducedRankHansenDetProductMinMaxCertificate.of_objective_extrema
      Xtilde Ytilde Etilde G lambda Aperp eta hG hGOpt hAperp hAperpOpt)
    hCross

omit [DecidableEq n] in
/-- Build Hansen's spectral-duality certificate directly from the two
normal-likelihood objective extrema. The determinant/product min-max bounds are
derived through `ReducedRankHansenDetProductMinMaxCertificate.of_objective_extrema`. -/
theorem ReducedRankHansenSpectralDualityCertificate.of_objective_extrema
    (Xtilde : Matrix n k ℝ) (Ytilde Etilde : Matrix n m ℝ)
    (G : Matrix k r ℝ) (lambda : r → ℝ)
    (Aperp : Matrix m s ℝ) (eta : s → ℝ)
    (hG : reducedRankHansenGEigenvectors Xtilde Ytilde lambda G)
    (hGOpt : reducedRankConcentratedObjectiveMaximizer Xtilde Ytilde G)
    (hAperp : reducedRankHansenAperpEigenvectors Etilde Ytilde eta Aperp)
    (hAperpOpt : reducedRankAperpObjectiveMinimizer Etilde Ytilde Aperp) :
    ReducedRankHansenSpectralDualityCertificate
      Xtilde Ytilde Etilde G lambda Aperp eta :=
  (ReducedRankHansenDetProductMinMaxCertificate.of_objective_extrema
    Xtilde Ytilde Etilde G lambda Aperp eta hG hGOpt hAperp hAperpOpt).to_spectralDualityCertificate

omit [DecidableEq n] in
/-- Build Hansen's spectral-duality certificate from generic generalized-pencil
product bounds for the two Hansen pencils. -/
theorem ReducedRankHansenSpectralDualityCertificate.of_generalized_product_bounds
    (Xtilde : Matrix n k ℝ) (Ytilde Etilde : Matrix n m ℝ)
    (G : Matrix k r ℝ) (lambda : r → ℝ)
    (Aperp : Matrix m s ℝ) (eta : s → ℝ)
    (hG : reducedRankHansenGEigenvectors Xtilde Ytilde lambda G)
    (hGNorm : reducedRankGNormalized Xtilde G)
    (hGBound : generalizedEigenDetProductUpperBound
      (reducedRankGPencilA Xtilde Ytilde) (reducedRankGPencilB Xtilde) lambda)
    (hAperp : reducedRankHansenAperpEigenvectors Etilde Ytilde eta Aperp)
    (hAperpNorm : reducedRankAperpNormalized Ytilde Aperp)
    (hAperpBound : generalizedEigenDetProductLowerBound
      (reducedRankAperpPencilA Etilde) (reducedRankAperpPencilB Ytilde) eta) :
    ReducedRankHansenSpectralDualityCertificate
      Xtilde Ytilde Etilde G lambda Aperp eta :=
  (ReducedRankHansenDetProductMinMaxCertificate.of_generalized_product_bounds
    Xtilde Ytilde Etilde G lambda Aperp eta
    hG hGNorm hGBound hAperp hAperpNorm hAperpBound).to_spectralDualityCertificate

/-- Build Hansen's spectral-duality certificate from the faithful whitened PSD
leading/trailing determinant-extrema surface. -/
theorem ReducedRankHansenSpectralDualityCertificate.of_whitened_psd_leading_trailing
    (Xtilde : Matrix n k ℝ) (Ytilde Etilde : Matrix n m ℝ)
    (G : Matrix k r ℝ) (lambda : r → ℝ)
    (Aperp : Matrix m s ℝ) (eta : s → ℝ)
    (R : Matrix n n ℝ) (G0 : Matrix n r ℝ) (A0 : Matrix n s ℝ)
    (hG : reducedRankHansenGEigenvectors Xtilde Ytilde lambda G)
    (hGNorm : reducedRankGNormalized Xtilde G)
    (hAperp : reducedRankHansenAperpEigenvectors Etilde Ytilde eta Aperp)
    (hAperpNorm : reducedRankAperpNormalized Ytilde Aperp)
    (hWhite : ReducedRankHansenWhitenedPSDLeadingTrailingCertificate
      Ytilde Etilde lambda eta R G0 A0) :
    ReducedRankHansenSpectralDualityCertificate
      Xtilde Ytilde Etilde G lambda Aperp eta :=
  (ReducedRankHansenDetProductMinMaxCertificate.of_whitened_psd_leading_trailing
    Xtilde Ytilde Etilde G lambda Aperp eta R G0 A0
    hG hGNorm hAperp hAperpNorm hWhite).to_spectralDualityCertificate

/-- Build Hansen's spectral-duality certificate for the actual residualized
Theorem 11.7 matrices from the ordinary whitened PSD leading/trailing
determinant-extrema inputs.

The concrete residual factor is fixed to `M_[X,Z]`, so the only remaining
spectral premise is the ordinary identity-denominator determinant theorem for
the two positive semidefinite whitened matrices. -/
theorem ReducedRankHansenSpectralDualityCertificate.of_residualized_whitened_psd_leading_trailing
    (Z : Matrix n ell ℝ) (X : Matrix n k ℝ) (Y : Matrix n m ℝ)
    (G : Matrix k r ℝ) (lambda : r → ℝ)
    (Aperp : Matrix m s ℝ) (eta : s → ℝ)
    (G0 : Matrix n r ℝ) (A0 : Matrix n s ℝ)
    [DecidableEq k] [Invertible (Zᵀ * Z)]
    [Invertible ((Matrix.fromCols X Z)ᵀ * Matrix.fromCols X Z)]
    (hG : reducedRankHansenGEigenvectors
      (reducedRankTildeX Z X) (reducedRankTildeY Z Y) lambda G)
    (hGNorm : reducedRankGNormalized (reducedRankTildeX Z X) G)
    (hAperp : reducedRankHansenAperpEigenvectors
      (reducedRankTildeE X Z Y) (reducedRankTildeY Z Y) eta Aperp)
    (hAperpNorm : reducedRankAperpNormalized (reducedRankTildeY Z Y) Aperp)
    (hG0 : generalizedEigenvectorColumns
      (reducedRankGWhitenedProjection (reducedRankTildeY Z Y))
      (1 : Matrix n n ℝ) lambda G0)
    (hG0Norm : G0ᵀ * G0 = 1)
    (hG0Max : ∀ H : Matrix n r ℝ, Hᵀ * H = 1 →
      (Hᵀ * reducedRankGWhitenedProjection (reducedRankTildeY Z Y) * H).det ≤
        (G0ᵀ * reducedRankGWhitenedProjection (reducedRankTildeY Z Y) * G0).det)
    (hA0 : generalizedEigenvectorColumns
      (reducedRankAperpResidualWhitenedMatrix (reducedRankAperpResidualFactor X Z))
      (1 : Matrix n n ℝ) eta A0)
    (hA0Norm : A0ᵀ * A0 = 1)
    (hA0Min : ∀ H : Matrix n s ℝ, Hᵀ * H = 1 →
      (A0ᵀ * reducedRankAperpResidualWhitenedMatrix
          (reducedRankAperpResidualFactor X Z) * A0).det ≤
        (Hᵀ * reducedRankAperpResidualWhitenedMatrix
          (reducedRankAperpResidualFactor X Z) * H).det) :
    ReducedRankHansenSpectralDualityCertificate
      (reducedRankTildeX Z X) (reducedRankTildeY Z Y) (reducedRankTildeE X Z Y)
      G lambda Aperp eta :=
  (ReducedRankHansenDetProductMinMaxCertificate.of_residualized_whitened_psd_leading_trailing
    Z X Y G lambda Aperp eta G0 A0
    hG hGNorm hAperp hAperpNorm
    hG0 hG0Norm hG0Max hA0 hA0Norm hA0Min).to_spectralDualityCertificate

omit [DecidableEq n] in
/-- The G component of the spectral-duality certificate gives Hansen's
concentrated-objective optimizer. -/
theorem ReducedRankHansenSpectralDualityCertificate.g_objectiveMaximizer
    {Xtilde : Matrix n k ℝ} {Ytilde Etilde : Matrix n m ℝ}
    {G : Matrix k r ℝ} {lambda : r → ℝ}
    {Aperp : Matrix m s ℝ} {eta : s → ℝ}
    (h : ReducedRankHansenSpectralDualityCertificate
      Xtilde Ytilde Etilde G lambda Aperp eta) :
    reducedRankConcentratedObjectiveMaximizer Xtilde Ytilde G :=
  reducedRankConcentratedObjectiveMaximizer_of_compressed_det_bound
    Xtilde Ytilde lambda G h.g_eigenvectors h.g_normalized h.g_det_bound

omit [DecidableEq n] in
/-- The `A⊥` component of the spectral-duality certificate gives Hansen's dual
determinant minimizer. -/
theorem ReducedRankHansenSpectralDualityCertificate.aperp_objectiveMinimizer
    {Xtilde : Matrix n k ℝ} {Ytilde Etilde : Matrix n m ℝ}
    {G : Matrix k r ℝ} {lambda : r → ℝ}
    {Aperp : Matrix m s ℝ} {eta : s → ℝ}
    (h : ReducedRankHansenSpectralDualityCertificate
      Xtilde Ytilde Etilde G lambda Aperp eta) :
    reducedRankAperpObjectiveMinimizer Etilde Ytilde Aperp :=
  reducedRankAperpObjectiveMinimizer_of_compressed_det_bound
    Etilde Ytilde eta Aperp h.aperp_eigenvectors h.aperp_normalized h.aperp_det_bound

omit [DecidableEq n] in
/-- Build Hansen's spectral-duality certificate from the natural compressed
determinant extrema for the selected `G` and `A⊥` subspaces.

This is the reusable bridge for Theorem 11.7: the remaining spectral argument
can prove determinant maximality/minimality of the selected subspaces, while
the generalized-eigenvector equations and normalizations here convert those
determinant extrema into Hansen's literal product variational bounds. -/
theorem ReducedRankHansenSpectralDualityCertificate.of_selected_compressedDet_extrema
    (Xtilde : Matrix n k ℝ) (Ytilde Etilde : Matrix n m ℝ)
    (G : Matrix k r ℝ) (lambda : r → ℝ)
    (Aperp : Matrix m s ℝ) (eta : s → ℝ)
    (hG : reducedRankHansenGEigenvectors Xtilde Ytilde lambda G)
    (hGNorm : reducedRankGNormalized Xtilde G)
    (hGMax : ∀ H : Matrix k r ℝ, reducedRankGNormalized Xtilde H →
      (Hᵀ * reducedRankGPencilA Xtilde Ytilde * H).det ≤
        (Gᵀ * reducedRankGPencilA Xtilde Ytilde * G).det)
    (hAperp : reducedRankHansenAperpEigenvectors Etilde Ytilde eta Aperp)
    (hAperpNorm : reducedRankAperpNormalized Ytilde Aperp)
    (hAperpMin : ∀ H : Matrix m s ℝ, reducedRankAperpNormalized Ytilde H →
      (Aperpᵀ * reducedRankAperpPencilA Etilde * Aperp).det ≤
        (Hᵀ * reducedRankAperpPencilA Etilde * H).det) :
    ReducedRankHansenSpectralDualityCertificate
      Xtilde Ytilde Etilde G lambda Aperp eta where
  g_eigenvectors := hG
  g_normalized := hGNorm
  g_det_bound :=
    reducedRankGDetVariationalBound_of_selected_compressedDet_maximal
      Xtilde Ytilde lambda G hG hGNorm hGMax
  aperp_eigenvectors := hAperp
  aperp_normalized := hAperpNorm
  aperp_det_bound :=
    reducedRankAperpDetVariationalBound_of_selected_compressedDet_minimal
      Etilde Ytilde eta Aperp hAperp hAperpNorm hAperpMin

/-- Objective-extrema compatibility certificate for Hansen's final
smallest-root summary.

The selected `G` columns maximize Hansen's concentrated determinant objective,
while the selected `A⊥` columns minimize the residual-pencil determinant
objective. That second field is not equation (11.21) and is not an MLE
condition. Canonical theorem-facing code uses the max/max certificate stack. -/
structure ReducedRankHansenObjectiveExtremaCertificate
    (Xtilde : Matrix n k ℝ) (Ytilde Etilde : Matrix n m ℝ)
    (G : Matrix k r ℝ) (lambda : r → ℝ)
    (Aperp : Matrix m s ℝ) (eta : s → ℝ) : Prop where
  g_eigenvectors : reducedRankHansenGEigenvectors Xtilde Ytilde lambda G
  g_objective_maximizer : reducedRankConcentratedObjectiveMaximizer Xtilde Ytilde G
  aperp_eigenvectors : reducedRankHansenAperpEigenvectors Etilde Ytilde eta Aperp
  aperp_objective_minimizer : reducedRankAperpObjectiveMinimizer Etilde Ytilde Aperp

omit [DecidableEq n] in
/-- Objective extrema imply the determinant/product min-max certificate used
by the spectral-duality layer. -/
theorem ReducedRankHansenObjectiveExtremaCertificate.to_detProductMinMaxCertificate
    {Xtilde : Matrix n k ℝ} {Ytilde Etilde : Matrix n m ℝ}
    {G : Matrix k r ℝ} {lambda : r → ℝ}
    {Aperp : Matrix m s ℝ} {eta : s → ℝ}
    (h : ReducedRankHansenObjectiveExtremaCertificate
      Xtilde Ytilde Etilde G lambda Aperp eta) :
    ReducedRankHansenDetProductMinMaxCertificate
      Xtilde Ytilde Etilde G lambda Aperp eta :=
  ReducedRankHansenDetProductMinMaxCertificate.of_objective_extrema
    Xtilde Ytilde Etilde G lambda Aperp eta
    h.g_eigenvectors h.g_objective_maximizer
    h.aperp_eigenvectors h.aperp_objective_minimizer

omit [DecidableEq n] in
/-- Objective extrema imply Hansen's spectral-duality certificate. -/
theorem ReducedRankHansenObjectiveExtremaCertificate.to_spectralDualityCertificate
    {Xtilde : Matrix n k ℝ} {Ytilde Etilde : Matrix n m ℝ}
    {G : Matrix k r ℝ} {lambda : r → ℝ}
    {Aperp : Matrix m s ℝ} {eta : s → ℝ}
    (h : ReducedRankHansenObjectiveExtremaCertificate
      Xtilde Ytilde Etilde G lambda Aperp eta) :
    ReducedRankHansenSpectralDualityCertificate
      Xtilde Ytilde Etilde G lambda Aperp eta :=
  h.to_detProductMinMaxCertificate.to_spectralDualityCertificate

omit [DecidableEq n] in
/-- Ordered generalized-eigenvalue determinant/product min-max certificates
also supply the objective-extrema certificate. -/
theorem ReducedRankHansenObjectiveExtremaCertificate.of_detProductMinMaxCertificate
    {Xtilde : Matrix n k ℝ} {Ytilde Etilde : Matrix n m ℝ}
    {G : Matrix k r ℝ} {lambda : r → ℝ}
    {Aperp : Matrix m s ℝ} {eta : s → ℝ}
    (h : ReducedRankHansenDetProductMinMaxCertificate
      Xtilde Ytilde Etilde G lambda Aperp eta) :
    ReducedRankHansenObjectiveExtremaCertificate
      Xtilde Ytilde Etilde G lambda Aperp eta where
  g_eigenvectors := h.g_max.eigenvectors
  g_objective_maximizer := h.g_objectiveMaximizer
  aperp_eigenvectors := h.aperp_min.eigenvectors
  aperp_objective_minimizer := h.aperp_objectiveMinimizer

omit [DecidableEq n] in
/-- The raw Hansen ordered min-max surface implies the spectral-duality
certificate used by the theorem-facing endpoint. -/
theorem ReducedRankHansenOrderedGeneralizedEigenMinMaxCertificate.to_spectralDualityCertificate
    {Xtilde : Matrix n k ℝ} {Ytilde Etilde : Matrix n m ℝ}
    {G : Matrix k r ℝ} {lambda : r → ℝ}
    {Aperp : Matrix m s ℝ} {eta : s → ℝ}
    (h : ReducedRankHansenOrderedGeneralizedEigenMinMaxCertificate
      Xtilde Ytilde Etilde G lambda Aperp eta) :
    ReducedRankHansenSpectralDualityCertificate
      Xtilde Ytilde Etilde G lambda Aperp eta :=
  h.to_detProductMinMaxCertificate.to_spectralDualityCertificate

omit [DecidableEq n] in
/-- The raw Hansen ordered min-max surface implies the objective-extrema
certificate consumed by the normal-likelihood MLE endpoint. -/
theorem
    ReducedRankHansenOrderedGeneralizedEigenMinMaxCertificate.to_objectiveExtremaCertificate
    {Xtilde : Matrix n k ℝ} {Ytilde Etilde : Matrix n m ℝ}
    {G : Matrix k r ℝ} {lambda : r → ℝ}
    {Aperp : Matrix m s ℝ} {eta : s → ℝ}
    (h : ReducedRankHansenOrderedGeneralizedEigenMinMaxCertificate
      Xtilde Ytilde Etilde G lambda Aperp eta) :
    ReducedRankHansenObjectiveExtremaCertificate
      Xtilde Ytilde Etilde G lambda Aperp eta :=
  ReducedRankHansenObjectiveExtremaCertificate.of_detProductMinMaxCertificate
    h.to_detProductMinMaxCertificate

omit [DecidableEq n] in
/-- Selected compressed-determinant extrema supply the objective-extrema
certificate for Hansen's two reduced-rank pencils. -/
theorem ReducedRankHansenObjectiveExtremaCertificate.of_selected_compressedDet_extrema
    (Xtilde : Matrix n k ℝ) (Ytilde Etilde : Matrix n m ℝ)
    (G : Matrix k r ℝ) (lambda : r → ℝ)
    (Aperp : Matrix m s ℝ) (eta : s → ℝ)
    (hG : reducedRankHansenGEigenvectors Xtilde Ytilde lambda G)
    (hGNorm : reducedRankGNormalized Xtilde G)
    (hGMax :
      generalizedEigenSelectedCompressedDetMaximal
        (reducedRankGPencilA Xtilde Ytilde) (reducedRankGPencilB Xtilde) G)
    (hAperp : reducedRankHansenAperpEigenvectors Etilde Ytilde eta Aperp)
    (hAperpNorm : reducedRankAperpNormalized Ytilde Aperp)
    (hAperpMin :
      generalizedEigenSelectedCompressedDetMinimal
        (reducedRankAperpPencilA Etilde) (reducedRankAperpPencilB Ytilde) Aperp) :
    ReducedRankHansenObjectiveExtremaCertificate
      Xtilde Ytilde Etilde G lambda Aperp eta :=
  ReducedRankHansenObjectiveExtremaCertificate.of_detProductMinMaxCertificate
    (ReducedRankHansenDetProductMinMaxCertificate.of_selected_compressedDet_extrema
      Xtilde Ytilde Etilde G lambda Aperp eta
      hG hGNorm hGMax hAperp hAperpNorm hAperpMin)

omit [DecidableEq n] in
/-- Literal determinant/product variational bounds supply the objective-extrema
certificate for Hansen's two reduced-rank pencils. This is the normal-likelihood
surface obtained after the raw ordered generalized-eigenvalue theorem has
proved Hansen's two product inequalities. -/
theorem ReducedRankHansenObjectiveExtremaCertificate.of_product_variational_bounds
    (Xtilde : Matrix n k ℝ) (Ytilde Etilde : Matrix n m ℝ)
    (G : Matrix k r ℝ) (lambda : r → ℝ)
    (Aperp : Matrix m s ℝ) (eta : s → ℝ)
    (hG : reducedRankHansenGEigenvectors Xtilde Ytilde lambda G)
    (hGNorm : reducedRankGNormalized Xtilde G)
    (hGBound : reducedRankGDetVariationalBound Xtilde Ytilde lambda)
    (hAperp : reducedRankHansenAperpEigenvectors Etilde Ytilde eta Aperp)
    (hAperpNorm : reducedRankAperpNormalized Ytilde Aperp)
    (hAperpBound : reducedRankAperpDetVariationalBound Etilde Ytilde eta) :
    ReducedRankHansenObjectiveExtremaCertificate
      Xtilde Ytilde Etilde G lambda Aperp eta :=
  ReducedRankHansenObjectiveExtremaCertificate.of_detProductMinMaxCertificate
    (ReducedRankHansenDetProductMinMaxCertificate.of_product_variational_bounds
      Xtilde Ytilde Etilde G lambda Aperp eta
      hG hGNorm hGBound hAperp hAperpNorm hAperpBound)

/-- Whitened PSD leading/trailing determinant-extrema supply the
normal-likelihood objective-extrema certificate for Hansen's two reduced-rank
pencils. -/
theorem ReducedRankHansenObjectiveExtremaCertificate.of_whitened_psd_leading_trailing
    (Xtilde : Matrix n k ℝ) (Ytilde Etilde : Matrix n m ℝ)
    (G : Matrix k r ℝ) (lambda : r → ℝ)
    (Aperp : Matrix m s ℝ) (eta : s → ℝ)
    (R : Matrix n n ℝ) (G0 : Matrix n r ℝ) (A0 : Matrix n s ℝ)
    (hG : reducedRankHansenGEigenvectors Xtilde Ytilde lambda G)
    (hGNorm : reducedRankGNormalized Xtilde G)
    (hAperp : reducedRankHansenAperpEigenvectors Etilde Ytilde eta Aperp)
    (hAperpNorm : reducedRankAperpNormalized Ytilde Aperp)
    (hWhite : ReducedRankHansenWhitenedPSDLeadingTrailingCertificate
      Ytilde Etilde lambda eta R G0 A0) :
    ReducedRankHansenObjectiveExtremaCertificate
      Xtilde Ytilde Etilde G lambda Aperp eta :=
  ReducedRankHansenObjectiveExtremaCertificate.of_detProductMinMaxCertificate
    (ReducedRankHansenDetProductMinMaxCertificate.of_whitened_psd_leading_trailing
      Xtilde Ytilde Etilde G lambda Aperp eta R G0 A0
      hG hGNorm hAperp hAperpNorm hWhite)

omit [DecidableEq n] in
/-- Generic generalized-pencil product bounds supply the objective-extrema
certificate for Hansen's two reduced-rank pencils. -/
theorem ReducedRankHansenObjectiveExtremaCertificate.of_generalized_product_bounds
    (Xtilde : Matrix n k ℝ) (Ytilde Etilde : Matrix n m ℝ)
    (G : Matrix k r ℝ) (lambda : r → ℝ)
    (Aperp : Matrix m s ℝ) (eta : s → ℝ)
    (hG : reducedRankHansenGEigenvectors Xtilde Ytilde lambda G)
    (hGNorm : reducedRankGNormalized Xtilde G)
    (hGBound : generalizedEigenDetProductUpperBound
      (reducedRankGPencilA Xtilde Ytilde) (reducedRankGPencilB Xtilde) lambda)
    (hAperp : reducedRankHansenAperpEigenvectors Etilde Ytilde eta Aperp)
    (hAperpNorm : reducedRankAperpNormalized Ytilde Aperp)
    (hAperpBound : generalizedEigenDetProductLowerBound
      (reducedRankAperpPencilA Etilde) (reducedRankAperpPencilB Ytilde) eta) :
    ReducedRankHansenObjectiveExtremaCertificate
      Xtilde Ytilde Etilde G lambda Aperp eta :=
  ReducedRankHansenObjectiveExtremaCertificate.of_detProductMinMaxCertificate
    (ReducedRankHansenDetProductMinMaxCertificate.of_generalized_product_bounds
      Xtilde Ytilde Etilde G lambda Aperp eta
      hG hGNorm hGBound hAperp hAperpNorm hAperpBound)

omit [DecidableEq n] in
/-- Generic generalized-pencil objective extrema supply Hansen's
objective-extrema certificate directly. -/
theorem ReducedRankHansenObjectiveExtremaCertificate.of_generalized_objective_extrema
    (Xtilde : Matrix n k ℝ) (Ytilde Etilde : Matrix n m ℝ)
    (G : Matrix k r ℝ) (lambda : r → ℝ)
    (Aperp : Matrix m s ℝ) (eta : s → ℝ)
    (hG : reducedRankHansenGEigenvectors Xtilde Ytilde lambda G)
    (hGOpt : generalizedEigenDetObjectiveMaximizer
      (reducedRankGPencilA Xtilde Ytilde) (reducedRankGPencilB Xtilde) G)
    (hAperp : reducedRankHansenAperpEigenvectors Etilde Ytilde eta Aperp)
    (hAperpOpt : generalizedEigenDetObjectiveMinimizer
      (reducedRankAperpPencilA Etilde) (reducedRankAperpPencilB Ytilde) Aperp) :
    ReducedRankHansenObjectiveExtremaCertificate
      Xtilde Ytilde Etilde G lambda Aperp eta :=
  ReducedRankHansenObjectiveExtremaCertificate.of_detProductMinMaxCertificate
    (ReducedRankHansenDetProductMinMaxCertificate.of_generalized_objective_extrema
      Xtilde Ytilde Etilde G lambda Aperp eta hG hGOpt hAperp hAperpOpt)

omit [DecidableEq n] in
/-- The G-side product variational bound derived from the objective-extrema
certificate. -/
theorem ReducedRankHansenObjectiveExtremaCertificate.g_det_bound
    {Xtilde : Matrix n k ℝ} {Ytilde Etilde : Matrix n m ℝ}
    {G : Matrix k r ℝ} {lambda : r → ℝ}
    {Aperp : Matrix m s ℝ} {eta : s → ℝ}
    (h : ReducedRankHansenObjectiveExtremaCertificate
      Xtilde Ytilde Etilde G lambda Aperp eta) :
    reducedRankGDetVariationalBound Xtilde Ytilde lambda :=
  h.to_spectralDualityCertificate.g_det_bound

omit [DecidableEq n] in
/-- The `A⊥` product variational bound derived from the objective-extrema
certificate. -/
theorem ReducedRankHansenObjectiveExtremaCertificate.aperp_det_bound
    {Xtilde : Matrix n k ℝ} {Ytilde Etilde : Matrix n m ℝ}
    {G : Matrix k r ℝ} {lambda : r → ℝ}
    {Aperp : Matrix m s ℝ} {eta : s → ℝ}
    (h : ReducedRankHansenObjectiveExtremaCertificate
      Xtilde Ytilde Etilde G lambda Aperp eta) :
    reducedRankAperpDetVariationalBound Etilde Ytilde eta :=
  h.to_spectralDualityCertificate.aperp_det_bound

end SpectralDualityCertificate

section Recovery

variable [Fintype r] [DecidableEq r]

/-- Hansen's concentrated least-squares recovery
`Â(G) = Ỹ'X̃G (G'X̃'X̃G)⁻¹`. -/
noncomputable def reducedRankAhat
    (Xtilde : Matrix n k ℝ) (Ytilde : Matrix n m ℝ) (G : Matrix k r ℝ) :
    Matrix m r ℝ :=
  Ytildeᵀ * Xtilde * G * (Gᵀ * Xtildeᵀ * Xtilde * G)⁻¹

omit [DecidableEq n] [Fintype m] [DecidableEq m] in
/-- Under Hansen's normalization `G'X̃'X̃G = I`, the reduced-rank least-squares
recovery formula collapses to the textbook expression `Â = Ỹ'X̃G`. -/
theorem reducedRankAhat_eq_cross_of_normalized
    (Xtilde : Matrix n k ℝ) (Ytilde : Matrix n m ℝ) (G : Matrix k r ℝ)
    (hNorm : reducedRankGNormalized Xtilde G) :
    reducedRankAhat Xtilde Ytilde G = Ytildeᵀ * Xtilde * G := by
  unfold reducedRankAhat
  have hGram : Gᵀ * Xtildeᵀ * Xtilde * G = (1 : Matrix r r ℝ) := by
    simpa [reducedRankGNormalized, generalizedEigenvectorBNormalized,
      reducedRankGPencilB, Matrix.mul_assoc] using hNorm
  rw [hGram]
  simp

/-- Least-squares recovery of the unrestricted `Z` coefficients after fixing
`G` and `A`: regress the remaining outcome `Y - X G A'` on `Z`. -/
noncomputable def reducedRankChat
    (Z : Matrix n ell ℝ) (X : Matrix n k ℝ) (Y : Matrix n m ℝ)
    (G : Matrix k r ℝ) (Acoef : Matrix m r ℝ) : Matrix ell m ℝ :=
  (Zᵀ * Z)⁻¹ * Zᵀ * (Y - X * G * Acoefᵀ)

/-- Hansen's concentrated covariance recovery
`Σ̂(G) = n⁻¹(Ỹ'Ỹ - Ỹ'X̃G(G'X̃'X̃G)⁻¹G'X̃'Ỹ)`. -/
noncomputable def reducedRankSigmaHat
    (Xtilde : Matrix n k ℝ) (Ytilde : Matrix n m ℝ) (G : Matrix k r ℝ) :
    Matrix m m ℝ :=
  (Fintype.card n : ℝ)⁻¹ •
    (Ytildeᵀ * Ytilde -
      Ytildeᵀ * Xtilde * G * (Gᵀ * Xtildeᵀ * Xtilde * G)⁻¹ * Gᵀ * Xtildeᵀ * Ytilde)

omit [DecidableEq n] [Fintype m] [DecidableEq m] in
/-- Under Hansen's normalization `G'X̃'X̃G = I`, the concentrated covariance
formula collapses to the displayed cross-product subtraction
`n⁻¹(Ỹ'Ỹ - Ỹ'X̃GG'X̃'Ỹ)`. -/
theorem reducedRankSigmaHat_eq_cross_of_normalized
    (Xtilde : Matrix n k ℝ) (Ytilde : Matrix n m ℝ) (G : Matrix k r ℝ)
    (hNorm : reducedRankGNormalized Xtilde G) :
    reducedRankSigmaHat Xtilde Ytilde G =
      (Fintype.card n : ℝ)⁻¹ •
        (Ytildeᵀ * Ytilde - Ytildeᵀ * Xtilde * G * Gᵀ * Xtildeᵀ * Ytilde) := by
  unfold reducedRankSigmaHat
  have hGram : Gᵀ * Xtildeᵀ * Xtilde * G = (1 : Matrix r r ℝ) := by
    simpa [reducedRankGNormalized, generalizedEigenvectorBNormalized,
      reducedRankGPencilB, Matrix.mul_assoc] using hNorm
  rw [hGram]
  simp [Matrix.mul_assoc]

omit [DecidableEq n] [Fintype m] [DecidableEq m] in
/-- Under Hansen's normalization, the concentrated covariance formula is the
textbook cross-product subtraction `n⁻¹(Ỹ'Ỹ - ÂÂ')` with
`Â = Ỹ'X̃G`. -/
theorem reducedRankSigmaHat_eq_Ahat_mul_transpose_of_normalized
    (Xtilde : Matrix n k ℝ) (Ytilde : Matrix n m ℝ) (G : Matrix k r ℝ)
    (hNorm : reducedRankGNormalized Xtilde G) :
    reducedRankSigmaHat Xtilde Ytilde G =
      (Fintype.card n : ℝ)⁻¹ •
        (Ytildeᵀ * Ytilde -
          (Ytildeᵀ * Xtilde * G) * (Ytildeᵀ * Xtilde * G)ᵀ) := by
  rw [reducedRankSigmaHat_eq_cross_of_normalized Xtilde Ytilde G hNorm]
  congr 1
  congr 1
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose]
  simp [Matrix.mul_assoc]

/-- Hansen's dual eigenvector relation between the selected `G` roots and the
complementary `A⊥` directions.

In the textbook notation this is
`W = (Ỹ'Ỹ)⁻¹ Â Λ`, equivalently `Ỹ'Ỹ W = Â Λ`, where `W` is the block of
dual generalized eigenvectors associated with the selected `G` roots. -/
def reducedRankDualEigenvectorRelation
    (Xtilde : Matrix n k ℝ) (Ytilde : Matrix n m ℝ)
    (G : Matrix k r ℝ) (W : Matrix m r ℝ) (Lambda : Matrix r r ℝ) : Prop :=
  reducedRankAhat Xtilde Ytilde G * Lambda = reducedRankAperpPencilB Ytilde * W

/-- Canonical dual block obtained by solving Hansen's displayed relation with
the nonsingular inverse of `Ỹ'Ỹ`. -/
noncomputable def reducedRankDualEigenvectorBlock
    (Xtilde : Matrix n k ℝ) (Ytilde : Matrix n m ℝ)
    (G : Matrix k r ℝ) (Lambda : Matrix r r ℝ) : Matrix m r ℝ :=
  (reducedRankAperpPencilB Ytilde)⁻¹ *
    reducedRankAhat Xtilde Ytilde G * Lambda

omit [DecidableEq n] in
/-- The canonical dual block with identity scaling lies in the complementary
residual-pencil eigenspaces with roots `1 - lambda`.

The exact complement identity states
`Etilde'Etilde = Ytilde'Ytilde - Ytilde'Xtilde
  (Xtilde'Xtilde)⁻¹ Xtilde'Ytilde`. Under the two positive-definite Grams,
Hansen's normalized G-eigenvector equations transport through the canonical
dual map. Nonzero selected G roots are needed only to prove that the transported
columns are nonzero generalized eigenvectors. Repeated selected roots are
allowed; no cross-orthogonality or simultaneous eigenspace membership is
assumed. -/
theorem reducedRankDualEigenvectorBlock_one_aperpEigenvectors_of_complement
    [DecidableEq k]
    (Xtilde : Matrix n k ℝ) (Ytilde Etilde : Matrix n m ℝ)
    (G : Matrix k r ℝ) (lambda : r → ℝ)
    (hXGram : (Xtildeᵀ * Xtilde).PosDef)
    (hYGram : (Ytildeᵀ * Ytilde).PosDef)
    (hComplement :
      reducedRankAperpPencilA Etilde =
        reducedRankAperpPencilB Ytilde -
          (Ytildeᵀ * Xtilde) * (reducedRankGPencilB Xtilde)⁻¹ *
            (Xtildeᵀ * Ytilde))
    (hG : reducedRankHansenGEigenvectors Xtilde Ytilde lambda G)
    (hNorm : reducedRankGNormalized Xtilde G)
    (hLambda : ∀ j, lambda j ≠ 0) :
    reducedRankHansenAperpEigenvectors Etilde Ytilde
      (fun j => 1 - lambda j)
      (reducedRankDualEigenvectorBlock Xtilde Ytilde G 1) := by
  let Q : Matrix k k ℝ := reducedRankGPencilB Xtilde
  let S : Matrix m m ℝ := reducedRankAperpPencilB Ytilde
  let W : Matrix m r ℝ := reducedRankDualEigenvectorBlock Xtilde Ytilde G 1
  have hQPos : Q.PosDef := by
    simpa [Q, reducedRankGPencilB] using hXGram
  have hQdet : IsUnit Q.det :=
    (Matrix.isUnit_iff_isUnit_det Q).mp hQPos.isUnit
  have hQInv : Q⁻¹ * Q = 1 := Matrix.nonsing_inv_mul Q hQdet
  have hSPos : S.PosDef := by
    simpa [S, reducedRankAperpPencilB] using hYGram
  have hSdet : IsUnit S.det :=
    (Matrix.isUnit_iff_isUnit_det S).mp hSPos.isUnit
  have hSW : S * W = Ytildeᵀ * Xtilde * G := by
    change S * (S⁻¹ * reducedRankAhat Xtilde Ytilde G * (1 : Matrix r r ℝ)) =
      Ytildeᵀ * Xtilde * G
    rw [Matrix.mul_assoc S⁻¹ (reducedRankAhat Xtilde Ytilde G) 1,
      ← Matrix.mul_assoc S S⁻¹ (reducedRankAhat Xtilde Ytilde G * 1),
      Matrix.mul_nonsing_inv S hSdet, Matrix.one_mul, Matrix.mul_one,
      reducedRankAhat_eq_cross_of_normalized Xtilde Ytilde G hNorm]
  have hGEq :
      reducedRankGPencilA Xtilde Ytilde * G =
        Q * G * Matrix.diagonal lambda := by
    simpa [Q] using
      generalizedEigenvectorColumns_mul_eq_mul_diagonal
        (reducedRankGPencilA Xtilde Ytilde) (reducedRankGPencilB Xtilde)
        lambda G hG
  have hXTYW :
      (Xtildeᵀ * Ytilde) * W = Q * G * Matrix.diagonal lambda := by
    calc
      (Xtildeᵀ * Ytilde) * W =
          (Xtildeᵀ * Ytilde) *
            ((Ytildeᵀ * Ytilde)⁻¹ * (Ytildeᵀ * Xtilde * G)) := by
              rw [show W = (Ytildeᵀ * Ytilde)⁻¹ *
                (Ytildeᵀ * Xtilde * G) by
                  simp [W, reducedRankDualEigenvectorBlock,
                    reducedRankAperpPencilB,
                    reducedRankAhat_eq_cross_of_normalized Xtilde Ytilde G hNorm,
                    Matrix.mul_assoc]]
      _ = reducedRankGPencilA Xtilde Ytilde * G := by
            simp [reducedRankGPencilA, Matrix.mul_assoc]
      _ = Q * G * Matrix.diagonal lambda := hGEq
  have hResidualTerm :
      ((Ytildeᵀ * Xtilde) * Q⁻¹ * (Xtildeᵀ * Ytilde)) * W =
        S * W * Matrix.diagonal lambda := by
    calc
      ((Ytildeᵀ * Xtilde) * Q⁻¹ * (Xtildeᵀ * Ytilde)) * W =
          (Ytildeᵀ * Xtilde) * Q⁻¹ * ((Xtildeᵀ * Ytilde) * W) := by
            simp [Matrix.mul_assoc]
      _ = (Ytildeᵀ * Xtilde) * Q⁻¹ *
          (Q * G * Matrix.diagonal lambda) := by rw [hXTYW]
      _ = (Ytildeᵀ * Xtilde) * ((Q⁻¹ * Q) * G) *
          Matrix.diagonal lambda := by simp [Matrix.mul_assoc]
      _ = (Ytildeᵀ * Xtilde) * G * Matrix.diagonal lambda := by
            rw [hQInv]
            simp
      _ = S * W * Matrix.diagonal lambda := by rw [hSW]
  have hWEq :
      reducedRankAperpPencilA Etilde * W =
        S * W * Matrix.diagonal (fun j => 1 - lambda j) := by
    calc
      reducedRankAperpPencilA Etilde * W =
          (S - (Ytildeᵀ * Xtilde) * Q⁻¹ * (Xtildeᵀ * Ytilde)) * W := by
            rw [hComplement]
      _ = S * W -
          ((Ytildeᵀ * Xtilde) * Q⁻¹ * (Xtildeᵀ * Ytilde)) * W := by
            rw [Matrix.sub_mul]
      _ = S * W - S * W * Matrix.diagonal lambda := by rw [hResidualTerm]
      _ = S * W * ((1 : Matrix r r ℝ) - Matrix.diagonal lambda) := by
            rw [Matrix.mul_sub, Matrix.mul_one]
      _ = S * W * Matrix.diagonal (fun j => 1 - lambda j) := by
            congr 1
            ext i j
            by_cases hij : i = j
            · subst j
              simp
            · simp [hij]
  change generalizedEigenvectorColumns
    (reducedRankAperpPencilA Etilde) (reducedRankAperpPencilB Ytilde)
    (fun j => 1 - lambda j) W
  intro j
  constructor
  · intro hWzero
    have hWcol : ∀ i, W i j = 0 := fun i => by
      simpa using congrFun hWzero i
    have hScaledCol : ∀ i, (Q * G * Matrix.diagonal lambda) i j = 0 := by
      intro i
      rw [← hXTYW]
      simp [Matrix.mul_apply, hWcol]
    have hQGcol : ∀ i, (Q * G) i j = 0 := by
      intro i
      have hi := hScaledCol i
      have hi' : (Q * G) i j * lambda j = 0 := by
        simpa [Matrix.mul_apply, Matrix.diagonal] using hi
      exact (mul_eq_zero.mp hi').resolve_right (hLambda j)
    have hQGvec : Q *ᵥ (fun a => G a j) = 0 := by
      ext i
      simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using hQGcol i
    have hpos := hQPos.dotProduct_mulVec_pos (hG j).1
    rw [hQGvec] at hpos
    simp at hpos
  · ext i
    have hentry := congrArg (fun M : Matrix m r ℝ => M i j) hWEq
    simpa [S, Matrix.mul_apply, Matrix.mulVec, dotProduct,
      Matrix.diagonal, mul_comm] using hentry

omit [DecidableEq n] in
/-- Positive definiteness of the residualized outcome Gram proves Hansen's
displayed dual relation for the canonical dual block.

Thus the dual relation itself is not an additional premise under the regular
full-Gram assumptions. The remaining content is identifying this block in the
appropriate residual-pencil eigenspace. -/
theorem reducedRankDualEigenvectorRelation_canonical_of_yGram_posDef
    (Xtilde : Matrix n k ℝ) (Ytilde : Matrix n m ℝ)
    (G : Matrix k r ℝ) (Lambda : Matrix r r ℝ)
    (hYGram : (Ytildeᵀ * Ytilde).PosDef) :
    reducedRankDualEigenvectorRelation Xtilde Ytilde G
      (reducedRankDualEigenvectorBlock Xtilde Ytilde G Lambda) Lambda := by
  let S : Matrix m m ℝ := reducedRankAperpPencilB Ytilde
  have hSPos : S.PosDef := by
    simpa [S, reducedRankAperpPencilB] using hYGram
  have hSdet : IsUnit S.det :=
    (Matrix.isUnit_iff_isUnit_det S).mp hSPos.isUnit
  unfold reducedRankDualEigenvectorRelation reducedRankDualEigenvectorBlock
  change reducedRankAhat Xtilde Ytilde G * Lambda =
    S * (S⁻¹ * reducedRankAhat Xtilde Ytilde G * Lambda)
  rw [Matrix.mul_assoc S⁻¹ (reducedRankAhat Xtilde Ytilde G) Lambda,
    ← Matrix.mul_assoc S S⁻¹ (reducedRankAhat Xtilde Ytilde G * Lambda),
    Matrix.mul_nonsing_inv S hSdet, Matrix.one_mul]

/-- Raw residualized full-Gram specialization of
`reducedRankDualEigenvectorRelation_canonical_of_yGram_posDef`.

Full column rank of `[Y,Z]` and `Z` supplies the only inverse needed to
construct Hansen's canonical dual block. -/
theorem reducedRankDualEigenvectorRelation_canonical_residualized_of_full_gram
    (Z : Matrix n ell ℝ) (X : Matrix n k ℝ) (Y : Matrix n m ℝ)
    (G : Matrix k r ℝ) (Lambda : Matrix r r ℝ)
    [Invertible (Zᵀ * Z)]
    [Invertible ((Matrix.fromCols Y Z)ᵀ * Matrix.fromCols Y Z)] :
    reducedRankDualEigenvectorRelation
      (reducedRankTildeX Z X) (reducedRankTildeY Z Y) G
      (reducedRankDualEigenvectorBlock
        (reducedRankTildeX Z X) (reducedRankTildeY Z Y) G Lambda)
      Lambda :=
  reducedRankDualEigenvectorRelation_canonical_of_yGram_posDef
    (reducedRankTildeX Z X) (reducedRankTildeY Z Y) G Lambda
    (reducedRankTildeY_gram_posDef Z Y)

/-- Hansen's `Ỹ'Ỹ`-orthogonality between the estimated `A⊥` block and the dual
selected-eigenvector block `W`. -/
def reducedRankAperpYOrthogonal
    (Ytilde : Matrix n m ℝ) (Aperp : Matrix m s ℝ) (W : Matrix m r ℝ) : Prop :=
  Aperpᵀ * reducedRankAperpPencilB Ytilde * W = 0

omit [DecidableEq n] in
/-- Residual-pencil eigenblocks with disjoint roots are orthogonal in Hansen's
`Ỹ'Ỹ` metric. -/
theorem reducedRankAperpYOrthogonal_of_disjoint_eigenblocks
    [Fintype s] [DecidableEq s]
    (Etilde Ytilde : Matrix n m ℝ)
    (eta : s → ℝ) (Aperp : Matrix m s ℝ)
    (mu : r → ℝ) (W : Matrix m r ℝ)
    (hAperp : reducedRankHansenAperpEigenvectors Etilde Ytilde eta Aperp)
    (hW : reducedRankHansenAperpEigenvectors Etilde Ytilde mu W)
    (hDisjoint : ∀ i j, eta i ≠ mu j) :
    reducedRankAperpYOrthogonal Ytilde Aperp W := by
  exact generalizedEigenvectorColumns_crossGram_eq_zero_of_disjoint_roots
    (reducedRankAperpPencilA Etilde) (reducedRankAperpPencilB Ytilde)
    eta Aperp mu W
    (by simp [reducedRankAperpPencilA, Matrix.transpose_mul])
    (by simp [reducedRankAperpPencilB, Matrix.transpose_mul])
    hAperp hW hDisjoint

omit [DecidableEq n] [DecidableEq m] [Fintype r] [DecidableEq r] in
/-- Under a fixed-root span witness `X̃G = ỸC`, Hansen's dual orthogonality
`A⊥'Ỹ'ỸC = 0` is equivalent to the displayed cross-orthogonality
`A⊥'Ỹ'X̃G = 0`. -/
theorem reducedRankAperpYOrthogonal_iff_crossOrthogonal_of_span
    (Xtilde : Matrix n k ℝ) (Ytilde : Matrix n m ℝ)
    (G : Matrix k r ℝ) (Aperp : Matrix m s ℝ) (C : Matrix m r ℝ)
    (hSpan : Xtilde * G = Ytilde * C) :
    reducedRankAperpYOrthogonal Ytilde Aperp C ↔
      reducedRankAperpCrossOrthogonal Xtilde Ytilde G Aperp := by
  unfold reducedRankAperpYOrthogonal reducedRankAperpCrossOrthogonal
    reducedRankAperpPencilB
  rw [show Ytildeᵀ * Xtilde * G = Ytildeᵀ * Ytilde * C by
    calc
      Ytildeᵀ * Xtilde * G = Ytildeᵀ * (Xtilde * G) := by
        rw [Matrix.mul_assoc]
      _ = Ytildeᵀ * (Ytilde * C) := by
        rw [hSpan]
      _ = Ytildeᵀ * Ytilde * C := by
        rw [Matrix.mul_assoc]]
  rw [Matrix.mul_assoc]

omit [DecidableEq n] [DecidableEq m] in
/-- A fixed-root span certificate supplies Hansen's displayed dual relation.

In the projection-specialized fixed-root route, `Λ = I` and a span witness
`X̃G = ỸC` lets the dual block be chosen as `W = C`. Hansen's diagonal dual
relation then follows from the normalized recovery formula for `Â(G)`. -/
theorem reducedRankDualEigenvectorRelation_one_of_span
    (Xtilde : Matrix n k ℝ) (Ytilde : Matrix n m ℝ)
    (G : Matrix k r ℝ) (C : Matrix m r ℝ)
    (hNorm : reducedRankGNormalized Xtilde G)
    (hSpan : Xtilde * G = Ytilde * C) :
    reducedRankDualEigenvectorRelation Xtilde Ytilde G C
      (Matrix.diagonal (fun _ : r => (1 : ℝ))) := by
  unfold reducedRankDualEigenvectorRelation reducedRankAperpPencilB
  rw [Matrix.diagonal_one, Matrix.mul_one,
    reducedRankAhat_eq_cross_of_normalized Xtilde Ytilde G hNorm]
  calc
    Ytildeᵀ * Xtilde * G = Ytildeᵀ * (Xtilde * G) := by
      rw [Matrix.mul_assoc]
    _ = Ytildeᵀ * (Ytilde * C) := by
      rw [hSpan]
    _ = Ytildeᵀ * Ytilde * C := by
      rw [Matrix.mul_assoc]

omit [DecidableEq n] [DecidableEq m] in
/-- Pointwise nonzero selected generalized roots make Hansen's diagonal root
block explicitly right-invertible.

This is the selected-root nonsingularity bridge needed by Theorem 11.7's dual
relation when the displayed matrix `Λ` is the diagonal matrix of the selected
`G` roots. -/
theorem reducedRankSelectedRootDiagonal_mul_inv_eq_one
    (lambda : r → ℝ) (hLambda : ∀ j, lambda j ≠ 0) :
    Matrix.diagonal lambda * Matrix.diagonal (fun j => (lambda j)⁻¹) = 1 := by
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr with j
  exact mul_inv_cancel₀ (hLambda j)

omit [DecidableEq n] [DecidableEq m] [DecidableEq r] in
/-- A nonzero selected-root product supplies pointwise selected-root
nonsingularity. This is often the form produced by determinant/product
variational arguments. -/
theorem reducedRankSelectedRoots_nonzero_of_prod_ne_zero
    (lambda : r → ℝ) (hprod : (∏ j, lambda j) ≠ 0) :
    ∀ j, lambda j ≠ 0 := by
  intro j hj
  exact hprod (Finset.prod_eq_zero (Finset.mem_univ j) hj)

omit [DecidableEq n] [DecidableEq m] [DecidableEq r] [Fintype r] in
/-- In the one-selected-root case, nonsingularity of the unique selected root
is exactly pointwise selected-root nonsingularity. -/
theorem reducedRankSelectedRoots_nonzero_rankOne
    [Unique r] (lambda : r → ℝ) (hroot : lambda default ≠ 0) :
    ∀ j, lambda j ≠ 0 := by
  intro j
  simpa [Subsingleton.elim j default] using hroot

omit [DecidableEq n] [DecidableEq m] [DecidableEq r] in
/-- Positive selected generalized roots make Hansen's selected-root product
strictly positive. This is the concrete nonsingularity output usually produced
by a raw generalized-pencil construction of the selected leading block. -/
theorem reducedRankSelectedRootProduct_pos_of_pos
    (lambda : r → ℝ) (hLambda : ∀ j, 0 < lambda j) :
    0 < ∏ j, lambda j :=
  Finset.prod_pos fun j _ => hLambda j

omit [DecidableEq n] [DecidableEq m] [DecidableEq r] in
/-- Positive selected generalized roots make Hansen's selected-root product
nonzero. -/
theorem reducedRankSelectedRootProduct_ne_zero_of_pos
    (lambda : r → ℝ) (hLambda : ∀ j, 0 < lambda j) :
    (∏ j, lambda j) ≠ 0 :=
  ne_of_gt (reducedRankSelectedRootProduct_pos_of_pos lambda hLambda)

omit [DecidableEq n] [DecidableEq m] in
/-- Nonzero determinant of Hansen's diagonal selected-root matrix supplies
pointwise selected-root nonsingularity. -/
theorem reducedRankSelectedRoots_nonzero_of_diagonal_det_ne_zero
    (lambda : r → ℝ) (hdet : (Matrix.diagonal lambda).det ≠ 0) :
    ∀ j, lambda j ≠ 0 := by
  rw [Matrix.det_diagonal] at hdet
  exact reducedRankSelectedRoots_nonzero_of_prod_ne_zero lambda hdet

omit [DecidableEq n] [DecidableEq m] in
/-- Nonzero product of selected roots makes Hansen's diagonal selected-root
matrix nonsingular at the determinant level. -/
theorem reducedRankSelectedRootDiagonal_det_ne_zero
    (lambda : r → ℝ) (hprod : (∏ j, lambda j) ≠ 0) :
    (Matrix.diagonal lambda).det ≠ 0 := by
  rw [Matrix.det_diagonal]
  exact hprod

omit [DecidableEq n] [DecidableEq m] in
/-- Positive selected roots make Hansen's diagonal selected-root block
nonsingular at the determinant level. -/
theorem reducedRankSelectedRootDiagonal_det_ne_zero_of_pos
    (lambda : r → ℝ) (hLambda : ∀ j, 0 < lambda j) :
    (Matrix.diagonal lambda).det ≠ 0 :=
  reducedRankSelectedRootDiagonal_det_ne_zero lambda
    (reducedRankSelectedRootProduct_ne_zero_of_pos lambda hLambda)

omit [DecidableEq n] [DecidableEq m] in
/-- Product-nonzero version of
`reducedRankSelectedRootDiagonal_mul_inv_eq_one`. -/
theorem reducedRankSelectedRootDiagonal_mul_inv_eq_one_of_prod_ne_zero
    (lambda : r → ℝ) (hprod : (∏ j, lambda j) ≠ 0) :
    Matrix.diagonal lambda * Matrix.diagonal (fun j => (lambda j)⁻¹) = 1 :=
  reducedRankSelectedRootDiagonal_mul_inv_eq_one lambda
    (reducedRankSelectedRoots_nonzero_of_prod_ne_zero lambda hprod)

omit [DecidableEq n] [DecidableEq m] in
/-- Diagonal-determinant version of
`reducedRankSelectedRootDiagonal_mul_inv_eq_one`. -/
theorem reducedRankSelectedRootDiagonal_mul_inv_eq_one_of_diagonal_det_ne_zero
    (lambda : r → ℝ) (hdet : (Matrix.diagonal lambda).det ≠ 0) :
    Matrix.diagonal lambda * Matrix.diagonal (fun j => (lambda j)⁻¹) = 1 :=
  reducedRankSelectedRootDiagonal_mul_inv_eq_one lambda
    (reducedRankSelectedRoots_nonzero_of_diagonal_det_ne_zero lambda hdet)

omit [DecidableEq n] [DecidableEq m] in
/-- Positive-root version of
`reducedRankSelectedRootDiagonal_mul_inv_eq_one`. -/
theorem reducedRankSelectedRootDiagonal_mul_inv_eq_one_of_pos
    (lambda : r → ℝ) (hLambda : ∀ j, 0 < lambda j) :
    Matrix.diagonal lambda * Matrix.diagonal (fun j => (lambda j)⁻¹) = 1 :=
  reducedRankSelectedRootDiagonal_mul_inv_eq_one lambda
    fun j => ne_of_gt (hLambda j)

omit [DecidableEq n] [DecidableEq m] in
/-- Hansen Theorem 11.7 duality algebra: the displayed dual eigenvector
relation and `Ỹ'Ỹ`-orthogonality imply `A⊥' Â = 0`.

This is the exact algebraic step in the proof after the dual generalized
eigenvalue theorem supplies `W = (Ỹ'Ỹ)⁻¹ Â Λ` and the selected eigenvalue
block `Λ` is nonsingular. -/
theorem reducedRankAperpAhat_orthogonal_of_dual_relation
    (Xtilde : Matrix n k ℝ) (Ytilde : Matrix n m ℝ)
    (G : Matrix k r ℝ) (Aperp : Matrix m s ℝ) (W : Matrix m r ℝ)
    (Lambda LambdaInv : Matrix r r ℝ)
    (hDual : reducedRankDualEigenvectorRelation Xtilde Ytilde G W Lambda)
    (hOrth : reducedRankAperpYOrthogonal Ytilde Aperp W)
    (hLambdaInv : Lambda * LambdaInv = 1) :
    Aperpᵀ * reducedRankAhat Xtilde Ytilde G = 0 := by
  let M : Matrix s r ℝ := Aperpᵀ * reducedRankAhat Xtilde Ytilde G
  change M = 0
  have hTimesLambda :
      M * Lambda = 0 := by
    change (Aperpᵀ * reducedRankAhat Xtilde Ytilde G) * Lambda = 0
    calc
      (Aperpᵀ * reducedRankAhat Xtilde Ytilde G) * Lambda =
          Aperpᵀ * (reducedRankAhat Xtilde Ytilde G * Lambda) := by
        rw [Matrix.mul_assoc]
      _ = Aperpᵀ * (reducedRankAperpPencilB Ytilde * W) := by
        rw [hDual]
      _ = Aperpᵀ * reducedRankAperpPencilB Ytilde * W := by
        rw [Matrix.mul_assoc]
      _ = 0 := hOrth
  calc
    M = M * (Lambda * LambdaInv) := by
      rw [hLambdaInv, Matrix.mul_one]
    _ = (M * Lambda) * LambdaInv := by
      exact (Matrix.mul_assoc M Lambda LambdaInv).symm
    _ = 0 := by
      rw [hTimesLambda]
      simp

omit [DecidableEq n] [DecidableEq m] in
/-- Diagonal selected-root version of
`reducedRankAperpAhat_orthogonal_of_dual_relation`.

When Hansen's dual relation is written with `Λ = diagonal λ`, the pointwise
nonzero selected roots synthesize the inverse block required by the generic
duality algebra. -/
theorem reducedRankAperpAhat_orthogonal_of_diagonal_dual_relation
    (Xtilde : Matrix n k ℝ) (Ytilde : Matrix n m ℝ)
    (G : Matrix k r ℝ) (Aperp : Matrix m s ℝ) (W : Matrix m r ℝ)
    (lambda : r → ℝ)
    (hLambda : ∀ j, lambda j ≠ 0)
    (hDual : reducedRankDualEigenvectorRelation
      Xtilde Ytilde G W (Matrix.diagonal lambda))
    (hOrth : reducedRankAperpYOrthogonal Ytilde Aperp W) :
    Aperpᵀ * reducedRankAhat Xtilde Ytilde G = 0 :=
  reducedRankAperpAhat_orthogonal_of_dual_relation
    Xtilde Ytilde G Aperp W (Matrix.diagonal lambda)
    (Matrix.diagonal fun j => (lambda j)⁻¹) hDual hOrth
    (reducedRankSelectedRootDiagonal_mul_inv_eq_one lambda hLambda)

omit [DecidableEq n] [DecidableEq m] in
/-- Normalized form of `reducedRankAperpAhat_orthogonal_of_dual_relation`.
Under Hansen's normalization `G'X̃'X̃G = I`, `Â = Ỹ'X̃G`, so the same duality
step gives the textbook conclusion `A⊥'Ỹ'X̃G = 0`. -/
theorem reducedRankAperp_cross_orthogonal_of_dual_relation
    (Xtilde : Matrix n k ℝ) (Ytilde : Matrix n m ℝ)
    (G : Matrix k r ℝ) (Aperp : Matrix m s ℝ) (W : Matrix m r ℝ)
    (Lambda LambdaInv : Matrix r r ℝ)
    (hNorm : reducedRankGNormalized Xtilde G)
    (hDual : reducedRankDualEigenvectorRelation Xtilde Ytilde G W Lambda)
    (hOrth : reducedRankAperpYOrthogonal Ytilde Aperp W)
    (hLambdaInv : Lambda * LambdaInv = 1) :
    Aperpᵀ * (Ytildeᵀ * Xtilde * G) = 0 := by
  rw [← reducedRankAhat_eq_cross_of_normalized Xtilde Ytilde G hNorm]
  exact reducedRankAperpAhat_orthogonal_of_dual_relation
    Xtilde Ytilde G Aperp W Lambda LambdaInv hDual hOrth hLambdaInv

omit [DecidableEq n] in
/-- Cross orthogonality from a canonical dual residual-pencil eigenblock.

Positive definiteness constructs the dual relation, while symmetry and
disjoint residual-pencil roots derive `Ỹ'Ỹ`-orthogonality. This removes both
of those premises from `reducedRankAperp_cross_orthogonal_of_dual_relation`;
the nontrivial remaining spectral premise is that the canonical dual block is
indeed a residual-pencil eigenblock with roots separated from `A⊥`. -/
theorem reducedRankAperp_cross_orthogonal_of_canonical_dual_eigenblock
    [Fintype s] [DecidableEq s]
    (Xtilde : Matrix n k ℝ) (Ytilde Etilde : Matrix n m ℝ)
    (G : Matrix k r ℝ) (Aperp : Matrix m s ℝ)
    (Lambda LambdaInv : Matrix r r ℝ)
    (eta : s → ℝ) (mu : r → ℝ)
    (hYGram : (Ytildeᵀ * Ytilde).PosDef)
    (hNorm : reducedRankGNormalized Xtilde G)
    (hAperp : reducedRankHansenAperpEigenvectors Etilde Ytilde eta Aperp)
    (hDualEig : reducedRankHansenAperpEigenvectors Etilde Ytilde mu
      (reducedRankDualEigenvectorBlock Xtilde Ytilde G Lambda))
    (hDisjoint : ∀ i j, eta i ≠ mu j)
    (hLambdaInv : Lambda * LambdaInv = 1) :
    reducedRankAperpCrossOrthogonal Xtilde Ytilde G Aperp := by
  exact reducedRankAperp_cross_orthogonal_of_dual_relation
    Xtilde Ytilde G Aperp
    (reducedRankDualEigenvectorBlock Xtilde Ytilde G Lambda)
    Lambda LambdaInv hNorm
    (reducedRankDualEigenvectorRelation_canonical_of_yGram_posDef
      Xtilde Ytilde G Lambda hYGram)
    (reducedRankAperpYOrthogonal_of_disjoint_eigenblocks
      Etilde Ytilde eta Aperp mu
      (reducedRankDualEigenvectorBlock Xtilde Ytilde G Lambda)
      hAperp hDualEig hDisjoint)
    hLambdaInv

omit [DecidableEq n] [DecidableEq m] in
/-- Normalized diagonal selected-root version of the duality step.

This is the Hansen-facing form: the displayed relation with
`Λ = diagonal λ`, selected-root nonsingularity `λ_j ≠ 0`, and
`Ỹ'Ỹ`-orthogonality imply the stored dual identity
`A⊥'Ỹ'X̃G = 0`. -/
theorem reducedRankAperp_cross_orthogonal_of_diagonal_dual_relation
    (Xtilde : Matrix n k ℝ) (Ytilde : Matrix n m ℝ)
    (G : Matrix k r ℝ) (Aperp : Matrix m s ℝ) (W : Matrix m r ℝ)
    (lambda : r → ℝ)
    (hNorm : reducedRankGNormalized Xtilde G)
    (hLambda : ∀ j, lambda j ≠ 0)
    (hDual : reducedRankDualEigenvectorRelation
      Xtilde Ytilde G W (Matrix.diagonal lambda))
    (hOrth : reducedRankAperpYOrthogonal Ytilde Aperp W) :
    Aperpᵀ * (Ytildeᵀ * Xtilde * G) = 0 := by
  rw [← reducedRankAhat_eq_cross_of_normalized Xtilde Ytilde G hNorm]
  exact reducedRankAperpAhat_orthogonal_of_diagonal_dual_relation
    Xtilde Ytilde G Aperp W lambda hLambda hDual hOrth

omit [DecidableEq n] in
/-- Add Hansen's displayed dual relation to the canonical max/max spectral
certificate.

The existing duality algebra derives and stores
`A⊥'Ỹ'X̃G = 0`; no separate cross-orthogonality premise is needed. -/
theorem
    ReducedRankHansenIdentifiedSpectralMaximizerCertificate.of_maxMax_and_dual_relation
    [Fintype s] [DecidableEq s]
    {Xtilde : Matrix n k ℝ} {Ytilde Etilde : Matrix n m ℝ}
    {G : Matrix k r ℝ} {lambda : r → ℝ}
    {Aperp : Matrix m s ℝ} {eta : s → ℝ}
    (hMax : ReducedRankHansenDetProductMaxMaxCertificate
      Xtilde Ytilde Etilde G lambda Aperp eta)
    (W : Matrix m r ℝ) (Lambda LambdaInv : Matrix r r ℝ)
    (hDual : reducedRankDualEigenvectorRelation Xtilde Ytilde G W Lambda)
    (hOrth : reducedRankAperpYOrthogonal Ytilde Aperp W)
    (hLambdaInv : Lambda * LambdaInv = 1) :
    ReducedRankHansenIdentifiedSpectralMaximizerCertificate
      Xtilde Ytilde Etilde G lambda Aperp eta where
  spectral_maximizers := hMax
  aperp_cross_orthogonal :=
    reducedRankAperp_cross_orthogonal_of_dual_relation
      Xtilde Ytilde G Aperp W Lambda LambdaInv hMax.g_max.normalized
      hDual hOrth hLambdaInv

omit [DecidableEq n] in
/-- Build the identified max/max certificate from the canonical dual
residual-pencil eigenblock.

The positive-definite outcome Gram synthesizes Hansen's displayed dual
relation, and disjoint residual-pencil roots synthesize dual orthogonality. No
cross-orthogonality premise is assumed. -/
theorem
    ReducedRankHansenIdentifiedSpectralMaximizerCertificate.of_maxMax_and_canonical_dual_eigenblock
    [Fintype s] [DecidableEq s]
    {Xtilde : Matrix n k ℝ} {Ytilde Etilde : Matrix n m ℝ}
    {G : Matrix k r ℝ} {lambda : r → ℝ}
    {Aperp : Matrix m s ℝ} {eta : s → ℝ}
    (hMax : ReducedRankHansenDetProductMaxMaxCertificate
      Xtilde Ytilde Etilde G lambda Aperp eta)
    (Lambda LambdaInv : Matrix r r ℝ) (mu : r → ℝ)
    (hYGram : (Ytildeᵀ * Ytilde).PosDef)
    (hDualEig : reducedRankHansenAperpEigenvectors Etilde Ytilde mu
      (reducedRankDualEigenvectorBlock Xtilde Ytilde G Lambda))
    (hDisjoint : ∀ i j, eta i ≠ mu j)
    (hLambdaInv : Lambda * LambdaInv = 1) :
    ReducedRankHansenIdentifiedSpectralMaximizerCertificate
      Xtilde Ytilde Etilde G lambda Aperp eta :=
  ReducedRankHansenIdentifiedSpectralMaximizerCertificate.of_maxMax_and_dual_relation
    hMax (reducedRankDualEigenvectorBlock Xtilde Ytilde G Lambda)
    Lambda LambdaInv
    (reducedRankDualEigenvectorRelation_canonical_of_yGram_posDef
      Xtilde Ytilde G Lambda hYGram)
    (reducedRankAperpYOrthogonal_of_disjoint_eigenblocks
      Etilde Ytilde eta Aperp mu
      (reducedRankDualEigenvectorBlock Xtilde Ytilde G Lambda)
      hMax.aperp_max.eigenvectors hDualEig hDisjoint)
    hLambdaInv

set_option linter.style.longLine false in
omit [DecidableEq n] in
/-- Conditional simultaneous G/`Aperp` constructor with a sharp cross-boundary
spectral-separation hypothesis.

The exact complement-pencil identity and nonzero selected G roots make the
identity-scaled canonical dual block a residual-pencil eigenblock with roots
`1 - lambda`. The existing disjoint-root orthogonality theorem then identifies
the independently selected direct-objective maximizers whenever
`eta_i != 1 - lambda_j`. Ties within the selected G family or within the
selected `Aperp` family are allowed; only a tie crossing the selected/complement
boundary is excluded. This is a conditional bridge, not Hansen's still-open
unconditional tied-boundary simultaneous construction. -/
theorem
    ReducedRankHansenIdentifiedSpectralMaximizerCertificate.of_maxMax_and_complement_pencil_of_separated_roots
    [DecidableEq k] [Fintype s] [DecidableEq s]
    (Xtilde : Matrix n k ℝ) (Ytilde Etilde : Matrix n m ℝ)
    (G : Matrix k r ℝ) (lambda : r → ℝ)
    (Aperp : Matrix m s ℝ) (eta : s → ℝ)
    (hMax : ReducedRankHansenDetProductMaxMaxCertificate
      Xtilde Ytilde Etilde G lambda Aperp eta)
    (hXGram : (Xtildeᵀ * Xtilde).PosDef)
    (hYGram : (Ytildeᵀ * Ytilde).PosDef)
    (hComplement :
      reducedRankAperpPencilA Etilde =
        reducedRankAperpPencilB Ytilde -
          (Ytildeᵀ * Xtilde) * (reducedRankGPencilB Xtilde)⁻¹ *
            (Xtildeᵀ * Ytilde))
    (hLambda : ∀ j, lambda j ≠ 0)
    (hSeparated : ∀ i j, eta i ≠ 1 - lambda j) :
    ReducedRankHansenIdentifiedSpectralMaximizerCertificate
      Xtilde Ytilde Etilde G lambda Aperp eta :=
  ReducedRankHansenIdentifiedSpectralMaximizerCertificate.of_maxMax_and_canonical_dual_eigenblock
    hMax (1 : Matrix r r ℝ) (1 : Matrix r r ℝ) (fun j => 1 - lambda j)
    hYGram
    (reducedRankDualEigenvectorBlock_one_aperpEigenvectors_of_complement
      Xtilde Ytilde Etilde G lambda hXGram hYGram hComplement
      hMax.g_max.eigenvectors hMax.g_max.normalized hLambda)
    hSeparated (by simp)

omit [DecidableEq n] in
/-- Build the strengthened spectral-duality certificate from the
determinant/product min-max certificate and Hansen's displayed dual
generalized-eigenvector relation. The dual relation proves the stored
subspace identity `A⊥'Ỹ'X̃G = 0`. -/
theorem ReducedRankHansenIdentifiedSpectralDualityCertificate.of_detProductMinMax_and_dual_relation
    [Fintype s] [DecidableEq s]
    {Xtilde : Matrix n k ℝ} {Ytilde Etilde : Matrix n m ℝ}
    {G : Matrix k r ℝ} {lambda : r → ℝ}
    {Aperp : Matrix m s ℝ} {eta : s → ℝ}
    (hMinMax : ReducedRankHansenDetProductMinMaxCertificate
      Xtilde Ytilde Etilde G lambda Aperp eta)
    (W : Matrix m r ℝ) (Lambda LambdaInv : Matrix r r ℝ)
    (hDual : reducedRankDualEigenvectorRelation Xtilde Ytilde G W Lambda)
    (hOrth : reducedRankAperpYOrthogonal Ytilde Aperp W)
    (hLambdaInv : Lambda * LambdaInv = 1) :
    ReducedRankHansenIdentifiedSpectralDualityCertificate
      Xtilde Ytilde Etilde G lambda Aperp eta :=
  ReducedRankHansenIdentifiedSpectralDualityCertificate.of_detProductMinMax_and_cross
    hMinMax
    (reducedRankAperp_cross_orthogonal_of_dual_relation
      Xtilde Ytilde G Aperp W Lambda LambdaInv
      hMinMax.g_max.normalized hDual hOrth hLambdaInv)

omit [DecidableEq n] in
/-- Build the strengthened spectral-duality certificate from determinant/product
min-max plus Hansen's displayed diagonal selected-root dual relation.

This wrapper closes the selected-root nonsingularity bookkeeping: callers give
`Λ = diagonal λ` and pointwise nonzero selected roots, and the inverse block is
constructed internally. -/
theorem
    ReducedRankHansenIdentifiedSpectralDualityCertificate.of_detProductMinMax_diagonalDual
    [Fintype s] [DecidableEq s]
    {Xtilde : Matrix n k ℝ} {Ytilde Etilde : Matrix n m ℝ}
    {G : Matrix k r ℝ} {lambda : r → ℝ}
    {Aperp : Matrix m s ℝ} {eta : s → ℝ}
    (hMinMax : ReducedRankHansenDetProductMinMaxCertificate
      Xtilde Ytilde Etilde G lambda Aperp eta)
    (W : Matrix m r ℝ)
    (hLambda : ∀ j, lambda j ≠ 0)
    (hDual : reducedRankDualEigenvectorRelation
      Xtilde Ytilde G W (Matrix.diagonal lambda))
    (hOrth : reducedRankAperpYOrthogonal Ytilde Aperp W) :
    ReducedRankHansenIdentifiedSpectralDualityCertificate
      Xtilde Ytilde Etilde G lambda Aperp eta :=
  ReducedRankHansenIdentifiedSpectralDualityCertificate.of_detProductMinMax_and_cross
    hMinMax
    (reducedRankAperp_cross_orthogonal_of_diagonal_dual_relation
      Xtilde Ytilde G Aperp W lambda hMinMax.g_max.normalized
      hLambda hDual hOrth)

set_option linter.style.longLine false in
omit [DecidableEq n] in
/-- Product-nonzero version of
`ReducedRankHansenIdentifiedSpectralDualityCertificate.of_detProductMinMax_diagonalDual`.

This matches the common spectral route where nonsingularity is obtained from a
nonzero product of the selected generalized roots. -/
theorem
    ReducedRankHansenIdentifiedSpectralDualityCertificate.of_detProductMinMax_diagonalDual_prod_ne_zero
    [Fintype s] [DecidableEq s]
    {Xtilde : Matrix n k ℝ} {Ytilde Etilde : Matrix n m ℝ}
    {G : Matrix k r ℝ} {lambda : r → ℝ}
    {Aperp : Matrix m s ℝ} {eta : s → ℝ}
    (hMinMax : ReducedRankHansenDetProductMinMaxCertificate
      Xtilde Ytilde Etilde G lambda Aperp eta)
    (W : Matrix m r ℝ)
    (hLambdaProd : (∏ j, lambda j) ≠ 0)
    (hDual : reducedRankDualEigenvectorRelation
      Xtilde Ytilde G W (Matrix.diagonal lambda))
    (hOrth : reducedRankAperpYOrthogonal Ytilde Aperp W) :
    ReducedRankHansenIdentifiedSpectralDualityCertificate
      Xtilde Ytilde Etilde G lambda Aperp eta :=
  ReducedRankHansenIdentifiedSpectralDualityCertificate.of_detProductMinMax_diagonalDual
    hMinMax W
    (reducedRankSelectedRoots_nonzero_of_prod_ne_zero lambda hLambdaProd)
    hDual hOrth

set_option linter.style.longLine false in
omit [DecidableEq n] in
/-- Positive-root version of
`ReducedRankHansenIdentifiedSpectralDualityCertificate.of_detProductMinMax_diagonalDual`.

This matches the raw spectral route where the selected `G` roots are returned
as positive roots; the nonzero selected-root product required for the diagonal
duality algebra is derived internally. -/
theorem
    ReducedRankHansenIdentifiedSpectralDualityCertificate.of_detProductMinMax_diagonalDual_pos
    [Fintype s] [DecidableEq s]
    {Xtilde : Matrix n k ℝ} {Ytilde Etilde : Matrix n m ℝ}
    {G : Matrix k r ℝ} {lambda : r → ℝ}
    {Aperp : Matrix m s ℝ} {eta : s → ℝ}
    (hMinMax : ReducedRankHansenDetProductMinMaxCertificate
      Xtilde Ytilde Etilde G lambda Aperp eta)
    (W : Matrix m r ℝ)
    (hLambda : ∀ j, 0 < lambda j)
    (hDual : reducedRankDualEigenvectorRelation
      Xtilde Ytilde G W (Matrix.diagonal lambda))
    (hOrth : reducedRankAperpYOrthogonal Ytilde Aperp W) :
    ReducedRankHansenIdentifiedSpectralDualityCertificate
      Xtilde Ytilde Etilde G lambda Aperp eta :=
  ReducedRankHansenIdentifiedSpectralDualityCertificate.of_detProductMinMax_diagonalDual_prod_ne_zero
    hMinMax W (reducedRankSelectedRootProduct_ne_zero_of_pos lambda hLambda)
    hDual hOrth

set_option linter.style.longLine false in
omit [DecidableEq n] in
/-- Objective-extrema version of
`ReducedRankHansenIdentifiedSpectralDualityCertificate.of_detProductMinMax_diagonalDual_pos`.

The normal-likelihood route can supply the two objective extrema and positive
selected `G` roots; this bridge derives the determinant/product min-max
certificate and diagonal selected-root nonsingularity internally. -/
theorem
    ReducedRankHansenIdentifiedSpectralDualityCertificate.of_objective_extrema_diagonalDual_pos
    [Fintype s] [DecidableEq s]
    (Xtilde : Matrix n k ℝ) (Ytilde Etilde : Matrix n m ℝ)
    (G : Matrix k r ℝ) (lambda : r → ℝ)
    (Aperp : Matrix m s ℝ) (eta : s → ℝ)
    (hG : reducedRankHansenGEigenvectors Xtilde Ytilde lambda G)
    (hGOpt : reducedRankConcentratedObjectiveMaximizer Xtilde Ytilde G)
    (hAperp : reducedRankHansenAperpEigenvectors Etilde Ytilde eta Aperp)
    (hAperpOpt : reducedRankAperpObjectiveMinimizer Etilde Ytilde Aperp)
    (W : Matrix m r ℝ)
    (hLambda : ∀ j, 0 < lambda j)
    (hDual : reducedRankDualEigenvectorRelation
      Xtilde Ytilde G W (Matrix.diagonal lambda))
    (hOrth : reducedRankAperpYOrthogonal Ytilde Aperp W) :
    ReducedRankHansenIdentifiedSpectralDualityCertificate
      Xtilde Ytilde Etilde G lambda Aperp eta :=
  ReducedRankHansenIdentifiedSpectralDualityCertificate.of_detProductMinMax_diagonalDual_pos
    (ReducedRankHansenDetProductMinMaxCertificate.of_objective_extrema
      Xtilde Ytilde Etilde G lambda Aperp eta hG hGOpt hAperp hAperpOpt)
    W hLambda hDual hOrth

set_option linter.style.longLine false in
omit [DecidableEq n] in
/-- Objective-extrema version of
`ReducedRankHansenIdentifiedSpectralDualityCertificate.of_detProductMinMax_diagonalDual_prod_ne_zero`.

This is the normal-likelihood bridge when nonsingularity is available as a
nonzero selected-root product rather than pointwise positive roots. -/
theorem
    ReducedRankHansenIdentifiedSpectralDualityCertificate.of_objective_extrema_diagonalDual_prod_ne_zero
    [Fintype s] [DecidableEq s]
    (Xtilde : Matrix n k ℝ) (Ytilde Etilde : Matrix n m ℝ)
    (G : Matrix k r ℝ) (lambda : r → ℝ)
    (Aperp : Matrix m s ℝ) (eta : s → ℝ)
    (hG : reducedRankHansenGEigenvectors Xtilde Ytilde lambda G)
    (hGOpt : reducedRankConcentratedObjectiveMaximizer Xtilde Ytilde G)
    (hAperp : reducedRankHansenAperpEigenvectors Etilde Ytilde eta Aperp)
    (hAperpOpt : reducedRankAperpObjectiveMinimizer Etilde Ytilde Aperp)
    (W : Matrix m r ℝ)
    (hLambdaProd : (∏ j, lambda j) ≠ 0)
    (hDual : reducedRankDualEigenvectorRelation
      Xtilde Ytilde G W (Matrix.diagonal lambda))
    (hOrth : reducedRankAperpYOrthogonal Ytilde Aperp W) :
    ReducedRankHansenIdentifiedSpectralDualityCertificate
      Xtilde Ytilde Etilde G lambda Aperp eta :=
  ReducedRankHansenIdentifiedSpectralDualityCertificate.of_detProductMinMax_diagonalDual_prod_ne_zero
    (ReducedRankHansenDetProductMinMaxCertificate.of_objective_extrema
      Xtilde Ytilde Etilde G lambda Aperp eta hG hGOpt hAperp hAperpOpt)
    W hLambdaProd hDual hOrth

set_option linter.style.longLine false in
omit [DecidableEq n] in
/-- Selected compressed-determinant extrema plus positive selected `G` roots
give the identified spectral-duality certificate with Hansen's diagonal dual
relation. -/
theorem
    ReducedRankHansenIdentifiedSpectralDualityCertificate.of_selectedExtrema_diagonalDual_pos
    [Fintype s] [DecidableEq s]
    (Xtilde : Matrix n k ℝ) (Ytilde Etilde : Matrix n m ℝ)
    (G : Matrix k r ℝ) (lambda : r → ℝ)
    (Aperp : Matrix m s ℝ) (eta : s → ℝ)
    (hG : reducedRankHansenGEigenvectors Xtilde Ytilde lambda G)
    (hGNorm : reducedRankGNormalized Xtilde G)
    (hGMax :
      generalizedEigenSelectedCompressedDetMaximal
        (reducedRankGPencilA Xtilde Ytilde) (reducedRankGPencilB Xtilde) G)
    (hAperp : reducedRankHansenAperpEigenvectors Etilde Ytilde eta Aperp)
    (hAperpNorm : reducedRankAperpNormalized Ytilde Aperp)
    (hAperpMin :
      generalizedEigenSelectedCompressedDetMinimal
        (reducedRankAperpPencilA Etilde) (reducedRankAperpPencilB Ytilde) Aperp)
    (W : Matrix m r ℝ)
    (hLambda : ∀ j, 0 < lambda j)
    (hDual : reducedRankDualEigenvectorRelation
      Xtilde Ytilde G W (Matrix.diagonal lambda))
    (hOrth : reducedRankAperpYOrthogonal Ytilde Aperp W) :
    ReducedRankHansenIdentifiedSpectralDualityCertificate
      Xtilde Ytilde Etilde G lambda Aperp eta :=
  ReducedRankHansenIdentifiedSpectralDualityCertificate.of_detProductMinMax_diagonalDual_pos
    (ReducedRankHansenDetProductMinMaxCertificate.of_selected_compressedDet_extrema
      Xtilde Ytilde Etilde G lambda Aperp eta
      hG hGNorm hGMax hAperp hAperpNorm hAperpMin)
    W hLambda hDual hOrth

set_option linter.style.longLine false in
omit [DecidableEq n] in
/-- Selected compressed-determinant extrema plus a nonzero selected-root
product give the identified spectral-duality certificate with Hansen's
diagonal dual relation. -/
theorem
    ReducedRankHansenIdentifiedSpectralDualityCertificate.of_selectedExtrema_diagonalDual_prod_ne_zero
    [Fintype s] [DecidableEq s]
    (Xtilde : Matrix n k ℝ) (Ytilde Etilde : Matrix n m ℝ)
    (G : Matrix k r ℝ) (lambda : r → ℝ)
    (Aperp : Matrix m s ℝ) (eta : s → ℝ)
    (hG : reducedRankHansenGEigenvectors Xtilde Ytilde lambda G)
    (hGNorm : reducedRankGNormalized Xtilde G)
    (hGMax :
      generalizedEigenSelectedCompressedDetMaximal
        (reducedRankGPencilA Xtilde Ytilde) (reducedRankGPencilB Xtilde) G)
    (hAperp : reducedRankHansenAperpEigenvectors Etilde Ytilde eta Aperp)
    (hAperpNorm : reducedRankAperpNormalized Ytilde Aperp)
    (hAperpMin :
      generalizedEigenSelectedCompressedDetMinimal
        (reducedRankAperpPencilA Etilde) (reducedRankAperpPencilB Ytilde) Aperp)
    (W : Matrix m r ℝ)
    (hLambdaProd : (∏ j, lambda j) ≠ 0)
    (hDual : reducedRankDualEigenvectorRelation
      Xtilde Ytilde G W (Matrix.diagonal lambda))
    (hOrth : reducedRankAperpYOrthogonal Ytilde Aperp W) :
    ReducedRankHansenIdentifiedSpectralDualityCertificate
      Xtilde Ytilde Etilde G lambda Aperp eta :=
  ReducedRankHansenIdentifiedSpectralDualityCertificate.of_detProductMinMax_diagonalDual_prod_ne_zero
    (ReducedRankHansenDetProductMinMaxCertificate.of_selected_compressedDet_extrema
      Xtilde Ytilde Etilde G lambda Aperp eta
      hG hGNorm hGMax hAperp hAperpNorm hAperpMin)
    W hLambdaProd hDual hOrth

set_option linter.style.longLine false in
omit [DecidableEq n] in
/-- Compressed-determinant version of
`ReducedRankHansenIdentifiedSpectralDualityCertificate.of_detProductMinMax_diagonalDual_prod_ne_zero`.

This is the determinant/product certificate route when the raw spectral
construction proves nonsingularity of the selected compressed `G` block
`det(G'AG) ≠ 0` rather than a nonzero selected-root product. -/
theorem
    ReducedRankHansenIdentifiedSpectralDualityCertificate.of_detProductMinMax_diagonalDual_compressedDet_ne_zero
    [Fintype s] [DecidableEq s]
    {Xtilde : Matrix n k ℝ} {Ytilde Etilde : Matrix n m ℝ}
    {G : Matrix k r ℝ} {lambda : r → ℝ}
    {Aperp : Matrix m s ℝ} {eta : s → ℝ}
    (hMinMax : ReducedRankHansenDetProductMinMaxCertificate
      Xtilde Ytilde Etilde G lambda Aperp eta)
    (W : Matrix m r ℝ)
    (hGdet : (Gᵀ * reducedRankGPencilA Xtilde Ytilde * G).det ≠ 0)
    (hDual : reducedRankDualEigenvectorRelation
      Xtilde Ytilde G W (Matrix.diagonal lambda))
    (hOrth : reducedRankAperpYOrthogonal Ytilde Aperp W) :
    ReducedRankHansenIdentifiedSpectralDualityCertificate
      Xtilde Ytilde Etilde G lambda Aperp eta :=
  ReducedRankHansenIdentifiedSpectralDualityCertificate.of_detProductMinMax_diagonalDual_prod_ne_zero
    hMinMax W
    (generalizedEigenSelectedRootProduct_ne_zero_of_compressedDet_ne_zero
      (reducedRankGPencilA Xtilde Ytilde) (reducedRankGPencilB Xtilde)
      lambda G hMinMax.g_max.eigenvectors hMinMax.g_max.normalized hGdet)
    hDual hOrth

set_option linter.style.longLine false in
omit [DecidableEq n] in
/-- Selected compressed-determinant extrema, Hansen's displayed diagonal dual
relation, and a nonzero selected compressed `G` determinant supply the
identified spectral-duality certificate.

This is the selected-extrema counterpart of
`ReducedRankHansenIdentifiedSpectralDualityCertificate.of_detProductMinMax_diagonalDual_compressedDet_ne_zero`:
the determinant/product min-max certificate is synthesized from the selected
compressed-determinant extrema, while the diagonal inverse block is synthesized
from `det(G'AG) ≠ 0`. -/
theorem
    ReducedRankHansenIdentifiedSpectralDualityCertificate.of_selectedExtrema_diagonalDual_compressedDet_ne_zero
    [Fintype s] [DecidableEq s]
    (Xtilde : Matrix n k ℝ) (Ytilde Etilde : Matrix n m ℝ)
    (G : Matrix k r ℝ) (lambda : r → ℝ)
    (Aperp : Matrix m s ℝ) (eta : s → ℝ)
    (hG : reducedRankHansenGEigenvectors Xtilde Ytilde lambda G)
    (hGNorm : reducedRankGNormalized Xtilde G)
    (hGMax :
      generalizedEigenSelectedCompressedDetMaximal
        (reducedRankGPencilA Xtilde Ytilde) (reducedRankGPencilB Xtilde) G)
    (hAperp : reducedRankHansenAperpEigenvectors Etilde Ytilde eta Aperp)
    (hAperpNorm : reducedRankAperpNormalized Ytilde Aperp)
    (hAperpMin :
      generalizedEigenSelectedCompressedDetMinimal
        (reducedRankAperpPencilA Etilde) (reducedRankAperpPencilB Ytilde) Aperp)
    (W : Matrix m r ℝ)
    (hGdet : (Gᵀ * reducedRankGPencilA Xtilde Ytilde * G).det ≠ 0)
    (hDual : reducedRankDualEigenvectorRelation
      Xtilde Ytilde G W (Matrix.diagonal lambda))
    (hOrth : reducedRankAperpYOrthogonal Ytilde Aperp W) :
    ReducedRankHansenIdentifiedSpectralDualityCertificate
      Xtilde Ytilde Etilde G lambda Aperp eta :=
  ReducedRankHansenIdentifiedSpectralDualityCertificate.of_detProductMinMax_diagonalDual_compressedDet_ne_zero
    (ReducedRankHansenDetProductMinMaxCertificate.of_selected_compressedDet_extrema
      Xtilde Ytilde Etilde G lambda Aperp eta
      hG hGNorm hGMax hAperp hAperpNorm hAperpMin)
    W hGdet hDual hOrth

set_option linter.style.longLine false in
omit [DecidableEq n] in
/-- Rank-one Rayleigh-bound version of the identified spectral-duality
certificate with Hansen's displayed diagonal dual relation.

This is the fully proved one-column route: scalar generalized Rayleigh bounds
give the two determinant/product min-max fields, and nonsingularity of the
unique selected `G` root gives the inverse diagonal block used in the dual
relation. -/
theorem
    ReducedRankHansenIdentifiedSpectralDualityCertificate.of_rankOne_rayleigh_bounds_diagonalDual
    [Fintype s] [DecidableEq s] [Unique r] [Unique s]
    (Xtilde : Matrix n k ℝ) (Ytilde Etilde : Matrix n m ℝ)
    (G : Matrix k r ℝ) (lambda : r → ℝ)
    (Aperp : Matrix m s ℝ) (eta : s → ℝ)
    (hG : reducedRankHansenGEigenvectors Xtilde Ytilde lambda G)
    (hGNorm : reducedRankGNormalized Xtilde G)
    (hGBound : ∀ v : k → ℝ,
      v ⬝ᵥ (reducedRankGPencilB Xtilde *ᵥ v) = 1 →
        v ⬝ᵥ (reducedRankGPencilA Xtilde Ytilde *ᵥ v) ≤ lambda default)
    (hAperp : reducedRankHansenAperpEigenvectors Etilde Ytilde eta Aperp)
    (hAperpNorm : reducedRankAperpNormalized Ytilde Aperp)
    (hAperpBound : ∀ v : m → ℝ,
      v ⬝ᵥ (reducedRankAperpPencilB Ytilde *ᵥ v) = 1 →
        eta default ≤ v ⬝ᵥ (reducedRankAperpPencilA Etilde *ᵥ v))
    (W : Matrix m r ℝ)
    (hLambda : lambda default ≠ 0)
    (hDual : reducedRankDualEigenvectorRelation
      Xtilde Ytilde G W (Matrix.diagonal lambda))
    (hOrth : reducedRankAperpYOrthogonal Ytilde Aperp W) :
    ReducedRankHansenIdentifiedSpectralDualityCertificate
      Xtilde Ytilde Etilde G lambda Aperp eta :=
  ReducedRankHansenIdentifiedSpectralDualityCertificate.of_detProductMinMax_diagonalDual
    (ReducedRankHansenDetProductMinMaxCertificate.of_rankOne_rayleigh_bounds
      Xtilde Ytilde Etilde G lambda Aperp eta
      hG hGNorm hGBound hAperp hAperpNorm hAperpBound)
    W (reducedRankSelectedRoots_nonzero_rankOne lambda hLambda) hDual hOrth

omit [DecidableEq n] in
/-- Build the strengthened spectral-duality certificate directly from the two
normal-likelihood objective extrema and Hansen's displayed dual relation. -/
theorem ReducedRankHansenIdentifiedSpectralDualityCertificate.of_objective_extrema_and_dual_relation
    [Fintype s] [DecidableEq s]
    (Xtilde : Matrix n k ℝ) (Ytilde Etilde : Matrix n m ℝ)
    (G : Matrix k r ℝ) (lambda : r → ℝ)
    (Aperp : Matrix m s ℝ) (eta : s → ℝ)
    (hG : reducedRankHansenGEigenvectors Xtilde Ytilde lambda G)
    (hGOpt : reducedRankConcentratedObjectiveMaximizer Xtilde Ytilde G)
    (hAperp : reducedRankHansenAperpEigenvectors Etilde Ytilde eta Aperp)
    (hAperpOpt : reducedRankAperpObjectiveMinimizer Etilde Ytilde Aperp)
    (W : Matrix m r ℝ) (Lambda LambdaInv : Matrix r r ℝ)
    (hDual : reducedRankDualEigenvectorRelation Xtilde Ytilde G W Lambda)
    (hOrth : reducedRankAperpYOrthogonal Ytilde Aperp W)
    (hLambdaInv : Lambda * LambdaInv = 1) :
    ReducedRankHansenIdentifiedSpectralDualityCertificate
      Xtilde Ytilde Etilde G lambda Aperp eta :=
  ReducedRankHansenIdentifiedSpectralDualityCertificate.of_detProductMinMax_and_dual_relation
    (ReducedRankHansenDetProductMinMaxCertificate.of_objective_extrema
      Xtilde Ytilde Etilde G lambda Aperp eta hG hGOpt hAperp hAperpOpt)
    W Lambda LambdaInv hDual hOrth hLambdaInv

omit [DecidableEq n] in
/-- Build the strengthened spectral-duality certificate from generic
generalized-pencil product bounds and Hansen's displayed dual relation. -/
theorem ReducedRankHansenIdentifiedSpectralDualityCertificate.of_genericProductBounds_dual
    [Fintype s] [DecidableEq s]
    (Xtilde : Matrix n k ℝ) (Ytilde Etilde : Matrix n m ℝ)
    (G : Matrix k r ℝ) (lambda : r → ℝ)
    (Aperp : Matrix m s ℝ) (eta : s → ℝ)
    (hG : reducedRankHansenGEigenvectors Xtilde Ytilde lambda G)
    (hGNorm : reducedRankGNormalized Xtilde G)
    (hGBound : generalizedEigenDetProductUpperBound
      (reducedRankGPencilA Xtilde Ytilde) (reducedRankGPencilB Xtilde) lambda)
    (hAperp : reducedRankHansenAperpEigenvectors Etilde Ytilde eta Aperp)
    (hAperpNorm : reducedRankAperpNormalized Ytilde Aperp)
    (hAperpBound : generalizedEigenDetProductLowerBound
      (reducedRankAperpPencilA Etilde) (reducedRankAperpPencilB Ytilde) eta)
    (W : Matrix m r ℝ) (Lambda LambdaInv : Matrix r r ℝ)
    (hDual : reducedRankDualEigenvectorRelation Xtilde Ytilde G W Lambda)
    (hOrth : reducedRankAperpYOrthogonal Ytilde Aperp W)
    (hLambdaInv : Lambda * LambdaInv = 1) :
    ReducedRankHansenIdentifiedSpectralDualityCertificate
      Xtilde Ytilde Etilde G lambda Aperp eta :=
  ReducedRankHansenIdentifiedSpectralDualityCertificate.of_detProductMinMax_and_dual_relation
    (ReducedRankHansenDetProductMinMaxCertificate.of_generalized_product_bounds
      Xtilde Ytilde Etilde G lambda Aperp eta
      hG hGNorm hGBound hAperp hAperpNorm hAperpBound)
    W Lambda LambdaInv hDual hOrth hLambdaInv

omit [DecidableEq n] in
/-- Build the strengthened spectral-duality certificate from generic
generalized-pencil product bounds and Hansen's diagonal selected-root dual
relation.

Compared with `of_genericProductBounds_dual`, this endpoint asks only for
pointwise nonzero selected roots instead of a separately supplied inverse for
the selected-root block. -/
theorem
    ReducedRankHansenIdentifiedSpectralDualityCertificate.of_genericProductBounds_diagonalDual
    [Fintype s] [DecidableEq s]
    (Xtilde : Matrix n k ℝ) (Ytilde Etilde : Matrix n m ℝ)
    (G : Matrix k r ℝ) (lambda : r → ℝ)
    (Aperp : Matrix m s ℝ) (eta : s → ℝ)
    (hG : reducedRankHansenGEigenvectors Xtilde Ytilde lambda G)
    (hGNorm : reducedRankGNormalized Xtilde G)
    (hGBound : generalizedEigenDetProductUpperBound
      (reducedRankGPencilA Xtilde Ytilde) (reducedRankGPencilB Xtilde) lambda)
    (hAperp : reducedRankHansenAperpEigenvectors Etilde Ytilde eta Aperp)
    (hAperpNorm : reducedRankAperpNormalized Ytilde Aperp)
    (hAperpBound : generalizedEigenDetProductLowerBound
      (reducedRankAperpPencilA Etilde) (reducedRankAperpPencilB Ytilde) eta)
    (W : Matrix m r ℝ)
    (hLambda : ∀ j, lambda j ≠ 0)
    (hDual : reducedRankDualEigenvectorRelation
      Xtilde Ytilde G W (Matrix.diagonal lambda))
    (hOrth : reducedRankAperpYOrthogonal Ytilde Aperp W) :
    ReducedRankHansenIdentifiedSpectralDualityCertificate
      Xtilde Ytilde Etilde G lambda Aperp eta :=
  ReducedRankHansenIdentifiedSpectralDualityCertificate.of_detProductMinMax_diagonalDual
    (ReducedRankHansenDetProductMinMaxCertificate.of_generalized_product_bounds
      Xtilde Ytilde Etilde G lambda Aperp eta
      hG hGNorm hGBound hAperp hAperpNorm hAperpBound)
    W hLambda hDual hOrth

set_option linter.style.longLine false in
omit [DecidableEq n] in
/-- Product-nonzero version of
`ReducedRankHansenIdentifiedSpectralDualityCertificate.of_genericProductBounds_diagonalDual`.

The product bound route still proves Hansen's two determinant inequalities;
this wrapper only reduces the selected-root nonsingularity obligation from
pointwise nonzero roots to a nonzero selected-root product. -/
theorem
    ReducedRankHansenIdentifiedSpectralDualityCertificate.of_genericProductBounds_diagonalDual_prod_ne_zero
    [Fintype s] [DecidableEq s]
    (Xtilde : Matrix n k ℝ) (Ytilde Etilde : Matrix n m ℝ)
    (G : Matrix k r ℝ) (lambda : r → ℝ)
    (Aperp : Matrix m s ℝ) (eta : s → ℝ)
    (hG : reducedRankHansenGEigenvectors Xtilde Ytilde lambda G)
    (hGNorm : reducedRankGNormalized Xtilde G)
    (hGBound : generalizedEigenDetProductUpperBound
      (reducedRankGPencilA Xtilde Ytilde) (reducedRankGPencilB Xtilde) lambda)
    (hAperp : reducedRankHansenAperpEigenvectors Etilde Ytilde eta Aperp)
    (hAperpNorm : reducedRankAperpNormalized Ytilde Aperp)
    (hAperpBound : generalizedEigenDetProductLowerBound
      (reducedRankAperpPencilA Etilde) (reducedRankAperpPencilB Ytilde) eta)
    (W : Matrix m r ℝ)
    (hLambdaProd : (∏ j, lambda j) ≠ 0)
    (hDual : reducedRankDualEigenvectorRelation
      Xtilde Ytilde G W (Matrix.diagonal lambda))
    (hOrth : reducedRankAperpYOrthogonal Ytilde Aperp W) :
    ReducedRankHansenIdentifiedSpectralDualityCertificate
      Xtilde Ytilde Etilde G lambda Aperp eta :=
  ReducedRankHansenIdentifiedSpectralDualityCertificate.of_genericProductBounds_diagonalDual
    Xtilde Ytilde Etilde G lambda Aperp eta
    hG hGNorm hGBound hAperp hAperpNorm hAperpBound
    W (reducedRankSelectedRoots_nonzero_of_prod_ne_zero lambda hLambdaProd)
    hDual hOrth

set_option linter.style.longLine false in
omit [DecidableEq n] in
/-- Compressed-determinant version of
`ReducedRankHansenIdentifiedSpectralDualityCertificate.of_genericProductBounds_diagonalDual_prod_ne_zero`.

This is the generic-product-bound route when the raw pencil construction proves
nonsingularity of the selected compressed `G` block rather than separately
returning a nonzero selected-root product. -/
theorem
    ReducedRankHansenIdentifiedSpectralDualityCertificate.of_genericProductBounds_diagonalDual_compressedDet_ne_zero
    [Fintype s] [DecidableEq s]
    (Xtilde : Matrix n k ℝ) (Ytilde Etilde : Matrix n m ℝ)
    (G : Matrix k r ℝ) (lambda : r → ℝ)
    (Aperp : Matrix m s ℝ) (eta : s → ℝ)
    (hG : reducedRankHansenGEigenvectors Xtilde Ytilde lambda G)
    (hGNorm : reducedRankGNormalized Xtilde G)
    (hGBound : generalizedEigenDetProductUpperBound
      (reducedRankGPencilA Xtilde Ytilde) (reducedRankGPencilB Xtilde) lambda)
    (hAperp : reducedRankHansenAperpEigenvectors Etilde Ytilde eta Aperp)
    (hAperpNorm : reducedRankAperpNormalized Ytilde Aperp)
    (hAperpBound : generalizedEigenDetProductLowerBound
      (reducedRankAperpPencilA Etilde) (reducedRankAperpPencilB Ytilde) eta)
    (W : Matrix m r ℝ)
    (hGdet : (Gᵀ * reducedRankGPencilA Xtilde Ytilde * G).det ≠ 0)
    (hDual : reducedRankDualEigenvectorRelation
      Xtilde Ytilde G W (Matrix.diagonal lambda))
    (hOrth : reducedRankAperpYOrthogonal Ytilde Aperp W) :
    ReducedRankHansenIdentifiedSpectralDualityCertificate
      Xtilde Ytilde Etilde G lambda Aperp eta :=
  ReducedRankHansenIdentifiedSpectralDualityCertificate.of_genericProductBounds_diagonalDual_prod_ne_zero
    Xtilde Ytilde Etilde G lambda Aperp eta
    hG hGNorm hGBound hAperp hAperpNorm hAperpBound W
    (generalizedEigenSelectedRootProduct_ne_zero_of_compressedDet_ne_zero
      (reducedRankGPencilA Xtilde Ytilde) (reducedRankGPencilB Xtilde)
      lambda G hG hGNorm hGdet)
    hDual hOrth

set_option linter.style.longLine false in
omit [DecidableEq n] in
/-- Build the strengthened spectral-duality certificate from the raw ordered
generalized-eigenvalue min-max surface and Hansen's diagonal dual relation.

This is the certificate-level bridge for the expected output of the missing raw
spectral theorem: the ordered certificate supplies the two product variational
bounds and normalizations, while the diagonal dual relation supplies the stored
identity `A⊥'Ỹ'X̃G = 0`. -/
theorem
    ReducedRankHansenIdentifiedSpectralDualityCertificate.of_orderedGeneralizedEigen_diagonalDual
    [Fintype s] [DecidableEq s]
    {Xtilde : Matrix n k ℝ} {Ytilde Etilde : Matrix n m ℝ}
    {G : Matrix k r ℝ} {lambda : r → ℝ}
    {Aperp : Matrix m s ℝ} {eta : s → ℝ}
    (hOrdered : ReducedRankHansenOrderedGeneralizedEigenMinMaxCertificate
      Xtilde Ytilde Etilde G lambda Aperp eta)
    (W : Matrix m r ℝ)
    (hLambda : ∀ j, lambda j ≠ 0)
    (hDual : reducedRankDualEigenvectorRelation
      Xtilde Ytilde G W (Matrix.diagonal lambda))
    (hOrth : reducedRankAperpYOrthogonal Ytilde Aperp W) :
    ReducedRankHansenIdentifiedSpectralDualityCertificate
      Xtilde Ytilde Etilde G lambda Aperp eta :=
  ReducedRankHansenIdentifiedSpectralDualityCertificate.of_detProductMinMax_diagonalDual
    hOrdered.to_detProductMinMaxCertificate W hLambda hDual hOrth

set_option linter.style.longLine false in
omit [DecidableEq n] in
/-- Product-nonzero version of
`ReducedRankHansenIdentifiedSpectralDualityCertificate.of_orderedGeneralizedEigen_diagonalDual`.

The raw ordered spectral theorem can provide a nonzero selected-root product
instead of pointwise selected-root nonzero assumptions; this bridge derives the
pointwise hypotheses internally. -/
theorem
    ReducedRankHansenIdentifiedSpectralDualityCertificate.of_orderedGeneralizedEigen_diagonalDual_prod_ne_zero
    [Fintype s] [DecidableEq s]
    {Xtilde : Matrix n k ℝ} {Ytilde Etilde : Matrix n m ℝ}
    {G : Matrix k r ℝ} {lambda : r → ℝ}
    {Aperp : Matrix m s ℝ} {eta : s → ℝ}
    (hOrdered : ReducedRankHansenOrderedGeneralizedEigenMinMaxCertificate
      Xtilde Ytilde Etilde G lambda Aperp eta)
    (W : Matrix m r ℝ)
    (hLambdaProd : (∏ j, lambda j) ≠ 0)
    (hDual : reducedRankDualEigenvectorRelation
      Xtilde Ytilde G W (Matrix.diagonal lambda))
    (hOrth : reducedRankAperpYOrthogonal Ytilde Aperp W) :
    ReducedRankHansenIdentifiedSpectralDualityCertificate
      Xtilde Ytilde Etilde G lambda Aperp eta :=
  ReducedRankHansenIdentifiedSpectralDualityCertificate.of_orderedGeneralizedEigen_diagonalDual
    hOrdered W (reducedRankSelectedRoots_nonzero_of_prod_ne_zero lambda hLambdaProd)
    hDual hOrth

set_option linter.style.longLine false in
omit [DecidableEq n] in
/-- Positive-root version of
`ReducedRankHansenIdentifiedSpectralDualityCertificate.of_orderedGeneralizedEigen_diagonalDual`.

This is the certificate bridge for a raw ordered spectral theorem that proves
the selected `G` roots are positive rather than separately packaging a nonzero
selected-root product. -/
theorem
    ReducedRankHansenIdentifiedSpectralDualityCertificate.of_orderedGeneralizedEigen_diagonalDual_pos
    [Fintype s] [DecidableEq s]
    {Xtilde : Matrix n k ℝ} {Ytilde Etilde : Matrix n m ℝ}
    {G : Matrix k r ℝ} {lambda : r → ℝ}
    {Aperp : Matrix m s ℝ} {eta : s → ℝ}
    (hOrdered : ReducedRankHansenOrderedGeneralizedEigenMinMaxCertificate
      Xtilde Ytilde Etilde G lambda Aperp eta)
    (W : Matrix m r ℝ)
    (hLambda : ∀ j, 0 < lambda j)
    (hDual : reducedRankDualEigenvectorRelation
      Xtilde Ytilde G W (Matrix.diagonal lambda))
    (hOrth : reducedRankAperpYOrthogonal Ytilde Aperp W) :
    ReducedRankHansenIdentifiedSpectralDualityCertificate
      Xtilde Ytilde Etilde G lambda Aperp eta :=
  ReducedRankHansenIdentifiedSpectralDualityCertificate.of_orderedGeneralizedEigen_diagonalDual_prod_ne_zero
    hOrdered W (reducedRankSelectedRootProduct_ne_zero_of_pos lambda hLambda)
    hDual hOrth

/-- Literal compatibility surface for Hansen Theorem 11.7's printed maximized
log-likelihood display.

The printed constant has the wrong sign and scale and omits the normalization
term induced by profiling `SigmaHat = n⁻¹ R'R`. This definition is retained only
to cite that textbook display; canonical formula certificates use
`reducedRankMaximizedLogLikelihood`. -/
noncomputable def reducedRankMaximizedLogLikelihood_textbookLiteralCompatibility
    (Ytilde : Matrix n m ℝ) (lambda : r → ℝ) : ℝ :=
  ((Fintype.card m : ℝ) / 2) *
      ((Fintype.card n : ℝ) * Real.log (2 * Real.pi) - 1)
    - ((Fintype.card n : ℝ) / 2) * Real.log (Ytildeᵀ * Ytilde).det
    - ((Fintype.card n : ℝ) / 2) * ∑ j, Real.log (1 - lambda j)

/-- Correct raw-Gaussian profiled log-likelihood value in terms of the
unnormalized residualized outcome Gram and selected generalized roots.

The first term includes the `+(n*m/2) log n` contribution from
`SigmaHat = n⁻¹ R'R`. This definition records the canonical candidate value
only. Equality with an attained raw Gaussian likelihood still requires the
relevant determinant factorization, positivity, and logarithm hypotheses. -/
noncomputable def reducedRankMaximizedLogLikelihood
    (Ytilde : Matrix n m ℝ) (lambda : r → ℝ) : ℝ :=
  (((Fintype.card n : ℝ) * (Fintype.card m : ℝ)) / 2) *
      (Real.log (Fintype.card n : ℝ) - Real.log (2 * Real.pi) - 1)
    - ((Fintype.card n : ℝ) / 2) * Real.log (Ytildeᵀ * Ytilde).det
    - ((Fintype.card n : ℝ) / 2) * ∑ j, Real.log (1 - lambda j)

/-- Concrete least-squares recovery predicate for Hansen Theorem 11.7. -/
def reducedRankLeastSquaresRecovery
    (Z : Matrix n ell ℝ) (X : Matrix n k ℝ) (Y : Matrix n m ℝ)
    (Xtilde : Matrix n k ℝ) (Ytilde : Matrix n m ℝ)
    (G : Matrix k r ℝ) (Acoef : Matrix m r ℝ) (C : Matrix ell m ℝ) : Prop :=
  Acoef = reducedRankAhat Xtilde Ytilde G ∧
    C = reducedRankChat Z X Y G Acoef

/-- Concrete covariance recovery predicate for Hansen Theorem 11.7. -/
def reducedRankCovarianceRecovery
    (Xtilde : Matrix n k ℝ) (Ytilde : Matrix n m ℝ)
    (G : Matrix k r ℝ) (Sigma : Matrix m m ℝ) : Prop :=
  Sigma = reducedRankSigmaHat Xtilde Ytilde G

/-- Equality with the corrected canonical profiled-likelihood value.

This predicate is a formula identity only; it contains no likelihood
comparison and assumes none of the determinant or logarithm hypotheses needed
to derive the identity from the raw Gaussian likelihood. -/
def reducedRankLikelihoodValue
    (Ytilde : Matrix n m ℝ) (lambda : r → ℝ) (logLikelihood : ℝ) : Prop :=
  logLikelihood = reducedRankMaximizedLogLikelihood Ytilde lambda

end Recovery

end HansenPencil

/-- Legacy-named formula certificate used by Hansen's reduced-rank MLE route.

This structure packages the spectral and recovery formulas only.  Its fields
do not define a Gaussian likelihood, require positive-definite covariance, or
compare the candidate with admissible competitors.  New theorem-facing code
should use `ReducedRankMLEFormulaCertificate`; the old name is retained for
compatibility. -/
structure ReducedRankMLE
    (G : Matrix k r ℝ) (A : Matrix m r ℝ) (C : Matrix ell m ℝ)
    (Sigma : Matrix m m ℝ) (logLikelihood : ℝ)
    (generalizedEigenvectors leastSquaresRecovery covarianceRecovery likelihoodValue : Prop) :
    Prop where
  generalized_eigenvectors : generalizedEigenvectors
  least_squares_recovery : leastSquaresRecovery
  covariance_recovery : covarianceRecovery
  likelihood_value : likelihoodValue

/-- Honest canonical name for the legacy `ReducedRankMLE` formula bundle. -/
abbrev ReducedRankMLEFormulaCertificate
    (G : Matrix k r ℝ) (A : Matrix m r ℝ) (C : Matrix ell m ℝ)
    (Sigma : Matrix m m ℝ) (logLikelihood : ℝ)
    (generalizedEigenvectors leastSquaresRecovery covarianceRecovery likelihoodValue : Prop) :
    Prop :=
  ReducedRankMLE G A C Sigma logLikelihood generalizedEigenvectors
    leastSquaresRecovery covarianceRecovery likelihoodValue

/-- Assemble the legacy reduced-rank formula certificate from its four
mathematical components. -/
theorem reducedRankMLE_of_certificate
    (G : Matrix k r ℝ) (A : Matrix m r ℝ) (C : Matrix ell m ℝ)
    (Sigma : Matrix m m ℝ) (logLikelihood : ℝ)
    {generalizedEigenvectors leastSquaresRecovery covarianceRecovery likelihoodValue : Prop}
    (hG : generalizedEigenvectors) (hA : leastSquaresRecovery)
    (hSigma : covarianceRecovery) (hLike : likelihoodValue) :
    ReducedRankMLE G A C Sigma logLikelihood generalizedEigenvectors leastSquaresRecovery
      covarianceRecovery likelihoodValue where
  generalized_eigenvectors := hG
  least_squares_recovery := hA
  covariance_recovery := hSigma
  likelihood_value := hLike

section GeneralizedEigenCertificate

variable [Fintype k]

/-- Legacy reduced-rank formula certificate whose generalized-eigenvector
component is the concrete matrix-pencil predicate used in Hansen Theorem 11.7. -/
theorem reducedRankMLE_of_generalizedEigenvectors
    (G : Matrix k r ℝ) (Acoef : Matrix m r ℝ) (C : Matrix ell m ℝ)
    (Sigma : Matrix m m ℝ) (logLikelihood : ℝ)
    (pencilA pencilB : Matrix k k ℝ) (lambda : r → ℝ)
    {leastSquaresRecovery covarianceRecovery likelihoodValue : Prop}
    (hG : generalizedEigenvectorColumns pencilA pencilB lambda G)
    (hA : leastSquaresRecovery)
    (hSigma : covarianceRecovery) (hLike : likelihoodValue) :
    ReducedRankMLE G Acoef C Sigma logLikelihood
      (generalizedEigenvectorColumns pencilA pencilB lambda G)
      leastSquaresRecovery covarianceRecovery likelihoodValue where
  generalized_eigenvectors := hG
  least_squares_recovery := hA
  covariance_recovery := hSigma
  likelihood_value := hLike

end GeneralizedEigenCertificate

section HansenGeneralizedEigenCertificate

variable {n : Type*}
variable [Fintype n] [DecidableEq n]
variable [Fintype k] [Fintype m] [Fintype ell]
variable [DecidableEq m] [DecidableEq ell]

omit [DecidableEq n] [Fintype ell] [DecidableEq ell] in
/-- Reduced-rank MLE certificate whose generalized-eigenvector component is
Hansen's residualized matrix pencil from Theorem 11.7. -/
theorem reducedRankMLE_of_hansen_generalizedEigenvectors
    (G : Matrix k r ℝ) (Acoef : Matrix m r ℝ) (C : Matrix ell m ℝ)
    (Sigma : Matrix m m ℝ) (logLikelihood : ℝ)
    (Xtilde : Matrix n k ℝ) (Ytilde : Matrix n m ℝ) (lambda : r → ℝ)
    {leastSquaresRecovery covarianceRecovery likelihoodValue : Prop}
    (hG : reducedRankHansenGEigenvectors Xtilde Ytilde lambda G)
    (hA : leastSquaresRecovery)
    (hSigma : covarianceRecovery) (hLike : likelihoodValue) :
    ReducedRankMLE G Acoef C Sigma logLikelihood
      (reducedRankHansenGEigenvectors Xtilde Ytilde lambda G)
      leastSquaresRecovery covarianceRecovery likelihoodValue :=
  reducedRankMLE_of_generalizedEigenvectors G Acoef C Sigma logLikelihood
    (reducedRankGPencilA Xtilde Ytilde) (reducedRankGPencilB Xtilde) lambda
    hG hA hSigma hLike

end HansenGeneralizedEigenCertificate

section HansenObjectiveCertificate

variable {n : Type*}
variable [Fintype n] [DecidableEq n]
variable [Fintype k] [Fintype m] [Fintype ell] [Fintype r]
variable [DecidableEq m] [DecidableEq ell] [DecidableEq r]

omit [DecidableEq n] in
/-- Hansen Theorem 11.7 certificate assembled from the concrete concentrated
objective optimizer, residualized generalized-eigenvector equations, and
least-squares recovery formulas. The remaining theorem needed for full closure
is the spectral/likelihood result proving that the leading generalized
eigenvectors satisfy `reducedRankConcentratedObjectiveMaximizer`. -/
theorem reducedRankMLE_of_hansen_objective_optimizer
    (Z : Matrix n ell ℝ) (X Xtilde : Matrix n k ℝ) (Y Ytilde : Matrix n m ℝ)
    (G : Matrix k r ℝ) (lambda : r → ℝ)
    (hG : reducedRankHansenGEigenvectors Xtilde Ytilde lambda G)
    (hOpt : reducedRankConcentratedObjectiveMaximizer Xtilde Ytilde G) :
    ReducedRankMLE G
      (reducedRankAhat Xtilde Ytilde G)
      (reducedRankChat Z X Y G (reducedRankAhat Xtilde Ytilde G))
      (reducedRankSigmaHat Xtilde Ytilde G)
      (reducedRankMaximizedLogLikelihood Ytilde lambda)
      (reducedRankHansenGEigenvectors Xtilde Ytilde lambda G ∧
        reducedRankConcentratedObjectiveMaximizer Xtilde Ytilde G)
      (reducedRankLeastSquaresRecovery Z X Y Xtilde Ytilde G
        (reducedRankAhat Xtilde Ytilde G)
        (reducedRankChat Z X Y G (reducedRankAhat Xtilde Ytilde G)))
      (reducedRankCovarianceRecovery Xtilde Ytilde G
        (reducedRankSigmaHat Xtilde Ytilde G))
      (reducedRankLikelihoodValue Ytilde lambda
        (reducedRankMaximizedLogLikelihood Ytilde lambda)) where
  generalized_eigenvectors := ⟨hG, hOpt⟩
  least_squares_recovery := ⟨rfl, rfl⟩
  covariance_recovery := rfl
  likelihood_value := rfl

omit [DecidableEq n] in
/-- Hansen Theorem 11.7 certificate assembled from a determinant-compression
variational bound instead of an already-packaged optimizer premise.

The remaining generalized-eigenvalue theorem should prove `hBound` for the
leading reduced-rank eigenspace. This wrapper then supplies the concrete global
optimizer used by the reduced-rank MLE recovery formulas. -/
theorem reducedRankMLE_of_hansen_compression_bound
    (Z : Matrix n ell ℝ) (X Xtilde : Matrix n k ℝ) (Y Ytilde : Matrix n m ℝ)
    (G : Matrix k r ℝ) (lambda : r → ℝ)
    (hG : reducedRankHansenGEigenvectors Xtilde Ytilde lambda G)
    (hNorm : reducedRankGNormalized Xtilde G)
    (hBound : ∀ H : Matrix k r ℝ, reducedRankGNormalized Xtilde H →
      ∃ C : Matrix r r ℝ,
        generalizedEigenCompression
          (reducedRankGPencilA Xtilde Ytilde) (reducedRankGPencilB Xtilde) H C ∧
          C.det ≤ ∏ j, lambda j) :
    ReducedRankMLE G
      (reducedRankAhat Xtilde Ytilde G)
      (reducedRankChat Z X Y G (reducedRankAhat Xtilde Ytilde G))
      (reducedRankSigmaHat Xtilde Ytilde G)
      (reducedRankMaximizedLogLikelihood Ytilde lambda)
      (reducedRankHansenGEigenvectors Xtilde Ytilde lambda G ∧
        reducedRankConcentratedObjectiveMaximizer Xtilde Ytilde G)
      (reducedRankLeastSquaresRecovery Z X Y Xtilde Ytilde G
        (reducedRankAhat Xtilde Ytilde G)
        (reducedRankChat Z X Y G (reducedRankAhat Xtilde Ytilde G)))
      (reducedRankCovarianceRecovery Xtilde Ytilde G
        (reducedRankSigmaHat Xtilde Ytilde G))
      (reducedRankLikelihoodValue Ytilde lambda
        (reducedRankMaximizedLogLikelihood Ytilde lambda)) :=
  reducedRankMLE_of_hansen_objective_optimizer Z X Xtilde Y Ytilde G lambda hG
    (reducedRankConcentratedObjectiveMaximizer_of_compression_det_bound
      Xtilde Ytilde lambda G hG hNorm hBound)

omit [DecidableEq n] in
/-- Hansen Theorem 11.7 certificate assembled from the exact
compressed-determinant variational bound.

The missing spectral theorem should prove the `hBound` premise for the leading
generalized eigenspace. This wrapper contains the remaining deterministic MLE
assembly without requiring arbitrary competitors to be invariant subspaces. -/
theorem reducedRankMLE_of_hansen_compressed_det_bound
    (Z : Matrix n ell ℝ) (X Xtilde : Matrix n k ℝ) (Y Ytilde : Matrix n m ℝ)
    (G : Matrix k r ℝ) (lambda : r → ℝ)
    (hG : reducedRankHansenGEigenvectors Xtilde Ytilde lambda G)
    (hNorm : reducedRankGNormalized Xtilde G)
    (hBound : ∀ H : Matrix k r ℝ, reducedRankGNormalized Xtilde H →
      (Hᵀ * reducedRankGPencilA Xtilde Ytilde * H).det ≤ ∏ j, lambda j) :
    ReducedRankMLE G
      (reducedRankAhat Xtilde Ytilde G)
      (reducedRankChat Z X Y G (reducedRankAhat Xtilde Ytilde G))
      (reducedRankSigmaHat Xtilde Ytilde G)
      (reducedRankMaximizedLogLikelihood Ytilde lambda)
      (reducedRankHansenGEigenvectors Xtilde Ytilde lambda G ∧
        reducedRankConcentratedObjectiveMaximizer Xtilde Ytilde G)
      (reducedRankLeastSquaresRecovery Z X Y Xtilde Ytilde G
        (reducedRankAhat Xtilde Ytilde G)
        (reducedRankChat Z X Y G (reducedRankAhat Xtilde Ytilde G)))
      (reducedRankCovarianceRecovery Xtilde Ytilde G
        (reducedRankSigmaHat Xtilde Ytilde G))
      (reducedRankLikelihoodValue Ytilde lambda
        (reducedRankMaximizedLogLikelihood Ytilde lambda)) :=
  reducedRankMLE_of_hansen_objective_optimizer Z X Xtilde Y Ytilde G lambda hG
    (reducedRankConcentratedObjectiveMaximizer_of_compressed_det_bound
      Xtilde Ytilde lambda G hG hNorm hBound)

omit [DecidableEq n] in
/-- Hansen Theorem 11.7 certificate with the normalized least-squares recovery
formula `Â = Ỹ'X̃Ĝ` exposed in the coefficient slot. This is the same objective
optimizer route as `reducedRankMLE_of_hansen_objective_optimizer`, specialized
through the normalization contained in the optimizer certificate. -/
theorem reducedRankMLE_of_hansen_normalized_objective_optimizer
    (Z : Matrix n ell ℝ) (X Xtilde : Matrix n k ℝ) (Y Ytilde : Matrix n m ℝ)
    (G : Matrix k r ℝ) (lambda : r → ℝ)
    (hG : reducedRankHansenGEigenvectors Xtilde Ytilde lambda G)
    (hOpt : reducedRankConcentratedObjectiveMaximizer Xtilde Ytilde G) :
    ReducedRankMLE G
      (Ytildeᵀ * Xtilde * G)
      (reducedRankChat Z X Y G (Ytildeᵀ * Xtilde * G))
      (reducedRankSigmaHat Xtilde Ytilde G)
      (reducedRankMaximizedLogLikelihood Ytilde lambda)
      (reducedRankHansenGEigenvectors Xtilde Ytilde lambda G ∧
        reducedRankConcentratedObjectiveMaximizer Xtilde Ytilde G)
      (reducedRankLeastSquaresRecovery Z X Y Xtilde Ytilde G
        (Ytildeᵀ * Xtilde * G)
        (reducedRankChat Z X Y G (Ytildeᵀ * Xtilde * G)))
      (reducedRankCovarianceRecovery Xtilde Ytilde G
        (reducedRankSigmaHat Xtilde Ytilde G))
      (reducedRankLikelihoodValue Ytilde lambda
        (reducedRankMaximizedLogLikelihood Ytilde lambda)) where
  generalized_eigenvectors := ⟨hG, hOpt⟩
  least_squares_recovery := by
    constructor
    · exact (reducedRankAhat_eq_cross_of_normalized Xtilde Ytilde G hOpt.1).symm
    · rfl
  covariance_recovery := rfl
  likelihood_value := rfl

/-- Hansen Theorem 11.7 certificate with the residualization by `Z` exposed in
the theorem statement. This is a notation bridge over
`reducedRankMLE_of_hansen_objective_optimizer`; the substantive missing premise
remains the global determinant-optimality proof for the leading generalized
eigenvectors of the residualized pencil. -/
theorem reducedRankMLE_of_hansen_residualized_objective_optimizer
    (Z : Matrix n ell ℝ) (X : Matrix n k ℝ) (Y : Matrix n m ℝ)
    [Invertible (Zᵀ * Z)]
    (G : Matrix k r ℝ) (lambda : r → ℝ)
    (hG : reducedRankHansenGEigenvectors
      (reducedRankTildeX Z X) (reducedRankTildeY Z Y) lambda G)
    (hOpt : reducedRankConcentratedObjectiveMaximizer
      (reducedRankTildeX Z X) (reducedRankTildeY Z Y) G) :
    ReducedRankMLE G
      (reducedRankAhat (reducedRankTildeX Z X) (reducedRankTildeY Z Y) G)
      (reducedRankChat Z X Y G
        (reducedRankAhat (reducedRankTildeX Z X) (reducedRankTildeY Z Y) G))
      (reducedRankSigmaHat (reducedRankTildeX Z X) (reducedRankTildeY Z Y) G)
      (reducedRankMaximizedLogLikelihood (reducedRankTildeY Z Y) lambda)
      (reducedRankHansenGEigenvectors
          (reducedRankTildeX Z X) (reducedRankTildeY Z Y) lambda G ∧
        reducedRankConcentratedObjectiveMaximizer
          (reducedRankTildeX Z X) (reducedRankTildeY Z Y) G)
      (reducedRankLeastSquaresRecovery Z X Y
        (reducedRankTildeX Z X) (reducedRankTildeY Z Y) G
        (reducedRankAhat (reducedRankTildeX Z X) (reducedRankTildeY Z Y) G)
        (reducedRankChat Z X Y G
          (reducedRankAhat (reducedRankTildeX Z X) (reducedRankTildeY Z Y) G)))
      (reducedRankCovarianceRecovery
        (reducedRankTildeX Z X) (reducedRankTildeY Z Y) G
        (reducedRankSigmaHat (reducedRankTildeX Z X) (reducedRankTildeY Z Y) G))
      (reducedRankLikelihoodValue (reducedRankTildeY Z Y) lambda
        (reducedRankMaximizedLogLikelihood (reducedRankTildeY Z Y) lambda)) :=
  reducedRankMLE_of_hansen_objective_optimizer Z X
    (reducedRankTildeX Z X) Y (reducedRankTildeY Z Y) G lambda hG hOpt

section HansenTheorem11_7Conclusion

variable {s : Type*} [Fintype s] [DecidableEq s]

/-- Canonical theorem-facing conclusion for Hansen Theorem 11.7.

The residual-pencil complement maximizes the direct determinant objective in
equation (11.21), so its selected roots are the largest roots on that surface.
The conclusion also retains the identifying equation
`A⊥'Ỹ'X̃G = 0`, which becomes `A⊥' Ahat = 0` under the displayed normalized
coefficient formula. The input certificate remains an explicit premise: this
structure does not manufacture the generalized eigenspaces from the raw normal
likelihood assumptions. Despite its compatibility name, this structure is only
the formula/spectral conclusion; it neither states covariance positive
definiteness nor compares the raw Gaussian likelihood with admissible
competitors. -/
structure ReducedRankHansenTheorem11_7
    (Z : Matrix n ell ℝ) (X Xtilde : Matrix n k ℝ) (Y Ytilde Etilde : Matrix n m ℝ)
    (G : Matrix k r ℝ) (Acoef : Matrix m r ℝ) (C : Matrix ell m ℝ)
    (Sigma : Matrix m m ℝ) (Aperp : Matrix m s ℝ)
    (lambda : r → ℝ) (eta : s → ℝ) (logLikelihood : ℝ) : Prop where
  identified_spectral_maximizers :
    ReducedRankHansenIdentifiedSpectralMaximizerCertificate
      Xtilde Ytilde Etilde G lambda Aperp eta
  g_objective_maximizer : reducedRankConcentratedObjectiveMaximizer Xtilde Ytilde G
  aperp_objective_maximizer : reducedRankAperpObjectiveMaximizer Etilde Ytilde Aperp
  aperp_cross_orthogonal : reducedRankAperpCrossOrthogonal Xtilde Ytilde G Aperp
  a_formula : Acoef = Ytildeᵀ * Xtilde * G
  c_formula : C = reducedRankChat Z X Y G Acoef
  sigma_formula :
    Sigma = (Fintype.card n : ℝ)⁻¹ • (Ytildeᵀ * Ytilde - Acoef * Acoefᵀ)
  likelihood_formula : logLikelihood = reducedRankMaximizedLogLikelihood Ytilde lambda
  least_squares_recovery :
    reducedRankLeastSquaresRecovery Z X Y Xtilde Ytilde G Acoef C
  covariance_recovery : reducedRankCovarianceRecovery Xtilde Ytilde G Sigma
  likelihood_value : reducedRankLikelihoodValue Ytilde lambda logLikelihood
  mle_formula_certificate :
    ReducedRankMLEFormulaCertificate G Acoef C Sigma logLikelihood
      (ReducedRankHansenIdentifiedSpectralMaximizerCertificate
        Xtilde Ytilde Etilde G lambda Aperp eta)
      (reducedRankLeastSquaresRecovery Z X Y Xtilde Ytilde G Acoef C)
      (reducedRankCovarianceRecovery Xtilde Ytilde G Sigma)
      (reducedRankLikelihoodValue Ytilde lambda logLikelihood)

/-- Canonical Hansen 11.7 conclusion with the exact complementary-rank
dimension recorded. -/
structure ReducedRankHansenTheorem11_7ExactDimension
    (Z : Matrix n ell ℝ) (X Xtilde : Matrix n k ℝ) (Y Ytilde Etilde : Matrix n m ℝ)
    (G : Matrix k r ℝ) (Acoef : Matrix m r ℝ) (C : Matrix ell m ℝ)
    (Sigma : Matrix m m ℝ) (Aperp : Matrix m s ℝ)
    (lambda : r → ℝ) (eta : s → ℝ) (logLikelihood : ℝ) : Prop where
  theorem11_7 :
    ReducedRankHansenTheorem11_7 Z X Xtilde Y Ytilde Etilde G Acoef C Sigma
      Aperp lambda eta logLikelihood
  aperp_dimension : Fintype.card s = Fintype.card m - Fintype.card r

omit [DecidableEq n] in
/-- Assemble the canonical identified Hansen 11.7 conclusion from the max/max
spectral certificate and the normalized recovery formulas. -/
theorem reducedRankHansenTheorem11_7_of_identified_spectral_maximizer_certificate
    (Z : Matrix n ell ℝ) (X Xtilde : Matrix n k ℝ) (Y Ytilde Etilde : Matrix n m ℝ)
    (G : Matrix k r ℝ) (lambda : r → ℝ)
    (Aperp : Matrix m s ℝ) (eta : s → ℝ)
    (hSpec : ReducedRankHansenIdentifiedSpectralMaximizerCertificate
      Xtilde Ytilde Etilde G lambda Aperp eta) :
    ReducedRankHansenTheorem11_7 Z X Xtilde Y Ytilde Etilde G
      (Ytildeᵀ * Xtilde * G)
      (reducedRankChat Z X Y G (Ytildeᵀ * Xtilde * G))
      ((Fintype.card n : ℝ)⁻¹ •
        (Ytildeᵀ * Ytilde -
          (Ytildeᵀ * Xtilde * G) * (Ytildeᵀ * Xtilde * G)ᵀ))
      Aperp lambda eta (reducedRankMaximizedLogLikelihood Ytilde lambda) where
  identified_spectral_maximizers := hSpec
  g_objective_maximizer := hSpec.spectral_maximizers.g_objectiveMaximizer
  aperp_objective_maximizer := hSpec.spectral_maximizers.aperp_objectiveMaximizer
  aperp_cross_orthogonal := hSpec.aperp_cross_orthogonal
  a_formula := rfl
  c_formula := rfl
  sigma_formula := rfl
  likelihood_formula := rfl
  least_squares_recovery := by
    constructor
    · exact (reducedRankAhat_eq_cross_of_normalized
        Xtilde Ytilde G hSpec.spectral_maximizers.g_max.normalized).symm
    · rfl
  covariance_recovery :=
    (reducedRankSigmaHat_eq_Ahat_mul_transpose_of_normalized
      Xtilde Ytilde G hSpec.spectral_maximizers.g_max.normalized).symm
  likelihood_value := rfl
  mle_formula_certificate := by
    exact reducedRankMLE_of_certificate G
      (Ytildeᵀ * Xtilde * G)
      (reducedRankChat Z X Y G (Ytildeᵀ * Xtilde * G))
      ((Fintype.card n : ℝ)⁻¹ •
        (Ytildeᵀ * Ytilde -
          (Ytildeᵀ * Xtilde * G) * (Ytildeᵀ * Xtilde * G)ᵀ))
      (reducedRankMaximizedLogLikelihood Ytilde lambda)
      hSpec
      (by
        constructor
        · exact (reducedRankAhat_eq_cross_of_normalized
            Xtilde Ytilde G hSpec.spectral_maximizers.g_max.normalized).symm
        · rfl)
      ((reducedRankSigmaHat_eq_Ahat_mul_transpose_of_normalized
        Xtilde Ytilde G hSpec.spectral_maximizers.g_max.normalized).symm)
      rfl

omit [DecidableEq n] in
/-- Direct objective form of the canonical identified Hansen 11.7 endpoint. -/
theorem reducedRankHansenTheorem11_7_of_objective_maximizers_and_cross
    (Z : Matrix n ell ℝ) (X Xtilde : Matrix n k ℝ) (Y Ytilde Etilde : Matrix n m ℝ)
    (G : Matrix k r ℝ) (lambda : r → ℝ)
    (Aperp : Matrix m s ℝ) (eta : s → ℝ)
    (hG : reducedRankHansenGEigenvectors Xtilde Ytilde lambda G)
    (hGOpt : reducedRankConcentratedObjectiveMaximizer Xtilde Ytilde G)
    (hAperp : reducedRankHansenAperpEigenvectors Etilde Ytilde eta Aperp)
    (hAperpOpt : reducedRankAperpObjectiveMaximizer Etilde Ytilde Aperp)
    (hCross : reducedRankAperpCrossOrthogonal Xtilde Ytilde G Aperp) :
    ReducedRankHansenTheorem11_7 Z X Xtilde Y Ytilde Etilde G
      (Ytildeᵀ * Xtilde * G)
      (reducedRankChat Z X Y G (Ytildeᵀ * Xtilde * G))
      ((Fintype.card n : ℝ)⁻¹ •
        (Ytildeᵀ * Ytilde -
          (Ytildeᵀ * Xtilde * G) * (Ytildeᵀ * Xtilde * G)ᵀ))
      Aperp lambda eta (reducedRankMaximizedLogLikelihood Ytilde lambda) :=
  reducedRankHansenTheorem11_7_of_identified_spectral_maximizer_certificate
    Z X Xtilde Y Ytilde Etilde G lambda Aperp eta
    (ReducedRankHansenIdentifiedSpectralMaximizerCertificate.of_objective_maximizers_and_cross
      Xtilde Ytilde Etilde G lambda Aperp eta
      hG hGOpt hAperp hAperpOpt hCross)

omit [DecidableEq n] in
/-- Canonical Hansen 11.7 endpoint from the max/max spectral certificate and
Hansen's displayed dual relation.

Cross orthogonality is derived by
`reducedRankAperp_cross_orthogonal_of_dual_relation` and remains a field of the
returned theorem conclusion. -/
theorem reducedRankHansenTheorem11_7_of_maxMax_and_dual_relation
    (Z : Matrix n ell ℝ) (X Xtilde : Matrix n k ℝ) (Y Ytilde Etilde : Matrix n m ℝ)
    (G : Matrix k r ℝ) (lambda : r → ℝ)
    (Aperp : Matrix m s ℝ) (eta : s → ℝ)
    (hMax : ReducedRankHansenDetProductMaxMaxCertificate
      Xtilde Ytilde Etilde G lambda Aperp eta)
    (W : Matrix m r ℝ) (Lambda LambdaInv : Matrix r r ℝ)
    (hDual : reducedRankDualEigenvectorRelation Xtilde Ytilde G W Lambda)
    (hOrth : reducedRankAperpYOrthogonal Ytilde Aperp W)
    (hLambdaInv : Lambda * LambdaInv = 1) :
    ReducedRankHansenTheorem11_7 Z X Xtilde Y Ytilde Etilde G
      (Ytildeᵀ * Xtilde * G)
      (reducedRankChat Z X Y G (Ytildeᵀ * Xtilde * G))
      ((Fintype.card n : ℝ)⁻¹ •
        (Ytildeᵀ * Ytilde -
          (Ytildeᵀ * Xtilde * G) * (Ytildeᵀ * Xtilde * G)ᵀ))
      Aperp lambda eta (reducedRankMaximizedLogLikelihood Ytilde lambda) :=
  reducedRankHansenTheorem11_7_of_identified_spectral_maximizer_certificate
    Z X Xtilde Y Ytilde Etilde G lambda Aperp eta
    (ReducedRankHansenIdentifiedSpectralMaximizerCertificate.of_maxMax_and_dual_relation
      hMax W Lambda LambdaInv hDual hOrth hLambdaInv)

omit [DecidableEq n] in
/-- Add Hansen's exact complementary dimension to the canonical identified
conclusion. -/
theorem ReducedRankHansenTheorem11_7ExactDimension.of_theorem11_7
    {Z : Matrix n ell ℝ} {X Xtilde : Matrix n k ℝ} {Y Ytilde Etilde : Matrix n m ℝ}
    {G : Matrix k r ℝ} {Acoef : Matrix m r ℝ} {C : Matrix ell m ℝ}
    {Sigma : Matrix m m ℝ} {Aperp : Matrix m s ℝ}
    {lambda : r → ℝ} {eta : s → ℝ} {logLikelihood : ℝ}
    (h : ReducedRankHansenTheorem11_7 Z X Xtilde Y Ytilde Etilde G Acoef C Sigma
      Aperp lambda eta logLikelihood)
    (hdim : Fintype.card s = Fintype.card m - Fintype.card r) :
    ReducedRankHansenTheorem11_7ExactDimension
      Z X Xtilde Y Ytilde Etilde G Acoef C Sigma Aperp lambda eta logLikelihood where
  theorem11_7 := h
  aperp_dimension := hdim

/-- Compatibility conclusion for the internally inconsistent smallest-root
sentence in the final summary of Hansen Theorem 11.7.

Equation (11.21), its derivation, and the equivalent residual-pencil display
all use a maximum and the largest roots. This structure preserves the literal
smallest-root summary only for old callers. In particular it has no MLE field
and does not identify its `A⊥` minimum as the MLE complement. -/
structure ReducedRankHansenSmallestSummaryCompatibility
    (Z : Matrix n ell ℝ) (X Xtilde : Matrix n k ℝ) (Y Ytilde Etilde : Matrix n m ℝ)
    (G : Matrix k r ℝ) (Acoef : Matrix m r ℝ) (C : Matrix ell m ℝ)
    (Sigma : Matrix m m ℝ) (Aperp : Matrix m s ℝ)
    (lambda : r → ℝ) (eta : s → ℝ) (logLikelihood : ℝ) : Prop where
  spectral_duality :
    ReducedRankHansenSpectralDualityCertificate Xtilde Ytilde Etilde G lambda Aperp eta
  g_objective_maximizer : reducedRankConcentratedObjectiveMaximizer Xtilde Ytilde G
  aperp_objective_minimizer : reducedRankAperpObjectiveMinimizer Etilde Ytilde Aperp
  a_formula : Acoef = Ytildeᵀ * Xtilde * G
  c_formula : C = reducedRankChat Z X Y G Acoef
  sigma_formula :
    Sigma = (Fintype.card n : ℝ)⁻¹ • (Ytildeᵀ * Ytilde - Acoef * Acoefᵀ)
  likelihood_formula : logLikelihood = reducedRankMaximizedLogLikelihood Ytilde lambda
  least_squares_recovery :
    reducedRankLeastSquaresRecovery Z X Y Xtilde Ytilde G Acoef C
  covariance_recovery : reducedRankCovarianceRecovery Xtilde Ytilde G Sigma
  likelihood_value : reducedRankLikelihoodValue Ytilde lambda logLikelihood

/-- Exact-dimension wrapper for the literal smallest-summary compatibility
surface. This remains non-MLE compatibility for Hansen's internal typo. -/
structure ReducedRankHansenSmallestSummaryCompatibilityExactDimension
    (Z : Matrix n ell ℝ) (X Xtilde : Matrix n k ℝ) (Y Ytilde Etilde : Matrix n m ℝ)
    (G : Matrix k r ℝ) (Acoef : Matrix m r ℝ) (C : Matrix ell m ℝ)
    (Sigma : Matrix m m ℝ) (Aperp : Matrix m s ℝ)
    (lambda : r → ℝ) (eta : s → ℝ) (logLikelihood : ℝ) : Prop where
  theorem11_7 :
    ReducedRankHansenSmallestSummaryCompatibility
      Z X Xtilde Y Ytilde Etilde G Acoef C Sigma
      Aperp lambda eta logLikelihood
  aperp_dimension : Fintype.card s = Fintype.card m - Fintype.card r

omit [DecidableEq n] in
/-- Add Hansen's exact complementary-rank dimension to an existing Theorem
11.7 certificate. -/
theorem ReducedRankHansenSmallestSummaryCompatibilityExactDimension.of_theorem11_7
    {Z : Matrix n ell ℝ} {X Xtilde : Matrix n k ℝ} {Y Ytilde Etilde : Matrix n m ℝ}
    {G : Matrix k r ℝ} {Acoef : Matrix m r ℝ} {C : Matrix ell m ℝ}
    {Sigma : Matrix m m ℝ} {Aperp : Matrix m s ℝ}
    {lambda : r → ℝ} {eta : s → ℝ} {logLikelihood : ℝ}
    (h : ReducedRankHansenSmallestSummaryCompatibility Z X Xtilde Y Ytilde Etilde G Acoef C Sigma
      Aperp lambda eta logLikelihood)
    (hdim : Fintype.card s = Fintype.card m - Fintype.card r) :
    ReducedRankHansenSmallestSummaryCompatibilityExactDimension
      Z X Xtilde Y Ytilde Etilde G Acoef C Sigma Aperp lambda eta logLikelihood where
  theorem11_7 := h
  aperp_dimension := hdim

omit [DecidableEq n] [DecidableEq m] [DecidableEq r] [DecidableEq s] in
/-- Convert a block-cardinality split `m = r + s` into Hansen's exact
complementary-rank dimension `s = m - r`. -/
theorem reducedRankAperpDimension_of_card_eq_add
    (hcard : Fintype.card m = Fintype.card r + Fintype.card s) :
    Fintype.card s = Fintype.card m - Fintype.card r := by
  rw [hcard, Nat.add_sub_cancel_left]

omit [DecidableEq n] [DecidableEq m] [DecidableEq r] [DecidableEq s] in
/-- Convert an index equivalence `m ≃ r ⊕ s` into Hansen's exact
complementary-rank dimension `s = m - r`. -/
theorem reducedRankAperpDimension_of_equiv_sum
    (e : m ≃ Sum r s) :
    Fintype.card s = Fintype.card m - Fintype.card r :=
  reducedRankAperpDimension_of_card_eq_add (m := m) (r := r) (s := s) <| by
    calc
      Fintype.card m = Fintype.card (Sum r s) := Fintype.card_congr e
      _ = Fintype.card r + Fintype.card s := Fintype.card_sum

omit [DecidableEq n] [DecidableEq m] [DecidableEq r] [DecidableEq s] in
/-- Convert an index equivalence `m ≃ s ⊕ r` into Hansen's exact
complementary-rank dimension `s = m - r`. -/
theorem reducedRankAperpDimension_of_equiv_sum_comm
    (e : m ≃ Sum s r) :
    Fintype.card s = Fintype.card m - Fintype.card r :=
  reducedRankAperpDimension_of_card_eq_add (m := m) (r := r) (s := s) <| by
    calc
      Fintype.card m = Fintype.card (Sum s r) := Fintype.card_congr e
      _ = Fintype.card s + Fintype.card r := Fintype.card_sum
      _ = Fintype.card r + Fintype.card s := Nat.add_comm _ _

/-- Canonical index type for Hansen's `A⊥` block with exactly `m - r`
columns. Using this index removes the need to pass a separate finite split
`m ≃ r ⊕ s` when the raw spectral construction already chooses the complement
with Hansen's displayed dimension. -/
abbrev reducedRankAperpIndex (m r : Type*) [Fintype m] [Fintype r] : Type :=
  Fin (Fintype.card m - Fintype.card r)

omit [DecidableEq n] [DecidableEq m] [DecidableEq r] [DecidableEq s] in
/-- Hansen's strict rank inequality makes the canonical `A⊥` index nonempty. -/
theorem reducedRankAperpIndex_nonempty_of_card_lt
    (hcard : Fintype.card r < Fintype.card m) :
    Nonempty (reducedRankAperpIndex m r) := by
  rw [reducedRankAperpIndex]
  exact Fin.pos_iff_nonempty.mp (Nat.sub_pos_of_lt hcard)

omit [DecidableEq n] [DecidableEq m] [DecidableEq r] [DecidableEq s] in
/-- The canonical `A⊥` index has Hansen's exact complementary dimension. -/
theorem reducedRankAperpDimension_canonical :
    Fintype.card (reducedRankAperpIndex m r) =
      Fintype.card m - Fintype.card r := by
  simp [reducedRankAperpIndex]

omit [DecidableEq n] in
/-- Exact-dimension canonical Hansen 11.7 endpoint from the identified max/max
spectral certificate. -/
theorem
    reducedRankHansenTheorem11_7_exactDimension_of_identified_spectral_maximizer_certificate
    (Z : Matrix n ell ℝ) (X Xtilde : Matrix n k ℝ) (Y Ytilde Etilde : Matrix n m ℝ)
    (G : Matrix k r ℝ) (lambda : r → ℝ)
    (Aperp : Matrix m s ℝ) (eta : s → ℝ)
    (hSpec : ReducedRankHansenIdentifiedSpectralMaximizerCertificate
      Xtilde Ytilde Etilde G lambda Aperp eta)
    (hdim : Fintype.card s = Fintype.card m - Fintype.card r) :
    ReducedRankHansenTheorem11_7ExactDimension Z X Xtilde Y Ytilde Etilde G
      (Ytildeᵀ * Xtilde * G)
      (reducedRankChat Z X Y G (Ytildeᵀ * Xtilde * G))
      ((Fintype.card n : ℝ)⁻¹ •
        (Ytildeᵀ * Ytilde -
          (Ytildeᵀ * Xtilde * G) * (Ytildeᵀ * Xtilde * G)ᵀ))
      Aperp lambda eta (reducedRankMaximizedLogLikelihood Ytilde lambda) :=
  ReducedRankHansenTheorem11_7ExactDimension.of_theorem11_7
    (reducedRankHansenTheorem11_7_of_identified_spectral_maximizer_certificate
      Z X Xtilde Y Ytilde Etilde G lambda Aperp eta hSpec)
    hdim

set_option linter.style.longLine false in
/-- Residualized exact-dimension canonical endpoint at Hansen's `Fin (m-r)`
complement index.

The max/max identified certificate is still an explicit premise; in
particular this wrapper does not claim the unresolved construction of that
certificate from the raw normal likelihood. -/
theorem
    reducedRankHansenTheorem11_7_residualized_exactDimension_of_identified_spectral_maximizer_certificate_canonicalAperp
    (Z : Matrix n ell ℝ) (X : Matrix n k ℝ) (Y : Matrix n m ℝ)
    [DecidableEq k]
    [Invertible (Zᵀ * Z)]
    [Invertible ((Matrix.fromCols X Z)ᵀ * Matrix.fromCols X Z)]
    (G : Matrix k r ℝ) (lambda : r → ℝ)
    (Aperp : Matrix m (reducedRankAperpIndex m r) ℝ)
    (eta : reducedRankAperpIndex m r → ℝ)
    (hSpec : ReducedRankHansenIdentifiedSpectralMaximizerCertificate
      (reducedRankTildeX Z X) (reducedRankTildeY Z Y) (reducedRankTildeE X Z Y)
      G lambda Aperp eta) :
    ReducedRankHansenTheorem11_7ExactDimension
      Z X (reducedRankTildeX Z X) Y (reducedRankTildeY Z Y) (reducedRankTildeE X Z Y) G
      ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G)
      (reducedRankChat Z X Y G
        ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G))
      ((Fintype.card n : ℝ)⁻¹ •
        ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeY Z Y) -
          ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G) *
            ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G)ᵀ))
      Aperp lambda eta (reducedRankMaximizedLogLikelihood (reducedRankTildeY Z Y) lambda) :=
  reducedRankHansenTheorem11_7_exactDimension_of_identified_spectral_maximizer_certificate
    Z X (reducedRankTildeX Z X) Y (reducedRankTildeY Z Y) (reducedRankTildeE X Z Y)
    G lambda Aperp eta hSpec reducedRankAperpDimension_canonical

set_option linter.style.longLine false in
/-- Residualized direct-objective form of the canonical exact-dimension
endpoint. Its `A⊥` premise is the equation (11.21) maximum and the returned
conclusion retains `A⊥'Ỹ'X̃G = 0`. -/
theorem
    reducedRankHansenTheorem11_7_residualized_exactDimension_of_objective_maximizers_and_cross_canonicalAperp
    (Z : Matrix n ell ℝ) (X : Matrix n k ℝ) (Y : Matrix n m ℝ)
    [DecidableEq k]
    [Invertible (Zᵀ * Z)]
    [Invertible ((Matrix.fromCols X Z)ᵀ * Matrix.fromCols X Z)]
    (G : Matrix k r ℝ) (lambda : r → ℝ)
    (Aperp : Matrix m (reducedRankAperpIndex m r) ℝ)
    (eta : reducedRankAperpIndex m r → ℝ)
    (hG : reducedRankHansenGEigenvectors
      (reducedRankTildeX Z X) (reducedRankTildeY Z Y) lambda G)
    (hGOpt : reducedRankConcentratedObjectiveMaximizer
      (reducedRankTildeX Z X) (reducedRankTildeY Z Y) G)
    (hAperp : reducedRankHansenAperpEigenvectors
      (reducedRankTildeE X Z Y) (reducedRankTildeY Z Y) eta Aperp)
    (hAperpOpt : reducedRankAperpObjectiveMaximizer
      (reducedRankTildeE X Z Y) (reducedRankTildeY Z Y) Aperp)
    (hCross : reducedRankAperpCrossOrthogonal
      (reducedRankTildeX Z X) (reducedRankTildeY Z Y) G Aperp) :
    ReducedRankHansenTheorem11_7ExactDimension
      Z X (reducedRankTildeX Z X) Y (reducedRankTildeY Z Y) (reducedRankTildeE X Z Y) G
      ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G)
      (reducedRankChat Z X Y G
        ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G))
      ((Fintype.card n : ℝ)⁻¹ •
        ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeY Z Y) -
          ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G) *
            ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G)ᵀ))
      Aperp lambda eta (reducedRankMaximizedLogLikelihood (reducedRankTildeY Z Y) lambda) :=
  reducedRankHansenTheorem11_7_residualized_exactDimension_of_identified_spectral_maximizer_certificate_canonicalAperp
    Z X Y G lambda Aperp eta
    (ReducedRankHansenIdentifiedSpectralMaximizerCertificate.of_objective_maximizers_and_cross
      (reducedRankTildeX Z X) (reducedRankTildeY Z Y) (reducedRankTildeE X Z Y)
      G lambda Aperp eta hG hGOpt hAperp hAperpOpt hCross)

omit [DecidableEq n] in
/-- Literal-smallest-summary compatibility from the old min-oriented spectral
certificate.

This exposes the recovery formulas but deliberately does not return an MLE:
the `A⊥` minimum reflects Hansen's internally inconsistent final summary, not
equation (11.21). Use
`reducedRankHansenTheorem11_7_of_identified_spectral_maximizer_certificate` for
the canonical theorem-facing result. -/
theorem reducedRankHansenTheorem11_7_of_spectral_duality_certificate
    (Z : Matrix n ell ℝ) (X Xtilde : Matrix n k ℝ) (Y Ytilde Etilde : Matrix n m ℝ)
    (G : Matrix k r ℝ) (lambda : r → ℝ)
    (Aperp : Matrix m s ℝ) (eta : s → ℝ)
    (hSpec : ReducedRankHansenSpectralDualityCertificate
      Xtilde Ytilde Etilde G lambda Aperp eta) :
    ReducedRankHansenSmallestSummaryCompatibility
      Z X Xtilde Y Ytilde Etilde G
      (Ytildeᵀ * Xtilde * G)
      (reducedRankChat Z X Y G (Ytildeᵀ * Xtilde * G))
      ((Fintype.card n : ℝ)⁻¹ •
        (Ytildeᵀ * Ytilde -
          (Ytildeᵀ * Xtilde * G) * (Ytildeᵀ * Xtilde * G)ᵀ))
      Aperp lambda eta (reducedRankMaximizedLogLikelihood Ytilde lambda) where
  spectral_duality := hSpec
  g_objective_maximizer :=
    ReducedRankHansenSpectralDualityCertificate.g_objectiveMaximizer hSpec
  aperp_objective_minimizer :=
    ReducedRankHansenSpectralDualityCertificate.aperp_objectiveMinimizer hSpec
  a_formula := rfl
  c_formula := rfl
  sigma_formula := rfl
  likelihood_formula := rfl
  least_squares_recovery := by
    constructor
    · exact (reducedRankAhat_eq_cross_of_normalized
        Xtilde Ytilde G hSpec.g_normalized).symm
    · rfl
  covariance_recovery :=
    (reducedRankSigmaHat_eq_Ahat_mul_transpose_of_normalized
      Xtilde Ytilde G hSpec.g_normalized).symm
  likelihood_value := rfl

omit [DecidableEq n] in
/-- Hansen Theorem 11.7 from the exact spectral-duality certificate, with
Hansen's complementary-rank condition `dim(A⊥) = m - r` carried explicitly. -/
theorem reducedRankHansenTheorem11_7_exactDimension_of_spectral_duality_certificate
    (Z : Matrix n ell ℝ) (X Xtilde : Matrix n k ℝ) (Y Ytilde Etilde : Matrix n m ℝ)
    (G : Matrix k r ℝ) (lambda : r → ℝ)
    (Aperp : Matrix m s ℝ) (eta : s → ℝ)
    (hSpec : ReducedRankHansenSpectralDualityCertificate
      Xtilde Ytilde Etilde G lambda Aperp eta)
    (hdim : Fintype.card s = Fintype.card m - Fintype.card r) :
    ReducedRankHansenSmallestSummaryCompatibilityExactDimension Z X Xtilde Y Ytilde Etilde G
      (Ytildeᵀ * Xtilde * G)
      (reducedRankChat Z X Y G (Ytildeᵀ * Xtilde * G))
      ((Fintype.card n : ℝ)⁻¹ •
        (Ytildeᵀ * Ytilde -
          (Ytildeᵀ * Xtilde * G) * (Ytildeᵀ * Xtilde * G)ᵀ))
      Aperp lambda eta (reducedRankMaximizedLogLikelihood Ytilde lambda) :=
  ReducedRankHansenSmallestSummaryCompatibilityExactDimension.of_theorem11_7
    (reducedRankHansenTheorem11_7_of_spectral_duality_certificate
      Z X Xtilde Y Ytilde Etilde G lambda Aperp eta hSpec)
    hdim

omit [DecidableEq n] in
/-- Smallest-summary compatibility projection from the old identified
min-oriented certificate.

This deliberately returns only the compatibility structure. Canonical
identified endpoints return `ReducedRankHansenTheorem11_7`, whose public
`aperp_cross_orthogonal` field retains `A⊥'Ỹ'X̃G = 0`. -/
theorem reducedRankHansenSmallestSummaryCompatibility_of_identified_spectral_duality_certificate
    (Z : Matrix n ell ℝ) (X Xtilde : Matrix n k ℝ) (Y Ytilde Etilde : Matrix n m ℝ)
    (G : Matrix k r ℝ) (lambda : r → ℝ)
    (Aperp : Matrix m s ℝ) (eta : s → ℝ)
    (hSpec : ReducedRankHansenIdentifiedSpectralDualityCertificate
      Xtilde Ytilde Etilde G lambda Aperp eta) :
    ReducedRankHansenSmallestSummaryCompatibility
      Z X Xtilde Y Ytilde Etilde G
      (Ytildeᵀ * Xtilde * G)
      (reducedRankChat Z X Y G (Ytildeᵀ * Xtilde * G))
      ((Fintype.card n : ℝ)⁻¹ •
        (Ytildeᵀ * Ytilde -
          (Ytildeᵀ * Xtilde * G) * (Ytildeᵀ * Xtilde * G)ᵀ))
      Aperp lambda eta (reducedRankMaximizedLogLikelihood Ytilde lambda) :=
  reducedRankHansenTheorem11_7_of_spectral_duality_certificate
    Z X Xtilde Y Ytilde Etilde G lambda Aperp eta
    hSpec.to_spectralDualityCertificate

omit [DecidableEq n] in
/-- Hansen Theorem 11.7 from the determinant/product min-max certificate plus
Hansen's displayed dual generalized-eigenvector relation.

The dual relation supplies the strengthened subspace identity
`A⊥'Ỹ'X̃G = 0`; the determinant/product min-max certificate supplies the exact
G-side and `A⊥`-side variational bounds. -/
theorem reducedRankHansenTheorem11_7_of_detProductMinMax_and_dual_relation
    (Z : Matrix n ell ℝ) (X Xtilde : Matrix n k ℝ) (Y Ytilde Etilde : Matrix n m ℝ)
    (G : Matrix k r ℝ) (lambda : r → ℝ)
    (Aperp : Matrix m s ℝ) (eta : s → ℝ)
    (hMinMax : ReducedRankHansenDetProductMinMaxCertificate
      Xtilde Ytilde Etilde G lambda Aperp eta)
    (W : Matrix m r ℝ) (Lambda LambdaInv : Matrix r r ℝ)
    (hDual : reducedRankDualEigenvectorRelation Xtilde Ytilde G W Lambda)
    (hOrth : reducedRankAperpYOrthogonal Ytilde Aperp W)
    (hLambdaInv : Lambda * LambdaInv = 1) :
    ReducedRankHansenSmallestSummaryCompatibility
      Z X Xtilde Y Ytilde Etilde G
      (Ytildeᵀ * Xtilde * G)
      (reducedRankChat Z X Y G (Ytildeᵀ * Xtilde * G))
      ((Fintype.card n : ℝ)⁻¹ •
        (Ytildeᵀ * Ytilde -
          (Ytildeᵀ * Xtilde * G) * (Ytildeᵀ * Xtilde * G)ᵀ))
      Aperp lambda eta (reducedRankMaximizedLogLikelihood Ytilde lambda) :=
  reducedRankHansenSmallestSummaryCompatibility_of_identified_spectral_duality_certificate
    Z X Xtilde Y Ytilde Etilde G lambda Aperp eta
    (ReducedRankHansenIdentifiedSpectralDualityCertificate.of_detProductMinMax_and_dual_relation
      hMinMax W Lambda LambdaInv hDual hOrth hLambdaInv)

omit [DecidableEq n] in
/-- Hansen Theorem 11.7 from the determinant/product min-max certificate.

This endpoint is the theorem-facing spectral route: it assumes selected
compressed determinant maximality/minimality for Hansen's two generalized
pencils, not the final spectral-duality product bounds or the MLE conclusion. -/
theorem reducedRankHansenTheorem11_7_of_detProductMinMax_certificate
    (Z : Matrix n ell ℝ) (X Xtilde : Matrix n k ℝ) (Y Ytilde Etilde : Matrix n m ℝ)
    (G : Matrix k r ℝ) (lambda : r → ℝ)
    (Aperp : Matrix m s ℝ) (eta : s → ℝ)
    (hMinMax : ReducedRankHansenDetProductMinMaxCertificate
      Xtilde Ytilde Etilde G lambda Aperp eta) :
    ReducedRankHansenSmallestSummaryCompatibility
      Z X Xtilde Y Ytilde Etilde G
      (Ytildeᵀ * Xtilde * G)
      (reducedRankChat Z X Y G (Ytildeᵀ * Xtilde * G))
      ((Fintype.card n : ℝ)⁻¹ •
        (Ytildeᵀ * Ytilde -
          (Ytildeᵀ * Xtilde * G) * (Ytildeᵀ * Xtilde * G)ᵀ))
      Aperp lambda eta (reducedRankMaximizedLogLikelihood Ytilde lambda) :=
  reducedRankHansenTheorem11_7_of_spectral_duality_certificate
    Z X Xtilde Y Ytilde Etilde G lambda Aperp eta
    (ReducedRankHansenDetProductMinMaxCertificate.to_spectralDualityCertificate hMinMax)

omit [DecidableEq n] in
/-- Hansen Theorem 11.7 from the normal-likelihood objective-extrema
certificate. This is the theorem-facing route for callers that have already
proved the exact G-side objective maximum and `A⊥` objective minimum. -/
theorem reducedRankHansenTheorem11_7_of_objective_extrema_certificate
    (Z : Matrix n ell ℝ) (X Xtilde : Matrix n k ℝ) (Y Ytilde Etilde : Matrix n m ℝ)
    (G : Matrix k r ℝ) (lambda : r → ℝ)
    (Aperp : Matrix m s ℝ) (eta : s → ℝ)
    (hObj : ReducedRankHansenObjectiveExtremaCertificate
      Xtilde Ytilde Etilde G lambda Aperp eta) :
    ReducedRankHansenSmallestSummaryCompatibility
      Z X Xtilde Y Ytilde Etilde G
      (Ytildeᵀ * Xtilde * G)
      (reducedRankChat Z X Y G (Ytildeᵀ * Xtilde * G))
      ((Fintype.card n : ℝ)⁻¹ •
        (Ytildeᵀ * Ytilde -
          (Ytildeᵀ * Xtilde * G) * (Ytildeᵀ * Xtilde * G)ᵀ))
      Aperp lambda eta (reducedRankMaximizedLogLikelihood Ytilde lambda) :=
  reducedRankHansenTheorem11_7_of_spectral_duality_certificate
    Z X Xtilde Y Ytilde Etilde G lambda Aperp eta
    hObj.to_spectralDualityCertificate

omit [DecidableEq n] in
/-- Hansen Theorem 11.7 from the normal-likelihood objective extrema for the
`G` and `A⊥` determinant objectives. The determinant/product min-max bounds are
derived, not assumed. -/
theorem reducedRankHansenTheorem11_7_of_objective_extrema
    (Z : Matrix n ell ℝ) (X Xtilde : Matrix n k ℝ) (Y Ytilde Etilde : Matrix n m ℝ)
    (G : Matrix k r ℝ) (lambda : r → ℝ)
    (Aperp : Matrix m s ℝ) (eta : s → ℝ)
    (hG : reducedRankHansenGEigenvectors Xtilde Ytilde lambda G)
    (hGOpt : reducedRankConcentratedObjectiveMaximizer Xtilde Ytilde G)
    (hAperp : reducedRankHansenAperpEigenvectors Etilde Ytilde eta Aperp)
    (hAperpOpt : reducedRankAperpObjectiveMinimizer Etilde Ytilde Aperp) :
    ReducedRankHansenSmallestSummaryCompatibility
      Z X Xtilde Y Ytilde Etilde G
      (Ytildeᵀ * Xtilde * G)
      (reducedRankChat Z X Y G (Ytildeᵀ * Xtilde * G))
      ((Fintype.card n : ℝ)⁻¹ •
        (Ytildeᵀ * Ytilde -
          (Ytildeᵀ * Xtilde * G) * (Ytildeᵀ * Xtilde * G)ᵀ))
      Aperp lambda eta (reducedRankMaximizedLogLikelihood Ytilde lambda) :=
  reducedRankHansenTheorem11_7_of_objective_extrema_certificate
    Z X Xtilde Y Ytilde Etilde G lambda Aperp eta
    { g_eigenvectors := hG
      g_objective_maximizer := hGOpt
      aperp_eigenvectors := hAperp
      aperp_objective_minimizer := hAperpOpt }

omit [DecidableEq n] in
/-- Hansen Theorem 11.7 from objective extrema plus Hansen's displayed dual
generalized-eigenvector relation, routed through the identified certificate
that stores `A⊥'Ỹ'X̃G = 0`. -/
theorem reducedRankHansenTheorem11_7_of_objective_extrema_certificate_and_dual_relation
    (Z : Matrix n ell ℝ) (X Xtilde : Matrix n k ℝ) (Y Ytilde Etilde : Matrix n m ℝ)
    (G : Matrix k r ℝ) (lambda : r → ℝ)
    (Aperp : Matrix m s ℝ) (eta : s → ℝ)
    (hObj : ReducedRankHansenObjectiveExtremaCertificate
      Xtilde Ytilde Etilde G lambda Aperp eta)
    (W : Matrix m r ℝ) (Lambda LambdaInv : Matrix r r ℝ)
    (hDual : reducedRankDualEigenvectorRelation Xtilde Ytilde G W Lambda)
    (hOrth : reducedRankAperpYOrthogonal Ytilde Aperp W)
    (hLambdaInv : Lambda * LambdaInv = 1) :
    ReducedRankHansenSmallestSummaryCompatibility
      Z X Xtilde Y Ytilde Etilde G
      (Ytildeᵀ * Xtilde * G)
      (reducedRankChat Z X Y G (Ytildeᵀ * Xtilde * G))
      ((Fintype.card n : ℝ)⁻¹ •
        (Ytildeᵀ * Ytilde -
          (Ytildeᵀ * Xtilde * G) * (Ytildeᵀ * Xtilde * G)ᵀ))
      Aperp lambda eta (reducedRankMaximizedLogLikelihood Ytilde lambda) :=
  reducedRankHansenTheorem11_7_of_detProductMinMax_and_dual_relation
    Z X Xtilde Y Ytilde Etilde G lambda Aperp eta
    hObj.to_detProductMinMaxCertificate W Lambda LambdaInv hDual hOrth hLambdaInv

omit [DecidableEq n] in
/-- Hansen Theorem 11.7 from normal-likelihood objective extrema plus Hansen's
displayed dual generalized-eigenvector relation. -/
theorem reducedRankHansenTheorem11_7_of_objective_extrema_and_dual_relation
    (Z : Matrix n ell ℝ) (X Xtilde : Matrix n k ℝ) (Y Ytilde Etilde : Matrix n m ℝ)
    (G : Matrix k r ℝ) (lambda : r → ℝ)
    (Aperp : Matrix m s ℝ) (eta : s → ℝ)
    (hG : reducedRankHansenGEigenvectors Xtilde Ytilde lambda G)
    (hGOpt : reducedRankConcentratedObjectiveMaximizer Xtilde Ytilde G)
    (hAperp : reducedRankHansenAperpEigenvectors Etilde Ytilde eta Aperp)
    (hAperpOpt : reducedRankAperpObjectiveMinimizer Etilde Ytilde Aperp)
    (W : Matrix m r ℝ) (Lambda LambdaInv : Matrix r r ℝ)
    (hDual : reducedRankDualEigenvectorRelation Xtilde Ytilde G W Lambda)
    (hOrth : reducedRankAperpYOrthogonal Ytilde Aperp W)
    (hLambdaInv : Lambda * LambdaInv = 1) :
    ReducedRankHansenSmallestSummaryCompatibility
      Z X Xtilde Y Ytilde Etilde G
      (Ytildeᵀ * Xtilde * G)
      (reducedRankChat Z X Y G (Ytildeᵀ * Xtilde * G))
      ((Fintype.card n : ℝ)⁻¹ •
        (Ytildeᵀ * Ytilde -
          (Ytildeᵀ * Xtilde * G) * (Ytildeᵀ * Xtilde * G)ᵀ))
      Aperp lambda eta (reducedRankMaximizedLogLikelihood Ytilde lambda) :=
  reducedRankHansenTheorem11_7_of_objective_extrema_certificate_and_dual_relation
    Z X Xtilde Y Ytilde Etilde G lambda Aperp eta
    { g_eigenvectors := hG
      g_objective_maximizer := hGOpt
      aperp_eigenvectors := hAperp
      aperp_objective_minimizer := hAperpOpt }
    W Lambda LambdaInv hDual hOrth hLambdaInv

omit [DecidableEq n] in
/-- Hansen Theorem 11.7 from the determinant/product min-max certificate and
Hansen's displayed dual generalized-eigenvector relation, with the exact
complementary-rank dimension carried explicitly.

This combines the strongest current deterministic route: the min-max
certificate supplies the G-side and `A⊥` determinant/product variational
bounds, the dual relation supplies `A⊥'Ỹ'X̃G = 0`, and `hdim` records
Hansen's `m-r` column count. -/
theorem reducedRankHansenTheorem11_7_exactDimension_of_detProductMinMax_and_dual_relation
    (Z : Matrix n ell ℝ) (X Xtilde : Matrix n k ℝ) (Y Ytilde Etilde : Matrix n m ℝ)
    (G : Matrix k r ℝ) (lambda : r → ℝ)
    (Aperp : Matrix m s ℝ) (eta : s → ℝ)
    (hMinMax : ReducedRankHansenDetProductMinMaxCertificate
      Xtilde Ytilde Etilde G lambda Aperp eta)
    (W : Matrix m r ℝ) (Lambda LambdaInv : Matrix r r ℝ)
    (hDual : reducedRankDualEigenvectorRelation Xtilde Ytilde G W Lambda)
    (hOrth : reducedRankAperpYOrthogonal Ytilde Aperp W)
    (hLambdaInv : Lambda * LambdaInv = 1)
    (hdim : Fintype.card s = Fintype.card m - Fintype.card r) :
    ReducedRankHansenSmallestSummaryCompatibilityExactDimension Z X Xtilde Y Ytilde Etilde G
      (Ytildeᵀ * Xtilde * G)
      (reducedRankChat Z X Y G (Ytildeᵀ * Xtilde * G))
      ((Fintype.card n : ℝ)⁻¹ •
        (Ytildeᵀ * Ytilde -
          (Ytildeᵀ * Xtilde * G) * (Ytildeᵀ * Xtilde * G)ᵀ))
      Aperp lambda eta (reducedRankMaximizedLogLikelihood Ytilde lambda) :=
  ReducedRankHansenSmallestSummaryCompatibilityExactDimension.of_theorem11_7
    (reducedRankHansenTheorem11_7_of_detProductMinMax_and_dual_relation
      Z X Xtilde Y Ytilde Etilde G lambda Aperp eta
      hMinMax W Lambda LambdaInv hDual hOrth hLambdaInv)
    hdim

set_option linter.style.longLine false in
omit [DecidableEq n] in
/-- Hansen Theorem 11.7 from the determinant/product min-max certificate,
Hansen's displayed diagonal dual relation, nonzero selected compressed
determinant, and a concrete complementary index split.

This is the exact-dimension route for a raw spectral proof that returns
selected compressed-determinant nonsingularity instead of an explicit
selected-root product or inverse diagonal block. -/
theorem
    reducedRankHansenTheorem11_7_exactDimension_of_detProductMinMax_diagonalDual_compressedDet_ne_zero_indexSplit
    (Z : Matrix n ell ℝ) (X Xtilde : Matrix n k ℝ) (Y Ytilde Etilde : Matrix n m ℝ)
    (G : Matrix k r ℝ) (lambda : r → ℝ)
    (Aperp : Matrix m s ℝ) (eta : s → ℝ)
    (hMinMax : ReducedRankHansenDetProductMinMaxCertificate
      Xtilde Ytilde Etilde G lambda Aperp eta)
    (W : Matrix m r ℝ)
    (hGdet : (Gᵀ * reducedRankGPencilA Xtilde Ytilde * G).det ≠ 0)
    (hDual : reducedRankDualEigenvectorRelation
      Xtilde Ytilde G W (Matrix.diagonal lambda))
    (hOrth : reducedRankAperpYOrthogonal Ytilde Aperp W)
    (hIndex : m ≃ Sum r s) :
    ReducedRankHansenSmallestSummaryCompatibilityExactDimension Z X Xtilde Y Ytilde Etilde G
      (Ytildeᵀ * Xtilde * G)
      (reducedRankChat Z X Y G (Ytildeᵀ * Xtilde * G))
      ((Fintype.card n : ℝ)⁻¹ •
        (Ytildeᵀ * Ytilde -
          (Ytildeᵀ * Xtilde * G) * (Ytildeᵀ * Xtilde * G)ᵀ))
      Aperp lambda eta (reducedRankMaximizedLogLikelihood Ytilde lambda) :=
  ReducedRankHansenSmallestSummaryCompatibilityExactDimension.of_theorem11_7
    (reducedRankHansenSmallestSummaryCompatibility_of_identified_spectral_duality_certificate
      Z X Xtilde Y Ytilde Etilde G lambda Aperp eta
      (ReducedRankHansenIdentifiedSpectralDualityCertificate.of_detProductMinMax_diagonalDual_compressedDet_ne_zero
        hMinMax W hGdet hDual hOrth))
    (reducedRankAperpDimension_of_equiv_sum (m := m) (r := r) (s := s) hIndex)

set_option linter.style.longLine false in
omit [DecidableEq n] in
/-- Hansen Theorem 11.7 from the determinant/product min-max certificate,
Hansen's displayed diagonal dual relation, nonzero selected compressed
determinant, and the canonical `A⊥` index `Fin (card m - card r)`.

This is the canonical-complement counterpart of
`reducedRankHansenTheorem11_7_exactDimension_of_detProductMinMax_diagonalDual_compressedDet_ne_zero_indexSplit`:
the selected-root nonsingularity and Hansen's exact `dim(A⊥)=m-r` conclusion
are both derived internally. -/
theorem
    reducedRankHansenTheorem11_7_exactDimension_of_detProductMinMax_diagonalDual_compressedDet_ne_zero_canonicalAperp
    (Z : Matrix n ell ℝ) (X Xtilde : Matrix n k ℝ) (Y Ytilde Etilde : Matrix n m ℝ)
    (G : Matrix k r ℝ) (lambda : r → ℝ)
    (Aperp : Matrix m (reducedRankAperpIndex m r) ℝ)
    (eta : reducedRankAperpIndex m r → ℝ)
    (hMinMax : ReducedRankHansenDetProductMinMaxCertificate
      Xtilde Ytilde Etilde G lambda Aperp eta)
    (W : Matrix m r ℝ)
    (hGdet : (Gᵀ * reducedRankGPencilA Xtilde Ytilde * G).det ≠ 0)
    (hDual : reducedRankDualEigenvectorRelation
      Xtilde Ytilde G W (Matrix.diagonal lambda))
    (hOrth : reducedRankAperpYOrthogonal Ytilde Aperp W) :
    ReducedRankHansenSmallestSummaryCompatibilityExactDimension Z X Xtilde Y Ytilde Etilde G
      (Ytildeᵀ * Xtilde * G)
      (reducedRankChat Z X Y G (Ytildeᵀ * Xtilde * G))
      ((Fintype.card n : ℝ)⁻¹ •
        (Ytildeᵀ * Ytilde -
          (Ytildeᵀ * Xtilde * G) * (Ytildeᵀ * Xtilde * G)ᵀ))
      Aperp lambda eta (reducedRankMaximizedLogLikelihood Ytilde lambda) :=
  ReducedRankHansenSmallestSummaryCompatibilityExactDimension.of_theorem11_7
    (reducedRankHansenSmallestSummaryCompatibility_of_identified_spectral_duality_certificate
      Z X Xtilde Y Ytilde Etilde G lambda Aperp eta
      (ReducedRankHansenIdentifiedSpectralDualityCertificate.of_detProductMinMax_diagonalDual_compressedDet_ne_zero
        hMinMax W hGdet hDual hOrth))
    (reducedRankAperpDimension_canonical (m := m) (r := r))

set_option linter.style.longLine false in
omit [DecidableEq n] in
/-- Hansen Theorem 11.7 from the determinant/product min-max certificate,
Hansen's displayed diagonal dual relation, positive selected `G` roots, and
the canonical `A⊥` index `Fin (card m - card r)`.

This removes the separate inverse selected-root block, selected-root
nonsingularity/product premise, and complementary-dimension proof from the
determinant/product min-max route. -/
theorem
    reducedRankHansenTheorem11_7_exactDimension_of_detProductMinMax_diagonalDual_pos_canonicalAperp
    (Z : Matrix n ell ℝ) (X Xtilde : Matrix n k ℝ) (Y Ytilde Etilde : Matrix n m ℝ)
    (G : Matrix k r ℝ) (lambda : r → ℝ)
    (Aperp : Matrix m (reducedRankAperpIndex m r) ℝ)
    (eta : reducedRankAperpIndex m r → ℝ)
    (hMinMax : ReducedRankHansenDetProductMinMaxCertificate
      Xtilde Ytilde Etilde G lambda Aperp eta)
    (W : Matrix m r ℝ)
    (hLambda : ∀ j, 0 < lambda j)
    (hDual : reducedRankDualEigenvectorRelation
      Xtilde Ytilde G W (Matrix.diagonal lambda))
    (hOrth : reducedRankAperpYOrthogonal Ytilde Aperp W) :
    ReducedRankHansenSmallestSummaryCompatibilityExactDimension Z X Xtilde Y Ytilde Etilde G
      (Ytildeᵀ * Xtilde * G)
      (reducedRankChat Z X Y G (Ytildeᵀ * Xtilde * G))
      ((Fintype.card n : ℝ)⁻¹ •
        (Ytildeᵀ * Ytilde -
          (Ytildeᵀ * Xtilde * G) * (Ytildeᵀ * Xtilde * G)ᵀ))
      Aperp lambda eta (reducedRankMaximizedLogLikelihood Ytilde lambda) :=
  ReducedRankHansenSmallestSummaryCompatibilityExactDimension.of_theorem11_7
    (reducedRankHansenSmallestSummaryCompatibility_of_identified_spectral_duality_certificate
      Z X Xtilde Y Ytilde Etilde G lambda Aperp eta
      (ReducedRankHansenIdentifiedSpectralDualityCertificate.of_detProductMinMax_diagonalDual_pos
        hMinMax W hLambda hDual hOrth))
    (reducedRankAperpDimension_canonical (m := m) (r := r))

omit [DecidableEq n] in
/-- Hansen Theorem 11.7 from the literal determinant/product variational bounds,
Hansen's displayed dual generalized-eigenvector relation, and the exact
complementary-rank dimension.

This is the direct endpoint for a raw generalized-pencil min-max theorem that
already proves the two product inequalities in Hansen's notation; the reusable
determinant/product min-max certificate and objective extrema are derived
internally. -/
theorem
    reducedRankHansenTheorem11_7_exactDimension_of_product_bounds_and_dual_relation
    (Z : Matrix n ell ℝ) (X Xtilde : Matrix n k ℝ) (Y Ytilde Etilde : Matrix n m ℝ)
    (G : Matrix k r ℝ) (lambda : r → ℝ)
    (Aperp : Matrix m s ℝ) (eta : s → ℝ)
    (hG : reducedRankHansenGEigenvectors Xtilde Ytilde lambda G)
    (hGNorm : reducedRankGNormalized Xtilde G)
    (hGBound : reducedRankGDetVariationalBound Xtilde Ytilde lambda)
    (hAperp : reducedRankHansenAperpEigenvectors Etilde Ytilde eta Aperp)
    (hAperpNorm : reducedRankAperpNormalized Ytilde Aperp)
    (hAperpBound : reducedRankAperpDetVariationalBound Etilde Ytilde eta)
    (W : Matrix m r ℝ) (Lambda LambdaInv : Matrix r r ℝ)
    (hDual : reducedRankDualEigenvectorRelation Xtilde Ytilde G W Lambda)
    (hOrth : reducedRankAperpYOrthogonal Ytilde Aperp W)
    (hLambdaInv : Lambda * LambdaInv = 1)
    (hdim : Fintype.card s = Fintype.card m - Fintype.card r) :
    ReducedRankHansenSmallestSummaryCompatibilityExactDimension Z X Xtilde Y Ytilde Etilde G
      (Ytildeᵀ * Xtilde * G)
      (reducedRankChat Z X Y G (Ytildeᵀ * Xtilde * G))
      ((Fintype.card n : ℝ)⁻¹ •
        (Ytildeᵀ * Ytilde -
          (Ytildeᵀ * Xtilde * G) * (Ytildeᵀ * Xtilde * G)ᵀ))
      Aperp lambda eta (reducedRankMaximizedLogLikelihood Ytilde lambda) :=
  reducedRankHansenTheorem11_7_exactDimension_of_detProductMinMax_and_dual_relation
    Z X Xtilde Y Ytilde Etilde G lambda Aperp eta
    (ReducedRankHansenDetProductMinMaxCertificate.of_product_variational_bounds
      Xtilde Ytilde Etilde G lambda Aperp eta
      hG hGNorm hGBound hAperp hAperpNorm hAperpBound)
    W Lambda LambdaInv hDual hOrth hLambdaInv hdim

omit [DecidableEq n] in
/-- Hansen Theorem 11.7 from literal determinant/product variational bounds
and Hansen's displayed diagonal selected-root dual relation.

This is the direct Hansen-notation counterpart of
`reducedRankHansenTheorem11_7_exactDimension_of_product_bounds_and_dual_relation`
when `Λ = diagonal λ`; the inverse selected-root block is synthesized from
pointwise nonzero selected roots. -/
theorem reducedRankHansenTheorem11_7_exactDimension_of_product_bounds_diagonalDual
    (Z : Matrix n ell ℝ) (X Xtilde : Matrix n k ℝ) (Y Ytilde Etilde : Matrix n m ℝ)
    (G : Matrix k r ℝ) (lambda : r → ℝ)
    (Aperp : Matrix m s ℝ) (eta : s → ℝ)
    (hG : reducedRankHansenGEigenvectors Xtilde Ytilde lambda G)
    (hGNorm : reducedRankGNormalized Xtilde G)
    (hGBound : reducedRankGDetVariationalBound Xtilde Ytilde lambda)
    (hAperp : reducedRankHansenAperpEigenvectors Etilde Ytilde eta Aperp)
    (hAperpNorm : reducedRankAperpNormalized Ytilde Aperp)
    (hAperpBound : reducedRankAperpDetVariationalBound Etilde Ytilde eta)
    (W : Matrix m r ℝ)
    (hLambda : ∀ j, lambda j ≠ 0)
    (hDual : reducedRankDualEigenvectorRelation
      Xtilde Ytilde G W (Matrix.diagonal lambda))
    (hOrth : reducedRankAperpYOrthogonal Ytilde Aperp W)
    (hdim : Fintype.card s = Fintype.card m - Fintype.card r) :
    ReducedRankHansenSmallestSummaryCompatibilityExactDimension Z X Xtilde Y Ytilde Etilde G
      (Ytildeᵀ * Xtilde * G)
      (reducedRankChat Z X Y G (Ytildeᵀ * Xtilde * G))
      ((Fintype.card n : ℝ)⁻¹ •
        (Ytildeᵀ * Ytilde -
          (Ytildeᵀ * Xtilde * G) * (Ytildeᵀ * Xtilde * G)ᵀ))
      Aperp lambda eta (reducedRankMaximizedLogLikelihood Ytilde lambda) :=
  reducedRankHansenTheorem11_7_exactDimension_of_product_bounds_and_dual_relation
    Z X Xtilde Y Ytilde Etilde G lambda Aperp eta
    hG hGNorm hGBound hAperp hAperpNorm hAperpBound
    W (Matrix.diagonal lambda) (Matrix.diagonal fun j => (lambda j)⁻¹)
    hDual hOrth
    (reducedRankSelectedRootDiagonal_mul_inv_eq_one lambda hLambda)
    hdim

set_option linter.style.longLine false in
omit [DecidableEq n] in
/-- Product-nonzero and index-split version of
`reducedRankHansenTheorem11_7_exactDimension_of_product_bounds_diagonalDual`.

The raw spectral theorem may provide only the selected-root product
nonzero and a concrete finite split `m ≃ r ⊕ s`; this wrapper derives the
pointwise root nonsingularity and Hansen's complementary-rank dimension. -/
theorem
    reducedRankHansenTheorem11_7_exactDimension_of_product_bounds_diagonalDual_prod_ne_zero_indexSplit
    (Z : Matrix n ell ℝ) (X Xtilde : Matrix n k ℝ) (Y Ytilde Etilde : Matrix n m ℝ)
    (G : Matrix k r ℝ) (lambda : r → ℝ)
    (Aperp : Matrix m s ℝ) (eta : s → ℝ)
    (hG : reducedRankHansenGEigenvectors Xtilde Ytilde lambda G)
    (hGNorm : reducedRankGNormalized Xtilde G)
    (hGBound : reducedRankGDetVariationalBound Xtilde Ytilde lambda)
    (hAperp : reducedRankHansenAperpEigenvectors Etilde Ytilde eta Aperp)
    (hAperpNorm : reducedRankAperpNormalized Ytilde Aperp)
    (hAperpBound : reducedRankAperpDetVariationalBound Etilde Ytilde eta)
    (W : Matrix m r ℝ)
    (hLambdaProd : (∏ j, lambda j) ≠ 0)
    (hDual : reducedRankDualEigenvectorRelation
      Xtilde Ytilde G W (Matrix.diagonal lambda))
    (hOrth : reducedRankAperpYOrthogonal Ytilde Aperp W)
    (hIndex : m ≃ Sum r s) :
    ReducedRankHansenSmallestSummaryCompatibilityExactDimension Z X Xtilde Y Ytilde Etilde G
      (Ytildeᵀ * Xtilde * G)
      (reducedRankChat Z X Y G (Ytildeᵀ * Xtilde * G))
      ((Fintype.card n : ℝ)⁻¹ •
        (Ytildeᵀ * Ytilde -
          (Ytildeᵀ * Xtilde * G) * (Ytildeᵀ * Xtilde * G)ᵀ))
      Aperp lambda eta (reducedRankMaximizedLogLikelihood Ytilde lambda) :=
  reducedRankHansenTheorem11_7_exactDimension_of_product_bounds_diagonalDual
    Z X Xtilde Y Ytilde Etilde G lambda Aperp eta
    hG hGNorm hGBound hAperp hAperpNorm hAperpBound W
    (reducedRankSelectedRoots_nonzero_of_prod_ne_zero lambda hLambdaProd)
    hDual hOrth
    (reducedRankAperpDimension_of_equiv_sum (m := m) (r := r) (s := s) hIndex)

set_option linter.style.longLine false in
omit [DecidableEq n] in
/-- Compressed-determinant and index-split version of
`reducedRankHansenTheorem11_7_exactDimension_of_product_bounds_diagonalDual`.

This endpoint keeps Hansen's literal determinant/product bounds while deriving
the selected-root product nonsingularity from the selected compressed
determinant `det(G'AG) ≠ 0`. -/
theorem
    reducedRankHansenTheorem11_7_exactDimension_of_product_bounds_diagonalDual_compressedDet_ne_zero_indexSplit
    (Z : Matrix n ell ℝ) (X Xtilde : Matrix n k ℝ) (Y Ytilde Etilde : Matrix n m ℝ)
    (G : Matrix k r ℝ) (lambda : r → ℝ)
    (Aperp : Matrix m s ℝ) (eta : s → ℝ)
    (hG : reducedRankHansenGEigenvectors Xtilde Ytilde lambda G)
    (hGNorm : reducedRankGNormalized Xtilde G)
    (hGBound : reducedRankGDetVariationalBound Xtilde Ytilde lambda)
    (hAperp : reducedRankHansenAperpEigenvectors Etilde Ytilde eta Aperp)
    (hAperpNorm : reducedRankAperpNormalized Ytilde Aperp)
    (hAperpBound : reducedRankAperpDetVariationalBound Etilde Ytilde eta)
    (W : Matrix m r ℝ)
    (hGdet : (Gᵀ * reducedRankGPencilA Xtilde Ytilde * G).det ≠ 0)
    (hDual : reducedRankDualEigenvectorRelation
      Xtilde Ytilde G W (Matrix.diagonal lambda))
    (hOrth : reducedRankAperpYOrthogonal Ytilde Aperp W)
    (hIndex : m ≃ Sum r s) :
    ReducedRankHansenSmallestSummaryCompatibilityExactDimension Z X Xtilde Y Ytilde Etilde G
      (Ytildeᵀ * Xtilde * G)
      (reducedRankChat Z X Y G (Ytildeᵀ * Xtilde * G))
      ((Fintype.card n : ℝ)⁻¹ •
        (Ytildeᵀ * Ytilde -
          (Ytildeᵀ * Xtilde * G) * (Ytildeᵀ * Xtilde * G)ᵀ))
      Aperp lambda eta (reducedRankMaximizedLogLikelihood Ytilde lambda) :=
  reducedRankHansenTheorem11_7_exactDimension_of_product_bounds_diagonalDual_prod_ne_zero_indexSplit
    Z X Xtilde Y Ytilde Etilde G lambda Aperp eta
    hG hGNorm hGBound hAperp hAperpNorm hAperpBound W
    (generalizedEigenSelectedRootProduct_ne_zero_of_compressedDet_ne_zero
      (reducedRankGPencilA Xtilde Ytilde) (reducedRankGPencilB Xtilde)
      lambda G hG hGNorm hGdet)
    hDual hOrth hIndex

set_option linter.style.longLine false in
omit [DecidableEq n] in
/-- Canonical-`A⊥` version of
`reducedRankHansenTheorem11_7_exactDimension_of_product_bounds_diagonalDual_prod_ne_zero_indexSplit`.

This keeps Hansen's literal determinant/product variational bounds, while the
canonical complement index supplies the exact `dim(A⊥)=m-r` conclusion
internally. -/
theorem
    reducedRankHansenTheorem11_7_exactDimension_of_product_bounds_diagonalDual_prod_ne_zero_canonicalAperp
    (Z : Matrix n ell ℝ) (X Xtilde : Matrix n k ℝ) (Y Ytilde Etilde : Matrix n m ℝ)
    (G : Matrix k r ℝ) (lambda : r → ℝ)
    (Aperp : Matrix m (reducedRankAperpIndex m r) ℝ)
    (eta : reducedRankAperpIndex m r → ℝ)
    (hG : reducedRankHansenGEigenvectors Xtilde Ytilde lambda G)
    (hGNorm : reducedRankGNormalized Xtilde G)
    (hGBound : reducedRankGDetVariationalBound Xtilde Ytilde lambda)
    (hAperp : reducedRankHansenAperpEigenvectors Etilde Ytilde eta Aperp)
    (hAperpNorm : reducedRankAperpNormalized Ytilde Aperp)
    (hAperpBound : reducedRankAperpDetVariationalBound Etilde Ytilde eta)
    (W : Matrix m r ℝ)
    (hLambdaProd : (∏ j, lambda j) ≠ 0)
    (hDual : reducedRankDualEigenvectorRelation
      Xtilde Ytilde G W (Matrix.diagonal lambda))
    (hOrth : reducedRankAperpYOrthogonal Ytilde Aperp W) :
    ReducedRankHansenSmallestSummaryCompatibilityExactDimension Z X Xtilde Y Ytilde Etilde G
      (Ytildeᵀ * Xtilde * G)
      (reducedRankChat Z X Y G (Ytildeᵀ * Xtilde * G))
      ((Fintype.card n : ℝ)⁻¹ •
        (Ytildeᵀ * Ytilde -
          (Ytildeᵀ * Xtilde * G) * (Ytildeᵀ * Xtilde * G)ᵀ))
      Aperp lambda eta (reducedRankMaximizedLogLikelihood Ytilde lambda) :=
  reducedRankHansenTheorem11_7_exactDimension_of_product_bounds_diagonalDual
    Z X Xtilde Y Ytilde Etilde G lambda Aperp eta
    hG hGNorm hGBound hAperp hAperpNorm hAperpBound W
    (reducedRankSelectedRoots_nonzero_of_prod_ne_zero lambda hLambdaProd)
    hDual hOrth
    (reducedRankAperpDimension_canonical (m := m) (r := r))

set_option linter.style.longLine false in
omit [DecidableEq n] in
/-- Canonical-`A⊥` product-bound endpoint where selected-root
nonsingularity is derived from the nonzero selected compressed determinant. -/
theorem
    reducedRankHansenTheorem11_7_exactDimension_of_product_bounds_diagonalDual_compressedDet_ne_zero_canonicalAperp
    (Z : Matrix n ell ℝ) (X Xtilde : Matrix n k ℝ) (Y Ytilde Etilde : Matrix n m ℝ)
    (G : Matrix k r ℝ) (lambda : r → ℝ)
    (Aperp : Matrix m (reducedRankAperpIndex m r) ℝ)
    (eta : reducedRankAperpIndex m r → ℝ)
    (hG : reducedRankHansenGEigenvectors Xtilde Ytilde lambda G)
    (hGNorm : reducedRankGNormalized Xtilde G)
    (hGBound : reducedRankGDetVariationalBound Xtilde Ytilde lambda)
    (hAperp : reducedRankHansenAperpEigenvectors Etilde Ytilde eta Aperp)
    (hAperpNorm : reducedRankAperpNormalized Ytilde Aperp)
    (hAperpBound : reducedRankAperpDetVariationalBound Etilde Ytilde eta)
    (W : Matrix m r ℝ)
    (hGdet : (Gᵀ * reducedRankGPencilA Xtilde Ytilde * G).det ≠ 0)
    (hDual : reducedRankDualEigenvectorRelation
      Xtilde Ytilde G W (Matrix.diagonal lambda))
    (hOrth : reducedRankAperpYOrthogonal Ytilde Aperp W) :
    ReducedRankHansenSmallestSummaryCompatibilityExactDimension Z X Xtilde Y Ytilde Etilde G
      (Ytildeᵀ * Xtilde * G)
      (reducedRankChat Z X Y G (Ytildeᵀ * Xtilde * G))
      ((Fintype.card n : ℝ)⁻¹ •
        (Ytildeᵀ * Ytilde -
          (Ytildeᵀ * Xtilde * G) * (Ytildeᵀ * Xtilde * G)ᵀ))
      Aperp lambda eta (reducedRankMaximizedLogLikelihood Ytilde lambda) :=
  reducedRankHansenTheorem11_7_exactDimension_of_product_bounds_diagonalDual_prod_ne_zero_canonicalAperp
    Z X Xtilde Y Ytilde Etilde G lambda Aperp eta
    hG hGNorm hGBound hAperp hAperpNorm hAperpBound W
    (generalizedEigenSelectedRootProduct_ne_zero_of_compressedDet_ne_zero
      (reducedRankGPencilA Xtilde Ytilde) (reducedRankGPencilB Xtilde)
      lambda G hG hGNorm hGdet)
    hDual hOrth

set_option linter.style.longLine false in
omit [DecidableEq n] in
/-- Hansen Theorem 11.7 exact-dimension endpoint for the proved rank-one
Rayleigh route, with Hansen's displayed diagonal dual relation.

For one-column `G` and one-column `A⊥`, the determinant/product min-max
premises reduce to scalar generalized Rayleigh bounds. This wrapper assembles
those bounds with the diagonal dual relation, derives pointwise selected-root
nonsingularity from the unique selected root, and then uses the existing
identified Theorem 11.7 endpoint. -/
theorem
    reducedRankHansenTheorem11_7_exactDimension_of_rankOne_rayleigh_bounds_diagonalDual
    [Unique r] [Unique s]
    (Z : Matrix n ell ℝ) (X Xtilde : Matrix n k ℝ) (Y Ytilde Etilde : Matrix n m ℝ)
    (G : Matrix k r ℝ) (lambda : r → ℝ)
    (Aperp : Matrix m s ℝ) (eta : s → ℝ)
    (hG : reducedRankHansenGEigenvectors Xtilde Ytilde lambda G)
    (hGNorm : reducedRankGNormalized Xtilde G)
    (hGBound : ∀ v : k → ℝ,
      v ⬝ᵥ (reducedRankGPencilB Xtilde *ᵥ v) = 1 →
        v ⬝ᵥ (reducedRankGPencilA Xtilde Ytilde *ᵥ v) ≤ lambda default)
    (hAperp : reducedRankHansenAperpEigenvectors Etilde Ytilde eta Aperp)
    (hAperpNorm : reducedRankAperpNormalized Ytilde Aperp)
    (hAperpBound : ∀ v : m → ℝ,
      v ⬝ᵥ (reducedRankAperpPencilB Ytilde *ᵥ v) = 1 →
        eta default ≤ v ⬝ᵥ (reducedRankAperpPencilA Etilde *ᵥ v))
    (W : Matrix m r ℝ)
    (hLambda : lambda default ≠ 0)
    (hDual : reducedRankDualEigenvectorRelation
      Xtilde Ytilde G W (Matrix.diagonal lambda))
    (hOrth : reducedRankAperpYOrthogonal Ytilde Aperp W)
    (hdim : Fintype.card s = Fintype.card m - Fintype.card r) :
    ReducedRankHansenSmallestSummaryCompatibilityExactDimension Z X Xtilde Y Ytilde Etilde G
      (Ytildeᵀ * Xtilde * G)
      (reducedRankChat Z X Y G (Ytildeᵀ * Xtilde * G))
      ((Fintype.card n : ℝ)⁻¹ •
        (Ytildeᵀ * Ytilde -
          (Ytildeᵀ * Xtilde * G) * (Ytildeᵀ * Xtilde * G)ᵀ))
      Aperp lambda eta (reducedRankMaximizedLogLikelihood Ytilde lambda) :=
  ReducedRankHansenSmallestSummaryCompatibilityExactDimension.of_theorem11_7
    (reducedRankHansenSmallestSummaryCompatibility_of_identified_spectral_duality_certificate
      Z X Xtilde Y Ytilde Etilde G lambda Aperp eta
      (ReducedRankHansenIdentifiedSpectralDualityCertificate.of_rankOne_rayleigh_bounds_diagonalDual
        Xtilde Ytilde Etilde G lambda Aperp eta
        hG hGNorm hGBound hAperp hAperpNorm hAperpBound
        W hLambda hDual hOrth))
    hdim

omit [DecidableEq n] in
/-- Hansen Theorem 11.7 from generic generalized-pencil product bounds, the
displayed dual relation, and the exact complementary-rank dimension.

This is the direct endpoint for a raw pencil theorem stated outside the
Hansen-specific notation: the raw theorem supplies
`generalizedEigenDetProductUpperBound` for the G pencil and
`generalizedEigenDetProductLowerBound` for the `A⊥` pencil. -/
theorem
    reducedRankHansenTheorem11_7_exactDimension_of_generalized_product_bounds_and_dual_relation
    (Z : Matrix n ell ℝ) (X Xtilde : Matrix n k ℝ) (Y Ytilde Etilde : Matrix n m ℝ)
    (G : Matrix k r ℝ) (lambda : r → ℝ)
    (Aperp : Matrix m s ℝ) (eta : s → ℝ)
    (hG : reducedRankHansenGEigenvectors Xtilde Ytilde lambda G)
    (hGNorm : reducedRankGNormalized Xtilde G)
    (hGBound : generalizedEigenDetProductUpperBound
      (reducedRankGPencilA Xtilde Ytilde) (reducedRankGPencilB Xtilde) lambda)
    (hAperp : reducedRankHansenAperpEigenvectors Etilde Ytilde eta Aperp)
    (hAperpNorm : reducedRankAperpNormalized Ytilde Aperp)
    (hAperpBound : generalizedEigenDetProductLowerBound
      (reducedRankAperpPencilA Etilde) (reducedRankAperpPencilB Ytilde) eta)
    (W : Matrix m r ℝ) (Lambda LambdaInv : Matrix r r ℝ)
    (hDual : reducedRankDualEigenvectorRelation Xtilde Ytilde G W Lambda)
    (hOrth : reducedRankAperpYOrthogonal Ytilde Aperp W)
    (hLambdaInv : Lambda * LambdaInv = 1)
    (hdim : Fintype.card s = Fintype.card m - Fintype.card r) :
    ReducedRankHansenSmallestSummaryCompatibilityExactDimension Z X Xtilde Y Ytilde Etilde G
      (Ytildeᵀ * Xtilde * G)
      (reducedRankChat Z X Y G (Ytildeᵀ * Xtilde * G))
      ((Fintype.card n : ℝ)⁻¹ •
        (Ytildeᵀ * Ytilde -
          (Ytildeᵀ * Xtilde * G) * (Ytildeᵀ * Xtilde * G)ᵀ))
      Aperp lambda eta (reducedRankMaximizedLogLikelihood Ytilde lambda) :=
  reducedRankHansenTheorem11_7_exactDimension_of_detProductMinMax_and_dual_relation
    Z X Xtilde Y Ytilde Etilde G lambda Aperp eta
    (ReducedRankHansenDetProductMinMaxCertificate.of_generalized_product_bounds
      Xtilde Ytilde Etilde G lambda Aperp eta
      hG hGNorm hGBound hAperp hAperpNorm hAperpBound)
    W Lambda LambdaInv hDual hOrth hLambdaInv hdim

omit [DecidableEq n] in
/-- Hansen Theorem 11.7 from generic generalized-pencil product bounds, the
displayed diagonal selected-root dual relation, pointwise selected-root
nonsingularity, and the exact complementary-rank dimension.

This is the same generic-pencil route as
`reducedRankHansenTheorem11_7_exactDimension_of_generalized_product_bounds_and_dual_relation`,
but it synthesizes the inverse selected-root block from `λ_j ≠ 0` when
Hansen's displayed `Λ` is `diagonal λ`. -/
theorem
    reducedRankHansenTheorem11_7_exactDimension_of_genericProductBounds_diagonalDual
    (Z : Matrix n ell ℝ) (X Xtilde : Matrix n k ℝ) (Y Ytilde Etilde : Matrix n m ℝ)
    (G : Matrix k r ℝ) (lambda : r → ℝ)
    (Aperp : Matrix m s ℝ) (eta : s → ℝ)
    (hG : reducedRankHansenGEigenvectors Xtilde Ytilde lambda G)
    (hGNorm : reducedRankGNormalized Xtilde G)
    (hGBound : generalizedEigenDetProductUpperBound
      (reducedRankGPencilA Xtilde Ytilde) (reducedRankGPencilB Xtilde) lambda)
    (hAperp : reducedRankHansenAperpEigenvectors Etilde Ytilde eta Aperp)
    (hAperpNorm : reducedRankAperpNormalized Ytilde Aperp)
    (hAperpBound : generalizedEigenDetProductLowerBound
      (reducedRankAperpPencilA Etilde) (reducedRankAperpPencilB Ytilde) eta)
    (W : Matrix m r ℝ)
    (hLambda : ∀ j, lambda j ≠ 0)
    (hDual : reducedRankDualEigenvectorRelation
      Xtilde Ytilde G W (Matrix.diagonal lambda))
    (hOrth : reducedRankAperpYOrthogonal Ytilde Aperp W)
    (hdim : Fintype.card s = Fintype.card m - Fintype.card r) :
    ReducedRankHansenSmallestSummaryCompatibilityExactDimension Z X Xtilde Y Ytilde Etilde G
      (Ytildeᵀ * Xtilde * G)
      (reducedRankChat Z X Y G (Ytildeᵀ * Xtilde * G))
      ((Fintype.card n : ℝ)⁻¹ •
        (Ytildeᵀ * Ytilde -
          (Ytildeᵀ * Xtilde * G) * (Ytildeᵀ * Xtilde * G)ᵀ))
      Aperp lambda eta (reducedRankMaximizedLogLikelihood Ytilde lambda) :=
  reducedRankHansenTheorem11_7_exactDimension_of_generalized_product_bounds_and_dual_relation
    Z X Xtilde Y Ytilde Etilde G lambda Aperp eta
    hG hGNorm hGBound hAperp hAperpNorm hAperpBound
    W (Matrix.diagonal lambda) (Matrix.diagonal fun j => (lambda j)⁻¹)
    hDual hOrth
    (reducedRankSelectedRootDiagonal_mul_inv_eq_one lambda hLambda)
    hdim

set_option linter.style.longLine false in
omit [DecidableEq n] in
/-- Product-nonzero and index-split version of
`reducedRankHansenTheorem11_7_exactDimension_of_genericProductBounds_diagonalDual`.

This endpoint keeps Hansen's exact determinant/product premises and diagonal
dual relation, but derives selected-root pointwise nonsingularity from
`∏ λ_j ≠ 0` and `dim(A⊥)=m-r` from a concrete finite index split
`m ≃ r ⊕ s`. -/
theorem
    reducedRankHansenTheorem11_7_exactDimension_of_genericProductBounds_diagonalDual_prod_ne_zero_indexSplit
    (Z : Matrix n ell ℝ) (X Xtilde : Matrix n k ℝ) (Y Ytilde Etilde : Matrix n m ℝ)
    (G : Matrix k r ℝ) (lambda : r → ℝ)
    (Aperp : Matrix m s ℝ) (eta : s → ℝ)
    (hG : reducedRankHansenGEigenvectors Xtilde Ytilde lambda G)
    (hGNorm : reducedRankGNormalized Xtilde G)
    (hGBound : generalizedEigenDetProductUpperBound
      (reducedRankGPencilA Xtilde Ytilde) (reducedRankGPencilB Xtilde) lambda)
    (hAperp : reducedRankHansenAperpEigenvectors Etilde Ytilde eta Aperp)
    (hAperpNorm : reducedRankAperpNormalized Ytilde Aperp)
    (hAperpBound : generalizedEigenDetProductLowerBound
      (reducedRankAperpPencilA Etilde) (reducedRankAperpPencilB Ytilde) eta)
    (W : Matrix m r ℝ)
    (hLambdaProd : (∏ j, lambda j) ≠ 0)
    (hDual : reducedRankDualEigenvectorRelation
      Xtilde Ytilde G W (Matrix.diagonal lambda))
    (hOrth : reducedRankAperpYOrthogonal Ytilde Aperp W)
    (hIndex : m ≃ Sum r s) :
    ReducedRankHansenSmallestSummaryCompatibilityExactDimension Z X Xtilde Y Ytilde Etilde G
      (Ytildeᵀ * Xtilde * G)
      (reducedRankChat Z X Y G (Ytildeᵀ * Xtilde * G))
      ((Fintype.card n : ℝ)⁻¹ •
        (Ytildeᵀ * Ytilde -
          (Ytildeᵀ * Xtilde * G) * (Ytildeᵀ * Xtilde * G)ᵀ))
      Aperp lambda eta (reducedRankMaximizedLogLikelihood Ytilde lambda) :=
  reducedRankHansenTheorem11_7_exactDimension_of_genericProductBounds_diagonalDual
    Z X Xtilde Y Ytilde Etilde G lambda Aperp eta
    hG hGNorm hGBound hAperp hAperpNorm hAperpBound W
    (reducedRankSelectedRoots_nonzero_of_prod_ne_zero lambda hLambdaProd)
    hDual hOrth
    (reducedRankAperpDimension_of_equiv_sum (m := m) (r := r) (s := s) hIndex)

set_option linter.style.longLine false in
omit [DecidableEq n] in
/-- Compressed-determinant and index-split version of
`reducedRankHansenTheorem11_7_exactDimension_of_genericProductBounds_diagonalDual`.

This is the generic generalized-pencil product-bound route when the raw pencil
construction proves nonsingularity of the selected compressed `G` determinant,
rather than positivity or nonzero product of the selected roots. -/
theorem
    reducedRankHansenTheorem11_7_exactDimension_of_genericProductBounds_diagonalDual_compressedDet_ne_zero_indexSplit
    (Z : Matrix n ell ℝ) (X Xtilde : Matrix n k ℝ) (Y Ytilde Etilde : Matrix n m ℝ)
    (G : Matrix k r ℝ) (lambda : r → ℝ)
    (Aperp : Matrix m s ℝ) (eta : s → ℝ)
    (hG : reducedRankHansenGEigenvectors Xtilde Ytilde lambda G)
    (hGNorm : reducedRankGNormalized Xtilde G)
    (hGBound : generalizedEigenDetProductUpperBound
      (reducedRankGPencilA Xtilde Ytilde) (reducedRankGPencilB Xtilde) lambda)
    (hAperp : reducedRankHansenAperpEigenvectors Etilde Ytilde eta Aperp)
    (hAperpNorm : reducedRankAperpNormalized Ytilde Aperp)
    (hAperpBound : generalizedEigenDetProductLowerBound
      (reducedRankAperpPencilA Etilde) (reducedRankAperpPencilB Ytilde) eta)
    (W : Matrix m r ℝ)
    (hGdet : (Gᵀ * reducedRankGPencilA Xtilde Ytilde * G).det ≠ 0)
    (hDual : reducedRankDualEigenvectorRelation
      Xtilde Ytilde G W (Matrix.diagonal lambda))
    (hOrth : reducedRankAperpYOrthogonal Ytilde Aperp W)
    (hIndex : m ≃ Sum r s) :
    ReducedRankHansenSmallestSummaryCompatibilityExactDimension Z X Xtilde Y Ytilde Etilde G
      (Ytildeᵀ * Xtilde * G)
      (reducedRankChat Z X Y G (Ytildeᵀ * Xtilde * G))
      ((Fintype.card n : ℝ)⁻¹ •
        (Ytildeᵀ * Ytilde -
          (Ytildeᵀ * Xtilde * G) * (Ytildeᵀ * Xtilde * G)ᵀ))
      Aperp lambda eta (reducedRankMaximizedLogLikelihood Ytilde lambda) :=
  reducedRankHansenTheorem11_7_exactDimension_of_genericProductBounds_diagonalDual_prod_ne_zero_indexSplit
    Z X Xtilde Y Ytilde Etilde G lambda Aperp eta
    hG hGNorm hGBound hAperp hAperpNorm hAperpBound W
    (generalizedEigenSelectedRootProduct_ne_zero_of_compressedDet_ne_zero
      (reducedRankGPencilA Xtilde Ytilde) (reducedRankGPencilB Xtilde)
      lambda G hG hGNorm hGdet)
    hDual hOrth hIndex

set_option linter.style.longLine false in
omit [DecidableEq n] in
/-- Positive-root and index-split version of
`reducedRankHansenTheorem11_7_exactDimension_of_genericProductBounds_diagonalDual`.

This endpoint consumes generic generalized-pencil product bounds, Hansen's
diagonal dual relation, positivity of the selected `G` roots, and a concrete
finite split `m ≃ r ⊕ s`; it derives the nonzero selected-root product,
pointwise root nonsingularity, and Hansen's complementary-rank equality
internally. -/
theorem
    reducedRankHansenTheorem11_7_exactDimension_of_genericProductBounds_diagonalDual_pos_indexSplit
    (Z : Matrix n ell ℝ) (X Xtilde : Matrix n k ℝ) (Y Ytilde Etilde : Matrix n m ℝ)
    (G : Matrix k r ℝ) (lambda : r → ℝ)
    (Aperp : Matrix m s ℝ) (eta : s → ℝ)
    (hG : reducedRankHansenGEigenvectors Xtilde Ytilde lambda G)
    (hGNorm : reducedRankGNormalized Xtilde G)
    (hGBound : generalizedEigenDetProductUpperBound
      (reducedRankGPencilA Xtilde Ytilde) (reducedRankGPencilB Xtilde) lambda)
    (hAperp : reducedRankHansenAperpEigenvectors Etilde Ytilde eta Aperp)
    (hAperpNorm : reducedRankAperpNormalized Ytilde Aperp)
    (hAperpBound : generalizedEigenDetProductLowerBound
      (reducedRankAperpPencilA Etilde) (reducedRankAperpPencilB Ytilde) eta)
    (W : Matrix m r ℝ)
    (hLambda : ∀ j, 0 < lambda j)
    (hDual : reducedRankDualEigenvectorRelation
      Xtilde Ytilde G W (Matrix.diagonal lambda))
    (hOrth : reducedRankAperpYOrthogonal Ytilde Aperp W)
    (hIndex : m ≃ Sum r s) :
    ReducedRankHansenSmallestSummaryCompatibilityExactDimension Z X Xtilde Y Ytilde Etilde G
      (Ytildeᵀ * Xtilde * G)
      (reducedRankChat Z X Y G (Ytildeᵀ * Xtilde * G))
      ((Fintype.card n : ℝ)⁻¹ •
        (Ytildeᵀ * Ytilde -
          (Ytildeᵀ * Xtilde * G) * (Ytildeᵀ * Xtilde * G)ᵀ))
      Aperp lambda eta (reducedRankMaximizedLogLikelihood Ytilde lambda) :=
  reducedRankHansenTheorem11_7_exactDimension_of_genericProductBounds_diagonalDual_prod_ne_zero_indexSplit
    Z X Xtilde Y Ytilde Etilde G lambda Aperp eta
    hG hGNorm hGBound hAperp hAperpNorm hAperpBound W
    (reducedRankSelectedRootProduct_ne_zero_of_pos lambda hLambda)
    hDual hOrth hIndex

set_option linter.style.longLine false in
omit [DecidableEq n] in
/-- Canonical-`A⊥` version of
`reducedRankHansenTheorem11_7_exactDimension_of_genericProductBounds_diagonalDual_prod_ne_zero_indexSplit`.

This is the generic generalized-pencil product-bound route with Hansen's
canonical complement index `Fin (card m - card r)`, so the exact `A⊥`
dimension is derived internally. -/
theorem
    reducedRankHansenTheorem11_7_exactDimension_of_genericProductBounds_diagonalDual_prod_ne_zero_canonicalAperp
    (Z : Matrix n ell ℝ) (X Xtilde : Matrix n k ℝ) (Y Ytilde Etilde : Matrix n m ℝ)
    (G : Matrix k r ℝ) (lambda : r → ℝ)
    (Aperp : Matrix m (reducedRankAperpIndex m r) ℝ)
    (eta : reducedRankAperpIndex m r → ℝ)
    (hG : reducedRankHansenGEigenvectors Xtilde Ytilde lambda G)
    (hGNorm : reducedRankGNormalized Xtilde G)
    (hGBound : generalizedEigenDetProductUpperBound
      (reducedRankGPencilA Xtilde Ytilde) (reducedRankGPencilB Xtilde) lambda)
    (hAperp : reducedRankHansenAperpEigenvectors Etilde Ytilde eta Aperp)
    (hAperpNorm : reducedRankAperpNormalized Ytilde Aperp)
    (hAperpBound : generalizedEigenDetProductLowerBound
      (reducedRankAperpPencilA Etilde) (reducedRankAperpPencilB Ytilde) eta)
    (W : Matrix m r ℝ)
    (hLambdaProd : (∏ j, lambda j) ≠ 0)
    (hDual : reducedRankDualEigenvectorRelation
      Xtilde Ytilde G W (Matrix.diagonal lambda))
    (hOrth : reducedRankAperpYOrthogonal Ytilde Aperp W) :
    ReducedRankHansenSmallestSummaryCompatibilityExactDimension Z X Xtilde Y Ytilde Etilde G
      (Ytildeᵀ * Xtilde * G)
      (reducedRankChat Z X Y G (Ytildeᵀ * Xtilde * G))
      ((Fintype.card n : ℝ)⁻¹ •
        (Ytildeᵀ * Ytilde -
          (Ytildeᵀ * Xtilde * G) * (Ytildeᵀ * Xtilde * G)ᵀ))
      Aperp lambda eta (reducedRankMaximizedLogLikelihood Ytilde lambda) :=
  reducedRankHansenTheorem11_7_exactDimension_of_genericProductBounds_diagonalDual
    Z X Xtilde Y Ytilde Etilde G lambda Aperp eta
    hG hGNorm hGBound hAperp hAperpNorm hAperpBound W
    (reducedRankSelectedRoots_nonzero_of_prod_ne_zero lambda hLambdaProd)
    hDual hOrth
    (reducedRankAperpDimension_canonical (m := m) (r := r))

set_option linter.style.longLine false in
omit [DecidableEq n] in
/-- Canonical-`A⊥` generic-product endpoint where selected-root
nonsingularity is derived from the nonzero selected compressed determinant. -/
theorem
    reducedRankHansenTheorem11_7_exactDimension_of_genericProductBounds_diagonalDual_compressedDet_ne_zero_canonicalAperp
    (Z : Matrix n ell ℝ) (X Xtilde : Matrix n k ℝ) (Y Ytilde Etilde : Matrix n m ℝ)
    (G : Matrix k r ℝ) (lambda : r → ℝ)
    (Aperp : Matrix m (reducedRankAperpIndex m r) ℝ)
    (eta : reducedRankAperpIndex m r → ℝ)
    (hG : reducedRankHansenGEigenvectors Xtilde Ytilde lambda G)
    (hGNorm : reducedRankGNormalized Xtilde G)
    (hGBound : generalizedEigenDetProductUpperBound
      (reducedRankGPencilA Xtilde Ytilde) (reducedRankGPencilB Xtilde) lambda)
    (hAperp : reducedRankHansenAperpEigenvectors Etilde Ytilde eta Aperp)
    (hAperpNorm : reducedRankAperpNormalized Ytilde Aperp)
    (hAperpBound : generalizedEigenDetProductLowerBound
      (reducedRankAperpPencilA Etilde) (reducedRankAperpPencilB Ytilde) eta)
    (W : Matrix m r ℝ)
    (hGdet : (Gᵀ * reducedRankGPencilA Xtilde Ytilde * G).det ≠ 0)
    (hDual : reducedRankDualEigenvectorRelation
      Xtilde Ytilde G W (Matrix.diagonal lambda))
    (hOrth : reducedRankAperpYOrthogonal Ytilde Aperp W) :
    ReducedRankHansenSmallestSummaryCompatibilityExactDimension Z X Xtilde Y Ytilde Etilde G
      (Ytildeᵀ * Xtilde * G)
      (reducedRankChat Z X Y G (Ytildeᵀ * Xtilde * G))
      ((Fintype.card n : ℝ)⁻¹ •
        (Ytildeᵀ * Ytilde -
          (Ytildeᵀ * Xtilde * G) * (Ytildeᵀ * Xtilde * G)ᵀ))
      Aperp lambda eta (reducedRankMaximizedLogLikelihood Ytilde lambda) :=
  reducedRankHansenTheorem11_7_exactDimension_of_genericProductBounds_diagonalDual_prod_ne_zero_canonicalAperp
    Z X Xtilde Y Ytilde Etilde G lambda Aperp eta
    hG hGNorm hGBound hAperp hAperpNorm hAperpBound W
    (generalizedEigenSelectedRootProduct_ne_zero_of_compressedDet_ne_zero
      (reducedRankGPencilA Xtilde Ytilde) (reducedRankGPencilB Xtilde)
      lambda G hG hGNorm hGdet)
    hDual hOrth

omit [DecidableEq n] in
/-- Objective-extrema version of
`reducedRankHansenTheorem11_7_exactDimension_of_detProductMinMax_and_dual_relation`.

The objective-extrema certificate is converted through the existing
determinant/product min-max layer; the raw generalized-pencil variational
theorem remains the only substantive spectral input. -/
theorem reducedRankHansenTheorem11_7_exactDimension_of_objective_extrema_and_dual_relation
    (Z : Matrix n ell ℝ) (X Xtilde : Matrix n k ℝ) (Y Ytilde Etilde : Matrix n m ℝ)
    (G : Matrix k r ℝ) (lambda : r → ℝ)
    (Aperp : Matrix m s ℝ) (eta : s → ℝ)
    (hG : reducedRankHansenGEigenvectors Xtilde Ytilde lambda G)
    (hGOpt : reducedRankConcentratedObjectiveMaximizer Xtilde Ytilde G)
    (hAperp : reducedRankHansenAperpEigenvectors Etilde Ytilde eta Aperp)
    (hAperpOpt : reducedRankAperpObjectiveMinimizer Etilde Ytilde Aperp)
    (W : Matrix m r ℝ) (Lambda LambdaInv : Matrix r r ℝ)
    (hDual : reducedRankDualEigenvectorRelation Xtilde Ytilde G W Lambda)
    (hOrth : reducedRankAperpYOrthogonal Ytilde Aperp W)
    (hLambdaInv : Lambda * LambdaInv = 1)
    (hdim : Fintype.card s = Fintype.card m - Fintype.card r) :
    ReducedRankHansenSmallestSummaryCompatibilityExactDimension Z X Xtilde Y Ytilde Etilde G
      (Ytildeᵀ * Xtilde * G)
      (reducedRankChat Z X Y G (Ytildeᵀ * Xtilde * G))
      ((Fintype.card n : ℝ)⁻¹ •
        (Ytildeᵀ * Ytilde -
          (Ytildeᵀ * Xtilde * G) * (Ytildeᵀ * Xtilde * G)ᵀ))
      Aperp lambda eta (reducedRankMaximizedLogLikelihood Ytilde lambda) :=
  ReducedRankHansenSmallestSummaryCompatibilityExactDimension.of_theorem11_7
    (reducedRankHansenTheorem11_7_of_objective_extrema_and_dual_relation
      Z X Xtilde Y Ytilde Etilde G lambda Aperp eta
      hG hGOpt hAperp hAperpOpt W Lambda LambdaInv hDual hOrth hLambdaInv)
    hdim

set_option linter.style.longLine false in
omit [DecidableEq n] in
/-- Canonical-`A⊥` normal-likelihood objective-extrema endpoint with Hansen's
displayed diagonal dual relation.

This is the objective-extrema counterpart of the determinant/product
canonical endpoints: a normal-likelihood proof only has to provide the two
objective extrema, Hansen's diagonal dual relation, and nonsingularity of the
selected compressed `G` determinant. The inverse selected-root block and exact
`dim(A⊥)=m-r` conclusion are derived internally. -/
theorem
    reducedRankHansenTheorem11_7_exactDimension_of_objective_extrema_certificate_diagonalDual_compressedDet_ne_zero_canonicalAperp
    (Z : Matrix n ell ℝ) (X Xtilde : Matrix n k ℝ) (Y Ytilde Etilde : Matrix n m ℝ)
    (G : Matrix k r ℝ) (lambda : r → ℝ)
    (Aperp : Matrix m (reducedRankAperpIndex m r) ℝ)
    (eta : reducedRankAperpIndex m r → ℝ)
    (hObj : ReducedRankHansenObjectiveExtremaCertificate
      Xtilde Ytilde Etilde G lambda Aperp eta)
    (W : Matrix m r ℝ)
    (hGdet : (Gᵀ * reducedRankGPencilA Xtilde Ytilde * G).det ≠ 0)
    (hDual : reducedRankDualEigenvectorRelation
      Xtilde Ytilde G W (Matrix.diagonal lambda))
    (hOrth : reducedRankAperpYOrthogonal Ytilde Aperp W) :
    ReducedRankHansenSmallestSummaryCompatibilityExactDimension Z X Xtilde Y Ytilde Etilde G
      (Ytildeᵀ * Xtilde * G)
      (reducedRankChat Z X Y G (Ytildeᵀ * Xtilde * G))
      ((Fintype.card n : ℝ)⁻¹ •
        (Ytildeᵀ * Ytilde -
          (Ytildeᵀ * Xtilde * G) * (Ytildeᵀ * Xtilde * G)ᵀ))
      Aperp lambda eta (reducedRankMaximizedLogLikelihood Ytilde lambda) :=
  ReducedRankHansenSmallestSummaryCompatibilityExactDimension.of_theorem11_7
    (reducedRankHansenSmallestSummaryCompatibility_of_identified_spectral_duality_certificate
      Z X Xtilde Y Ytilde Etilde G lambda Aperp eta
      (ReducedRankHansenIdentifiedSpectralDualityCertificate.of_detProductMinMax_diagonalDual_compressedDet_ne_zero
        hObj.to_detProductMinMaxCertificate W hGdet hDual hOrth))
    (reducedRankAperpDimension_canonical (m := m) (r := r))

set_option linter.style.longLine false in
omit [DecidableEq n] in
/-- Raw objective-extrema version of
`reducedRankHansenTheorem11_7_exactDimension_of_objective_extrema_certificate_diagonalDual_compressedDet_ne_zero_canonicalAperp`. -/
theorem
    reducedRankHansenTheorem11_7_exactDimension_of_objective_extrema_diagonalDual_compressedDet_ne_zero_canonicalAperp
    (Z : Matrix n ell ℝ) (X Xtilde : Matrix n k ℝ) (Y Ytilde Etilde : Matrix n m ℝ)
    (G : Matrix k r ℝ) (lambda : r → ℝ)
    (Aperp : Matrix m (reducedRankAperpIndex m r) ℝ)
    (eta : reducedRankAperpIndex m r → ℝ)
    (hG : reducedRankHansenGEigenvectors Xtilde Ytilde lambda G)
    (hGOpt : reducedRankConcentratedObjectiveMaximizer Xtilde Ytilde G)
    (hAperp : reducedRankHansenAperpEigenvectors Etilde Ytilde eta Aperp)
    (hAperpOpt : reducedRankAperpObjectiveMinimizer Etilde Ytilde Aperp)
    (W : Matrix m r ℝ)
    (hGdet : (Gᵀ * reducedRankGPencilA Xtilde Ytilde * G).det ≠ 0)
    (hDual : reducedRankDualEigenvectorRelation
      Xtilde Ytilde G W (Matrix.diagonal lambda))
    (hOrth : reducedRankAperpYOrthogonal Ytilde Aperp W) :
    ReducedRankHansenSmallestSummaryCompatibilityExactDimension Z X Xtilde Y Ytilde Etilde G
      (Ytildeᵀ * Xtilde * G)
      (reducedRankChat Z X Y G (Ytildeᵀ * Xtilde * G))
      ((Fintype.card n : ℝ)⁻¹ •
        (Ytildeᵀ * Ytilde -
          (Ytildeᵀ * Xtilde * G) * (Ytildeᵀ * Xtilde * G)ᵀ))
      Aperp lambda eta (reducedRankMaximizedLogLikelihood Ytilde lambda) :=
  reducedRankHansenTheorem11_7_exactDimension_of_objective_extrema_certificate_diagonalDual_compressedDet_ne_zero_canonicalAperp
    Z X Xtilde Y Ytilde Etilde G lambda Aperp eta
    { g_eigenvectors := hG
      g_objective_maximizer := hGOpt
      aperp_eigenvectors := hAperp
      aperp_objective_minimizer := hAperpOpt }
    W hGdet hDual hOrth

set_option linter.style.longLine false in
omit [DecidableEq n] in
/-- Canonical-`A⊥` normal-likelihood objective-extrema endpoint with Hansen's
displayed diagonal dual relation and nonzero selected-root product.

This is the product-nonzero counterpart of the compressed-determinant and
positive-root objective-extrema routes. -/
theorem
    reducedRankHansenTheorem11_7_exactDimension_of_objective_extrema_certificate_diagonalDual_prod_ne_zero_canonicalAperp
    (Z : Matrix n ell ℝ) (X Xtilde : Matrix n k ℝ) (Y Ytilde Etilde : Matrix n m ℝ)
    (G : Matrix k r ℝ) (lambda : r → ℝ)
    (Aperp : Matrix m (reducedRankAperpIndex m r) ℝ)
    (eta : reducedRankAperpIndex m r → ℝ)
    (hObj : ReducedRankHansenObjectiveExtremaCertificate
      Xtilde Ytilde Etilde G lambda Aperp eta)
    (W : Matrix m r ℝ)
    (hLambdaProd : (∏ j, lambda j) ≠ 0)
    (hDual : reducedRankDualEigenvectorRelation
      Xtilde Ytilde G W (Matrix.diagonal lambda))
    (hOrth : reducedRankAperpYOrthogonal Ytilde Aperp W) :
    ReducedRankHansenSmallestSummaryCompatibilityExactDimension Z X Xtilde Y Ytilde Etilde G
      (Ytildeᵀ * Xtilde * G)
      (reducedRankChat Z X Y G (Ytildeᵀ * Xtilde * G))
      ((Fintype.card n : ℝ)⁻¹ •
        (Ytildeᵀ * Ytilde -
          (Ytildeᵀ * Xtilde * G) * (Ytildeᵀ * Xtilde * G)ᵀ))
      Aperp lambda eta (reducedRankMaximizedLogLikelihood Ytilde lambda) :=
  ReducedRankHansenSmallestSummaryCompatibilityExactDimension.of_theorem11_7
    (reducedRankHansenSmallestSummaryCompatibility_of_identified_spectral_duality_certificate
      Z X Xtilde Y Ytilde Etilde G lambda Aperp eta
      (ReducedRankHansenIdentifiedSpectralDualityCertificate.of_detProductMinMax_diagonalDual_prod_ne_zero
        hObj.to_detProductMinMaxCertificate W hLambdaProd hDual hOrth))
    (reducedRankAperpDimension_canonical (m := m) (r := r))

set_option linter.style.longLine false in
omit [DecidableEq n] in
/-- Raw objective-extrema version of
`reducedRankHansenTheorem11_7_exactDimension_of_objective_extrema_certificate_diagonalDual_prod_ne_zero_canonicalAperp`. -/
theorem
    reducedRankHansenTheorem11_7_exactDimension_of_objective_extrema_diagonalDual_prod_ne_zero_canonicalAperp
    (Z : Matrix n ell ℝ) (X Xtilde : Matrix n k ℝ) (Y Ytilde Etilde : Matrix n m ℝ)
    (G : Matrix k r ℝ) (lambda : r → ℝ)
    (Aperp : Matrix m (reducedRankAperpIndex m r) ℝ)
    (eta : reducedRankAperpIndex m r → ℝ)
    (hG : reducedRankHansenGEigenvectors Xtilde Ytilde lambda G)
    (hGOpt : reducedRankConcentratedObjectiveMaximizer Xtilde Ytilde G)
    (hAperp : reducedRankHansenAperpEigenvectors Etilde Ytilde eta Aperp)
    (hAperpOpt : reducedRankAperpObjectiveMinimizer Etilde Ytilde Aperp)
    (W : Matrix m r ℝ)
    (hLambdaProd : (∏ j, lambda j) ≠ 0)
    (hDual : reducedRankDualEigenvectorRelation
      Xtilde Ytilde G W (Matrix.diagonal lambda))
    (hOrth : reducedRankAperpYOrthogonal Ytilde Aperp W) :
    ReducedRankHansenSmallestSummaryCompatibilityExactDimension Z X Xtilde Y Ytilde Etilde G
      (Ytildeᵀ * Xtilde * G)
      (reducedRankChat Z X Y G (Ytildeᵀ * Xtilde * G))
      ((Fintype.card n : ℝ)⁻¹ •
        (Ytildeᵀ * Ytilde -
          (Ytildeᵀ * Xtilde * G) * (Ytildeᵀ * Xtilde * G)ᵀ))
      Aperp lambda eta (reducedRankMaximizedLogLikelihood Ytilde lambda) :=
  reducedRankHansenTheorem11_7_exactDimension_of_objective_extrema_certificate_diagonalDual_prod_ne_zero_canonicalAperp
    Z X Xtilde Y Ytilde Etilde G lambda Aperp eta
    { g_eigenvectors := hG
      g_objective_maximizer := hGOpt
      aperp_eigenvectors := hAperp
      aperp_objective_minimizer := hAperpOpt }
    W hLambdaProd hDual hOrth

set_option linter.style.longLine false in
omit [DecidableEq n] in
/-- Canonical-`A⊥` objective-extrema endpoint with Hansen's displayed
diagonal dual relation and positive selected `G` roots.

This removes the explicit `det(G'AG) ≠ 0` premise from the normal-likelihood
route: positivity of the selected roots implies the selected compressed
determinant is nonsingular. -/
theorem
    reducedRankHansenTheorem11_7_exactDimension_of_objective_extrema_certificate_diagonalDual_pos_canonicalAperp
    (Z : Matrix n ell ℝ) (X Xtilde : Matrix n k ℝ) (Y Ytilde Etilde : Matrix n m ℝ)
    (G : Matrix k r ℝ) (lambda : r → ℝ)
    (Aperp : Matrix m (reducedRankAperpIndex m r) ℝ)
    (eta : reducedRankAperpIndex m r → ℝ)
    (hObj : ReducedRankHansenObjectiveExtremaCertificate
      Xtilde Ytilde Etilde G lambda Aperp eta)
    (W : Matrix m r ℝ)
    (hLambda : ∀ j, 0 < lambda j)
    (hDual : reducedRankDualEigenvectorRelation
      Xtilde Ytilde G W (Matrix.diagonal lambda))
    (hOrth : reducedRankAperpYOrthogonal Ytilde Aperp W) :
    ReducedRankHansenSmallestSummaryCompatibilityExactDimension Z X Xtilde Y Ytilde Etilde G
      (Ytildeᵀ * Xtilde * G)
      (reducedRankChat Z X Y G (Ytildeᵀ * Xtilde * G))
      ((Fintype.card n : ℝ)⁻¹ •
        (Ytildeᵀ * Ytilde -
          (Ytildeᵀ * Xtilde * G) * (Ytildeᵀ * Xtilde * G)ᵀ))
      Aperp lambda eta (reducedRankMaximizedLogLikelihood Ytilde lambda) :=
  ReducedRankHansenSmallestSummaryCompatibilityExactDimension.of_theorem11_7
    (reducedRankHansenSmallestSummaryCompatibility_of_identified_spectral_duality_certificate
      Z X Xtilde Y Ytilde Etilde G lambda Aperp eta
      (ReducedRankHansenIdentifiedSpectralDualityCertificate.of_detProductMinMax_diagonalDual_pos
        hObj.to_detProductMinMaxCertificate W hLambda hDual hOrth))
    (reducedRankAperpDimension_canonical (m := m) (r := r))

set_option linter.style.longLine false in
omit [DecidableEq n] in
/-- Raw objective-extrema version of
`reducedRankHansenTheorem11_7_exactDimension_of_objective_extrema_certificate_diagonalDual_pos_canonicalAperp`. -/
theorem
    reducedRankHansenTheorem11_7_exactDimension_of_objective_extrema_diagonalDual_pos_canonicalAperp
    (Z : Matrix n ell ℝ) (X Xtilde : Matrix n k ℝ) (Y Ytilde Etilde : Matrix n m ℝ)
    (G : Matrix k r ℝ) (lambda : r → ℝ)
    (Aperp : Matrix m (reducedRankAperpIndex m r) ℝ)
    (eta : reducedRankAperpIndex m r → ℝ)
    (hG : reducedRankHansenGEigenvectors Xtilde Ytilde lambda G)
    (hGOpt : reducedRankConcentratedObjectiveMaximizer Xtilde Ytilde G)
    (hAperp : reducedRankHansenAperpEigenvectors Etilde Ytilde eta Aperp)
    (hAperpOpt : reducedRankAperpObjectiveMinimizer Etilde Ytilde Aperp)
    (W : Matrix m r ℝ)
    (hLambda : ∀ j, 0 < lambda j)
    (hDual : reducedRankDualEigenvectorRelation
      Xtilde Ytilde G W (Matrix.diagonal lambda))
    (hOrth : reducedRankAperpYOrthogonal Ytilde Aperp W) :
    ReducedRankHansenSmallestSummaryCompatibilityExactDimension Z X Xtilde Y Ytilde Etilde G
      (Ytildeᵀ * Xtilde * G)
      (reducedRankChat Z X Y G (Ytildeᵀ * Xtilde * G))
      ((Fintype.card n : ℝ)⁻¹ •
        (Ytildeᵀ * Ytilde -
          (Ytildeᵀ * Xtilde * G) * (Ytildeᵀ * Xtilde * G)ᵀ))
      Aperp lambda eta (reducedRankMaximizedLogLikelihood Ytilde lambda) :=
  reducedRankHansenTheorem11_7_exactDimension_of_objective_extrema_certificate_diagonalDual_pos_canonicalAperp
    Z X Xtilde Y Ytilde Etilde G lambda Aperp eta
    { g_eigenvectors := hG
      g_objective_maximizer := hGOpt
      aperp_eigenvectors := hAperp
      aperp_objective_minimizer := hAperpOpt }
    W hLambda hDual hOrth

omit [DecidableEq n] in
/-- Hansen Theorem 11.7 from selected compressed-determinant extrema for the
two reduced-rank pencils. These extrema are converted to objective extrema and
then to the theorem-facing spectral certificate. -/
theorem reducedRankHansenTheorem11_7_of_selected_compressedDet_extrema
    (Z : Matrix n ell ℝ) (X Xtilde : Matrix n k ℝ) (Y Ytilde Etilde : Matrix n m ℝ)
    (G : Matrix k r ℝ) (lambda : r → ℝ)
    (Aperp : Matrix m s ℝ) (eta : s → ℝ)
    (hG : reducedRankHansenGEigenvectors Xtilde Ytilde lambda G)
    (hGNorm : reducedRankGNormalized Xtilde G)
    (hGMax :
      generalizedEigenSelectedCompressedDetMaximal
        (reducedRankGPencilA Xtilde Ytilde) (reducedRankGPencilB Xtilde) G)
    (hAperp : reducedRankHansenAperpEigenvectors Etilde Ytilde eta Aperp)
    (hAperpNorm : reducedRankAperpNormalized Ytilde Aperp)
    (hAperpMin :
      generalizedEigenSelectedCompressedDetMinimal
        (reducedRankAperpPencilA Etilde) (reducedRankAperpPencilB Ytilde) Aperp) :
    ReducedRankHansenSmallestSummaryCompatibility
      Z X Xtilde Y Ytilde Etilde G
      (Ytildeᵀ * Xtilde * G)
      (reducedRankChat Z X Y G (Ytildeᵀ * Xtilde * G))
      ((Fintype.card n : ℝ)⁻¹ •
        (Ytildeᵀ * Ytilde -
          (Ytildeᵀ * Xtilde * G) * (Ytildeᵀ * Xtilde * G)ᵀ))
      Aperp lambda eta (reducedRankMaximizedLogLikelihood Ytilde lambda) :=
  reducedRankHansenTheorem11_7_of_objective_extrema_certificate
    Z X Xtilde Y Ytilde Etilde G lambda Aperp eta
    (ReducedRankHansenObjectiveExtremaCertificate.of_selected_compressedDet_extrema
      Xtilde Ytilde Etilde G lambda Aperp eta
      hG hGNorm hGMax hAperp hAperpNorm hAperpMin)

omit [DecidableEq n] in
/-- Hansen Theorem 11.7 from selected compressed-determinant extrema plus the
displayed dual generalized-eigenvector relation. -/
theorem reducedRankHansenTheorem11_7_of_selected_compressedDet_extrema_and_dual_relation
    (Z : Matrix n ell ℝ) (X Xtilde : Matrix n k ℝ) (Y Ytilde Etilde : Matrix n m ℝ)
    (G : Matrix k r ℝ) (lambda : r → ℝ)
    (Aperp : Matrix m s ℝ) (eta : s → ℝ)
    (hG : reducedRankHansenGEigenvectors Xtilde Ytilde lambda G)
    (hGNorm : reducedRankGNormalized Xtilde G)
    (hGMax :
      generalizedEigenSelectedCompressedDetMaximal
        (reducedRankGPencilA Xtilde Ytilde) (reducedRankGPencilB Xtilde) G)
    (hAperp : reducedRankHansenAperpEigenvectors Etilde Ytilde eta Aperp)
    (hAperpNorm : reducedRankAperpNormalized Ytilde Aperp)
    (hAperpMin :
      generalizedEigenSelectedCompressedDetMinimal
        (reducedRankAperpPencilA Etilde) (reducedRankAperpPencilB Ytilde) Aperp)
    (W : Matrix m r ℝ) (Lambda LambdaInv : Matrix r r ℝ)
    (hDual : reducedRankDualEigenvectorRelation Xtilde Ytilde G W Lambda)
    (hOrth : reducedRankAperpYOrthogonal Ytilde Aperp W)
    (hLambdaInv : Lambda * LambdaInv = 1) :
    ReducedRankHansenSmallestSummaryCompatibility
      Z X Xtilde Y Ytilde Etilde G
      (Ytildeᵀ * Xtilde * G)
      (reducedRankChat Z X Y G (Ytildeᵀ * Xtilde * G))
      ((Fintype.card n : ℝ)⁻¹ •
        (Ytildeᵀ * Ytilde -
          (Ytildeᵀ * Xtilde * G) * (Ytildeᵀ * Xtilde * G)ᵀ))
      Aperp lambda eta (reducedRankMaximizedLogLikelihood Ytilde lambda) :=
  reducedRankHansenTheorem11_7_of_objective_extrema_certificate_and_dual_relation
    Z X Xtilde Y Ytilde Etilde G lambda Aperp eta
    (ReducedRankHansenObjectiveExtremaCertificate.of_selected_compressedDet_extrema
      Xtilde Ytilde Etilde G lambda Aperp eta
      hG hGNorm hGMax hAperp hAperpNorm hAperpMin)
    W Lambda LambdaInv hDual hOrth hLambdaInv

omit [DecidableEq n] in
/-- Hansen Theorem 11.7 from selected compressed-determinant extrema plus the
displayed dual relation, with Hansen's exact complementary dimension
`dim(A⊥) = m - r` carried explicitly. -/
theorem
    reducedRankHansenTheorem11_7_exactDimension_of_selected_compressedDet_extrema_and_dual_relation
    (Z : Matrix n ell ℝ) (X Xtilde : Matrix n k ℝ) (Y Ytilde Etilde : Matrix n m ℝ)
    (G : Matrix k r ℝ) (lambda : r → ℝ)
    (Aperp : Matrix m s ℝ) (eta : s → ℝ)
    (hG : reducedRankHansenGEigenvectors Xtilde Ytilde lambda G)
    (hGNorm : reducedRankGNormalized Xtilde G)
    (hGMax :
      generalizedEigenSelectedCompressedDetMaximal
        (reducedRankGPencilA Xtilde Ytilde) (reducedRankGPencilB Xtilde) G)
    (hAperp : reducedRankHansenAperpEigenvectors Etilde Ytilde eta Aperp)
    (hAperpNorm : reducedRankAperpNormalized Ytilde Aperp)
    (hAperpMin :
      generalizedEigenSelectedCompressedDetMinimal
        (reducedRankAperpPencilA Etilde) (reducedRankAperpPencilB Ytilde) Aperp)
    (W : Matrix m r ℝ) (Lambda LambdaInv : Matrix r r ℝ)
    (hDual : reducedRankDualEigenvectorRelation Xtilde Ytilde G W Lambda)
    (hOrth : reducedRankAperpYOrthogonal Ytilde Aperp W)
    (hLambdaInv : Lambda * LambdaInv = 1)
    (hdim : Fintype.card s = Fintype.card m - Fintype.card r) :
    ReducedRankHansenSmallestSummaryCompatibilityExactDimension Z X Xtilde Y Ytilde Etilde G
      (Ytildeᵀ * Xtilde * G)
      (reducedRankChat Z X Y G (Ytildeᵀ * Xtilde * G))
      ((Fintype.card n : ℝ)⁻¹ •
        (Ytildeᵀ * Ytilde -
          (Ytildeᵀ * Xtilde * G) * (Ytildeᵀ * Xtilde * G)ᵀ))
      Aperp lambda eta (reducedRankMaximizedLogLikelihood Ytilde lambda) :=
  ReducedRankHansenSmallestSummaryCompatibilityExactDimension.of_theorem11_7
    (reducedRankHansenTheorem11_7_of_selected_compressedDet_extrema_and_dual_relation
      Z X Xtilde Y Ytilde Etilde G lambda Aperp eta
      hG hGNorm hGMax hAperp hAperpNorm hAperpMin
      W Lambda LambdaInv hDual hOrth hLambdaInv)
    hdim

set_option linter.style.longLine false in
omit [DecidableEq n] in
/-- Canonical-`A⊥` selected-extrema endpoint with Hansen's displayed diagonal
dual relation and a nonzero selected-root product.

This is the product-nonzero counterpart of the compressed-determinant and
positive-root selected-extrema routes. -/
theorem
    reducedRankHansenTheorem11_7_exactDimension_of_selectedExtrema_diagonalDual_prod_ne_zero_canonicalAperp
    (Z : Matrix n ell ℝ) (X Xtilde : Matrix n k ℝ) (Y Ytilde Etilde : Matrix n m ℝ)
    (G : Matrix k r ℝ) (lambda : r → ℝ)
    (Aperp : Matrix m (reducedRankAperpIndex m r) ℝ)
    (eta : reducedRankAperpIndex m r → ℝ)
    (hG : reducedRankHansenGEigenvectors Xtilde Ytilde lambda G)
    (hGNorm : reducedRankGNormalized Xtilde G)
    (hGMax :
      generalizedEigenSelectedCompressedDetMaximal
        (reducedRankGPencilA Xtilde Ytilde) (reducedRankGPencilB Xtilde) G)
    (hAperp : reducedRankHansenAperpEigenvectors Etilde Ytilde eta Aperp)
    (hAperpNorm : reducedRankAperpNormalized Ytilde Aperp)
    (hAperpMin :
      generalizedEigenSelectedCompressedDetMinimal
        (reducedRankAperpPencilA Etilde) (reducedRankAperpPencilB Ytilde) Aperp)
    (W : Matrix m r ℝ)
    (hLambdaProd : (∏ j, lambda j) ≠ 0)
    (hDual : reducedRankDualEigenvectorRelation
      Xtilde Ytilde G W (Matrix.diagonal lambda))
    (hOrth : reducedRankAperpYOrthogonal Ytilde Aperp W) :
    ReducedRankHansenSmallestSummaryCompatibilityExactDimension Z X Xtilde Y Ytilde Etilde G
      (Ytildeᵀ * Xtilde * G)
      (reducedRankChat Z X Y G (Ytildeᵀ * Xtilde * G))
      ((Fintype.card n : ℝ)⁻¹ •
        (Ytildeᵀ * Ytilde -
          (Ytildeᵀ * Xtilde * G) * (Ytildeᵀ * Xtilde * G)ᵀ))
      Aperp lambda eta (reducedRankMaximizedLogLikelihood Ytilde lambda) :=
  ReducedRankHansenSmallestSummaryCompatibilityExactDimension.of_theorem11_7
    (reducedRankHansenSmallestSummaryCompatibility_of_identified_spectral_duality_certificate
      Z X Xtilde Y Ytilde Etilde G lambda Aperp eta
      (ReducedRankHansenIdentifiedSpectralDualityCertificate.of_selectedExtrema_diagonalDual_prod_ne_zero
        Xtilde Ytilde Etilde G lambda Aperp eta
        hG hGNorm hGMax hAperp hAperpNorm hAperpMin W hLambdaProd hDual hOrth))
    (reducedRankAperpDimension_canonical (m := m) (r := r))

set_option linter.style.longLine false in
omit [DecidableEq n] in
/-- Canonical-`A⊥` selected-extrema endpoint with Hansen's displayed diagonal
dual relation.

Compared with
`reducedRankHansenTheorem11_7_exactDimension_of_selected_compressedDet_extrema_and_dual_relation`,
this wrapper removes the arbitrary inverse selected-root block and the separate
dimension premise. The inverse block is derived from `det(G'AG) ≠ 0`, and the
exact `dim(A⊥)=m-r` equality is derived from the canonical
`reducedRankAperpIndex m r` index. -/
theorem
    reducedRankHansenTheorem11_7_exactDimension_of_selectedExtrema_diagonalDual_compressedDet_ne_zero_canonicalAperp
    (Z : Matrix n ell ℝ) (X Xtilde : Matrix n k ℝ) (Y Ytilde Etilde : Matrix n m ℝ)
    (G : Matrix k r ℝ) (lambda : r → ℝ)
    (Aperp : Matrix m (reducedRankAperpIndex m r) ℝ)
    (eta : reducedRankAperpIndex m r → ℝ)
    (hG : reducedRankHansenGEigenvectors Xtilde Ytilde lambda G)
    (hGNorm : reducedRankGNormalized Xtilde G)
    (hGMax :
      generalizedEigenSelectedCompressedDetMaximal
        (reducedRankGPencilA Xtilde Ytilde) (reducedRankGPencilB Xtilde) G)
    (hAperp : reducedRankHansenAperpEigenvectors Etilde Ytilde eta Aperp)
    (hAperpNorm : reducedRankAperpNormalized Ytilde Aperp)
    (hAperpMin :
      generalizedEigenSelectedCompressedDetMinimal
        (reducedRankAperpPencilA Etilde) (reducedRankAperpPencilB Ytilde) Aperp)
    (W : Matrix m r ℝ)
    (hGdet : (Gᵀ * reducedRankGPencilA Xtilde Ytilde * G).det ≠ 0)
    (hDual : reducedRankDualEigenvectorRelation
      Xtilde Ytilde G W (Matrix.diagonal lambda))
    (hOrth : reducedRankAperpYOrthogonal Ytilde Aperp W) :
    ReducedRankHansenSmallestSummaryCompatibilityExactDimension Z X Xtilde Y Ytilde Etilde G
      (Ytildeᵀ * Xtilde * G)
      (reducedRankChat Z X Y G (Ytildeᵀ * Xtilde * G))
      ((Fintype.card n : ℝ)⁻¹ •
        (Ytildeᵀ * Ytilde -
          (Ytildeᵀ * Xtilde * G) * (Ytildeᵀ * Xtilde * G)ᵀ))
      Aperp lambda eta (reducedRankMaximizedLogLikelihood Ytilde lambda) :=
  ReducedRankHansenSmallestSummaryCompatibilityExactDimension.of_theorem11_7
    (reducedRankHansenSmallestSummaryCompatibility_of_identified_spectral_duality_certificate
      Z X Xtilde Y Ytilde Etilde G lambda Aperp eta
      (ReducedRankHansenIdentifiedSpectralDualityCertificate.of_selectedExtrema_diagonalDual_compressedDet_ne_zero
        Xtilde Ytilde Etilde G lambda Aperp eta
        hG hGNorm hGMax hAperp hAperpNorm hAperpMin W hGdet hDual hOrth))
    (reducedRankAperpDimension_canonical (m := m) (r := r))

set_option linter.style.longLine false in
omit [DecidableEq n] in
/-- Canonical-`A⊥` selected-extrema endpoint with Hansen's displayed diagonal
dual relation and positive selected `G` roots.

This is the selected-compressed-determinant route with the determinant
nonsingularity premise removed: the selected generalized-eigenvector equations,
normalization, and positive roots imply `det(G'AG) ≠ 0`. -/
theorem
    reducedRankHansenTheorem11_7_exactDimension_of_selectedExtrema_diagonalDual_pos_canonicalAperp
    (Z : Matrix n ell ℝ) (X Xtilde : Matrix n k ℝ) (Y Ytilde Etilde : Matrix n m ℝ)
    (G : Matrix k r ℝ) (lambda : r → ℝ)
    (Aperp : Matrix m (reducedRankAperpIndex m r) ℝ)
    (eta : reducedRankAperpIndex m r → ℝ)
    (hG : reducedRankHansenGEigenvectors Xtilde Ytilde lambda G)
    (hGNorm : reducedRankGNormalized Xtilde G)
    (hGMax :
      generalizedEigenSelectedCompressedDetMaximal
        (reducedRankGPencilA Xtilde Ytilde) (reducedRankGPencilB Xtilde) G)
    (hAperp : reducedRankHansenAperpEigenvectors Etilde Ytilde eta Aperp)
    (hAperpNorm : reducedRankAperpNormalized Ytilde Aperp)
    (hAperpMin :
      generalizedEigenSelectedCompressedDetMinimal
        (reducedRankAperpPencilA Etilde) (reducedRankAperpPencilB Ytilde) Aperp)
    (W : Matrix m r ℝ)
    (hLambda : ∀ j, 0 < lambda j)
    (hDual : reducedRankDualEigenvectorRelation
      Xtilde Ytilde G W (Matrix.diagonal lambda))
    (hOrth : reducedRankAperpYOrthogonal Ytilde Aperp W) :
    ReducedRankHansenSmallestSummaryCompatibilityExactDimension Z X Xtilde Y Ytilde Etilde G
      (Ytildeᵀ * Xtilde * G)
      (reducedRankChat Z X Y G (Ytildeᵀ * Xtilde * G))
      ((Fintype.card n : ℝ)⁻¹ •
        (Ytildeᵀ * Ytilde -
          (Ytildeᵀ * Xtilde * G) * (Ytildeᵀ * Xtilde * G)ᵀ))
      Aperp lambda eta (reducedRankMaximizedLogLikelihood Ytilde lambda) :=
  reducedRankHansenTheorem11_7_exactDimension_of_selectedExtrema_diagonalDual_compressedDet_ne_zero_canonicalAperp
    Z X Xtilde Y Ytilde Etilde G lambda Aperp eta
    hG hGNorm hGMax hAperp hAperpNorm hAperpMin W
    (reducedRankGCompressedDet_ne_zero_of_pos Xtilde Ytilde lambda G
      hG hGNorm hLambda)
    hDual hOrth

omit [DecidableEq n] in
/-- Hansen Theorem 11.7 from the ordered generalized-eigenvalue min-max
certificate, routed through the objective-extrema theorem.

The certificate stores the exact G-side selected compressed-determinant maximum
and `A⊥` selected compressed-determinant minimum over all normalized
competitors. These extrema imply the two normal-likelihood objective extrema,
which are then consumed by `reducedRankHansenTheorem11_7_of_objective_extrema`. -/
theorem reducedRankHansenTheorem11_7_of_orderedGeneralizedEigen_minMax_certificate
    (Z : Matrix n ell ℝ) (X Xtilde : Matrix n k ℝ) (Y Ytilde Etilde : Matrix n m ℝ)
    (G : Matrix k r ℝ) (lambda : r → ℝ)
    (Aperp : Matrix m s ℝ) (eta : s → ℝ)
    (hMinMax : ReducedRankHansenDetProductMinMaxCertificate
      Xtilde Ytilde Etilde G lambda Aperp eta) :
    ReducedRankHansenSmallestSummaryCompatibility
      Z X Xtilde Y Ytilde Etilde G
      (Ytildeᵀ * Xtilde * G)
      (reducedRankChat Z X Y G (Ytildeᵀ * Xtilde * G))
      ((Fintype.card n : ℝ)⁻¹ •
        (Ytildeᵀ * Ytilde -
          (Ytildeᵀ * Xtilde * G) * (Ytildeᵀ * Xtilde * G)ᵀ))
      Aperp lambda eta (reducedRankMaximizedLogLikelihood Ytilde lambda) :=
  reducedRankHansenTheorem11_7_of_objective_extrema
    Z X Xtilde Y Ytilde Etilde G lambda Aperp eta
    hMinMax.g_max.eigenvectors
    hMinMax.g_objectiveMaximizer
    hMinMax.aperp_min.eigenvectors
    hMinMax.aperp_objectiveMinimizer

omit [DecidableEq n] in
/-- Hansen Theorem 11.7 from the ordered generalized-eigenvalue min-max
certificate, with the exact `A⊥` dimension `m - r` carried explicitly. -/
theorem reducedRankHansenTheorem11_7_exactDimension_of_orderedGeneralizedEigen_minMax_certificate
    (Z : Matrix n ell ℝ) (X Xtilde : Matrix n k ℝ) (Y Ytilde Etilde : Matrix n m ℝ)
    (G : Matrix k r ℝ) (lambda : r → ℝ)
    (Aperp : Matrix m s ℝ) (eta : s → ℝ)
    (hMinMax : ReducedRankHansenDetProductMinMaxCertificate
      Xtilde Ytilde Etilde G lambda Aperp eta)
    (hdim : Fintype.card s = Fintype.card m - Fintype.card r) :
    ReducedRankHansenSmallestSummaryCompatibilityExactDimension Z X Xtilde Y Ytilde Etilde G
      (Ytildeᵀ * Xtilde * G)
      (reducedRankChat Z X Y G (Ytildeᵀ * Xtilde * G))
      ((Fintype.card n : ℝ)⁻¹ •
        (Ytildeᵀ * Ytilde -
          (Ytildeᵀ * Xtilde * G) * (Ytildeᵀ * Xtilde * G)ᵀ))
      Aperp lambda eta (reducedRankMaximizedLogLikelihood Ytilde lambda) :=
  ReducedRankHansenSmallestSummaryCompatibilityExactDimension.of_theorem11_7
    (reducedRankHansenTheorem11_7_of_orderedGeneralizedEigen_minMax_certificate
      Z X Xtilde Y Ytilde Etilde G lambda Aperp eta hMinMax)
    hdim

omit [DecidableEq n] in
/-- Hansen Theorem 11.7 from the raw ordered generalized-eigenvalue min-max
surface.

This wrapper consumes the literal ordered product certificate and delegates
through its determinant/product certificate bridge. -/
theorem reducedRankHansenTheorem11_7_of_orderedGeneralizedEigen_certificate
    (Z : Matrix n ell ℝ) (X Xtilde : Matrix n k ℝ) (Y Ytilde Etilde : Matrix n m ℝ)
    (G : Matrix k r ℝ) (lambda : r → ℝ)
    (Aperp : Matrix m s ℝ) (eta : s → ℝ)
    (hOrdered : ReducedRankHansenOrderedGeneralizedEigenMinMaxCertificate
      Xtilde Ytilde Etilde G lambda Aperp eta) :
    ReducedRankHansenSmallestSummaryCompatibility
      Z X Xtilde Y Ytilde Etilde G
      (Ytildeᵀ * Xtilde * G)
      (reducedRankChat Z X Y G (Ytildeᵀ * Xtilde * G))
      ((Fintype.card n : ℝ)⁻¹ •
        (Ytildeᵀ * Ytilde -
          (Ytildeᵀ * Xtilde * G) * (Ytildeᵀ * Xtilde * G)ᵀ))
      Aperp lambda eta (reducedRankMaximizedLogLikelihood Ytilde lambda) :=
  reducedRankHansenTheorem11_7_of_orderedGeneralizedEigen_minMax_certificate
    Z X Xtilde Y Ytilde Etilde G lambda Aperp eta
    hOrdered.to_detProductMinMaxCertificate

omit [DecidableEq n] in
/-- Hansen Theorem 11.7 from the raw ordered generalized-eigenvalue min-max
surface, with Hansen's exact `dim(A⊥) = m - r` equality attached. -/
theorem reducedRankHansenTheorem11_7_exactDimension_of_orderedGeneralizedEigen_certificate
    (Z : Matrix n ell ℝ) (X Xtilde : Matrix n k ℝ) (Y Ytilde Etilde : Matrix n m ℝ)
    (G : Matrix k r ℝ) (lambda : r → ℝ)
    (Aperp : Matrix m s ℝ) (eta : s → ℝ)
    (hOrdered : ReducedRankHansenOrderedGeneralizedEigenMinMaxCertificate
      Xtilde Ytilde Etilde G lambda Aperp eta)
    (hdim : Fintype.card s = Fintype.card m - Fintype.card r) :
    ReducedRankHansenSmallestSummaryCompatibilityExactDimension Z X Xtilde Y Ytilde Etilde G
      (Ytildeᵀ * Xtilde * G)
      (reducedRankChat Z X Y G (Ytildeᵀ * Xtilde * G))
      ((Fintype.card n : ℝ)⁻¹ •
        (Ytildeᵀ * Ytilde -
          (Ytildeᵀ * Xtilde * G) * (Ytildeᵀ * Xtilde * G)ᵀ))
      Aperp lambda eta (reducedRankMaximizedLogLikelihood Ytilde lambda) :=
  ReducedRankHansenSmallestSummaryCompatibilityExactDimension.of_theorem11_7
    (reducedRankHansenTheorem11_7_of_orderedGeneralizedEigen_certificate
      Z X Xtilde Y Ytilde Etilde G lambda Aperp eta hOrdered)
    hdim

set_option linter.style.longLine false in
omit [DecidableEq n] in
/-- Hansen Theorem 11.7 from the raw ordered generalized-eigenvalue min-max
surface, Hansen's displayed diagonal dual relation, a nonzero selected-root
product, and a concrete complementary index split.

Compared with the generic product-bound endpoint, this wrapper consumes the
single ordered min-max certificate that the raw spectral theorem is expected to
produce. It derives pointwise selected-root nonsingularity and Hansen's exact
`dim(A⊥)=m-r` equality internally. -/
theorem
    reducedRankHansenTheorem11_7_exactDimension_of_orderedGeneralizedEigen_diagonalDual_prod_ne_zero_indexSplit
    (Z : Matrix n ell ℝ) (X Xtilde : Matrix n k ℝ) (Y Ytilde Etilde : Matrix n m ℝ)
    (G : Matrix k r ℝ) (lambda : r → ℝ)
    (Aperp : Matrix m s ℝ) (eta : s → ℝ)
    (hOrdered : ReducedRankHansenOrderedGeneralizedEigenMinMaxCertificate
      Xtilde Ytilde Etilde G lambda Aperp eta)
    (W : Matrix m r ℝ)
    (hLambdaProd : (∏ j, lambda j) ≠ 0)
    (hDual : reducedRankDualEigenvectorRelation
      Xtilde Ytilde G W (Matrix.diagonal lambda))
    (hOrth : reducedRankAperpYOrthogonal Ytilde Aperp W)
    (hIndex : m ≃ Sum r s) :
    ReducedRankHansenSmallestSummaryCompatibilityExactDimension Z X Xtilde Y Ytilde Etilde G
      (Ytildeᵀ * Xtilde * G)
      (reducedRankChat Z X Y G (Ytildeᵀ * Xtilde * G))
      ((Fintype.card n : ℝ)⁻¹ •
        (Ytildeᵀ * Ytilde -
          (Ytildeᵀ * Xtilde * G) * (Ytildeᵀ * Xtilde * G)ᵀ))
      Aperp lambda eta (reducedRankMaximizedLogLikelihood Ytilde lambda) :=
  ReducedRankHansenSmallestSummaryCompatibilityExactDimension.of_theorem11_7
    (reducedRankHansenSmallestSummaryCompatibility_of_identified_spectral_duality_certificate
      Z X Xtilde Y Ytilde Etilde G lambda Aperp eta
      (ReducedRankHansenIdentifiedSpectralDualityCertificate.of_orderedGeneralizedEigen_diagonalDual_prod_ne_zero
        hOrdered W hLambdaProd hDual hOrth))
    (reducedRankAperpDimension_of_equiv_sum (m := m) (r := r) (s := s) hIndex)

set_option linter.style.longLine false in
omit [DecidableEq n] in
/-- Compressed-determinant and index-split version of
`reducedRankHansenTheorem11_7_exactDimension_of_orderedGeneralizedEigen_diagonalDual_prod_ne_zero_indexSplit`.

The ordered min-max certificate supplies the selected generalized-eigenvector
equations and normalization, so nonsingularity of `det(G'AG)` is enough to
derive the nonzero selected-root product used by the diagonal duality step. -/
theorem
    reducedRankHansenTheorem11_7_exactDimension_of_orderedGeneralizedEigen_diagonalDual_compressedDet_ne_zero_indexSplit
    (Z : Matrix n ell ℝ) (X Xtilde : Matrix n k ℝ) (Y Ytilde Etilde : Matrix n m ℝ)
    (G : Matrix k r ℝ) (lambda : r → ℝ)
    (Aperp : Matrix m s ℝ) (eta : s → ℝ)
    (hOrdered : ReducedRankHansenOrderedGeneralizedEigenMinMaxCertificate
      Xtilde Ytilde Etilde G lambda Aperp eta)
    (W : Matrix m r ℝ)
    (hGdet : (Gᵀ * reducedRankGPencilA Xtilde Ytilde * G).det ≠ 0)
    (hDual : reducedRankDualEigenvectorRelation
      Xtilde Ytilde G W (Matrix.diagonal lambda))
    (hOrth : reducedRankAperpYOrthogonal Ytilde Aperp W)
    (hIndex : m ≃ Sum r s) :
    ReducedRankHansenSmallestSummaryCompatibilityExactDimension Z X Xtilde Y Ytilde Etilde G
      (Ytildeᵀ * Xtilde * G)
      (reducedRankChat Z X Y G (Ytildeᵀ * Xtilde * G))
      ((Fintype.card n : ℝ)⁻¹ •
        (Ytildeᵀ * Ytilde -
          (Ytildeᵀ * Xtilde * G) * (Ytildeᵀ * Xtilde * G)ᵀ))
      Aperp lambda eta (reducedRankMaximizedLogLikelihood Ytilde lambda) :=
  reducedRankHansenTheorem11_7_exactDimension_of_orderedGeneralizedEigen_diagonalDual_prod_ne_zero_indexSplit
    Z X Xtilde Y Ytilde Etilde G lambda Aperp eta hOrdered W
    (hOrdered.g_ordered.rootProduct_ne_zero_of_compressedDet_ne_zero hGdet)
    hDual hOrth hIndex

set_option linter.style.longLine false in
omit [DecidableEq n] in
/-- Hansen Theorem 11.7 from the raw ordered generalized-eigenvalue min-max
surface, Hansen's displayed diagonal dual relation, positive selected `G`
roots, and a concrete complementary index split.

This is the positive-root variant of
`reducedRankHansenTheorem11_7_exactDimension_of_orderedGeneralizedEigen_diagonalDual_prod_ne_zero_indexSplit`;
it derives the nonzero selected-root product internally. -/
theorem
    reducedRankHansenTheorem11_7_exactDimension_of_orderedGeneralizedEigen_diagonalDual_pos_indexSplit
    (Z : Matrix n ell ℝ) (X Xtilde : Matrix n k ℝ) (Y Ytilde Etilde : Matrix n m ℝ)
    (G : Matrix k r ℝ) (lambda : r → ℝ)
    (Aperp : Matrix m s ℝ) (eta : s → ℝ)
    (hOrdered : ReducedRankHansenOrderedGeneralizedEigenMinMaxCertificate
      Xtilde Ytilde Etilde G lambda Aperp eta)
    (W : Matrix m r ℝ)
    (hLambda : ∀ j, 0 < lambda j)
    (hDual : reducedRankDualEigenvectorRelation
      Xtilde Ytilde G W (Matrix.diagonal lambda))
    (hOrth : reducedRankAperpYOrthogonal Ytilde Aperp W)
    (hIndex : m ≃ Sum r s) :
    ReducedRankHansenSmallestSummaryCompatibilityExactDimension Z X Xtilde Y Ytilde Etilde G
      (Ytildeᵀ * Xtilde * G)
      (reducedRankChat Z X Y G (Ytildeᵀ * Xtilde * G))
      ((Fintype.card n : ℝ)⁻¹ •
        (Ytildeᵀ * Ytilde -
          (Ytildeᵀ * Xtilde * G) * (Ytildeᵀ * Xtilde * G)ᵀ))
      Aperp lambda eta (reducedRankMaximizedLogLikelihood Ytilde lambda) :=
  reducedRankHansenTheorem11_7_exactDimension_of_orderedGeneralizedEigen_diagonalDual_prod_ne_zero_indexSplit
    Z X Xtilde Y Ytilde Etilde G lambda Aperp eta hOrdered W
    (reducedRankSelectedRootProduct_ne_zero_of_pos lambda hLambda)
    hDual hOrth hIndex

set_option linter.style.longLine false in
omit [DecidableEq n] in
/-- Hansen Theorem 11.7 from the raw ordered generalized-eigenvalue min-max
surface, diagonal dual relation, and nonzero selected-root product, using the
canonical `A⊥` index `Fin (card m - card r)`.

Compared with
`reducedRankHansenTheorem11_7_exactDimension_of_orderedGeneralizedEigen_diagonalDual_prod_ne_zero_indexSplit`,
this endpoint removes the separate finite split premise: the exact
complementary-rank dimension is derived from the chosen `A⊥` index type. -/
theorem
    reducedRankHansenTheorem11_7_exactDimension_of_orderedGeneralizedEigen_diagonalDual_prod_ne_zero_canonicalAperp
    (Z : Matrix n ell ℝ) (X Xtilde : Matrix n k ℝ) (Y Ytilde Etilde : Matrix n m ℝ)
    (G : Matrix k r ℝ) (lambda : r → ℝ)
    (Aperp : Matrix m (reducedRankAperpIndex m r) ℝ)
    (eta : reducedRankAperpIndex m r → ℝ)
    (hOrdered : ReducedRankHansenOrderedGeneralizedEigenMinMaxCertificate
      Xtilde Ytilde Etilde G lambda Aperp eta)
    (W : Matrix m r ℝ)
    (hLambdaProd : (∏ j, lambda j) ≠ 0)
    (hDual : reducedRankDualEigenvectorRelation
      Xtilde Ytilde G W (Matrix.diagonal lambda))
    (hOrth : reducedRankAperpYOrthogonal Ytilde Aperp W) :
    ReducedRankHansenSmallestSummaryCompatibilityExactDimension Z X Xtilde Y Ytilde Etilde G
      (Ytildeᵀ * Xtilde * G)
      (reducedRankChat Z X Y G (Ytildeᵀ * Xtilde * G))
      ((Fintype.card n : ℝ)⁻¹ •
        (Ytildeᵀ * Ytilde -
          (Ytildeᵀ * Xtilde * G) * (Ytildeᵀ * Xtilde * G)ᵀ))
      Aperp lambda eta (reducedRankMaximizedLogLikelihood Ytilde lambda) :=
  ReducedRankHansenSmallestSummaryCompatibilityExactDimension.of_theorem11_7
    (reducedRankHansenSmallestSummaryCompatibility_of_identified_spectral_duality_certificate
      Z X Xtilde Y Ytilde Etilde G lambda Aperp eta
      (ReducedRankHansenIdentifiedSpectralDualityCertificate.of_orderedGeneralizedEigen_diagonalDual_prod_ne_zero
        hOrdered W hLambdaProd hDual hOrth))
    (reducedRankAperpDimension_canonical (m := m) (r := r))

set_option linter.style.longLine false in
omit [DecidableEq n] in
/-- Positive-root canonical-`A⊥` version of
`reducedRankHansenTheorem11_7_exactDimension_of_orderedGeneralizedEigen_diagonalDual_prod_ne_zero_canonicalAperp`.

The positive selected `G` roots supply the nonzero product, and the canonical
`A⊥` index supplies Hansen's exact `m-r` dimension. -/
theorem
    reducedRankHansenTheorem11_7_exactDimension_of_orderedGeneralizedEigen_diagonalDual_pos_canonicalAperp
    (Z : Matrix n ell ℝ) (X Xtilde : Matrix n k ℝ) (Y Ytilde Etilde : Matrix n m ℝ)
    (G : Matrix k r ℝ) (lambda : r → ℝ)
    (Aperp : Matrix m (reducedRankAperpIndex m r) ℝ)
    (eta : reducedRankAperpIndex m r → ℝ)
    (hOrdered : ReducedRankHansenOrderedGeneralizedEigenMinMaxCertificate
      Xtilde Ytilde Etilde G lambda Aperp eta)
    (W : Matrix m r ℝ)
    (hLambda : ∀ j, 0 < lambda j)
    (hDual : reducedRankDualEigenvectorRelation
      Xtilde Ytilde G W (Matrix.diagonal lambda))
    (hOrth : reducedRankAperpYOrthogonal Ytilde Aperp W) :
    ReducedRankHansenSmallestSummaryCompatibilityExactDimension Z X Xtilde Y Ytilde Etilde G
      (Ytildeᵀ * Xtilde * G)
      (reducedRankChat Z X Y G (Ytildeᵀ * Xtilde * G))
      ((Fintype.card n : ℝ)⁻¹ •
        (Ytildeᵀ * Ytilde -
          (Ytildeᵀ * Xtilde * G) * (Ytildeᵀ * Xtilde * G)ᵀ))
      Aperp lambda eta (reducedRankMaximizedLogLikelihood Ytilde lambda) :=
  reducedRankHansenTheorem11_7_exactDimension_of_orderedGeneralizedEigen_diagonalDual_prod_ne_zero_canonicalAperp
    Z X Xtilde Y Ytilde Etilde G lambda Aperp eta hOrdered W
    (reducedRankSelectedRootProduct_ne_zero_of_pos lambda hLambda)
    hDual hOrth

set_option linter.style.longLine false in
omit [DecidableEq n] in
/-- Canonical-`A⊥` endpoint where selected-root nonsingularity is derived from
the nonzero selected compressed determinant.

This replaces the explicit positive-root/nonzero-product premise by the
determinant primitive most directly connected to the ordered generalized-pencil
product setup: under the selected generalized-eigenvector equations and Hansen
normalization, `det(G'AG) = ∏ λ_j`. -/
theorem
    reducedRankHansenTheorem11_7_exactDimension_of_orderedGeneralizedEigen_diagonalDual_compressedDet_ne_zero_canonicalAperp
    (Z : Matrix n ell ℝ) (X Xtilde : Matrix n k ℝ) (Y Ytilde Etilde : Matrix n m ℝ)
    (G : Matrix k r ℝ) (lambda : r → ℝ)
    (Aperp : Matrix m (reducedRankAperpIndex m r) ℝ)
    (eta : reducedRankAperpIndex m r → ℝ)
    (hOrdered : ReducedRankHansenOrderedGeneralizedEigenMinMaxCertificate
      Xtilde Ytilde Etilde G lambda Aperp eta)
    (W : Matrix m r ℝ)
    (hGdet : (Gᵀ * reducedRankGPencilA Xtilde Ytilde * G).det ≠ 0)
    (hDual : reducedRankDualEigenvectorRelation
      Xtilde Ytilde G W (Matrix.diagonal lambda))
    (hOrth : reducedRankAperpYOrthogonal Ytilde Aperp W) :
    ReducedRankHansenSmallestSummaryCompatibilityExactDimension Z X Xtilde Y Ytilde Etilde G
      (Ytildeᵀ * Xtilde * G)
      (reducedRankChat Z X Y G (Ytildeᵀ * Xtilde * G))
      ((Fintype.card n : ℝ)⁻¹ •
        (Ytildeᵀ * Ytilde -
          (Ytildeᵀ * Xtilde * G) * (Ytildeᵀ * Xtilde * G)ᵀ))
      Aperp lambda eta (reducedRankMaximizedLogLikelihood Ytilde lambda) :=
  reducedRankHansenTheorem11_7_exactDimension_of_orderedGeneralizedEigen_diagonalDual_prod_ne_zero_canonicalAperp
    Z X Xtilde Y Ytilde Etilde G lambda Aperp eta hOrdered W
    (hOrdered.g_ordered.rootProduct_ne_zero_of_compressedDet_ne_zero hGdet)
    hDual hOrth

/-- Residualized Hansen Theorem 11.7 endpoint.

This specializes the theorem-facing conclusion to `X̃ = M_Z X`,
`Ỹ = M_Z Y`, and `Ẽ = M_[X,Z]Y`. -/
theorem reducedRankHansenTheorem11_7_residualized_of_spectral_duality_certificate
    (Z : Matrix n ell ℝ) (X : Matrix n k ℝ) (Y : Matrix n m ℝ)
    [DecidableEq k]
    [Invertible (Zᵀ * Z)]
    [Invertible ((Matrix.fromCols X Z)ᵀ * Matrix.fromCols X Z)]
    (G : Matrix k r ℝ) (lambda : r → ℝ)
    (Aperp : Matrix m s ℝ) (eta : s → ℝ)
    (hSpec : ReducedRankHansenSpectralDualityCertificate
      (reducedRankTildeX Z X) (reducedRankTildeY Z Y) (reducedRankTildeE X Z Y)
      G lambda Aperp eta) :
    ReducedRankHansenSmallestSummaryCompatibility
      Z X (reducedRankTildeX Z X) Y (reducedRankTildeY Z Y)
      (reducedRankTildeE X Z Y) G
      ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G)
      (reducedRankChat Z X Y G
        ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G))
      ((Fintype.card n : ℝ)⁻¹ •
        ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeY Z Y) -
          ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G) *
            ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G)ᵀ))
      Aperp lambda eta (reducedRankMaximizedLogLikelihood (reducedRankTildeY Z Y) lambda) :=
  reducedRankHansenTheorem11_7_of_spectral_duality_certificate Z X
    (reducedRankTildeX Z X) Y (reducedRankTildeY Z Y) (reducedRankTildeE X Z Y)
    G lambda Aperp eta hSpec

/-- Residualized Hansen Theorem 11.7 from the exact spectral-duality
certificate, with Hansen's complementary-rank condition `dim(A⊥) = m - r`
carried explicitly. -/
theorem reducedRankHansenTheorem11_7_residualized_exactDimension_of_spectral_duality_certificate
    (Z : Matrix n ell ℝ) (X : Matrix n k ℝ) (Y : Matrix n m ℝ)
    [DecidableEq k]
    [Invertible (Zᵀ * Z)]
    [Invertible ((Matrix.fromCols X Z)ᵀ * Matrix.fromCols X Z)]
    (G : Matrix k r ℝ) (lambda : r → ℝ)
    (Aperp : Matrix m s ℝ) (eta : s → ℝ)
    (hSpec : ReducedRankHansenSpectralDualityCertificate
      (reducedRankTildeX Z X) (reducedRankTildeY Z Y) (reducedRankTildeE X Z Y)
      G lambda Aperp eta)
    (hdim : Fintype.card s = Fintype.card m - Fintype.card r) :
    ReducedRankHansenSmallestSummaryCompatibilityExactDimension
      Z X (reducedRankTildeX Z X) Y (reducedRankTildeY Z Y) (reducedRankTildeE X Z Y) G
      ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G)
      (reducedRankChat Z X Y G
        ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G))
      ((Fintype.card n : ℝ)⁻¹ •
        ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeY Z Y) -
          ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G) *
            ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G)ᵀ))
      Aperp lambda eta (reducedRankMaximizedLogLikelihood (reducedRankTildeY Z Y) lambda) :=
  ReducedRankHansenSmallestSummaryCompatibilityExactDimension.of_theorem11_7
    (reducedRankHansenTheorem11_7_residualized_of_spectral_duality_certificate
      Z X Y G lambda Aperp eta hSpec)
    hdim

/-- Residualized Hansen Theorem 11.7 endpoint from the objective-extrema
certificate for Hansen's two residualized determinant objectives. -/
theorem reducedRankHansenTheorem11_7_residualized_of_objective_extrema_certificate
    (Z : Matrix n ell ℝ) (X : Matrix n k ℝ) (Y : Matrix n m ℝ)
    [DecidableEq k]
    [Invertible (Zᵀ * Z)]
    [Invertible ((Matrix.fromCols X Z)ᵀ * Matrix.fromCols X Z)]
    (G : Matrix k r ℝ) (lambda : r → ℝ)
    (Aperp : Matrix m s ℝ) (eta : s → ℝ)
    (hObj : ReducedRankHansenObjectiveExtremaCertificate
      (reducedRankTildeX Z X) (reducedRankTildeY Z Y) (reducedRankTildeE X Z Y)
      G lambda Aperp eta) :
    ReducedRankHansenSmallestSummaryCompatibility
      Z X (reducedRankTildeX Z X) Y (reducedRankTildeY Z Y)
      (reducedRankTildeE X Z Y) G
      ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G)
      (reducedRankChat Z X Y G
        ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G))
      ((Fintype.card n : ℝ)⁻¹ •
        ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeY Z Y) -
          ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G) *
            ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G)ᵀ))
      Aperp lambda eta (reducedRankMaximizedLogLikelihood (reducedRankTildeY Z Y) lambda) :=
  reducedRankHansenTheorem11_7_residualized_of_spectral_duality_certificate
    Z X Y G lambda Aperp eta hObj.to_spectralDualityCertificate

/-- Residualized Hansen Theorem 11.7 endpoint from the concrete objective
extrema for Hansen's two residualized determinant objectives. -/
theorem reducedRankHansenTheorem11_7_residualized_of_objective_extrema
    (Z : Matrix n ell ℝ) (X : Matrix n k ℝ) (Y : Matrix n m ℝ)
    [DecidableEq k]
    [Invertible (Zᵀ * Z)]
    [Invertible ((Matrix.fromCols X Z)ᵀ * Matrix.fromCols X Z)]
    (G : Matrix k r ℝ) (lambda : r → ℝ)
    (Aperp : Matrix m s ℝ) (eta : s → ℝ)
    (hG : reducedRankHansenGEigenvectors
      (reducedRankTildeX Z X) (reducedRankTildeY Z Y) lambda G)
    (hGOpt : reducedRankConcentratedObjectiveMaximizer
      (reducedRankTildeX Z X) (reducedRankTildeY Z Y) G)
    (hAperp : reducedRankHansenAperpEigenvectors
      (reducedRankTildeE X Z Y) (reducedRankTildeY Z Y) eta Aperp)
    (hAperpOpt : reducedRankAperpObjectiveMinimizer
      (reducedRankTildeE X Z Y) (reducedRankTildeY Z Y) Aperp) :
    ReducedRankHansenSmallestSummaryCompatibility
      Z X (reducedRankTildeX Z X) Y (reducedRankTildeY Z Y)
      (reducedRankTildeE X Z Y) G
      ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G)
      (reducedRankChat Z X Y G
        ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G))
      ((Fintype.card n : ℝ)⁻¹ •
        ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeY Z Y) -
          ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G) *
            ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G)ᵀ))
      Aperp lambda eta (reducedRankMaximizedLogLikelihood (reducedRankTildeY Z Y) lambda) :=
  reducedRankHansenTheorem11_7_residualized_of_objective_extrema_certificate
    Z X Y G lambda Aperp eta
    { g_eigenvectors := hG
      g_objective_maximizer := hGOpt
      aperp_eigenvectors := hAperp
      aperp_objective_minimizer := hAperpOpt }

/-- Residualized Hansen Theorem 11.7 endpoint from the determinant/product
min-max certificate for Hansen's two residualized pencils. -/
theorem reducedRankHansenTheorem11_7_residualized_of_detProductMinMax_certificate
    (Z : Matrix n ell ℝ) (X : Matrix n k ℝ) (Y : Matrix n m ℝ)
    [DecidableEq k]
    [Invertible (Zᵀ * Z)]
    [Invertible ((Matrix.fromCols X Z)ᵀ * Matrix.fromCols X Z)]
    (G : Matrix k r ℝ) (lambda : r → ℝ)
    (Aperp : Matrix m s ℝ) (eta : s → ℝ)
    (hMinMax : ReducedRankHansenDetProductMinMaxCertificate
      (reducedRankTildeX Z X) (reducedRankTildeY Z Y) (reducedRankTildeE X Z Y)
      G lambda Aperp eta) :
    ReducedRankHansenSmallestSummaryCompatibility
      Z X (reducedRankTildeX Z X) Y (reducedRankTildeY Z Y)
      (reducedRankTildeE X Z Y) G
      ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G)
      (reducedRankChat Z X Y G
        ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G))
      ((Fintype.card n : ℝ)⁻¹ •
        ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeY Z Y) -
          ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G) *
            ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G)ᵀ))
      Aperp lambda eta (reducedRankMaximizedLogLikelihood (reducedRankTildeY Z Y) lambda) :=
  reducedRankHansenTheorem11_7_residualized_of_spectral_duality_certificate
    Z X Y G lambda Aperp eta
    (ReducedRankHansenDetProductMinMaxCertificate.to_spectralDualityCertificate hMinMax)

/-- Residualized Hansen Theorem 11.7 endpoint from the determinant/product
min-max certificate and Hansen's displayed dual generalized-eigenvector
relation. -/
theorem reducedRankHansenTheorem11_7_residualized_of_detProductMinMax_and_dual_relation
    (Z : Matrix n ell ℝ) (X : Matrix n k ℝ) (Y : Matrix n m ℝ)
    [DecidableEq k]
    [Invertible (Zᵀ * Z)]
    [Invertible ((Matrix.fromCols X Z)ᵀ * Matrix.fromCols X Z)]
    (G : Matrix k r ℝ) (lambda : r → ℝ)
    (Aperp : Matrix m s ℝ) (eta : s → ℝ)
    (hMinMax : ReducedRankHansenDetProductMinMaxCertificate
      (reducedRankTildeX Z X) (reducedRankTildeY Z Y) (reducedRankTildeE X Z Y)
      G lambda Aperp eta)
    (W : Matrix m r ℝ) (Lambda LambdaInv : Matrix r r ℝ)
    (hDual : reducedRankDualEigenvectorRelation
      (reducedRankTildeX Z X) (reducedRankTildeY Z Y) G W Lambda)
    (hOrth : reducedRankAperpYOrthogonal (reducedRankTildeY Z Y) Aperp W)
    (hLambdaInv : Lambda * LambdaInv = 1) :
    ReducedRankHansenSmallestSummaryCompatibility
      Z X (reducedRankTildeX Z X) Y (reducedRankTildeY Z Y)
      (reducedRankTildeE X Z Y) G
      ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G)
      (reducedRankChat Z X Y G
        ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G))
      ((Fintype.card n : ℝ)⁻¹ •
        ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeY Z Y) -
          ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G) *
            ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G)ᵀ))
      Aperp lambda eta (reducedRankMaximizedLogLikelihood (reducedRankTildeY Z Y) lambda) :=
  reducedRankHansenTheorem11_7_of_detProductMinMax_and_dual_relation
    Z X (reducedRankTildeX Z X) Y (reducedRankTildeY Z Y) (reducedRankTildeE X Z Y)
    G lambda Aperp eta hMinMax W Lambda LambdaInv hDual hOrth hLambdaInv

/-- Residualized Hansen Theorem 11.7 endpoint from objective extrema plus
Hansen's displayed dual generalized-eigenvector relation. -/
theorem reducedRankHansenTheorem11_7_residualized_of_objective_extrema_and_dual_relation
    (Z : Matrix n ell ℝ) (X : Matrix n k ℝ) (Y : Matrix n m ℝ)
    [DecidableEq k]
    [Invertible (Zᵀ * Z)]
    [Invertible ((Matrix.fromCols X Z)ᵀ * Matrix.fromCols X Z)]
    (G : Matrix k r ℝ) (lambda : r → ℝ)
    (Aperp : Matrix m s ℝ) (eta : s → ℝ)
    (hG : reducedRankHansenGEigenvectors
      (reducedRankTildeX Z X) (reducedRankTildeY Z Y) lambda G)
    (hGOpt : reducedRankConcentratedObjectiveMaximizer
      (reducedRankTildeX Z X) (reducedRankTildeY Z Y) G)
    (hAperp : reducedRankHansenAperpEigenvectors
      (reducedRankTildeE X Z Y) (reducedRankTildeY Z Y) eta Aperp)
    (hAperpOpt : reducedRankAperpObjectiveMinimizer
      (reducedRankTildeE X Z Y) (reducedRankTildeY Z Y) Aperp)
    (W : Matrix m r ℝ) (Lambda LambdaInv : Matrix r r ℝ)
    (hDual : reducedRankDualEigenvectorRelation
      (reducedRankTildeX Z X) (reducedRankTildeY Z Y) G W Lambda)
    (hOrth : reducedRankAperpYOrthogonal (reducedRankTildeY Z Y) Aperp W)
    (hLambdaInv : Lambda * LambdaInv = 1) :
    ReducedRankHansenSmallestSummaryCompatibility
      Z X (reducedRankTildeX Z X) Y (reducedRankTildeY Z Y)
      (reducedRankTildeE X Z Y) G
      ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G)
      (reducedRankChat Z X Y G
        ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G))
      ((Fintype.card n : ℝ)⁻¹ •
        ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeY Z Y) -
          ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G) *
            ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G)ᵀ))
      Aperp lambda eta (reducedRankMaximizedLogLikelihood (reducedRankTildeY Z Y) lambda) :=
  reducedRankHansenTheorem11_7_of_objective_extrema_and_dual_relation
    Z X (reducedRankTildeX Z X) Y (reducedRankTildeY Z Y) (reducedRankTildeE X Z Y)
    G lambda Aperp eta hG hGOpt hAperp hAperpOpt
    W Lambda LambdaInv hDual hOrth hLambdaInv

/-- Residualized Hansen Theorem 11.7 from the determinant/product min-max
certificate and Hansen's displayed dual generalized-eigenvector relation, with
the exact `A⊥` dimension `m-r` carried explicitly. -/
theorem
    reducedRankHansenTheorem11_7_residualized_exactDimension_of_detProductMinMax_and_dual_relation
    (Z : Matrix n ell ℝ) (X : Matrix n k ℝ) (Y : Matrix n m ℝ)
    [DecidableEq k]
    [Invertible (Zᵀ * Z)]
    [Invertible ((Matrix.fromCols X Z)ᵀ * Matrix.fromCols X Z)]
    (G : Matrix k r ℝ) (lambda : r → ℝ)
    (Aperp : Matrix m s ℝ) (eta : s → ℝ)
    (hMinMax : ReducedRankHansenDetProductMinMaxCertificate
      (reducedRankTildeX Z X) (reducedRankTildeY Z Y) (reducedRankTildeE X Z Y)
      G lambda Aperp eta)
    (W : Matrix m r ℝ) (Lambda LambdaInv : Matrix r r ℝ)
    (hDual : reducedRankDualEigenvectorRelation
      (reducedRankTildeX Z X) (reducedRankTildeY Z Y) G W Lambda)
    (hOrth : reducedRankAperpYOrthogonal (reducedRankTildeY Z Y) Aperp W)
    (hLambdaInv : Lambda * LambdaInv = 1)
    (hdim : Fintype.card s = Fintype.card m - Fintype.card r) :
    ReducedRankHansenSmallestSummaryCompatibilityExactDimension
      Z X (reducedRankTildeX Z X) Y (reducedRankTildeY Z Y) (reducedRankTildeE X Z Y) G
      ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G)
      (reducedRankChat Z X Y G
        ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G))
      ((Fintype.card n : ℝ)⁻¹ •
        ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeY Z Y) -
          ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G) *
            ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G)ᵀ))
      Aperp lambda eta (reducedRankMaximizedLogLikelihood (reducedRankTildeY Z Y) lambda) :=
  ReducedRankHansenSmallestSummaryCompatibilityExactDimension.of_theorem11_7
    (reducedRankHansenTheorem11_7_residualized_of_detProductMinMax_and_dual_relation
      Z X Y G lambda Aperp eta hMinMax W Lambda LambdaInv hDual hOrth hLambdaInv)
    hdim

set_option linter.style.longLine false in
/-- Residualized determinant/product min-max endpoint with Hansen's diagonal
dual relation, a nonzero selected compressed determinant, and canonical `A⊥`
index.

This specializes
`reducedRankHansenTheorem11_7_exactDimension_of_detProductMinMax_diagonalDual_compressedDet_ne_zero_canonicalAperp`
to `X̃ = M_ZX`, `Ỹ = M_ZY`, and `Ẽ = M_[X,Z]Y`. -/
theorem
    reducedRankHansenTheorem11_7_residualized_exactDimension_of_detProductMinMax_diagonalDual_compressedDet_ne_zero_canonicalAperp
    (Z : Matrix n ell ℝ) (X : Matrix n k ℝ) (Y : Matrix n m ℝ)
    [DecidableEq k]
    [Invertible (Zᵀ * Z)]
    [Invertible ((Matrix.fromCols X Z)ᵀ * Matrix.fromCols X Z)]
    (G : Matrix k r ℝ) (lambda : r → ℝ)
    (Aperp : Matrix m (reducedRankAperpIndex m r) ℝ)
    (eta : reducedRankAperpIndex m r → ℝ)
    (hMinMax : ReducedRankHansenDetProductMinMaxCertificate
      (reducedRankTildeX Z X) (reducedRankTildeY Z Y) (reducedRankTildeE X Z Y)
      G lambda Aperp eta)
    (W : Matrix m r ℝ)
    (hGdet :
      (Gᵀ * reducedRankGPencilA (reducedRankTildeX Z X) (reducedRankTildeY Z Y) * G).det ≠ 0)
    (hDual : reducedRankDualEigenvectorRelation
      (reducedRankTildeX Z X) (reducedRankTildeY Z Y) G W (Matrix.diagonal lambda))
    (hOrth : reducedRankAperpYOrthogonal (reducedRankTildeY Z Y) Aperp W) :
    ReducedRankHansenSmallestSummaryCompatibilityExactDimension
      Z X (reducedRankTildeX Z X) Y (reducedRankTildeY Z Y) (reducedRankTildeE X Z Y) G
      ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G)
      (reducedRankChat Z X Y G
        ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G))
      ((Fintype.card n : ℝ)⁻¹ •
        ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeY Z Y) -
          ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G) *
            ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G)ᵀ))
      Aperp lambda eta (reducedRankMaximizedLogLikelihood (reducedRankTildeY Z Y) lambda) :=
  reducedRankHansenTheorem11_7_exactDimension_of_detProductMinMax_diagonalDual_compressedDet_ne_zero_canonicalAperp
    Z X (reducedRankTildeX Z X) Y (reducedRankTildeY Z Y) (reducedRankTildeE X Z Y)
    G lambda Aperp eta hMinMax W hGdet hDual hOrth

set_option linter.style.longLine false in
/-- Residualized determinant/product min-max endpoint with Hansen's diagonal
dual relation, positive selected `G` roots, and canonical `A⊥` index.

This specializes
`reducedRankHansenTheorem11_7_exactDimension_of_detProductMinMax_diagonalDual_pos_canonicalAperp`
to `X̃ = M_ZX`, `Ỹ = M_ZY`, and `Ẽ = M_[X,Z]Y`. -/
theorem
    reducedRankHansenTheorem11_7_residualized_exactDimension_of_detProductMinMax_diagonalDual_pos_canonicalAperp
    (Z : Matrix n ell ℝ) (X : Matrix n k ℝ) (Y : Matrix n m ℝ)
    [DecidableEq k]
    [Invertible (Zᵀ * Z)]
    [Invertible ((Matrix.fromCols X Z)ᵀ * Matrix.fromCols X Z)]
    (G : Matrix k r ℝ) (lambda : r → ℝ)
    (Aperp : Matrix m (reducedRankAperpIndex m r) ℝ)
    (eta : reducedRankAperpIndex m r → ℝ)
    (hMinMax : ReducedRankHansenDetProductMinMaxCertificate
      (reducedRankTildeX Z X) (reducedRankTildeY Z Y) (reducedRankTildeE X Z Y)
      G lambda Aperp eta)
    (W : Matrix m r ℝ)
    (hLambda : ∀ j, 0 < lambda j)
    (hDual : reducedRankDualEigenvectorRelation
      (reducedRankTildeX Z X) (reducedRankTildeY Z Y) G W (Matrix.diagonal lambda))
    (hOrth : reducedRankAperpYOrthogonal (reducedRankTildeY Z Y) Aperp W) :
    ReducedRankHansenSmallestSummaryCompatibilityExactDimension
      Z X (reducedRankTildeX Z X) Y (reducedRankTildeY Z Y) (reducedRankTildeE X Z Y) G
      ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G)
      (reducedRankChat Z X Y G
        ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G))
      ((Fintype.card n : ℝ)⁻¹ •
        ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeY Z Y) -
          ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G) *
            ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G)ᵀ))
      Aperp lambda eta (reducedRankMaximizedLogLikelihood (reducedRankTildeY Z Y) lambda) :=
  reducedRankHansenTheorem11_7_exactDimension_of_detProductMinMax_diagonalDual_pos_canonicalAperp
    Z X (reducedRankTildeX Z X) Y (reducedRankTildeY Z Y) (reducedRankTildeE X Z Y)
    G lambda Aperp eta hMinMax W hLambda hDual hOrth

set_option linter.style.longLine false in
/-- Residualized Hansen Theorem 11.7 from a whitened PSD leading/trailing
certificate, Hansen's displayed diagonal dual relation, a nonzero selected
compressed determinant, and the canonical `A⊥` index.

This is the compressed-determinant sibling of
`reducedRankHansenTheorem11_7_residualized_exactDimension_of_whitened_psd_leading_trailing_diagonalDual_pos_canonicalAperp`.
It avoids strengthening the theorem boundary to positive selected `G` roots
when the caller already has Hansen's nonzero selected compressed determinant. -/
theorem
    reducedRankHansenTheorem11_7_residualized_exactDimension_of_whitened_psd_leading_trailing_diagonalDual_compressedDet_ne_zero_canonicalAperp
    (Z : Matrix n ell ℝ) (X : Matrix n k ℝ) (Y : Matrix n m ℝ)
    [DecidableEq k]
    [Invertible (Zᵀ * Z)]
    [Invertible ((Matrix.fromCols X Z)ᵀ * Matrix.fromCols X Z)]
    (G : Matrix k r ℝ) (lambda : r → ℝ)
    (Aperp : Matrix m (reducedRankAperpIndex m r) ℝ)
    (eta : reducedRankAperpIndex m r → ℝ)
    (G0 : Matrix n r ℝ) (A0 : Matrix n (reducedRankAperpIndex m r) ℝ)
    (hG : reducedRankHansenGEigenvectors
      (reducedRankTildeX Z X) (reducedRankTildeY Z Y) lambda G)
    (hGNorm : reducedRankGNormalized (reducedRankTildeX Z X) G)
    (hAperp : reducedRankHansenAperpEigenvectors
      (reducedRankTildeE X Z Y) (reducedRankTildeY Z Y) eta Aperp)
    (hAperpNorm : reducedRankAperpNormalized (reducedRankTildeY Z Y) Aperp)
    (hWhite : ReducedRankHansenWhitenedPSDLeadingTrailingCertificate
      (reducedRankTildeY Z Y) (reducedRankTildeE X Z Y) lambda eta
      (reducedRankAperpResidualFactor X Z) G0 A0)
    (W : Matrix m r ℝ)
    (hGdet :
      (Gᵀ *
        reducedRankGPencilA (reducedRankTildeX Z X) (reducedRankTildeY Z Y) *
          G).det ≠ 0)
    (hDual : reducedRankDualEigenvectorRelation
      (reducedRankTildeX Z X) (reducedRankTildeY Z Y) G W (Matrix.diagonal lambda))
    (hOrth : reducedRankAperpYOrthogonal (reducedRankTildeY Z Y) Aperp W) :
    ReducedRankHansenSmallestSummaryCompatibilityExactDimension
      Z X (reducedRankTildeX Z X) Y (reducedRankTildeY Z Y) (reducedRankTildeE X Z Y) G
      ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G)
      (reducedRankChat Z X Y G
        ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G))
      ((Fintype.card n : ℝ)⁻¹ •
        ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeY Z Y) -
          ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G) *
            ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G)ᵀ))
      Aperp lambda eta (reducedRankMaximizedLogLikelihood (reducedRankTildeY Z Y) lambda) :=
  reducedRankHansenTheorem11_7_residualized_exactDimension_of_detProductMinMax_diagonalDual_compressedDet_ne_zero_canonicalAperp
    Z X Y G lambda Aperp eta
    (ReducedRankHansenDetProductMinMaxCertificate.of_whitened_psd_leading_trailing
      (reducedRankTildeX Z X) (reducedRankTildeY Z Y) (reducedRankTildeE X Z Y)
      G lambda Aperp eta (reducedRankAperpResidualFactor X Z) G0 A0
      hG hGNorm hAperp hAperpNorm hWhite)
    W hGdet hDual hOrth

set_option linter.style.longLine false in
/-- Residualized Hansen Theorem 11.7 from a whitened PSD leading/trailing
certificate, Hansen's displayed diagonal dual relation, positive selected `G`
roots, and the canonical `A⊥` index.

This is a theorem-facing wrapper over the existing min-max bridge: the
whitened certificate supplies the ordinary determinant extrema after
residualization, `ReducedRankHansenDetProductMinMaxCertificate` transports
them to Hansen's two generalized pencils, and the canonical endpoint supplies
the exact `dim(A⊥)=m-r` conclusion. -/
theorem
    reducedRankHansenTheorem11_7_residualized_exactDimension_of_whitened_psd_leading_trailing_diagonalDual_pos_canonicalAperp
    (Z : Matrix n ell ℝ) (X : Matrix n k ℝ) (Y : Matrix n m ℝ)
    [DecidableEq k]
    [Invertible (Zᵀ * Z)]
    [Invertible ((Matrix.fromCols X Z)ᵀ * Matrix.fromCols X Z)]
    (G : Matrix k r ℝ) (lambda : r → ℝ)
    (Aperp : Matrix m (reducedRankAperpIndex m r) ℝ)
    (eta : reducedRankAperpIndex m r → ℝ)
    (G0 : Matrix n r ℝ) (A0 : Matrix n (reducedRankAperpIndex m r) ℝ)
    (hG : reducedRankHansenGEigenvectors
      (reducedRankTildeX Z X) (reducedRankTildeY Z Y) lambda G)
    (hGNorm : reducedRankGNormalized (reducedRankTildeX Z X) G)
    (hAperp : reducedRankHansenAperpEigenvectors
      (reducedRankTildeE X Z Y) (reducedRankTildeY Z Y) eta Aperp)
    (hAperpNorm : reducedRankAperpNormalized (reducedRankTildeY Z Y) Aperp)
    (hWhite : ReducedRankHansenWhitenedPSDLeadingTrailingCertificate
      (reducedRankTildeY Z Y) (reducedRankTildeE X Z Y) lambda eta
      (reducedRankAperpResidualFactor X Z) G0 A0)
    (W : Matrix m r ℝ)
    (hLambda : ∀ j, 0 < lambda j)
    (hDual : reducedRankDualEigenvectorRelation
      (reducedRankTildeX Z X) (reducedRankTildeY Z Y) G W (Matrix.diagonal lambda))
    (hOrth : reducedRankAperpYOrthogonal (reducedRankTildeY Z Y) Aperp W) :
    ReducedRankHansenSmallestSummaryCompatibilityExactDimension
      Z X (reducedRankTildeX Z X) Y (reducedRankTildeY Z Y) (reducedRankTildeE X Z Y) G
      ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G)
      (reducedRankChat Z X Y G
        ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G))
      ((Fintype.card n : ℝ)⁻¹ •
        ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeY Z Y) -
          ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G) *
            ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G)ᵀ))
      Aperp lambda eta (reducedRankMaximizedLogLikelihood (reducedRankTildeY Z Y) lambda) :=
  reducedRankHansenTheorem11_7_residualized_exactDimension_of_detProductMinMax_diagonalDual_pos_canonicalAperp
    Z X Y G lambda Aperp eta
    (ReducedRankHansenDetProductMinMaxCertificate.of_whitened_psd_leading_trailing
      (reducedRankTildeX Z X) (reducedRankTildeY Z Y) (reducedRankTildeE X Z Y)
      G lambda Aperp eta (reducedRankAperpResidualFactor X Z) G0 A0
      hG hGNorm hAperp hAperpNorm hWhite)
    W hLambda hDual hOrth

/-- Fixed-root projection/span/nullspace algebraic certificate package.

This is a singular-boundary route, not a finite normal MLE construction. It
records the exact ordinary witnesses used by the projection-specialized
fixed-root algebra:
`X̃G = ỸC` gives the selected top-root block, `ẼA⊥ = 0` gives the residual
null block, and `A⊥'Ỹ'ỸC = 0` is the remaining dual orthogonality. Its public
endpoints below return only determinant/product or identified spectral
certificates; they do not return `ReducedRankMLE` or
`ReducedRankHansenTheorem11_7`. -/
structure ReducedRankHansenProjectionSpanNullConditions
    (Z : Matrix n ell ℝ) (X : Matrix n k ℝ) (Y : Matrix n m ℝ)
    [DecidableEq k]
    [Invertible (Zᵀ * Z)]
    [Invertible ((Matrix.fromCols X Z)ᵀ * Matrix.fromCols X Z)]
    (G : Matrix k r ℝ) (Aperp : Matrix m (reducedRankAperpIndex m r) ℝ)
    (C : Matrix m r ℝ) : Prop where
  g_normalized : reducedRankGNormalized (reducedRankTildeX Z X) G
  g_span : reducedRankTildeX Z X * G = reducedRankTildeY Z Y * C
  aperp_normalized : reducedRankAperpNormalized (reducedRankTildeY Z Y) Aperp
  tildeE_null : reducedRankTildeE X Z Y * Aperp = 0
  aperp_span_orthogonal :
    reducedRankAperpYOrthogonal (reducedRankTildeY Z Y) Aperp C

namespace ReducedRankHansenProjectionSpanNullConditions

omit [DecidableEq m] in
/-- Constructor for the fixed-root projection/span/nullspace package from
Hansen's displayed cross-orthogonality `A⊥'Ỹ'X̃G = 0`.

The package stores the equivalent `A⊥'Ỹ'ỸC = 0` form because the downstream
diagonal-dual route uses `W = C`; the span equation `X̃G = ỸC` performs the
translation. -/
theorem of_crossOrthogonal
    (Z : Matrix n ell ℝ) (X : Matrix n k ℝ) (Y : Matrix n m ℝ)
    [DecidableEq k]
    [Invertible (Zᵀ * Z)]
    [Invertible ((Matrix.fromCols X Z)ᵀ * Matrix.fromCols X Z)]
    (G : Matrix k r ℝ) (Aperp : Matrix m (reducedRankAperpIndex m r) ℝ)
    (C : Matrix m r ℝ)
    (hGNorm : reducedRankGNormalized (reducedRankTildeX Z X) G)
    (hGSpan : reducedRankTildeX Z X * G = reducedRankTildeY Z Y * C)
    (hAperpNorm : reducedRankAperpNormalized (reducedRankTildeY Z Y) Aperp)
    (hTildeENull : reducedRankTildeE X Z Y * Aperp = 0)
    (hCross : reducedRankAperpCrossOrthogonal
      (reducedRankTildeX Z X) (reducedRankTildeY Z Y) G Aperp) :
    ReducedRankHansenProjectionSpanNullConditions Z X Y G Aperp C where
  g_normalized := hGNorm
  g_span := hGSpan
  aperp_normalized := hAperpNorm
  tildeE_null := hTildeENull
  aperp_span_orthogonal :=
    (reducedRankAperpYOrthogonal_iff_crossOrthogonal_of_span
      (reducedRankTildeX Z X) (reducedRankTildeY Z Y) G Aperp C
      hGSpan).2 hCross

set_option linter.style.longLine false in
/-- Convert the fixed-root projection/span/nullspace package into the reusable
determinant/product max/min compatibility certificate.

This is an API bridge over the already-proved projection-specialized route: it
constructs the ordinary selected blocks `G₀ = X̃G = ỸC` and `A₀ = ỸA⊥`, then
reuses
`ReducedRankHansenDetProductMinMaxCertificate.of_residualized_projection_span_residual_null`.
It is algebraic support only and does not supply the canonical max/max MLE
certificate. -/
theorem to_detProductMinMaxCertificate
    (Z : Matrix n ell ℝ) (X : Matrix n k ℝ) (Y : Matrix n m ℝ)
    [DecidableEq k]
    [Invertible (Zᵀ * Z)]
    [Invertible ((Matrix.fromCols X Z)ᵀ * Matrix.fromCols X Z)]
    [Invertible ((reducedRankTildeY Z Y)ᵀ * reducedRankTildeY Z Y)]
    [Nonempty (reducedRankAperpIndex m r)]
    (G : Matrix k r ℝ)
    (Aperp : Matrix m (reducedRankAperpIndex m r) ℝ)
    (C : Matrix m r ℝ)
    (h : ReducedRankHansenProjectionSpanNullConditions Z X Y G Aperp C) :
    ReducedRankHansenDetProductMinMaxCertificate
      (reducedRankTildeX Z X) (reducedRankTildeY Z Y) (reducedRankTildeE X Z Y)
      G (fun _ : r => (1 : ℝ)) Aperp
      (fun _ : reducedRankAperpIndex m r => (0 : ℝ)) := by
  let G0 : Matrix n r ℝ := reducedRankTildeX Z X * G
  let A0 : Matrix n (reducedRankAperpIndex m r) ℝ := reducedRankTildeY Z Y * Aperp
  have hGImageRange :
      reducedRankGWhitenedProjection (reducedRankTildeY Z Y) *
        (reducedRankTildeX Z X * G) =
          reducedRankTildeX Z X * G :=
    reducedRankGWhitenedProjection_image_range_of_span
      (reducedRankTildeX Z X) (reducedRankTildeY Z Y) G C h.g_span
  have hAperpImageNull :
      reducedRankAperpResidualFactor X Z *
        (reducedRankTildeY Z Y * Aperp) = 0 :=
    reducedRankAperpResidualFactor_image_null_of_tildeE_null
      Z X Y Aperp h.tildeE_null
  have hG :
      reducedRankHansenGEigenvectors
        (reducedRankTildeX Z X) (reducedRankTildeY Z Y) (fun _ : r => (1 : ℝ)) G :=
    reducedRankHansenGEigenvectors_one_of_whitened_projection_image_range
      (reducedRankTildeX Z X) (reducedRankTildeY Z Y) G h.g_normalized hGImageRange
  have hAperp :
      reducedRankHansenAperpEigenvectors
        (reducedRankTildeE X Z Y) (reducedRankTildeY Z Y)
        (fun _ : reducedRankAperpIndex m r => (0 : ℝ)) Aperp :=
    reducedRankHansenAperpEigenvectors_zero_of_residualized_image_null
      Z X Y Aperp h.aperp_normalized hAperpImageNull
  have hG0Span : G0 = reducedRankTildeY Z Y * C := by
    simpa [G0] using h.g_span
  have hG0Norm : G0ᵀ * G0 = (1 : Matrix r r ℝ) := by
    simpa [G0] using reducedRankG_image_orthonormal_of_normalized
      (reducedRankTildeX Z X) G h.g_normalized
  have hA0Norm :
      A0ᵀ * A0 =
        (1 : Matrix (reducedRankAperpIndex m r) (reducedRankAperpIndex m r) ℝ) := by
    simpa [A0] using reducedRankAperp_image_orthonormal_of_normalized
      (reducedRankTildeY Z Y) Aperp h.aperp_normalized
  have hA0ResidualNull : reducedRankAperpResidualFactor X Z * A0 = 0 := by
    simpa [A0] using hAperpImageNull
  exact
    ReducedRankHansenDetProductMinMaxCertificate.of_residualized_projection_span_residual_null
      Z X Y G Aperp G0 A0 C
      hG h.g_normalized hAperp h.aperp_normalized
      hG0Span hG0Norm hA0Norm hA0ResidualNull

set_option linter.style.longLine false in
/-- Rank-inequality facade for
`ReducedRankHansenProjectionSpanNullConditions.to_detProductMinMaxCertificate`.

The fixed-root package uses the canonical `Fin (m-r)` complement. Hansen's
strict rank inequality supplies the required nonempty complement index. -/
theorem to_detProductMinMaxCertificate_of_rank_lt
    (Z : Matrix n ell ℝ) (X : Matrix n k ℝ) (Y : Matrix n m ℝ)
    [DecidableEq k]
    [Invertible (Zᵀ * Z)]
    [Invertible ((Matrix.fromCols X Z)ᵀ * Matrix.fromCols X Z)]
    [Invertible ((reducedRankTildeY Z Y)ᵀ * reducedRankTildeY Z Y)]
    (hrank : Fintype.card r < Fintype.card m)
    (G : Matrix k r ℝ)
    (Aperp : Matrix m (reducedRankAperpIndex m r) ℝ)
    (C : Matrix m r ℝ)
    (h : ReducedRankHansenProjectionSpanNullConditions Z X Y G Aperp C) :
    ReducedRankHansenDetProductMinMaxCertificate
      (reducedRankTildeX Z X) (reducedRankTildeY Z Y) (reducedRankTildeE X Z Y)
      G (fun _ : r => (1 : ℝ)) Aperp
      (fun _ : reducedRankAperpIndex m r => (0 : ℝ)) := by
  letI : Nonempty (reducedRankAperpIndex m r) :=
    reducedRankAperpIndex_nonempty_of_card_lt (m := m) (r := r) hrank
  exact h.to_detProductMinMaxCertificate Z X Y G Aperp C

set_option linter.style.longLine false in
/-- Convert the fixed-root projection/span/nullspace package into the reusable
identified max/min compatibility certificate, retaining Hansen's explicit
cross-orthogonality `A⊥'Ỹ'X̃G = 0`. This remains an algebraic singular-boundary
result, not the canonical max/max MLE certificate. -/
theorem to_identifiedSpectralDualityCertificate
    (Z : Matrix n ell ℝ) (X : Matrix n k ℝ) (Y : Matrix n m ℝ)
    [DecidableEq k]
    [Invertible (Zᵀ * Z)]
    [Invertible ((Matrix.fromCols X Z)ᵀ * Matrix.fromCols X Z)]
    [Invertible ((reducedRankTildeY Z Y)ᵀ * reducedRankTildeY Z Y)]
    [Nonempty (reducedRankAperpIndex m r)]
    (G : Matrix k r ℝ)
    (Aperp : Matrix m (reducedRankAperpIndex m r) ℝ)
    (C : Matrix m r ℝ)
    (h : ReducedRankHansenProjectionSpanNullConditions Z X Y G Aperp C) :
    ReducedRankHansenIdentifiedSpectralDualityCertificate
      (reducedRankTildeX Z X) (reducedRankTildeY Z Y) (reducedRankTildeE X Z Y)
      G (fun _ : r => (1 : ℝ)) Aperp
      (fun _ : reducedRankAperpIndex m r => (0 : ℝ)) :=
  ReducedRankHansenIdentifiedSpectralDualityCertificate.of_detProductMinMax_and_cross
    (h.to_detProductMinMaxCertificate Z X Y G Aperp C)
    ((reducedRankAperpYOrthogonal_iff_crossOrthogonal_of_span
      (reducedRankTildeX Z X) (reducedRankTildeY Z Y) G Aperp C h.g_span).1
        h.aperp_span_orthogonal)

set_option linter.style.longLine false in
/-- Rank-inequality facade for
`ReducedRankHansenProjectionSpanNullConditions.to_identifiedSpectralDualityCertificate`. -/
theorem to_identifiedSpectralDualityCertificate_of_rank_lt
    (Z : Matrix n ell ℝ) (X : Matrix n k ℝ) (Y : Matrix n m ℝ)
    [DecidableEq k]
    [Invertible (Zᵀ * Z)]
    [Invertible ((Matrix.fromCols X Z)ᵀ * Matrix.fromCols X Z)]
    [Invertible ((reducedRankTildeY Z Y)ᵀ * reducedRankTildeY Z Y)]
    (hrank : Fintype.card r < Fintype.card m)
    (G : Matrix k r ℝ)
    (Aperp : Matrix m (reducedRankAperpIndex m r) ℝ)
    (C : Matrix m r ℝ)
    (h : ReducedRankHansenProjectionSpanNullConditions Z X Y G Aperp C) :
    ReducedRankHansenIdentifiedSpectralDualityCertificate
      (reducedRankTildeX Z X) (reducedRankTildeY Z Y) (reducedRankTildeE X Z Y)
      G (fun _ : r => (1 : ℝ)) Aperp
      (fun _ : reducedRankAperpIndex m r => (0 : ℝ)) := by
  letI : Nonempty (reducedRankAperpIndex m r) :=
    reducedRankAperpIndex_nonempty_of_card_lt (m := m) (r := r) hrank
  exact h.to_identifiedSpectralDualityCertificate Z X Y G Aperp C

end ReducedRankHansenProjectionSpanNullConditions

/-- Residualized Hansen Theorem 11.7 from the literal determinant/product
variational bounds, the displayed dual relation, and the exact
`dim(A⊥) = m-r` condition. -/
theorem
    reducedRankHansenTheorem11_7_residualized_exactDimension_of_product_bounds_and_dual_relation
    (Z : Matrix n ell ℝ) (X : Matrix n k ℝ) (Y : Matrix n m ℝ)
    [DecidableEq k]
    [Invertible (Zᵀ * Z)]
    [Invertible ((Matrix.fromCols X Z)ᵀ * Matrix.fromCols X Z)]
    (G : Matrix k r ℝ) (lambda : r → ℝ)
    (Aperp : Matrix m s ℝ) (eta : s → ℝ)
    (hG : reducedRankHansenGEigenvectors
      (reducedRankTildeX Z X) (reducedRankTildeY Z Y) lambda G)
    (hGNorm : reducedRankGNormalized (reducedRankTildeX Z X) G)
    (hGBound :
      reducedRankGDetVariationalBound (reducedRankTildeX Z X) (reducedRankTildeY Z Y)
        lambda)
    (hAperp : reducedRankHansenAperpEigenvectors
      (reducedRankTildeE X Z Y) (reducedRankTildeY Z Y) eta Aperp)
    (hAperpNorm : reducedRankAperpNormalized (reducedRankTildeY Z Y) Aperp)
    (hAperpBound :
      reducedRankAperpDetVariationalBound (reducedRankTildeE X Z Y)
        (reducedRankTildeY Z Y) eta)
    (W : Matrix m r ℝ) (Lambda LambdaInv : Matrix r r ℝ)
    (hDual : reducedRankDualEigenvectorRelation
      (reducedRankTildeX Z X) (reducedRankTildeY Z Y) G W Lambda)
    (hOrth : reducedRankAperpYOrthogonal (reducedRankTildeY Z Y) Aperp W)
    (hLambdaInv : Lambda * LambdaInv = 1)
    (hdim : Fintype.card s = Fintype.card m - Fintype.card r) :
    ReducedRankHansenSmallestSummaryCompatibilityExactDimension
      Z X (reducedRankTildeX Z X) Y (reducedRankTildeY Z Y) (reducedRankTildeE X Z Y) G
      ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G)
      (reducedRankChat Z X Y G
        ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G))
      ((Fintype.card n : ℝ)⁻¹ •
        ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeY Z Y) -
          ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G) *
            ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G)ᵀ))
      Aperp lambda eta (reducedRankMaximizedLogLikelihood (reducedRankTildeY Z Y) lambda) :=
  reducedRankHansenTheorem11_7_exactDimension_of_product_bounds_and_dual_relation
    Z X (reducedRankTildeX Z X) Y (reducedRankTildeY Z Y) (reducedRankTildeE X Z Y)
    G lambda Aperp eta
    hG hGNorm hGBound hAperp hAperpNorm hAperpBound
    W Lambda LambdaInv hDual hOrth hLambdaInv hdim

/-- Residualized Hansen Theorem 11.7 from literal determinant/product
variational bounds and Hansen's displayed diagonal selected-root dual
relation.

This is the residualized Hansen-notation counterpart of
`reducedRankHansenTheorem11_7_exactDimension_of_product_bounds_diagonalDual`.
-/
theorem
    reducedRankHansenTheorem11_7_residualized_exactDimension_of_product_bounds_diagonalDual
    (Z : Matrix n ell ℝ) (X : Matrix n k ℝ) (Y : Matrix n m ℝ)
    [DecidableEq k]
    [Invertible (Zᵀ * Z)]
    [Invertible ((Matrix.fromCols X Z)ᵀ * Matrix.fromCols X Z)]
    (G : Matrix k r ℝ) (lambda : r → ℝ)
    (Aperp : Matrix m s ℝ) (eta : s → ℝ)
    (hG : reducedRankHansenGEigenvectors
      (reducedRankTildeX Z X) (reducedRankTildeY Z Y) lambda G)
    (hGNorm : reducedRankGNormalized (reducedRankTildeX Z X) G)
    (hGBound :
      reducedRankGDetVariationalBound (reducedRankTildeX Z X) (reducedRankTildeY Z Y)
        lambda)
    (hAperp : reducedRankHansenAperpEigenvectors
      (reducedRankTildeE X Z Y) (reducedRankTildeY Z Y) eta Aperp)
    (hAperpNorm : reducedRankAperpNormalized (reducedRankTildeY Z Y) Aperp)
    (hAperpBound :
      reducedRankAperpDetVariationalBound (reducedRankTildeE X Z Y)
        (reducedRankTildeY Z Y) eta)
    (W : Matrix m r ℝ)
    (hLambda : ∀ j, lambda j ≠ 0)
    (hDual : reducedRankDualEigenvectorRelation
      (reducedRankTildeX Z X) (reducedRankTildeY Z Y) G W (Matrix.diagonal lambda))
    (hOrth : reducedRankAperpYOrthogonal (reducedRankTildeY Z Y) Aperp W)
    (hdim : Fintype.card s = Fintype.card m - Fintype.card r) :
    ReducedRankHansenSmallestSummaryCompatibilityExactDimension
      Z X (reducedRankTildeX Z X) Y (reducedRankTildeY Z Y) (reducedRankTildeE X Z Y) G
      ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G)
      (reducedRankChat Z X Y G
        ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G))
      ((Fintype.card n : ℝ)⁻¹ •
        ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeY Z Y) -
          ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G) *
            ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G)ᵀ))
      Aperp lambda eta (reducedRankMaximizedLogLikelihood (reducedRankTildeY Z Y) lambda) :=
  reducedRankHansenTheorem11_7_exactDimension_of_product_bounds_diagonalDual
    Z X (reducedRankTildeX Z X) Y (reducedRankTildeY Z Y) (reducedRankTildeE X Z Y)
    G lambda Aperp eta
    hG hGNorm hGBound hAperp hAperpNorm hAperpBound
    W hLambda hDual hOrth hdim

set_option linter.style.longLine false in
/-- Residualized product-nonzero and index-split version of
`reducedRankHansenTheorem11_7_residualized_exactDimension_of_product_bounds_diagonalDual`.

This is the direct residualized endpoint for a raw spectral theorem stated in
Hansen's literal determinant/product notation, with selected-root product
nonsingularity and a concrete `m ≃ r ⊕ s` split. -/
theorem
    reducedRankHansenTheorem11_7_residualized_exactDimension_of_product_bounds_diagonalDual_prod_ne_zero_indexSplit
    (Z : Matrix n ell ℝ) (X : Matrix n k ℝ) (Y : Matrix n m ℝ)
    [DecidableEq k]
    [Invertible (Zᵀ * Z)]
    [Invertible ((Matrix.fromCols X Z)ᵀ * Matrix.fromCols X Z)]
    (G : Matrix k r ℝ) (lambda : r → ℝ)
    (Aperp : Matrix m s ℝ) (eta : s → ℝ)
    (hG : reducedRankHansenGEigenvectors
      (reducedRankTildeX Z X) (reducedRankTildeY Z Y) lambda G)
    (hGNorm : reducedRankGNormalized (reducedRankTildeX Z X) G)
    (hGBound :
      reducedRankGDetVariationalBound (reducedRankTildeX Z X) (reducedRankTildeY Z Y)
        lambda)
    (hAperp : reducedRankHansenAperpEigenvectors
      (reducedRankTildeE X Z Y) (reducedRankTildeY Z Y) eta Aperp)
    (hAperpNorm : reducedRankAperpNormalized (reducedRankTildeY Z Y) Aperp)
    (hAperpBound :
      reducedRankAperpDetVariationalBound (reducedRankTildeE X Z Y)
        (reducedRankTildeY Z Y) eta)
    (W : Matrix m r ℝ)
    (hLambdaProd : (∏ j, lambda j) ≠ 0)
    (hDual : reducedRankDualEigenvectorRelation
      (reducedRankTildeX Z X) (reducedRankTildeY Z Y) G W (Matrix.diagonal lambda))
    (hOrth : reducedRankAperpYOrthogonal (reducedRankTildeY Z Y) Aperp W)
    (hIndex : m ≃ Sum r s) :
    ReducedRankHansenSmallestSummaryCompatibilityExactDimension
      Z X (reducedRankTildeX Z X) Y (reducedRankTildeY Z Y) (reducedRankTildeE X Z Y) G
      ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G)
      (reducedRankChat Z X Y G
        ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G))
      ((Fintype.card n : ℝ)⁻¹ •
        ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeY Z Y) -
          ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G) *
            ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G)ᵀ))
      Aperp lambda eta (reducedRankMaximizedLogLikelihood (reducedRankTildeY Z Y) lambda) :=
  reducedRankHansenTheorem11_7_residualized_exactDimension_of_product_bounds_diagonalDual
    Z X Y G lambda Aperp eta
    hG hGNorm hGBound hAperp hAperpNorm hAperpBound W
    (reducedRankSelectedRoots_nonzero_of_prod_ne_zero lambda hLambdaProd)
    hDual hOrth
    (reducedRankAperpDimension_of_equiv_sum (m := m) (r := r) (s := s) hIndex)

set_option linter.style.longLine false in
/-- Residualized compressed-determinant and index-split version of
`reducedRankHansenTheorem11_7_residualized_exactDimension_of_product_bounds_diagonalDual`.

This is the literal Hansen product-bound route for the residualized matrices
when selected-root nonsingularity is supplied as `det(G'AG) ≠ 0`. -/
theorem
    reducedRankHansenTheorem11_7_residualized_exactDimension_of_product_bounds_diagonalDual_compressedDet_ne_zero_indexSplit
    (Z : Matrix n ell ℝ) (X : Matrix n k ℝ) (Y : Matrix n m ℝ)
    [DecidableEq k]
    [Invertible (Zᵀ * Z)]
    [Invertible ((Matrix.fromCols X Z)ᵀ * Matrix.fromCols X Z)]
    (G : Matrix k r ℝ) (lambda : r → ℝ)
    (Aperp : Matrix m s ℝ) (eta : s → ℝ)
    (hG : reducedRankHansenGEigenvectors
      (reducedRankTildeX Z X) (reducedRankTildeY Z Y) lambda G)
    (hGNorm : reducedRankGNormalized (reducedRankTildeX Z X) G)
    (hGBound :
      reducedRankGDetVariationalBound (reducedRankTildeX Z X) (reducedRankTildeY Z Y)
        lambda)
    (hAperp : reducedRankHansenAperpEigenvectors
      (reducedRankTildeE X Z Y) (reducedRankTildeY Z Y) eta Aperp)
    (hAperpNorm : reducedRankAperpNormalized (reducedRankTildeY Z Y) Aperp)
    (hAperpBound :
      reducedRankAperpDetVariationalBound (reducedRankTildeE X Z Y)
        (reducedRankTildeY Z Y) eta)
    (W : Matrix m r ℝ)
    (hGdet :
      (Gᵀ * reducedRankGPencilA (reducedRankTildeX Z X) (reducedRankTildeY Z Y) * G).det ≠
        0)
    (hDual : reducedRankDualEigenvectorRelation
      (reducedRankTildeX Z X) (reducedRankTildeY Z Y) G W (Matrix.diagonal lambda))
    (hOrth : reducedRankAperpYOrthogonal (reducedRankTildeY Z Y) Aperp W)
    (hIndex : m ≃ Sum r s) :
    ReducedRankHansenSmallestSummaryCompatibilityExactDimension
      Z X (reducedRankTildeX Z X) Y (reducedRankTildeY Z Y) (reducedRankTildeE X Z Y) G
      ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G)
      (reducedRankChat Z X Y G
        ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G))
      ((Fintype.card n : ℝ)⁻¹ •
        ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeY Z Y) -
          ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G) *
            ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G)ᵀ))
      Aperp lambda eta (reducedRankMaximizedLogLikelihood (reducedRankTildeY Z Y) lambda) :=
  reducedRankHansenTheorem11_7_residualized_exactDimension_of_product_bounds_diagonalDual_prod_ne_zero_indexSplit
    Z X Y G lambda Aperp eta
    hG hGNorm hGBound hAperp hAperpNorm hAperpBound W
    (generalizedEigenSelectedRootProduct_ne_zero_of_compressedDet_ne_zero
      (reducedRankGPencilA (reducedRankTildeX Z X) (reducedRankTildeY Z Y))
      (reducedRankGPencilB (reducedRankTildeX Z X))
      lambda G hG hGNorm hGdet)
    hDual hOrth hIndex

set_option linter.style.longLine false in
/-- Residualized canonical-`A⊥` product-bound endpoint with selected-root
product nonsingularity.

This specializes
`reducedRankHansenTheorem11_7_exactDimension_of_product_bounds_diagonalDual_prod_ne_zero_canonicalAperp`
to `X̃ = M_ZX`, `Ỹ = M_ZY`, and `Ẽ = M_[X,Z]Y`. -/
theorem
    reducedRankHansenTheorem11_7_residualized_exactDimension_of_product_bounds_diagonalDual_prod_ne_zero_canonicalAperp
    (Z : Matrix n ell ℝ) (X : Matrix n k ℝ) (Y : Matrix n m ℝ)
    [DecidableEq k]
    [Invertible (Zᵀ * Z)]
    [Invertible ((Matrix.fromCols X Z)ᵀ * Matrix.fromCols X Z)]
    (G : Matrix k r ℝ) (lambda : r → ℝ)
    (Aperp : Matrix m (reducedRankAperpIndex m r) ℝ)
    (eta : reducedRankAperpIndex m r → ℝ)
    (hG : reducedRankHansenGEigenvectors
      (reducedRankTildeX Z X) (reducedRankTildeY Z Y) lambda G)
    (hGNorm : reducedRankGNormalized (reducedRankTildeX Z X) G)
    (hGBound :
      reducedRankGDetVariationalBound (reducedRankTildeX Z X) (reducedRankTildeY Z Y)
        lambda)
    (hAperp : reducedRankHansenAperpEigenvectors
      (reducedRankTildeE X Z Y) (reducedRankTildeY Z Y) eta Aperp)
    (hAperpNorm : reducedRankAperpNormalized (reducedRankTildeY Z Y) Aperp)
    (hAperpBound :
      reducedRankAperpDetVariationalBound (reducedRankTildeE X Z Y)
        (reducedRankTildeY Z Y) eta)
    (W : Matrix m r ℝ)
    (hLambdaProd : (∏ j, lambda j) ≠ 0)
    (hDual : reducedRankDualEigenvectorRelation
      (reducedRankTildeX Z X) (reducedRankTildeY Z Y) G W (Matrix.diagonal lambda))
    (hOrth : reducedRankAperpYOrthogonal (reducedRankTildeY Z Y) Aperp W) :
    ReducedRankHansenSmallestSummaryCompatibilityExactDimension
      Z X (reducedRankTildeX Z X) Y (reducedRankTildeY Z Y) (reducedRankTildeE X Z Y) G
      ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G)
      (reducedRankChat Z X Y G
        ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G))
      ((Fintype.card n : ℝ)⁻¹ •
        ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeY Z Y) -
          ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G) *
            ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G)ᵀ))
      Aperp lambda eta (reducedRankMaximizedLogLikelihood (reducedRankTildeY Z Y) lambda) :=
  reducedRankHansenTheorem11_7_exactDimension_of_product_bounds_diagonalDual_prod_ne_zero_canonicalAperp
    Z X (reducedRankTildeX Z X) Y (reducedRankTildeY Z Y) (reducedRankTildeE X Z Y)
    G lambda Aperp eta
    hG hGNorm hGBound hAperp hAperpNorm hAperpBound W
    hLambdaProd hDual hOrth

set_option linter.style.longLine false in
/-- Residualized canonical-`A⊥` product-bound endpoint where selected-root
nonsingularity is derived from the nonzero selected compressed determinant. -/
theorem
    reducedRankHansenTheorem11_7_residualized_exactDimension_of_product_bounds_diagonalDual_compressedDet_ne_zero_canonicalAperp
    (Z : Matrix n ell ℝ) (X : Matrix n k ℝ) (Y : Matrix n m ℝ)
    [DecidableEq k]
    [Invertible (Zᵀ * Z)]
    [Invertible ((Matrix.fromCols X Z)ᵀ * Matrix.fromCols X Z)]
    (G : Matrix k r ℝ) (lambda : r → ℝ)
    (Aperp : Matrix m (reducedRankAperpIndex m r) ℝ)
    (eta : reducedRankAperpIndex m r → ℝ)
    (hG : reducedRankHansenGEigenvectors
      (reducedRankTildeX Z X) (reducedRankTildeY Z Y) lambda G)
    (hGNorm : reducedRankGNormalized (reducedRankTildeX Z X) G)
    (hGBound :
      reducedRankGDetVariationalBound (reducedRankTildeX Z X) (reducedRankTildeY Z Y)
        lambda)
    (hAperp : reducedRankHansenAperpEigenvectors
      (reducedRankTildeE X Z Y) (reducedRankTildeY Z Y) eta Aperp)
    (hAperpNorm : reducedRankAperpNormalized (reducedRankTildeY Z Y) Aperp)
    (hAperpBound :
      reducedRankAperpDetVariationalBound (reducedRankTildeE X Z Y)
        (reducedRankTildeY Z Y) eta)
    (W : Matrix m r ℝ)
    (hGdet :
      (Gᵀ * reducedRankGPencilA (reducedRankTildeX Z X) (reducedRankTildeY Z Y) * G).det ≠
        0)
    (hDual : reducedRankDualEigenvectorRelation
      (reducedRankTildeX Z X) (reducedRankTildeY Z Y) G W (Matrix.diagonal lambda))
    (hOrth : reducedRankAperpYOrthogonal (reducedRankTildeY Z Y) Aperp W) :
    ReducedRankHansenSmallestSummaryCompatibilityExactDimension
      Z X (reducedRankTildeX Z X) Y (reducedRankTildeY Z Y) (reducedRankTildeE X Z Y) G
      ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G)
      (reducedRankChat Z X Y G
        ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G))
      ((Fintype.card n : ℝ)⁻¹ •
        ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeY Z Y) -
          ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G) *
            ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G)ᵀ))
      Aperp lambda eta (reducedRankMaximizedLogLikelihood (reducedRankTildeY Z Y) lambda) :=
  reducedRankHansenTheorem11_7_exactDimension_of_product_bounds_diagonalDual_compressedDet_ne_zero_canonicalAperp
    Z X (reducedRankTildeX Z X) Y (reducedRankTildeY Z Y) (reducedRankTildeE X Z Y)
    G lambda Aperp eta
    hG hGNorm hGBound hAperp hAperpNorm hAperpBound W
    hGdet hDual hOrth

set_option linter.style.longLine false in
/-- Residualized Hansen Theorem 11.7 exact-dimension endpoint for the proved
rank-one Rayleigh route, with Hansen's displayed diagonal dual relation.

This specializes
`reducedRankHansenTheorem11_7_exactDimension_of_rankOne_rayleigh_bounds_diagonalDual`
to the actual residualized matrices `X̃ = M_ZX`, `Ỹ = M_ZY`, and
`Ẽ = M_[X,Z]Y`. -/
theorem
    reducedRankHansenTheorem11_7_residualized_exactDimension_of_rankOne_rayleigh_bounds_diagonalDual
    (Z : Matrix n ell ℝ) (X : Matrix n k ℝ) (Y : Matrix n m ℝ)
    [DecidableEq k]
    [Invertible (Zᵀ * Z)]
    [Invertible ((Matrix.fromCols X Z)ᵀ * Matrix.fromCols X Z)]
    [Unique r] [Unique s]
    (G : Matrix k r ℝ) (lambda : r → ℝ)
    (Aperp : Matrix m s ℝ) (eta : s → ℝ)
    (hG : reducedRankHansenGEigenvectors
      (reducedRankTildeX Z X) (reducedRankTildeY Z Y) lambda G)
    (hGNorm : reducedRankGNormalized (reducedRankTildeX Z X) G)
    (hGBound : ∀ v : k → ℝ,
      v ⬝ᵥ (reducedRankGPencilB (reducedRankTildeX Z X) *ᵥ v) = 1 →
        v ⬝ᵥ
          (reducedRankGPencilA (reducedRankTildeX Z X) (reducedRankTildeY Z Y) *ᵥ v) ≤
            lambda default)
    (hAperp : reducedRankHansenAperpEigenvectors
      (reducedRankTildeE X Z Y) (reducedRankTildeY Z Y) eta Aperp)
    (hAperpNorm : reducedRankAperpNormalized (reducedRankTildeY Z Y) Aperp)
    (hAperpBound : ∀ v : m → ℝ,
      v ⬝ᵥ (reducedRankAperpPencilB (reducedRankTildeY Z Y) *ᵥ v) = 1 →
        eta default ≤
          v ⬝ᵥ (reducedRankAperpPencilA (reducedRankTildeE X Z Y) *ᵥ v))
    (W : Matrix m r ℝ)
    (hLambda : lambda default ≠ 0)
    (hDual : reducedRankDualEigenvectorRelation
      (reducedRankTildeX Z X) (reducedRankTildeY Z Y) G W (Matrix.diagonal lambda))
    (hOrth : reducedRankAperpYOrthogonal (reducedRankTildeY Z Y) Aperp W)
    (hdim : Fintype.card s = Fintype.card m - Fintype.card r) :
    ReducedRankHansenSmallestSummaryCompatibilityExactDimension
      Z X (reducedRankTildeX Z X) Y (reducedRankTildeY Z Y) (reducedRankTildeE X Z Y) G
      ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G)
      (reducedRankChat Z X Y G
        ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G))
      ((Fintype.card n : ℝ)⁻¹ •
        ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeY Z Y) -
          ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G) *
            ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G)ᵀ))
      Aperp lambda eta (reducedRankMaximizedLogLikelihood (reducedRankTildeY Z Y) lambda) :=
  reducedRankHansenTheorem11_7_exactDimension_of_rankOne_rayleigh_bounds_diagonalDual
    Z X (reducedRankTildeX Z X) Y (reducedRankTildeY Z Y) (reducedRankTildeE X Z Y)
    G lambda Aperp eta hG hGNorm hGBound hAperp hAperpNorm hAperpBound
    W hLambda hDual hOrth hdim

/-- Residualized Hansen Theorem 11.7 from generic generalized-pencil product
bounds, the displayed dual relation, and the exact `dim(A⊥)=m-r` condition. -/
theorem
    reducedRankHansenTheorem11_7_residualized_exactDimension_of_genericProductBounds_dual
    (Z : Matrix n ell ℝ) (X : Matrix n k ℝ) (Y : Matrix n m ℝ)
    [DecidableEq k]
    [Invertible (Zᵀ * Z)]
    [Invertible ((Matrix.fromCols X Z)ᵀ * Matrix.fromCols X Z)]
    (G : Matrix k r ℝ) (lambda : r → ℝ)
    (Aperp : Matrix m s ℝ) (eta : s → ℝ)
    (hG : reducedRankHansenGEigenvectors
      (reducedRankTildeX Z X) (reducedRankTildeY Z Y) lambda G)
    (hGNorm : reducedRankGNormalized (reducedRankTildeX Z X) G)
    (hGBound : generalizedEigenDetProductUpperBound
      (reducedRankGPencilA (reducedRankTildeX Z X) (reducedRankTildeY Z Y))
      (reducedRankGPencilB (reducedRankTildeX Z X)) lambda)
    (hAperp : reducedRankHansenAperpEigenvectors
      (reducedRankTildeE X Z Y) (reducedRankTildeY Z Y) eta Aperp)
    (hAperpNorm : reducedRankAperpNormalized (reducedRankTildeY Z Y) Aperp)
    (hAperpBound : generalizedEigenDetProductLowerBound
      (reducedRankAperpPencilA (reducedRankTildeE X Z Y))
      (reducedRankAperpPencilB (reducedRankTildeY Z Y)) eta)
    (W : Matrix m r ℝ) (Lambda LambdaInv : Matrix r r ℝ)
    (hDual : reducedRankDualEigenvectorRelation
      (reducedRankTildeX Z X) (reducedRankTildeY Z Y) G W Lambda)
    (hOrth : reducedRankAperpYOrthogonal (reducedRankTildeY Z Y) Aperp W)
    (hLambdaInv : Lambda * LambdaInv = 1)
    (hdim : Fintype.card s = Fintype.card m - Fintype.card r) :
    ReducedRankHansenSmallestSummaryCompatibilityExactDimension
      Z X (reducedRankTildeX Z X) Y (reducedRankTildeY Z Y) (reducedRankTildeE X Z Y) G
      ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G)
      (reducedRankChat Z X Y G
        ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G))
      ((Fintype.card n : ℝ)⁻¹ •
        ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeY Z Y) -
          ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G) *
            ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G)ᵀ))
      Aperp lambda eta (reducedRankMaximizedLogLikelihood (reducedRankTildeY Z Y) lambda) :=
  reducedRankHansenTheorem11_7_exactDimension_of_generalized_product_bounds_and_dual_relation
    Z X (reducedRankTildeX Z X) Y (reducedRankTildeY Z Y) (reducedRankTildeE X Z Y)
    G lambda Aperp eta
    hG hGNorm hGBound hAperp hAperpNorm hAperpBound
    W Lambda LambdaInv hDual hOrth hLambdaInv hdim

/-- Residualized Hansen Theorem 11.7 from generic generalized-pencil product
bounds, the displayed diagonal selected-root dual relation, pointwise
selected-root nonsingularity, and the exact `dim(A⊥)=m-r` condition. -/
theorem
    reducedRankHansenTheorem11_7_residualized_exactDimension_of_genericProductBounds_diagonalDual
    (Z : Matrix n ell ℝ) (X : Matrix n k ℝ) (Y : Matrix n m ℝ)
    [DecidableEq k]
    [Invertible (Zᵀ * Z)]
    [Invertible ((Matrix.fromCols X Z)ᵀ * Matrix.fromCols X Z)]
    (G : Matrix k r ℝ) (lambda : r → ℝ)
    (Aperp : Matrix m s ℝ) (eta : s → ℝ)
    (hG : reducedRankHansenGEigenvectors
      (reducedRankTildeX Z X) (reducedRankTildeY Z Y) lambda G)
    (hGNorm : reducedRankGNormalized (reducedRankTildeX Z X) G)
    (hGBound : generalizedEigenDetProductUpperBound
      (reducedRankGPencilA (reducedRankTildeX Z X) (reducedRankTildeY Z Y))
      (reducedRankGPencilB (reducedRankTildeX Z X)) lambda)
    (hAperp : reducedRankHansenAperpEigenvectors
      (reducedRankTildeE X Z Y) (reducedRankTildeY Z Y) eta Aperp)
    (hAperpNorm : reducedRankAperpNormalized (reducedRankTildeY Z Y) Aperp)
    (hAperpBound : generalizedEigenDetProductLowerBound
      (reducedRankAperpPencilA (reducedRankTildeE X Z Y))
      (reducedRankAperpPencilB (reducedRankTildeY Z Y)) eta)
    (W : Matrix m r ℝ)
    (hLambda : ∀ j, lambda j ≠ 0)
    (hDual : reducedRankDualEigenvectorRelation
      (reducedRankTildeX Z X) (reducedRankTildeY Z Y) G W (Matrix.diagonal lambda))
    (hOrth : reducedRankAperpYOrthogonal (reducedRankTildeY Z Y) Aperp W)
    (hdim : Fintype.card s = Fintype.card m - Fintype.card r) :
    ReducedRankHansenSmallestSummaryCompatibilityExactDimension
      Z X (reducedRankTildeX Z X) Y (reducedRankTildeY Z Y) (reducedRankTildeE X Z Y) G
      ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G)
      (reducedRankChat Z X Y G
        ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G))
      ((Fintype.card n : ℝ)⁻¹ •
        ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeY Z Y) -
          ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G) *
            ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G)ᵀ))
      Aperp lambda eta (reducedRankMaximizedLogLikelihood (reducedRankTildeY Z Y) lambda) :=
  reducedRankHansenTheorem11_7_exactDimension_of_genericProductBounds_diagonalDual
    Z X (reducedRankTildeX Z X) Y (reducedRankTildeY Z Y) (reducedRankTildeE X Z Y)
    G lambda Aperp eta
    hG hGNorm hGBound hAperp hAperpNorm hAperpBound
    W hLambda hDual hOrth hdim

set_option linter.style.longLine false in
/-- Residualized product-nonzero and index-split version of
`reducedRankHansenTheorem11_7_residualized_exactDimension_of_genericProductBounds_diagonalDual`.

This matches the non-residualized theorem-facing API: it keeps Hansen's exact
determinant/product premises and diagonal dual relation, while deriving
selected-root pointwise nonsingularity from `∏ λ_j ≠ 0` and the complementary
rank from a concrete finite index split `m ≃ r ⊕ s`. -/
theorem
    reducedRankHansenTheorem11_7_residualized_exactDimension_of_genericProductBounds_diagonalDual_prod_ne_zero_indexSplit
    (Z : Matrix n ell ℝ) (X : Matrix n k ℝ) (Y : Matrix n m ℝ)
    [DecidableEq k]
    [Invertible (Zᵀ * Z)]
    [Invertible ((Matrix.fromCols X Z)ᵀ * Matrix.fromCols X Z)]
    (G : Matrix k r ℝ) (lambda : r → ℝ)
    (Aperp : Matrix m s ℝ) (eta : s → ℝ)
    (hG : reducedRankHansenGEigenvectors
      (reducedRankTildeX Z X) (reducedRankTildeY Z Y) lambda G)
    (hGNorm : reducedRankGNormalized (reducedRankTildeX Z X) G)
    (hGBound : generalizedEigenDetProductUpperBound
      (reducedRankGPencilA (reducedRankTildeX Z X) (reducedRankTildeY Z Y))
      (reducedRankGPencilB (reducedRankTildeX Z X)) lambda)
    (hAperp : reducedRankHansenAperpEigenvectors
      (reducedRankTildeE X Z Y) (reducedRankTildeY Z Y) eta Aperp)
    (hAperpNorm : reducedRankAperpNormalized (reducedRankTildeY Z Y) Aperp)
    (hAperpBound : generalizedEigenDetProductLowerBound
      (reducedRankAperpPencilA (reducedRankTildeE X Z Y))
      (reducedRankAperpPencilB (reducedRankTildeY Z Y)) eta)
    (W : Matrix m r ℝ)
    (hLambdaProd : (∏ j, lambda j) ≠ 0)
    (hDual : reducedRankDualEigenvectorRelation
      (reducedRankTildeX Z X) (reducedRankTildeY Z Y) G W (Matrix.diagonal lambda))
    (hOrth : reducedRankAperpYOrthogonal (reducedRankTildeY Z Y) Aperp W)
    (hIndex : m ≃ Sum r s) :
    ReducedRankHansenSmallestSummaryCompatibilityExactDimension
      Z X (reducedRankTildeX Z X) Y (reducedRankTildeY Z Y) (reducedRankTildeE X Z Y) G
      ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G)
      (reducedRankChat Z X Y G
        ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G))
      ((Fintype.card n : ℝ)⁻¹ •
        ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeY Z Y) -
          ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G) *
            ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G)ᵀ))
      Aperp lambda eta (reducedRankMaximizedLogLikelihood (reducedRankTildeY Z Y) lambda) :=
  reducedRankHansenTheorem11_7_residualized_exactDimension_of_genericProductBounds_diagonalDual
    Z X Y G lambda Aperp eta
    hG hGNorm hGBound hAperp hAperpNorm hAperpBound W
    (reducedRankSelectedRoots_nonzero_of_prod_ne_zero lambda hLambdaProd)
    hDual hOrth
    (reducedRankAperpDimension_of_equiv_sum (m := m) (r := r) (s := s) hIndex)

set_option linter.style.longLine false in
/-- Residualized compressed-determinant and index-split version of
`reducedRankHansenTheorem11_7_residualized_exactDimension_of_genericProductBounds_diagonalDual`.

The generic product-bound theorem can now feed the residualized Hansen endpoint
with a nonzero selected compressed determinant instead of a separate nonzero
selected-root product. -/
theorem
    reducedRankHansenTheorem11_7_residualized_exactDimension_of_genericProductBounds_diagonalDual_compressedDet_ne_zero_indexSplit
    (Z : Matrix n ell ℝ) (X : Matrix n k ℝ) (Y : Matrix n m ℝ)
    [DecidableEq k]
    [Invertible (Zᵀ * Z)]
    [Invertible ((Matrix.fromCols X Z)ᵀ * Matrix.fromCols X Z)]
    (G : Matrix k r ℝ) (lambda : r → ℝ)
    (Aperp : Matrix m s ℝ) (eta : s → ℝ)
    (hG : reducedRankHansenGEigenvectors
      (reducedRankTildeX Z X) (reducedRankTildeY Z Y) lambda G)
    (hGNorm : reducedRankGNormalized (reducedRankTildeX Z X) G)
    (hGBound : generalizedEigenDetProductUpperBound
      (reducedRankGPencilA (reducedRankTildeX Z X) (reducedRankTildeY Z Y))
      (reducedRankGPencilB (reducedRankTildeX Z X)) lambda)
    (hAperp : reducedRankHansenAperpEigenvectors
      (reducedRankTildeE X Z Y) (reducedRankTildeY Z Y) eta Aperp)
    (hAperpNorm : reducedRankAperpNormalized (reducedRankTildeY Z Y) Aperp)
    (hAperpBound : generalizedEigenDetProductLowerBound
      (reducedRankAperpPencilA (reducedRankTildeE X Z Y))
      (reducedRankAperpPencilB (reducedRankTildeY Z Y)) eta)
    (W : Matrix m r ℝ)
    (hGdet :
      (Gᵀ * reducedRankGPencilA (reducedRankTildeX Z X) (reducedRankTildeY Z Y) * G).det ≠
        0)
    (hDual : reducedRankDualEigenvectorRelation
      (reducedRankTildeX Z X) (reducedRankTildeY Z Y) G W (Matrix.diagonal lambda))
    (hOrth : reducedRankAperpYOrthogonal (reducedRankTildeY Z Y) Aperp W)
    (hIndex : m ≃ Sum r s) :
    ReducedRankHansenSmallestSummaryCompatibilityExactDimension
      Z X (reducedRankTildeX Z X) Y (reducedRankTildeY Z Y) (reducedRankTildeE X Z Y) G
      ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G)
      (reducedRankChat Z X Y G
        ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G))
      ((Fintype.card n : ℝ)⁻¹ •
        ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeY Z Y) -
          ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G) *
            ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G)ᵀ))
      Aperp lambda eta (reducedRankMaximizedLogLikelihood (reducedRankTildeY Z Y) lambda) :=
  reducedRankHansenTheorem11_7_residualized_exactDimension_of_genericProductBounds_diagonalDual_prod_ne_zero_indexSplit
    Z X Y G lambda Aperp eta
    hG hGNorm hGBound hAperp hAperpNorm hAperpBound W
    (generalizedEigenSelectedRootProduct_ne_zero_of_compressedDet_ne_zero
      (reducedRankGPencilA (reducedRankTildeX Z X) (reducedRankTildeY Z Y))
      (reducedRankGPencilB (reducedRankTildeX Z X))
      lambda G hG hGNorm hGdet)
    hDual hOrth hIndex

set_option linter.style.longLine false in
/-- Residualized positive-root and index-split version of
`reducedRankHansenTheorem11_7_residualized_exactDimension_of_genericProductBounds_diagonalDual`.

It consumes generic generalized-pencil product bounds, Hansen's displayed
diagonal dual relation, positive selected `G` roots, and a concrete finite
split `m ≃ r ⊕ s`, deriving the nonzero selected-root product and dimension
equality internally. -/
theorem
    reducedRankHansenTheorem11_7_residualized_exactDimension_of_genericProductBounds_diagonalDual_pos_indexSplit
    (Z : Matrix n ell ℝ) (X : Matrix n k ℝ) (Y : Matrix n m ℝ)
    [DecidableEq k]
    [Invertible (Zᵀ * Z)]
    [Invertible ((Matrix.fromCols X Z)ᵀ * Matrix.fromCols X Z)]
    (G : Matrix k r ℝ) (lambda : r → ℝ)
    (Aperp : Matrix m s ℝ) (eta : s → ℝ)
    (hG : reducedRankHansenGEigenvectors
      (reducedRankTildeX Z X) (reducedRankTildeY Z Y) lambda G)
    (hGNorm : reducedRankGNormalized (reducedRankTildeX Z X) G)
    (hGBound : generalizedEigenDetProductUpperBound
      (reducedRankGPencilA (reducedRankTildeX Z X) (reducedRankTildeY Z Y))
      (reducedRankGPencilB (reducedRankTildeX Z X)) lambda)
    (hAperp : reducedRankHansenAperpEigenvectors
      (reducedRankTildeE X Z Y) (reducedRankTildeY Z Y) eta Aperp)
    (hAperpNorm : reducedRankAperpNormalized (reducedRankTildeY Z Y) Aperp)
    (hAperpBound : generalizedEigenDetProductLowerBound
      (reducedRankAperpPencilA (reducedRankTildeE X Z Y))
      (reducedRankAperpPencilB (reducedRankTildeY Z Y)) eta)
    (W : Matrix m r ℝ)
    (hLambda : ∀ j, 0 < lambda j)
    (hDual : reducedRankDualEigenvectorRelation
      (reducedRankTildeX Z X) (reducedRankTildeY Z Y) G W (Matrix.diagonal lambda))
    (hOrth : reducedRankAperpYOrthogonal (reducedRankTildeY Z Y) Aperp W)
    (hIndex : m ≃ Sum r s) :
    ReducedRankHansenSmallestSummaryCompatibilityExactDimension
      Z X (reducedRankTildeX Z X) Y (reducedRankTildeY Z Y) (reducedRankTildeE X Z Y) G
      ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G)
      (reducedRankChat Z X Y G
        ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G))
      ((Fintype.card n : ℝ)⁻¹ •
        ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeY Z Y) -
          ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G) *
            ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G)ᵀ))
      Aperp lambda eta (reducedRankMaximizedLogLikelihood (reducedRankTildeY Z Y) lambda) :=
  reducedRankHansenTheorem11_7_residualized_exactDimension_of_genericProductBounds_diagonalDual_prod_ne_zero_indexSplit
    Z X Y G lambda Aperp eta
    hG hGNorm hGBound hAperp hAperpNorm hAperpBound W
    (reducedRankSelectedRootProduct_ne_zero_of_pos lambda hLambda)
    hDual hOrth hIndex

set_option linter.style.longLine false in
/-- Residualized canonical-`A⊥` version of
`reducedRankHansenTheorem11_7_residualized_exactDimension_of_genericProductBounds_diagonalDual_prod_ne_zero_indexSplit`.

This is the generic generalized-pencil product-bound route for the actual
Hansen residualized matrices with canonical complement index
`Fin (card m - card r)`. -/
theorem
    reducedRankHansenTheorem11_7_residualized_exactDimension_of_genericProductBounds_diagonalDual_prod_ne_zero_canonicalAperp
    (Z : Matrix n ell ℝ) (X : Matrix n k ℝ) (Y : Matrix n m ℝ)
    [DecidableEq k]
    [Invertible (Zᵀ * Z)]
    [Invertible ((Matrix.fromCols X Z)ᵀ * Matrix.fromCols X Z)]
    (G : Matrix k r ℝ) (lambda : r → ℝ)
    (Aperp : Matrix m (reducedRankAperpIndex m r) ℝ)
    (eta : reducedRankAperpIndex m r → ℝ)
    (hG : reducedRankHansenGEigenvectors
      (reducedRankTildeX Z X) (reducedRankTildeY Z Y) lambda G)
    (hGNorm : reducedRankGNormalized (reducedRankTildeX Z X) G)
    (hGBound : generalizedEigenDetProductUpperBound
      (reducedRankGPencilA (reducedRankTildeX Z X) (reducedRankTildeY Z Y))
      (reducedRankGPencilB (reducedRankTildeX Z X)) lambda)
    (hAperp : reducedRankHansenAperpEigenvectors
      (reducedRankTildeE X Z Y) (reducedRankTildeY Z Y) eta Aperp)
    (hAperpNorm : reducedRankAperpNormalized (reducedRankTildeY Z Y) Aperp)
    (hAperpBound : generalizedEigenDetProductLowerBound
      (reducedRankAperpPencilA (reducedRankTildeE X Z Y))
      (reducedRankAperpPencilB (reducedRankTildeY Z Y)) eta)
    (W : Matrix m r ℝ)
    (hLambdaProd : (∏ j, lambda j) ≠ 0)
    (hDual : reducedRankDualEigenvectorRelation
      (reducedRankTildeX Z X) (reducedRankTildeY Z Y) G W (Matrix.diagonal lambda))
    (hOrth : reducedRankAperpYOrthogonal (reducedRankTildeY Z Y) Aperp W) :
    ReducedRankHansenSmallestSummaryCompatibilityExactDimension
      Z X (reducedRankTildeX Z X) Y (reducedRankTildeY Z Y) (reducedRankTildeE X Z Y) G
      ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G)
      (reducedRankChat Z X Y G
        ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G))
      ((Fintype.card n : ℝ)⁻¹ •
        ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeY Z Y) -
          ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G) *
            ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G)ᵀ))
      Aperp lambda eta (reducedRankMaximizedLogLikelihood (reducedRankTildeY Z Y) lambda) :=
  reducedRankHansenTheorem11_7_exactDimension_of_genericProductBounds_diagonalDual_prod_ne_zero_canonicalAperp
    Z X (reducedRankTildeX Z X) Y (reducedRankTildeY Z Y) (reducedRankTildeE X Z Y)
    G lambda Aperp eta hG hGNorm hGBound hAperp hAperpNorm hAperpBound
    W hLambdaProd hDual hOrth

set_option linter.style.longLine false in
/-- Residualized canonical-`A⊥` generic-product endpoint where selected-root
nonsingularity is derived from the nonzero selected compressed determinant. -/
theorem
    reducedRankHansenTheorem11_7_residualized_exactDimension_of_genericProductBounds_diagonalDual_compressedDet_ne_zero_canonicalAperp
    (Z : Matrix n ell ℝ) (X : Matrix n k ℝ) (Y : Matrix n m ℝ)
    [DecidableEq k]
    [Invertible (Zᵀ * Z)]
    [Invertible ((Matrix.fromCols X Z)ᵀ * Matrix.fromCols X Z)]
    (G : Matrix k r ℝ) (lambda : r → ℝ)
    (Aperp : Matrix m (reducedRankAperpIndex m r) ℝ)
    (eta : reducedRankAperpIndex m r → ℝ)
    (hG : reducedRankHansenGEigenvectors
      (reducedRankTildeX Z X) (reducedRankTildeY Z Y) lambda G)
    (hGNorm : reducedRankGNormalized (reducedRankTildeX Z X) G)
    (hGBound : generalizedEigenDetProductUpperBound
      (reducedRankGPencilA (reducedRankTildeX Z X) (reducedRankTildeY Z Y))
      (reducedRankGPencilB (reducedRankTildeX Z X)) lambda)
    (hAperp : reducedRankHansenAperpEigenvectors
      (reducedRankTildeE X Z Y) (reducedRankTildeY Z Y) eta Aperp)
    (hAperpNorm : reducedRankAperpNormalized (reducedRankTildeY Z Y) Aperp)
    (hAperpBound : generalizedEigenDetProductLowerBound
      (reducedRankAperpPencilA (reducedRankTildeE X Z Y))
      (reducedRankAperpPencilB (reducedRankTildeY Z Y)) eta)
    (W : Matrix m r ℝ)
    (hGdet :
      (Gᵀ * reducedRankGPencilA (reducedRankTildeX Z X) (reducedRankTildeY Z Y) * G).det ≠
        0)
    (hDual : reducedRankDualEigenvectorRelation
      (reducedRankTildeX Z X) (reducedRankTildeY Z Y) G W (Matrix.diagonal lambda))
    (hOrth : reducedRankAperpYOrthogonal (reducedRankTildeY Z Y) Aperp W) :
    ReducedRankHansenSmallestSummaryCompatibilityExactDimension
      Z X (reducedRankTildeX Z X) Y (reducedRankTildeY Z Y) (reducedRankTildeE X Z Y) G
      ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G)
      (reducedRankChat Z X Y G
        ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G))
      ((Fintype.card n : ℝ)⁻¹ •
        ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeY Z Y) -
          ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G) *
            ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G)ᵀ))
      Aperp lambda eta (reducedRankMaximizedLogLikelihood (reducedRankTildeY Z Y) lambda) :=
  reducedRankHansenTheorem11_7_residualized_exactDimension_of_genericProductBounds_diagonalDual_prod_ne_zero_canonicalAperp
    Z X Y G lambda Aperp eta hG hGNorm hGBound hAperp hAperpNorm hAperpBound
    W
    (generalizedEigenSelectedRootProduct_ne_zero_of_compressedDet_ne_zero
      (reducedRankGPencilA (reducedRankTildeX Z X) (reducedRankTildeY Z Y))
      (reducedRankGPencilB (reducedRankTildeX Z X))
      lambda G hG hGNorm hGdet)
    hDual hOrth

/-- Residualized objective-extrema version of the exact-dimension dual-relation
endpoint. -/
theorem
    reducedRankHansenTheorem11_7_residualized_exactDimension_of_objective_extrema_and_dual_relation
    (Z : Matrix n ell ℝ) (X : Matrix n k ℝ) (Y : Matrix n m ℝ)
    [DecidableEq k]
    [Invertible (Zᵀ * Z)]
    [Invertible ((Matrix.fromCols X Z)ᵀ * Matrix.fromCols X Z)]
    (G : Matrix k r ℝ) (lambda : r → ℝ)
    (Aperp : Matrix m s ℝ) (eta : s → ℝ)
    (hG : reducedRankHansenGEigenvectors
      (reducedRankTildeX Z X) (reducedRankTildeY Z Y) lambda G)
    (hGOpt : reducedRankConcentratedObjectiveMaximizer
      (reducedRankTildeX Z X) (reducedRankTildeY Z Y) G)
    (hAperp : reducedRankHansenAperpEigenvectors
      (reducedRankTildeE X Z Y) (reducedRankTildeY Z Y) eta Aperp)
    (hAperpOpt : reducedRankAperpObjectiveMinimizer
      (reducedRankTildeE X Z Y) (reducedRankTildeY Z Y) Aperp)
    (W : Matrix m r ℝ) (Lambda LambdaInv : Matrix r r ℝ)
    (hDual : reducedRankDualEigenvectorRelation
      (reducedRankTildeX Z X) (reducedRankTildeY Z Y) G W Lambda)
    (hOrth : reducedRankAperpYOrthogonal (reducedRankTildeY Z Y) Aperp W)
    (hLambdaInv : Lambda * LambdaInv = 1)
    (hdim : Fintype.card s = Fintype.card m - Fintype.card r) :
    ReducedRankHansenSmallestSummaryCompatibilityExactDimension
      Z X (reducedRankTildeX Z X) Y (reducedRankTildeY Z Y) (reducedRankTildeE X Z Y) G
      ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G)
      (reducedRankChat Z X Y G
        ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G))
      ((Fintype.card n : ℝ)⁻¹ •
        ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeY Z Y) -
          ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G) *
            ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G)ᵀ))
      Aperp lambda eta (reducedRankMaximizedLogLikelihood (reducedRankTildeY Z Y) lambda) :=
  ReducedRankHansenSmallestSummaryCompatibilityExactDimension.of_theorem11_7
    (reducedRankHansenTheorem11_7_residualized_of_objective_extrema_and_dual_relation
      Z X Y G lambda Aperp eta
      hG hGOpt hAperp hAperpOpt W Lambda LambdaInv hDual hOrth hLambdaInv)
    hdim

set_option linter.style.longLine false in
/-- Residualized canonical-`A⊥` objective-extrema endpoint with Hansen's
displayed diagonal dual relation.

This specializes the objective-extrema bridge to `X̃ = M_ZX`, `Ỹ = M_ZY`,
and `Ẽ = M_[X,Z]Y`. It removes the separate inverse diagonal block and
`dim(A⊥)=m-r` premise from the normal-likelihood route, leaving the genuine
primitive as the proof of the two objective extrema plus the displayed dual
relation for the selected generalized eigenspaces. -/
theorem
    reducedRankHansenTheorem11_7_residualized_exactDimension_of_objective_extrema_diagonalDual_compressedDet_ne_zero_canonicalAperp
    (Z : Matrix n ell ℝ) (X : Matrix n k ℝ) (Y : Matrix n m ℝ)
    [DecidableEq k]
    [Invertible (Zᵀ * Z)]
    [Invertible ((Matrix.fromCols X Z)ᵀ * Matrix.fromCols X Z)]
    (G : Matrix k r ℝ) (lambda : r → ℝ)
    (Aperp : Matrix m (reducedRankAperpIndex m r) ℝ)
    (eta : reducedRankAperpIndex m r → ℝ)
    (hG : reducedRankHansenGEigenvectors
      (reducedRankTildeX Z X) (reducedRankTildeY Z Y) lambda G)
    (hGOpt : reducedRankConcentratedObjectiveMaximizer
      (reducedRankTildeX Z X) (reducedRankTildeY Z Y) G)
    (hAperp : reducedRankHansenAperpEigenvectors
      (reducedRankTildeE X Z Y) (reducedRankTildeY Z Y) eta Aperp)
    (hAperpOpt : reducedRankAperpObjectiveMinimizer
      (reducedRankTildeE X Z Y) (reducedRankTildeY Z Y) Aperp)
    (W : Matrix m r ℝ)
    (hGdet :
      (Gᵀ * reducedRankGPencilA (reducedRankTildeX Z X) (reducedRankTildeY Z Y) * G).det ≠
        0)
    (hDual : reducedRankDualEigenvectorRelation
      (reducedRankTildeX Z X) (reducedRankTildeY Z Y) G W (Matrix.diagonal lambda))
    (hOrth : reducedRankAperpYOrthogonal (reducedRankTildeY Z Y) Aperp W) :
    ReducedRankHansenSmallestSummaryCompatibilityExactDimension
      Z X (reducedRankTildeX Z X) Y (reducedRankTildeY Z Y) (reducedRankTildeE X Z Y) G
      ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G)
      (reducedRankChat Z X Y G
        ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G))
      ((Fintype.card n : ℝ)⁻¹ •
        ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeY Z Y) -
          ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G) *
            ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G)ᵀ))
      Aperp lambda eta (reducedRankMaximizedLogLikelihood (reducedRankTildeY Z Y) lambda) :=
  reducedRankHansenTheorem11_7_exactDimension_of_objective_extrema_diagonalDual_compressedDet_ne_zero_canonicalAperp
    Z X (reducedRankTildeX Z X) Y (reducedRankTildeY Z Y) (reducedRankTildeE X Z Y)
    G lambda Aperp eta hG hGOpt hAperp hAperpOpt W hGdet hDual hOrth

set_option linter.style.longLine false in
/-- Residualized canonical-`A⊥` objective-extrema endpoint with Hansen's
displayed diagonal dual relation and a nonzero selected-root product. -/
theorem
    reducedRankHansenTheorem11_7_residualized_exactDimension_of_objective_extrema_diagonalDual_prod_ne_zero_canonicalAperp
    (Z : Matrix n ell ℝ) (X : Matrix n k ℝ) (Y : Matrix n m ℝ)
    [DecidableEq k]
    [Invertible (Zᵀ * Z)]
    [Invertible ((Matrix.fromCols X Z)ᵀ * Matrix.fromCols X Z)]
    (G : Matrix k r ℝ) (lambda : r → ℝ)
    (Aperp : Matrix m (reducedRankAperpIndex m r) ℝ)
    (eta : reducedRankAperpIndex m r → ℝ)
    (hG : reducedRankHansenGEigenvectors
      (reducedRankTildeX Z X) (reducedRankTildeY Z Y) lambda G)
    (hGOpt : reducedRankConcentratedObjectiveMaximizer
      (reducedRankTildeX Z X) (reducedRankTildeY Z Y) G)
    (hAperp : reducedRankHansenAperpEigenvectors
      (reducedRankTildeE X Z Y) (reducedRankTildeY Z Y) eta Aperp)
    (hAperpOpt : reducedRankAperpObjectiveMinimizer
      (reducedRankTildeE X Z Y) (reducedRankTildeY Z Y) Aperp)
    (W : Matrix m r ℝ)
    (hLambdaProd : (∏ j, lambda j) ≠ 0)
    (hDual : reducedRankDualEigenvectorRelation
      (reducedRankTildeX Z X) (reducedRankTildeY Z Y) G W (Matrix.diagonal lambda))
    (hOrth : reducedRankAperpYOrthogonal (reducedRankTildeY Z Y) Aperp W) :
    ReducedRankHansenSmallestSummaryCompatibilityExactDimension
      Z X (reducedRankTildeX Z X) Y (reducedRankTildeY Z Y) (reducedRankTildeE X Z Y) G
      ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G)
      (reducedRankChat Z X Y G
        ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G))
      ((Fintype.card n : ℝ)⁻¹ •
        ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeY Z Y) -
          ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G) *
            ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G)ᵀ))
      Aperp lambda eta (reducedRankMaximizedLogLikelihood (reducedRankTildeY Z Y) lambda) :=
  reducedRankHansenTheorem11_7_exactDimension_of_objective_extrema_diagonalDual_prod_ne_zero_canonicalAperp
    Z X (reducedRankTildeX Z X) Y (reducedRankTildeY Z Y) (reducedRankTildeE X Z Y)
    G lambda Aperp eta hG hGOpt hAperp hAperpOpt W hLambdaProd hDual hOrth

set_option linter.style.longLine false in
/-- Residualized canonical-`A⊥` objective-extrema endpoint with Hansen's
displayed diagonal dual relation and positive selected `G` roots.

This residualized theorem-facing route removes the separate selected
compressed-determinant nonsingularity premise from the normal-likelihood
objective-extrema path. -/
theorem
    reducedRankHansenTheorem11_7_residualized_exactDimension_of_objective_extrema_diagonalDual_pos_canonicalAperp
    (Z : Matrix n ell ℝ) (X : Matrix n k ℝ) (Y : Matrix n m ℝ)
    [DecidableEq k]
    [Invertible (Zᵀ * Z)]
    [Invertible ((Matrix.fromCols X Z)ᵀ * Matrix.fromCols X Z)]
    (G : Matrix k r ℝ) (lambda : r → ℝ)
    (Aperp : Matrix m (reducedRankAperpIndex m r) ℝ)
    (eta : reducedRankAperpIndex m r → ℝ)
    (hG : reducedRankHansenGEigenvectors
      (reducedRankTildeX Z X) (reducedRankTildeY Z Y) lambda G)
    (hGOpt : reducedRankConcentratedObjectiveMaximizer
      (reducedRankTildeX Z X) (reducedRankTildeY Z Y) G)
    (hAperp : reducedRankHansenAperpEigenvectors
      (reducedRankTildeE X Z Y) (reducedRankTildeY Z Y) eta Aperp)
    (hAperpOpt : reducedRankAperpObjectiveMinimizer
      (reducedRankTildeE X Z Y) (reducedRankTildeY Z Y) Aperp)
    (W : Matrix m r ℝ)
    (hLambda : ∀ j, 0 < lambda j)
    (hDual : reducedRankDualEigenvectorRelation
      (reducedRankTildeX Z X) (reducedRankTildeY Z Y) G W (Matrix.diagonal lambda))
    (hOrth : reducedRankAperpYOrthogonal (reducedRankTildeY Z Y) Aperp W) :
    ReducedRankHansenSmallestSummaryCompatibilityExactDimension
      Z X (reducedRankTildeX Z X) Y (reducedRankTildeY Z Y) (reducedRankTildeE X Z Y) G
      ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G)
      (reducedRankChat Z X Y G
        ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G))
      ((Fintype.card n : ℝ)⁻¹ •
        ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeY Z Y) -
          ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G) *
            ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G)ᵀ))
      Aperp lambda eta (reducedRankMaximizedLogLikelihood (reducedRankTildeY Z Y) lambda) :=
  reducedRankHansenTheorem11_7_exactDimension_of_objective_extrema_diagonalDual_pos_canonicalAperp
    Z X (reducedRankTildeX Z X) Y (reducedRankTildeY Z Y) (reducedRankTildeE X Z Y)
    G lambda Aperp eta hG hGOpt hAperp hAperpOpt W hLambda hDual hOrth

/-- Residualized selected-compressed-determinant version of the exact-dimension
dual-relation endpoint. The determinant min-max theorem is now available; this
conditional surface remains useful when callers already have selected extrema
and a compatible dual relation. -/
theorem
    reducedRankHansenTheorem11_7_residualized_exactDimension_of_selectedExtrema_dual_relation
    (Z : Matrix n ell ℝ) (X : Matrix n k ℝ) (Y : Matrix n m ℝ)
    [DecidableEq k]
    [Invertible (Zᵀ * Z)]
    [Invertible ((Matrix.fromCols X Z)ᵀ * Matrix.fromCols X Z)]
    (G : Matrix k r ℝ) (lambda : r → ℝ)
    (Aperp : Matrix m s ℝ) (eta : s → ℝ)
    (hG : reducedRankHansenGEigenvectors
      (reducedRankTildeX Z X) (reducedRankTildeY Z Y) lambda G)
    (hGNorm : reducedRankGNormalized (reducedRankTildeX Z X) G)
    (hGMax :
      generalizedEigenSelectedCompressedDetMaximal
        (reducedRankGPencilA (reducedRankTildeX Z X) (reducedRankTildeY Z Y))
        (reducedRankGPencilB (reducedRankTildeX Z X)) G)
    (hAperp : reducedRankHansenAperpEigenvectors
      (reducedRankTildeE X Z Y) (reducedRankTildeY Z Y) eta Aperp)
    (hAperpNorm : reducedRankAperpNormalized (reducedRankTildeY Z Y) Aperp)
    (hAperpMin :
      generalizedEigenSelectedCompressedDetMinimal
        (reducedRankAperpPencilA (reducedRankTildeE X Z Y))
        (reducedRankAperpPencilB (reducedRankTildeY Z Y)) Aperp)
    (W : Matrix m r ℝ) (Lambda LambdaInv : Matrix r r ℝ)
    (hDual : reducedRankDualEigenvectorRelation
      (reducedRankTildeX Z X) (reducedRankTildeY Z Y) G W Lambda)
    (hOrth : reducedRankAperpYOrthogonal (reducedRankTildeY Z Y) Aperp W)
    (hLambdaInv : Lambda * LambdaInv = 1)
    (hdim : Fintype.card s = Fintype.card m - Fintype.card r) :
    ReducedRankHansenSmallestSummaryCompatibilityExactDimension
      Z X (reducedRankTildeX Z X) Y (reducedRankTildeY Z Y) (reducedRankTildeE X Z Y) G
      ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G)
      (reducedRankChat Z X Y G
        ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G))
      ((Fintype.card n : ℝ)⁻¹ •
        ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeY Z Y) -
          ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G) *
            ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G)ᵀ))
      Aperp lambda eta (reducedRankMaximizedLogLikelihood (reducedRankTildeY Z Y) lambda) :=
  reducedRankHansenTheorem11_7_exactDimension_of_selected_compressedDet_extrema_and_dual_relation
    Z X (reducedRankTildeX Z X) Y (reducedRankTildeY Z Y) (reducedRankTildeE X Z Y)
    G lambda Aperp eta hG hGNorm hGMax hAperp hAperpNorm hAperpMin
    W Lambda LambdaInv hDual hOrth hLambdaInv hdim

set_option linter.style.longLine false in
/-- Residualized canonical-`A⊥` selected-extrema endpoint with Hansen's
displayed diagonal dual relation and a nonzero selected-root product. -/
theorem
    reducedRankHansenTheorem11_7_residualized_exactDimension_of_selectedExtrema_diagonalDual_prod_ne_zero_canonicalAperp
    (Z : Matrix n ell ℝ) (X : Matrix n k ℝ) (Y : Matrix n m ℝ)
    [DecidableEq k]
    [Invertible (Zᵀ * Z)]
    [Invertible ((Matrix.fromCols X Z)ᵀ * Matrix.fromCols X Z)]
    (G : Matrix k r ℝ) (lambda : r → ℝ)
    (Aperp : Matrix m (reducedRankAperpIndex m r) ℝ)
    (eta : reducedRankAperpIndex m r → ℝ)
    (hG : reducedRankHansenGEigenvectors
      (reducedRankTildeX Z X) (reducedRankTildeY Z Y) lambda G)
    (hGNorm : reducedRankGNormalized (reducedRankTildeX Z X) G)
    (hGMax :
      generalizedEigenSelectedCompressedDetMaximal
        (reducedRankGPencilA (reducedRankTildeX Z X) (reducedRankTildeY Z Y))
        (reducedRankGPencilB (reducedRankTildeX Z X)) G)
    (hAperp : reducedRankHansenAperpEigenvectors
      (reducedRankTildeE X Z Y) (reducedRankTildeY Z Y) eta Aperp)
    (hAperpNorm : reducedRankAperpNormalized (reducedRankTildeY Z Y) Aperp)
    (hAperpMin :
      generalizedEigenSelectedCompressedDetMinimal
        (reducedRankAperpPencilA (reducedRankTildeE X Z Y))
        (reducedRankAperpPencilB (reducedRankTildeY Z Y)) Aperp)
    (W : Matrix m r ℝ)
    (hLambdaProd : (∏ j, lambda j) ≠ 0)
    (hDual : reducedRankDualEigenvectorRelation
      (reducedRankTildeX Z X) (reducedRankTildeY Z Y) G W (Matrix.diagonal lambda))
    (hOrth : reducedRankAperpYOrthogonal (reducedRankTildeY Z Y) Aperp W) :
    ReducedRankHansenSmallestSummaryCompatibilityExactDimension
      Z X (reducedRankTildeX Z X) Y (reducedRankTildeY Z Y) (reducedRankTildeE X Z Y) G
      ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G)
      (reducedRankChat Z X Y G
        ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G))
      ((Fintype.card n : ℝ)⁻¹ •
        ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeY Z Y) -
          ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G) *
            ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G)ᵀ))
      Aperp lambda eta (reducedRankMaximizedLogLikelihood (reducedRankTildeY Z Y) lambda) :=
  reducedRankHansenTheorem11_7_exactDimension_of_selectedExtrema_diagonalDual_prod_ne_zero_canonicalAperp
    Z X (reducedRankTildeX Z X) Y (reducedRankTildeY Z Y) (reducedRankTildeE X Z Y)
    G lambda Aperp eta hG hGNorm hGMax hAperp hAperpNorm hAperpMin
    W hLambdaProd hDual hOrth

set_option linter.style.longLine false in
/-- Residualized canonical-`A⊥` selected-extrema endpoint with Hansen's
displayed diagonal dual relation.

This is the closest selected-compressed-determinant surface to Hansen Theorem
11.7 before the full multi-column determinant/product variational theorem is
proved: selected compressed-determinant extrema provide the objective extrema,
`det(G'AG) ≠ 0` supplies selected-root nonsingularity, and the canonical
`A⊥` index supplies the exact `m-r` dimension. -/
theorem
    reducedRankHansenTheorem11_7_residualized_exactDimension_of_selectedExtrema_diagonalDual_compressedDet_ne_zero_canonicalAperp
    (Z : Matrix n ell ℝ) (X : Matrix n k ℝ) (Y : Matrix n m ℝ)
    [DecidableEq k]
    [Invertible (Zᵀ * Z)]
    [Invertible ((Matrix.fromCols X Z)ᵀ * Matrix.fromCols X Z)]
    (G : Matrix k r ℝ) (lambda : r → ℝ)
    (Aperp : Matrix m (reducedRankAperpIndex m r) ℝ)
    (eta : reducedRankAperpIndex m r → ℝ)
    (hG : reducedRankHansenGEigenvectors
      (reducedRankTildeX Z X) (reducedRankTildeY Z Y) lambda G)
    (hGNorm : reducedRankGNormalized (reducedRankTildeX Z X) G)
    (hGMax :
      generalizedEigenSelectedCompressedDetMaximal
        (reducedRankGPencilA (reducedRankTildeX Z X) (reducedRankTildeY Z Y))
        (reducedRankGPencilB (reducedRankTildeX Z X)) G)
    (hAperp : reducedRankHansenAperpEigenvectors
      (reducedRankTildeE X Z Y) (reducedRankTildeY Z Y) eta Aperp)
    (hAperpNorm : reducedRankAperpNormalized (reducedRankTildeY Z Y) Aperp)
    (hAperpMin :
      generalizedEigenSelectedCompressedDetMinimal
        (reducedRankAperpPencilA (reducedRankTildeE X Z Y))
        (reducedRankAperpPencilB (reducedRankTildeY Z Y)) Aperp)
    (W : Matrix m r ℝ)
    (hGdet :
      (Gᵀ * reducedRankGPencilA (reducedRankTildeX Z X) (reducedRankTildeY Z Y) * G).det ≠
        0)
    (hDual : reducedRankDualEigenvectorRelation
      (reducedRankTildeX Z X) (reducedRankTildeY Z Y) G W (Matrix.diagonal lambda))
    (hOrth : reducedRankAperpYOrthogonal (reducedRankTildeY Z Y) Aperp W) :
    ReducedRankHansenSmallestSummaryCompatibilityExactDimension
      Z X (reducedRankTildeX Z X) Y (reducedRankTildeY Z Y) (reducedRankTildeE X Z Y) G
      ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G)
      (reducedRankChat Z X Y G
        ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G))
      ((Fintype.card n : ℝ)⁻¹ •
        ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeY Z Y) -
          ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G) *
            ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G)ᵀ))
      Aperp lambda eta (reducedRankMaximizedLogLikelihood (reducedRankTildeY Z Y) lambda) :=
  reducedRankHansenTheorem11_7_exactDimension_of_selectedExtrema_diagonalDual_compressedDet_ne_zero_canonicalAperp
    Z X (reducedRankTildeX Z X) Y (reducedRankTildeY Z Y) (reducedRankTildeE X Z Y)
    G lambda Aperp eta hG hGNorm hGMax hAperp hAperpNorm hAperpMin
    W hGdet hDual hOrth

set_option linter.style.longLine false in
/-- Residualized canonical-`A⊥` selected-extrema endpoint with Hansen's
displayed diagonal dual relation and positive selected `G` roots.

This is the residualized selected-extrema route with the determinant
nonsingularity premise replaced by the more spectral positive-root condition. -/
theorem
    reducedRankHansenTheorem11_7_residualized_exactDimension_of_selectedExtrema_diagonalDual_pos_canonicalAperp
    (Z : Matrix n ell ℝ) (X : Matrix n k ℝ) (Y : Matrix n m ℝ)
    [DecidableEq k]
    [Invertible (Zᵀ * Z)]
    [Invertible ((Matrix.fromCols X Z)ᵀ * Matrix.fromCols X Z)]
    (G : Matrix k r ℝ) (lambda : r → ℝ)
    (Aperp : Matrix m (reducedRankAperpIndex m r) ℝ)
    (eta : reducedRankAperpIndex m r → ℝ)
    (hG : reducedRankHansenGEigenvectors
      (reducedRankTildeX Z X) (reducedRankTildeY Z Y) lambda G)
    (hGNorm : reducedRankGNormalized (reducedRankTildeX Z X) G)
    (hGMax :
      generalizedEigenSelectedCompressedDetMaximal
        (reducedRankGPencilA (reducedRankTildeX Z X) (reducedRankTildeY Z Y))
        (reducedRankGPencilB (reducedRankTildeX Z X)) G)
    (hAperp : reducedRankHansenAperpEigenvectors
      (reducedRankTildeE X Z Y) (reducedRankTildeY Z Y) eta Aperp)
    (hAperpNorm : reducedRankAperpNormalized (reducedRankTildeY Z Y) Aperp)
    (hAperpMin :
      generalizedEigenSelectedCompressedDetMinimal
        (reducedRankAperpPencilA (reducedRankTildeE X Z Y))
        (reducedRankAperpPencilB (reducedRankTildeY Z Y)) Aperp)
    (W : Matrix m r ℝ)
    (hLambda : ∀ j, 0 < lambda j)
    (hDual : reducedRankDualEigenvectorRelation
      (reducedRankTildeX Z X) (reducedRankTildeY Z Y) G W (Matrix.diagonal lambda))
    (hOrth : reducedRankAperpYOrthogonal (reducedRankTildeY Z Y) Aperp W) :
    ReducedRankHansenSmallestSummaryCompatibilityExactDimension
      Z X (reducedRankTildeX Z X) Y (reducedRankTildeY Z Y) (reducedRankTildeE X Z Y) G
      ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G)
      (reducedRankChat Z X Y G
        ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G))
      ((Fintype.card n : ℝ)⁻¹ •
        ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeY Z Y) -
          ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G) *
            ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G)ᵀ))
      Aperp lambda eta (reducedRankMaximizedLogLikelihood (reducedRankTildeY Z Y) lambda) :=
  reducedRankHansenTheorem11_7_exactDimension_of_selectedExtrema_diagonalDual_pos_canonicalAperp
    Z X (reducedRankTildeX Z X) Y (reducedRankTildeY Z Y) (reducedRankTildeE X Z Y)
    G lambda Aperp eta hG hGNorm hGMax hAperp hAperpNorm hAperpMin
    W hLambda hDual hOrth

/-- Residualized Hansen Theorem 11.7 endpoint from the ordered
generalized-eigenvalue min-max certificate, routed through the objective-extrema
constructor. -/
theorem reducedRankHansenTheorem11_7_residualized_of_orderedGeneralizedEigen_minMax_certificate
    (Z : Matrix n ell ℝ) (X : Matrix n k ℝ) (Y : Matrix n m ℝ)
    [DecidableEq k]
    [Invertible (Zᵀ * Z)]
    [Invertible ((Matrix.fromCols X Z)ᵀ * Matrix.fromCols X Z)]
    (G : Matrix k r ℝ) (lambda : r → ℝ)
    (Aperp : Matrix m s ℝ) (eta : s → ℝ)
    (hMinMax : ReducedRankHansenDetProductMinMaxCertificate
      (reducedRankTildeX Z X) (reducedRankTildeY Z Y) (reducedRankTildeE X Z Y)
      G lambda Aperp eta) :
    ReducedRankHansenSmallestSummaryCompatibility
      Z X (reducedRankTildeX Z X) Y (reducedRankTildeY Z Y)
      (reducedRankTildeE X Z Y) G
      ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G)
      (reducedRankChat Z X Y G
        ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G))
      ((Fintype.card n : ℝ)⁻¹ •
        ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeY Z Y) -
          ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G) *
            ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G)ᵀ))
      Aperp lambda eta (reducedRankMaximizedLogLikelihood (reducedRankTildeY Z Y) lambda) :=
  reducedRankHansenTheorem11_7_of_orderedGeneralizedEigen_minMax_certificate
    Z X (reducedRankTildeX Z X) Y (reducedRankTildeY Z Y) (reducedRankTildeE X Z Y)
    G lambda Aperp eta hMinMax

/-- Residualized Hansen Theorem 11.7 from the raw ordered
generalized-eigenvalue min-max surface. -/
theorem reducedRankHansenTheorem11_7_residualized_of_orderedGeneralizedEigen_certificate
    (Z : Matrix n ell ℝ) (X : Matrix n k ℝ) (Y : Matrix n m ℝ)
    [DecidableEq k]
    [Invertible (Zᵀ * Z)]
    [Invertible ((Matrix.fromCols X Z)ᵀ * Matrix.fromCols X Z)]
    (G : Matrix k r ℝ) (lambda : r → ℝ)
    (Aperp : Matrix m s ℝ) (eta : s → ℝ)
    (hOrdered : ReducedRankHansenOrderedGeneralizedEigenMinMaxCertificate
      (reducedRankTildeX Z X) (reducedRankTildeY Z Y) (reducedRankTildeE X Z Y)
      G lambda Aperp eta) :
    ReducedRankHansenSmallestSummaryCompatibility
      Z X (reducedRankTildeX Z X) Y (reducedRankTildeY Z Y)
      (reducedRankTildeE X Z Y) G
      ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G)
      (reducedRankChat Z X Y G
        ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G))
      ((Fintype.card n : ℝ)⁻¹ •
        ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeY Z Y) -
          ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G) *
            ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G)ᵀ))
      Aperp lambda eta (reducedRankMaximizedLogLikelihood (reducedRankTildeY Z Y) lambda) :=
  reducedRankHansenTheorem11_7_residualized_of_orderedGeneralizedEigen_minMax_certificate
    Z X Y G lambda Aperp eta hOrdered.to_detProductMinMaxCertificate

/-- Residualized Hansen Theorem 11.7 from the ordered min-max certificate, with
the exact `A⊥` dimension `m - r` carried explicitly. -/
theorem reducedRankHansenTheorem11_7_residualized_exactDimension_of_minMax_certificate
    (Z : Matrix n ell ℝ) (X : Matrix n k ℝ) (Y : Matrix n m ℝ)
    [DecidableEq k]
    [Invertible (Zᵀ * Z)]
    [Invertible ((Matrix.fromCols X Z)ᵀ * Matrix.fromCols X Z)]
    (G : Matrix k r ℝ) (lambda : r → ℝ)
    (Aperp : Matrix m s ℝ) (eta : s → ℝ)
    (hMinMax : ReducedRankHansenDetProductMinMaxCertificate
      (reducedRankTildeX Z X) (reducedRankTildeY Z Y) (reducedRankTildeE X Z Y)
      G lambda Aperp eta)
    (hdim : Fintype.card s = Fintype.card m - Fintype.card r) :
    ReducedRankHansenSmallestSummaryCompatibilityExactDimension
      Z X (reducedRankTildeX Z X) Y (reducedRankTildeY Z Y) (reducedRankTildeE X Z Y) G
      ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G)
      (reducedRankChat Z X Y G
        ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G))
      ((Fintype.card n : ℝ)⁻¹ •
        ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeY Z Y) -
          ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G) *
            ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G)ᵀ))
      Aperp lambda eta (reducedRankMaximizedLogLikelihood (reducedRankTildeY Z Y) lambda) :=
  ReducedRankHansenSmallestSummaryCompatibilityExactDimension.of_theorem11_7
    (reducedRankHansenTheorem11_7_residualized_of_orderedGeneralizedEigen_minMax_certificate
      Z X Y G lambda Aperp eta hMinMax)
    hdim

set_option linter.style.longLine false in
/-- Residualized Hansen Theorem 11.7 from the raw ordered generalized-eigenvalue
min-max surface, with Hansen's exact `dim(A⊥) = m - r` equality attached. -/
theorem reducedRankHansenTheorem11_7_residualized_exactDimension_of_orderedGeneralizedEigen_certificate
    (Z : Matrix n ell ℝ) (X : Matrix n k ℝ) (Y : Matrix n m ℝ)
    [DecidableEq k]
    [Invertible (Zᵀ * Z)]
    [Invertible ((Matrix.fromCols X Z)ᵀ * Matrix.fromCols X Z)]
    (G : Matrix k r ℝ) (lambda : r → ℝ)
    (Aperp : Matrix m s ℝ) (eta : s → ℝ)
    (hOrdered : ReducedRankHansenOrderedGeneralizedEigenMinMaxCertificate
      (reducedRankTildeX Z X) (reducedRankTildeY Z Y) (reducedRankTildeE X Z Y)
      G lambda Aperp eta)
    (hdim : Fintype.card s = Fintype.card m - Fintype.card r) :
    ReducedRankHansenSmallestSummaryCompatibilityExactDimension
      Z X (reducedRankTildeX Z X) Y (reducedRankTildeY Z Y) (reducedRankTildeE X Z Y) G
      ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G)
      (reducedRankChat Z X Y G
        ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G))
      ((Fintype.card n : ℝ)⁻¹ •
        ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeY Z Y) -
          ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G) *
            ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G)ᵀ))
      Aperp lambda eta (reducedRankMaximizedLogLikelihood (reducedRankTildeY Z Y) lambda) :=
  ReducedRankHansenSmallestSummaryCompatibilityExactDimension.of_theorem11_7
    (reducedRankHansenTheorem11_7_residualized_of_orderedGeneralizedEigen_certificate
      Z X Y G lambda Aperp eta hOrdered)
    hdim

set_option linter.style.longLine false in
/-- Residualized Hansen Theorem 11.7 from the raw ordered generalized-eigenvalue
min-max surface, diagonal dual relation, nonzero selected-root product, and a
concrete finite index split `m ≃ r ⊕ s`.

This is the residualized counterpart of
`reducedRankHansenTheorem11_7_exactDimension_of_orderedGeneralizedEigen_diagonalDual_prod_ne_zero_indexSplit`;
it packages the current closest raw spectral input to Hansen's statement
without separately asking for product-bound fields, pointwise root
nonsingularity, or the computed complementary-rank equality. -/
theorem
    reducedRankHansenTheorem11_7_residualized_exactDimension_of_orderedGeneralizedEigen_diagonalDual_prod_ne_zero_indexSplit
    (Z : Matrix n ell ℝ) (X : Matrix n k ℝ) (Y : Matrix n m ℝ)
    [DecidableEq k]
    [Invertible (Zᵀ * Z)]
    [Invertible ((Matrix.fromCols X Z)ᵀ * Matrix.fromCols X Z)]
    (G : Matrix k r ℝ) (lambda : r → ℝ)
    (Aperp : Matrix m s ℝ) (eta : s → ℝ)
    (hOrdered : ReducedRankHansenOrderedGeneralizedEigenMinMaxCertificate
      (reducedRankTildeX Z X) (reducedRankTildeY Z Y) (reducedRankTildeE X Z Y)
      G lambda Aperp eta)
    (W : Matrix m r ℝ)
    (hLambdaProd : (∏ j, lambda j) ≠ 0)
    (hDual : reducedRankDualEigenvectorRelation
      (reducedRankTildeX Z X) (reducedRankTildeY Z Y) G W (Matrix.diagonal lambda))
    (hOrth : reducedRankAperpYOrthogonal (reducedRankTildeY Z Y) Aperp W)
    (hIndex : m ≃ Sum r s) :
    ReducedRankHansenSmallestSummaryCompatibilityExactDimension
      Z X (reducedRankTildeX Z X) Y (reducedRankTildeY Z Y) (reducedRankTildeE X Z Y) G
      ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G)
      (reducedRankChat Z X Y G
        ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G))
      ((Fintype.card n : ℝ)⁻¹ •
        ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeY Z Y) -
          ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G) *
            ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G)ᵀ))
      Aperp lambda eta (reducedRankMaximizedLogLikelihood (reducedRankTildeY Z Y) lambda) :=
  reducedRankHansenTheorem11_7_exactDimension_of_orderedGeneralizedEigen_diagonalDual_prod_ne_zero_indexSplit
    Z X (reducedRankTildeX Z X) Y (reducedRankTildeY Z Y) (reducedRankTildeE X Z Y)
    G lambda Aperp eta hOrdered W hLambdaProd hDual hOrth hIndex

set_option linter.style.longLine false in
/-- Residualized compressed-determinant and index-split version of
`reducedRankHansenTheorem11_7_residualized_exactDimension_of_orderedGeneralizedEigen_diagonalDual_prod_ne_zero_indexSplit`.

This is the residualized ordered-certificate surface when the raw generalized
pencil construction proves nonsingularity of the selected compressed `G`
determinant instead of returning `∏ λ_j ≠ 0` explicitly. -/
theorem
    reducedRankHansenTheorem11_7_residualized_exactDimension_of_orderedGeneralizedEigen_diagonalDual_compressedDet_ne_zero_indexSplit
    (Z : Matrix n ell ℝ) (X : Matrix n k ℝ) (Y : Matrix n m ℝ)
    [DecidableEq k]
    [Invertible (Zᵀ * Z)]
    [Invertible ((Matrix.fromCols X Z)ᵀ * Matrix.fromCols X Z)]
    (G : Matrix k r ℝ) (lambda : r → ℝ)
    (Aperp : Matrix m s ℝ) (eta : s → ℝ)
    (hOrdered : ReducedRankHansenOrderedGeneralizedEigenMinMaxCertificate
      (reducedRankTildeX Z X) (reducedRankTildeY Z Y) (reducedRankTildeE X Z Y)
      G lambda Aperp eta)
    (W : Matrix m r ℝ)
    (hGdet :
      (Gᵀ * reducedRankGPencilA (reducedRankTildeX Z X) (reducedRankTildeY Z Y) * G).det ≠
        0)
    (hDual : reducedRankDualEigenvectorRelation
      (reducedRankTildeX Z X) (reducedRankTildeY Z Y) G W (Matrix.diagonal lambda))
    (hOrth : reducedRankAperpYOrthogonal (reducedRankTildeY Z Y) Aperp W)
    (hIndex : m ≃ Sum r s) :
    ReducedRankHansenSmallestSummaryCompatibilityExactDimension
      Z X (reducedRankTildeX Z X) Y (reducedRankTildeY Z Y) (reducedRankTildeE X Z Y) G
      ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G)
      (reducedRankChat Z X Y G
        ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G))
      ((Fintype.card n : ℝ)⁻¹ •
        ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeY Z Y) -
          ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G) *
            ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G)ᵀ))
      Aperp lambda eta (reducedRankMaximizedLogLikelihood (reducedRankTildeY Z Y) lambda) :=
  reducedRankHansenTheorem11_7_residualized_exactDimension_of_orderedGeneralizedEigen_diagonalDual_prod_ne_zero_indexSplit
    Z X Y G lambda Aperp eta hOrdered W
    (hOrdered.g_ordered.rootProduct_ne_zero_of_compressedDet_ne_zero hGdet)
    hDual hOrth hIndex

set_option linter.style.longLine false in
/-- Residualized Hansen Theorem 11.7 from the raw ordered generalized-eigenvalue
min-max surface, diagonal dual relation, positive selected `G` roots, and a
concrete finite index split.

This is the residualized positive-root counterpart of
`reducedRankHansenTheorem11_7_exactDimension_of_orderedGeneralizedEigen_diagonalDual_pos_indexSplit`. -/
theorem
    reducedRankHansenTheorem11_7_residualized_exactDimension_of_orderedGeneralizedEigen_diagonalDual_pos_indexSplit
    (Z : Matrix n ell ℝ) (X : Matrix n k ℝ) (Y : Matrix n m ℝ)
    [DecidableEq k]
    [Invertible (Zᵀ * Z)]
    [Invertible ((Matrix.fromCols X Z)ᵀ * Matrix.fromCols X Z)]
    (G : Matrix k r ℝ) (lambda : r → ℝ)
    (Aperp : Matrix m s ℝ) (eta : s → ℝ)
    (hOrdered : ReducedRankHansenOrderedGeneralizedEigenMinMaxCertificate
      (reducedRankTildeX Z X) (reducedRankTildeY Z Y) (reducedRankTildeE X Z Y)
      G lambda Aperp eta)
    (W : Matrix m r ℝ)
    (hLambda : ∀ j, 0 < lambda j)
    (hDual : reducedRankDualEigenvectorRelation
      (reducedRankTildeX Z X) (reducedRankTildeY Z Y) G W (Matrix.diagonal lambda))
    (hOrth : reducedRankAperpYOrthogonal (reducedRankTildeY Z Y) Aperp W)
    (hIndex : m ≃ Sum r s) :
    ReducedRankHansenSmallestSummaryCompatibilityExactDimension
      Z X (reducedRankTildeX Z X) Y (reducedRankTildeY Z Y) (reducedRankTildeE X Z Y) G
      ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G)
      (reducedRankChat Z X Y G
        ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G))
      ((Fintype.card n : ℝ)⁻¹ •
        ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeY Z Y) -
          ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G) *
            ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G)ᵀ))
      Aperp lambda eta (reducedRankMaximizedLogLikelihood (reducedRankTildeY Z Y) lambda) :=
  reducedRankHansenTheorem11_7_residualized_exactDimension_of_orderedGeneralizedEigen_diagonalDual_prod_ne_zero_indexSplit
    Z X Y G lambda Aperp eta hOrdered W
    (reducedRankSelectedRootProduct_ne_zero_of_pos lambda hLambda)
    hDual hOrth hIndex

set_option linter.style.longLine false in
/-- Residualized Hansen Theorem 11.7 from the raw ordered generalized-eigenvalue
min-max surface, diagonal dual relation, and nonzero selected-root product,
using the canonical `A⊥` index `Fin (card m - card r)`.

This is the residualized counterpart of
`reducedRankHansenTheorem11_7_exactDimension_of_orderedGeneralizedEigen_diagonalDual_prod_ne_zero_canonicalAperp`;
it removes the explicit finite split premise from the actual Hansen
residualized matrices. -/
theorem
    reducedRankHansenTheorem11_7_residualized_exactDimension_of_orderedGeneralizedEigen_diagonalDual_prod_ne_zero_canonicalAperp
    (Z : Matrix n ell ℝ) (X : Matrix n k ℝ) (Y : Matrix n m ℝ)
    [DecidableEq k]
    [Invertible (Zᵀ * Z)]
    [Invertible ((Matrix.fromCols X Z)ᵀ * Matrix.fromCols X Z)]
    (G : Matrix k r ℝ) (lambda : r → ℝ)
    (Aperp : Matrix m (reducedRankAperpIndex m r) ℝ)
    (eta : reducedRankAperpIndex m r → ℝ)
    (hOrdered : ReducedRankHansenOrderedGeneralizedEigenMinMaxCertificate
      (reducedRankTildeX Z X) (reducedRankTildeY Z Y) (reducedRankTildeE X Z Y)
      G lambda Aperp eta)
    (W : Matrix m r ℝ)
    (hLambdaProd : (∏ j, lambda j) ≠ 0)
    (hDual : reducedRankDualEigenvectorRelation
      (reducedRankTildeX Z X) (reducedRankTildeY Z Y) G W (Matrix.diagonal lambda))
    (hOrth : reducedRankAperpYOrthogonal (reducedRankTildeY Z Y) Aperp W) :
    ReducedRankHansenSmallestSummaryCompatibilityExactDimension
      Z X (reducedRankTildeX Z X) Y (reducedRankTildeY Z Y) (reducedRankTildeE X Z Y) G
      ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G)
      (reducedRankChat Z X Y G
        ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G))
      ((Fintype.card n : ℝ)⁻¹ •
        ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeY Z Y) -
          ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G) *
            ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G)ᵀ))
      Aperp lambda eta (reducedRankMaximizedLogLikelihood (reducedRankTildeY Z Y) lambda) :=
  reducedRankHansenTheorem11_7_exactDimension_of_orderedGeneralizedEigen_diagonalDual_prod_ne_zero_canonicalAperp
    Z X (reducedRankTildeX Z X) Y (reducedRankTildeY Z Y) (reducedRankTildeE X Z Y)
    G lambda Aperp eta hOrdered W hLambdaProd hDual hOrth

set_option linter.style.longLine false in
/-- Residualized positive-root canonical-`A⊥` version of
`reducedRankHansenTheorem11_7_residualized_exactDimension_of_orderedGeneralizedEigen_diagonalDual_prod_ne_zero_canonicalAperp`. -/
theorem
    reducedRankHansenTheorem11_7_residualized_exactDimension_of_orderedGeneralizedEigen_diagonalDual_pos_canonicalAperp
    (Z : Matrix n ell ℝ) (X : Matrix n k ℝ) (Y : Matrix n m ℝ)
    [DecidableEq k]
    [Invertible (Zᵀ * Z)]
    [Invertible ((Matrix.fromCols X Z)ᵀ * Matrix.fromCols X Z)]
    (G : Matrix k r ℝ) (lambda : r → ℝ)
    (Aperp : Matrix m (reducedRankAperpIndex m r) ℝ)
    (eta : reducedRankAperpIndex m r → ℝ)
    (hOrdered : ReducedRankHansenOrderedGeneralizedEigenMinMaxCertificate
      (reducedRankTildeX Z X) (reducedRankTildeY Z Y) (reducedRankTildeE X Z Y)
      G lambda Aperp eta)
    (W : Matrix m r ℝ)
    (hLambda : ∀ j, 0 < lambda j)
    (hDual : reducedRankDualEigenvectorRelation
      (reducedRankTildeX Z X) (reducedRankTildeY Z Y) G W (Matrix.diagonal lambda))
    (hOrth : reducedRankAperpYOrthogonal (reducedRankTildeY Z Y) Aperp W) :
    ReducedRankHansenSmallestSummaryCompatibilityExactDimension
      Z X (reducedRankTildeX Z X) Y (reducedRankTildeY Z Y) (reducedRankTildeE X Z Y) G
      ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G)
      (reducedRankChat Z X Y G
        ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G))
      ((Fintype.card n : ℝ)⁻¹ •
        ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeY Z Y) -
          ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G) *
            ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G)ᵀ))
      Aperp lambda eta (reducedRankMaximizedLogLikelihood (reducedRankTildeY Z Y) lambda) :=
  reducedRankHansenTheorem11_7_residualized_exactDimension_of_orderedGeneralizedEigen_diagonalDual_prod_ne_zero_canonicalAperp
    Z X Y G lambda Aperp eta hOrdered W
    (reducedRankSelectedRootProduct_ne_zero_of_pos lambda hLambda)
    hDual hOrth

set_option linter.style.longLine false in
/-- Residualized canonical-`A⊥` endpoint where selected-root nonsingularity is
derived from the nonzero selected compressed determinant. -/
theorem
    reducedRankHansenTheorem11_7_residualized_exactDimension_of_orderedGeneralizedEigen_diagonalDual_compressedDet_ne_zero_canonicalAperp
    (Z : Matrix n ell ℝ) (X : Matrix n k ℝ) (Y : Matrix n m ℝ)
    [DecidableEq k]
    [Invertible (Zᵀ * Z)]
    [Invertible ((Matrix.fromCols X Z)ᵀ * Matrix.fromCols X Z)]
    (G : Matrix k r ℝ) (lambda : r → ℝ)
    (Aperp : Matrix m (reducedRankAperpIndex m r) ℝ)
    (eta : reducedRankAperpIndex m r → ℝ)
    (hOrdered : ReducedRankHansenOrderedGeneralizedEigenMinMaxCertificate
      (reducedRankTildeX Z X) (reducedRankTildeY Z Y) (reducedRankTildeE X Z Y)
      G lambda Aperp eta)
    (W : Matrix m r ℝ)
    (hGdet :
      (Gᵀ * reducedRankGPencilA (reducedRankTildeX Z X) (reducedRankTildeY Z Y) * G).det ≠
        0)
    (hDual : reducedRankDualEigenvectorRelation
      (reducedRankTildeX Z X) (reducedRankTildeY Z Y) G W (Matrix.diagonal lambda))
    (hOrth : reducedRankAperpYOrthogonal (reducedRankTildeY Z Y) Aperp W) :
    ReducedRankHansenSmallestSummaryCompatibilityExactDimension
      Z X (reducedRankTildeX Z X) Y (reducedRankTildeY Z Y) (reducedRankTildeE X Z Y) G
      ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G)
      (reducedRankChat Z X Y G
        ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G))
      ((Fintype.card n : ℝ)⁻¹ •
        ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeY Z Y) -
          ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G) *
            ((reducedRankTildeY Z Y)ᵀ * (reducedRankTildeX Z X) * G)ᵀ))
      Aperp lambda eta (reducedRankMaximizedLogLikelihood (reducedRankTildeY Z Y) lambda) :=
  reducedRankHansenTheorem11_7_residualized_exactDimension_of_orderedGeneralizedEigen_diagonalDual_prod_ne_zero_canonicalAperp
    Z X Y G lambda Aperp eta hOrdered W
    (hOrdered.g_ordered.rootProduct_ne_zero_of_compressedDet_ne_zero hGdet)
    hDual hOrth

end HansenTheorem11_7Conclusion

end HansenObjectiveCertificate

end HansenEconometrics
