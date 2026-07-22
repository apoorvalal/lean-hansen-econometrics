import HansenEconometrics.Chapter11MultivariateRegression.ReducedRank

/-!
# Chapter 11 — joint reduced-rank spectrum

This module constructs the primal and dual spectral blocks in Hansen Theorem
11.7 simultaneously.  The joint construction is needed when a selected
canonical-correlation root is tied with the first omitted root: independently
chosen determinant maximizers need not satisfy Hansen's identifying
orthogonality inside that tied eigenspace.

The proof works after positive-definite whitening.  It transfers the common
nonzero spectrum of the two rectangular Gram matrices, normalizes the selected
dual block, splits one ordered right-Gram eigenbasis at the rank boundary, and
transports its reversed tail back to the residual generalized pencil. The
public endpoint
returns the canonical `m - r` block together with both global determinant
maxima and the same G-side complement-determinant minimum consumed by the raw
Gaussian likelihood proof.
-/

open scoped Matrix MatrixOrder

namespace HansenEconometrics

open Matrix

/-- Citeable ordered-root witness for Hansen's two residualized generalized
eigenvalue pencils.

The matrices `Sx` and `Sy` whiten the two positive-definite denominator Grams,
and `D` is the resulting rectangular cross matrix. Thus the displayed
equalities identify `lambda` and `eta` pointwise with the leading ordered roots
used in equations (11.20) and (11.21), rather than merely characterizing their
eigenspaces variationally. -/
def ReducedRankHansenOrderedRootWitness
    {n k m r s : Type*}
    [Fintype n]
    [Fintype k] [DecidableEq k]
    [Fintype m] [DecidableEq m]
    [Fintype r] [Fintype s]
    (Xtilde : Matrix n k ℝ) (Ytilde : Matrix n m ℝ)
    (lambda : r → ℝ) (eta : s → ℝ) : Prop :=
  ∃ (hrk : Fintype.card r ≤ Fintype.card k)
      (hsm : Fintype.card s ≤ Fintype.card m)
      (Sx : Matrix k k ℝ) (Sy : Matrix m m ℝ) (D : Matrix k m ℝ),
    Sxᵀ * (Xtildeᵀ * Xtilde) * Sx = 1 ∧
    Syᵀ * (Ytildeᵀ * Ytilde) * Sy = 1 ∧
    D = Sxᵀ * (Xtildeᵀ * Ytilde) * Sy ∧
    (∀ j, lambda j =
      (mul_transpose_isHermitian D).eigenvalues₀
        (Fin.castLE hrk ((Fintype.equivFin r) j))) ∧
    (∀ j, eta j =
      (isHermitian_one.sub (transpose_mul_isHermitian D)).eigenvalues₀
        (Fin.castLE hsm ((Fintype.equivFin s) j)))

/-- An explicit two-sided whitening of a positive-definite real matrix. -/
private structure PosDefWhitening {k : Type*} [Fintype k] [DecidableEq k]
    (B : Matrix k k ℝ) where
  T : Matrix k k ℝ
  S : Matrix k k ℝ
  factor : B = Tᵀ * T
  inv_mul : S * T = 1
  mul_inv : T * S = 1

attribute [simp] PosDefWhitening.inv_mul PosDefWhitening.mul_inv

@[simp]
private theorem PosDefWhitening.transpose_inv_mul
    {k : Type*} [Fintype k] [DecidableEq k]
    {B : Matrix k k ℝ} (w : PosDefWhitening B) :
    w.Tᵀ * w.Sᵀ = 1 := by
  rw [← Matrix.transpose_mul, w.inv_mul, Matrix.transpose_one]

@[simp]
private theorem PosDefWhitening.transpose_mul_inv
    {k : Type*} [Fintype k] [DecidableEq k]
    {B : Matrix k k ℝ} (w : PosDefWhitening B) :
    w.Sᵀ * w.Tᵀ = 1 := by
  rw [← Matrix.transpose_mul, w.mul_inv, Matrix.transpose_one]

/-- Mathlib's strictly-positive factorization supplies a two-sided whitening. -/
private theorem PosDefWhitening.exists {k : Type*}
    [Fintype k] [DecidableEq k] (B : Matrix k k ℝ) (hB : B.PosDef) :
    Nonempty (PosDefWhitening B) := by
  obtain ⟨T, hTunit, hBT⟩ :=
    CStarAlgebra.isStrictlyPositive_iff_eq_star_mul_self.mp hB.isStrictlyPositive
  have hFactor : B = Tᵀ * T := by
    simpa [star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
      using hBT
  have hTdet : IsUnit T.det := (Matrix.isUnit_iff_isUnit_det T).mp hTunit
  exact ⟨{
    T := T
    S := T⁻¹
    factor := hFactor
    inv_mul := Matrix.nonsing_inv_mul T hTdet
    mul_inv := Matrix.mul_nonsing_inv T hTdet
  }⟩

/-- The inverse of a positive-definite Gram factor is the expected whitening
congruence. -/
private theorem PosDefWhitening.nonsingInv_eq
    {k : Type*} [Fintype k] [DecidableEq k]
    {B : Matrix k k ℝ} (w : PosDefWhitening B) :
    B⁻¹ = w.S * w.Sᵀ := by
  simpa [← w.factor] using nonsingInv_conjugate_of_inverse
    (1 : Matrix k k ℝ) w.T w.S w.inv_mul w.mul_inv (by simp)

private theorem PosDefWhitening.T_det_isUnit
    {k : Type*} [Fintype k] [DecidableEq k]
    {B : Matrix k k ℝ} (w : PosDefWhitening B) : IsUnit w.T.det :=
  (Matrix.isUnit_iff_isUnit_det w.T).mp
    (isUnit_iff_exists.mpr ⟨w.S, w.mul_inv, w.inv_mul⟩)

private theorem PosDefWhitening.S_det_isUnit
    {k : Type*} [Fintype k] [DecidableEq k]
    {B : Matrix k k ℝ} (w : PosDefWhitening B) : IsUnit w.S.det :=
  (Matrix.isUnit_iff_isUnit_det w.S).mp
    (isUnit_iff_exists.mpr ⟨w.T, w.inv_mul, w.mul_inv⟩)

private theorem PosDefWhitening.S_mulVec_injective
    {k : Type*} [Fintype k] [DecidableEq k]
    {B : Matrix k k ℝ} (w : PosDefWhitening B) :
    Function.Injective w.S.mulVec :=
  Matrix.mulVec_injective_of_isUnit
    ((Matrix.isUnit_iff_isUnit_det w.S).mpr w.S_det_isUnit)

/-- The inverse factor whitens the original positive-definite matrix. -/
private theorem PosDefWhitening.whitened
    {k : Type*} [Fintype k] [DecidableEq k]
    {B : Matrix k k ℝ} (w : PosDefWhitening B) :
    w.Sᵀ * B * w.S = 1 := by
  calc
    w.Sᵀ * B * w.S = w.Sᵀ * (w.Tᵀ * w.T) * w.S :=
      congrArg (fun C : Matrix k k ℝ => w.Sᵀ * C * w.S) w.factor
    w.Sᵀ * (w.Tᵀ * w.T) * w.S = (w.T * w.S)ᵀ * (w.T * w.S) := by
      simp only [Matrix.transpose_mul, Matrix.mul_assoc]
    _ = 1 := by simp

/-- Invertible left and right whitenings preserve the rank of a rectangular
cross matrix. -/
private theorem whitenedCross_rank
    {k m : Type*}
    [Fintype k] [DecidableEq k] [Fintype m] [DecidableEq m]
    {Bx : Matrix k k ℝ} {By : Matrix m m ℝ}
    (wx : PosDefWhitening Bx) (wy : PosDefWhitening By)
    (C : Matrix k m ℝ) :
    (wx.Sᵀ * C * wy.S).rank = C.rank := by
  calc
    (wx.Sᵀ * C * wy.S).rank = (wx.Sᵀ * C).rank :=
      Matrix.rank_mul_eq_left_of_isUnit_det wy.S (wx.Sᵀ * C) wy.S_det_isUnit
    _ = C.rank :=
      Matrix.rank_mul_eq_right_of_isUnit_det wx.Sᵀ C (by
        simpa [Matrix.det_transpose] using wx.S_det_isUnit)

private theorem PosDefWhitening.factor_of_whitened
    {k : Type*} [Fintype k] [DecidableEq k]
    {B : Matrix k k ℝ} (w : PosDefWhitening B)
    (A M : Matrix k k ℝ) (hM : M = w.Sᵀ * A * w.S) :
    A = w.Tᵀ * M * w.T := by
  calc
    A = (w.S * w.T)ᵀ * A * (w.S * w.T) := by simp
    _ = w.Tᵀ * (w.Sᵀ * A * w.S) * w.T := by
      simp only [Matrix.transpose_mul, Matrix.mul_assoc]
    _ = w.Tᵀ * M * w.T := by rw [← hM]

/-- Canonical split of the right Gram eigenbasis into the selected leading
block and the reversed complementary tail.

The two blocks are selected from one orthonormal basis, so their cross Gram is
zero even when an eigenvalue is tied across the split. The complementary block
is reversed because it becomes the leading block of `I - DᵀD`. -/
private theorem rectangularGramCanonicalSplit_exists
    {k m r s : Type*}
    [Fintype k] [DecidableEq k]
    [Fintype m] [DecidableEq m]
    [Fintype r] [DecidableEq r]
    [Fintype s] [DecidableEq s]
    (D : Matrix k m ℝ)
    (hrk : Fintype.card r ≤ Fintype.card k)
    (hrm : Fintype.card r ≤ Fintype.card m)
    (hdim : Fintype.card s = Fintype.card m - Fintype.card r) :
    ∃ (lambda : r → ℝ) (mu : s → ℝ)
        (V : Matrix m r ℝ) (Q : Matrix m s ℝ),
      (∀ j, lambda j =
        (mul_transpose_isHermitian D).eigenvalues₀
          (Fin.castLE hrk ((Fintype.equivFin r) j))) ∧
      Vᵀ * V = 1 ∧
      (Dᵀ * D) * V = V * Matrix.diagonal lambda ∧
      Qᵀ * Q = 1 ∧
      (Dᵀ * D) * Q = Q * Matrix.diagonal mu ∧
      Qᵀ * V = 0 ∧
      (∀ j, 1 - mu j =
        (isHermitian_one.sub (transpose_mul_isHermitian D)).eigenvalues₀
          (Fin.castLE (by omega : Fintype.card s ≤ Fintype.card m)
            ((Fintype.equivFin s) j))) := by
  classical
  let hK : (Dᵀ * D).IsHermitian := transpose_mul_isHermitian D
  let e : Fin (Fintype.card m) ≃ m :=
    Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card m))
  let selected : r → Fin (Fintype.card m) := fun j =>
    Fin.castLE hrm ((Fintype.equivFin r) j)
  have hsm : Fintype.card s ≤ Fintype.card m := by omega
  let complement : s → Fin (Fintype.card m) := fun j =>
    Fin.rev (Fin.castLE hsm ((Fintype.equivFin s) j))
  have hSelectedInjective : Function.Injective selected := by
    intro i j hij
    apply (Fintype.equivFin r).injective
    exact Fin.castLE_injective hrm hij
  have hComplementInjective : Function.Injective complement := by
    intro i j hij
    apply (Fintype.equivFin s).injective
    apply Fin.castLE_injective hsm
    exact Fin.rev_injective hij
  have hSelectedComplement : ∀ i j, selected i ≠ complement j := by
    intro i j hij
    have hi : (selected i).val < Fintype.card r := by
      simp [selected]
    have hj : Fintype.card r ≤ (complement j).val := by
      simp only [complement, Fin.val_rev, Fin.val_castLE]
      have hslt : ((Fintype.equivFin s) j).val <
          Fintype.card m - Fintype.card r := by
        simpa [hdim] using ((Fintype.equivFin s) j).isLt
      omega
    have := congrArg Fin.val hij
    omega
  let lambda : r → ℝ := fun j =>
    (mul_transpose_isHermitian D).eigenvalues₀
      (Fin.castLE hrk ((Fintype.equivFin r) j))
  let mu : s → ℝ := fun j => hK.eigenvalues₀ (complement j)
  let V : Matrix m r ℝ := fun i j =>
    (hK.eigenvectorBasis (e (selected j)) : EuclideanSpace ℝ m) i
  let Q : Matrix m s ℝ := fun i j =>
    (hK.eigenvectorBasis (e (complement j)) : EuclideanSpace ℝ m) i
  have hTransfer : ∀ j, hK.eigenvalues₀ (selected j) = lambda j := by
    intro j
    let t : Fin (Fintype.card r) := (Fintype.equivFin r) j
    have htk : t.val < Fintype.card k := lt_of_lt_of_le t.isLt hrk
    have htm : t.val < Fintype.card m := lt_of_lt_of_le t.isLt hrm
    simpa [hK, selected, lambda, t] using
      (mul_transpose_eigenvalues₀_eq_of_lt D t.val htk htm).symm
  have hVBlock := hermitianEigenvectorBasis_columnBlock
    (Dᵀ * D) hK selected hSelectedInjective
  have hVNorm : Vᵀ * V = 1 := by
    simpa [V, e] using hVBlock.1
  have hVEig : (Dᵀ * D) * V = V * Matrix.diagonal lambda := by
    simpa [V, e, hTransfer] using hVBlock.2
  have hQBlock := hermitianEigenvectorBasis_columnBlock
    (Dᵀ * D) hK complement hComplementInjective
  have hQNorm : Qᵀ * Q = 1 := by
    simpa [Q, e] using hQBlock.1
  have hQEig : (Dᵀ * D) * Q = Q * Matrix.diagonal mu := by
    simpa [Q, e, mu] using hQBlock.2
  have hCross : Qᵀ * V = 0 := by
    simpa [Q, V, e] using
      hermitianEigenvectorBasis_crossGram_eq_zero
        (Dᵀ * D) hK selected complement hSelectedComplement
  have hResidualRoots : ∀ j, 1 - mu j =
      (isHermitian_one.sub (transpose_mul_isHermitian D)).eigenvalues₀
        (Fin.castLE hsm ((Fintype.equivFin s) j)) := by
    intro j
    have hroot := one_sub_ordered_eigenvalues₀_apply hK
      (Fin.castLE hsm ((Fintype.equivFin s) j))
    simpa [hK, mu, complement] using hroot.symm
  exact ⟨lambda, mu, V, Q, fun _ => rfl, hVNorm, hVEig,
    hQNorm, hQEig, hCross, hResidualRoots⟩

/-- Positive right-Gram eigenvectors transport to normalized left-Gram
eigenvectors with the same roots.

The retained identity `DᵀU = V diag(sqrt λ)` is the finite-dimensional
singular-vector relation used to transport Hansen's identifying
orthogonality. -/
private theorem normalizedLeftGramBlock_exists
    {k m r : Type*}
    [Fintype k] [Fintype m]
    [Fintype r] [DecidableEq r]
    (D : Matrix k m ℝ) (lambda : r → ℝ) (V : Matrix m r ℝ)
    (hPos : ∀ j, 0 < lambda j)
    (hVNorm : Vᵀ * V = 1)
    (hVEig : (Dᵀ * D) * V = V * Matrix.diagonal lambda) :
    ∃ U : Matrix k r ℝ,
      Uᵀ * U = 1 ∧
        (D * Dᵀ) * U = U * Matrix.diagonal lambda ∧
        Dᵀ * U = V * Matrix.diagonal (fun j => Real.sqrt (lambda j)) := by
  classical
  let a : r → ℝ := fun j => (Real.sqrt (lambda j))⁻¹
  let U : Matrix k r ℝ := D * V * Matrix.diagonal a
  have hsqrt_ne : ∀ j, Real.sqrt (lambda j) ≠ 0 := fun j =>
    ne_of_gt (Real.sqrt_pos.2 (hPos j))
  have hsqrt_sq : ∀ j, Real.sqrt (lambda j) * Real.sqrt (lambda j) = lambda j :=
    fun j => Real.mul_self_sqrt (hPos j).le
  have hVCompression : Vᵀ * (Dᵀ * D) * V = Matrix.diagonal lambda := by
    calc
      Vᵀ * (Dᵀ * D) * V = Vᵀ * ((Dᵀ * D) * V) := by
        rw [Matrix.mul_assoc]
      _ = Vᵀ * (V * Matrix.diagonal lambda) := by rw [hVEig]
      _ = (Vᵀ * V) * Matrix.diagonal lambda := by rw [Matrix.mul_assoc]
      _ = Matrix.diagonal lambda := by rw [hVNorm, Matrix.one_mul]
  have hScale :
      Matrix.diagonal a * Matrix.diagonal lambda * Matrix.diagonal a = 1 := by
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal,
      ← Matrix.diagonal_one]
    congr with i
    dsimp [a]
    calc
      (Real.sqrt (lambda i))⁻¹ * lambda i * (Real.sqrt (lambda i))⁻¹ =
          (Real.sqrt (lambda i))⁻¹ *
            (Real.sqrt (lambda i) * Real.sqrt (lambda i)) *
              (Real.sqrt (lambda i))⁻¹ := by rw [hsqrt_sq i]
      _ = ((Real.sqrt (lambda i))⁻¹ * Real.sqrt (lambda i)) *
          (Real.sqrt (lambda i) * (Real.sqrt (lambda i))⁻¹) := by ring
      _ = 1 := by rw [inv_mul_cancel₀ (hsqrt_ne i),
        mul_inv_cancel₀ (hsqrt_ne i), mul_one]
  have hUNorm : Uᵀ * U = 1 := by
    calc
      Uᵀ * U = Matrix.diagonal a * (Vᵀ * (Dᵀ * D) * V) *
          Matrix.diagonal a := by
        simp [U, Matrix.transpose_mul, Matrix.mul_assoc]
      _ = Matrix.diagonal a * Matrix.diagonal lambda * Matrix.diagonal a := by
        rw [hVCompression]
      _ = 1 := hScale
  have hDiagComm :
      Matrix.diagonal lambda * Matrix.diagonal a =
        Matrix.diagonal a * Matrix.diagonal lambda := by
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr with i
    exact mul_comm _ _
  have hUEig : (D * Dᵀ) * U = U * Matrix.diagonal lambda := by
    calc
      (D * Dᵀ) * U = D * ((Dᵀ * D) * V) * Matrix.diagonal a := by
        simp [U, Matrix.mul_assoc]
      _ = D * (V * Matrix.diagonal lambda) * Matrix.diagonal a := by rw [hVEig]
      _ = D * V * (Matrix.diagonal lambda * Matrix.diagonal a) := by
        simp [Matrix.mul_assoc]
      _ = D * V * (Matrix.diagonal a * Matrix.diagonal lambda) := by rw [hDiagComm]
      _ = U * Matrix.diagonal lambda := by simp [U, Matrix.mul_assoc]
  have hLambdaScale :
      Matrix.diagonal lambda * Matrix.diagonal a =
        Matrix.diagonal (fun j => Real.sqrt (lambda j)) := by
    simp [Matrix.diagonal_mul_diagonal, a, ← div_eq_mul_inv]
  have hDual : Dᵀ * U = V * Matrix.diagonal (fun j => Real.sqrt (lambda j)) := by
    calc
      Dᵀ * U = ((Dᵀ * D) * V) * Matrix.diagonal a := by
        simp [U, Matrix.mul_assoc]
      _ = V * Matrix.diagonal lambda * Matrix.diagonal a := by rw [hVEig]
      _ = V * (Matrix.diagonal lambda * Matrix.diagonal a) := by
        rw [Matrix.mul_assoc]
      _ = V * Matrix.diagonal (fun j => Real.sqrt (lambda j)) := by
        rw [hLambdaScale]
  exact ⟨U, hUNorm, hUEig, hDual⟩

/-- Tie-safe ordinary spectral witnesses for the two rectangular Gram
matrices and the complementary residual matrix. -/
private structure RectangularJointSpectrum
    {k m r s : Type*}
    [Fintype k] [DecidableEq k]
    [Fintype m] [DecidableEq m]
    [Fintype r] [DecidableEq r]
    [Fintype s] [DecidableEq s]
    (D : Matrix k m ℝ) where
  rank_card : Fintype.card r ≤ Fintype.card k
  complement_card : Fintype.card s ≤ Fintype.card m
  lambda : r → ℝ
  eta : s → ℝ
  U : Matrix k r ℝ
  Q : Matrix m s ℝ
  lambda_pos : ∀ j, 0 < lambda j
  lambda_ordered : ∀ j, lambda j =
    (mul_transpose_isHermitian D).eigenvalues₀
      (Fin.castLE rank_card ((Fintype.equivFin r) j))
  eta_ordered : ∀ j, eta j =
    (isHermitian_one.sub (transpose_mul_isHermitian D)).eigenvalues₀
      (Fin.castLE complement_card ((Fintype.equivFin s) j))
  u_norm : Uᵀ * U = 1
  u_eigenvectors : (D * Dᵀ) * U = U * Matrix.diagonal lambda
  q_norm : Qᵀ * Q = 1
  q_residual_eigenvectors :
    (1 - Dᵀ * D) * Q = Q * Matrix.diagonal eta
  cross_orthogonal : Qᵀ * (Dᵀ * U) = 0

/-- Construct the ordinary joint spectrum from one right-Gram eigenbasis.

The rank hypothesis is exactly what makes the selected left block positive
and hence normalizable. -/
private theorem RectangularJointSpectrum.exists
    {k m r s : Type*}
    [Fintype k] [DecidableEq k]
    [Fintype m] [DecidableEq m]
    [Fintype r] [DecidableEq r]
    [Fintype s] [DecidableEq s]
    (D : Matrix k m ℝ)
    (hrk : Fintype.card r ≤ Fintype.card k)
    (hrm : Fintype.card r ≤ Fintype.card m)
    (hdim : Fintype.card s = Fintype.card m - Fintype.card r)
    (hrank : Fintype.card r ≤ D.rank) :
    Nonempty (RectangularJointSpectrum (r := r) (s := s) D) := by
  classical
  obtain ⟨lambda, mu, V, Q, hLambdaOrdered, hVNorm, hVEig,
      hQNorm, hQEig, hQV, hResidualRoots⟩ :=
    rectangularGramCanonicalSplit_exists D hrk hrm hdim
  have hMPos : (D * Dᵀ).PosSemidef := by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.posSemidef_self_mul_conjTranspose D
  have hLambdaPos : ∀ j, 0 < lambda j := by
    have hrankM : Fintype.card r ≤ (D * Dᵀ).rank := by
      rw [Matrix.rank_self_mul_transpose]
      exact hrank
    intro j
    rw [hLambdaOrdered j]
    exact leading_eigenvalues₀_pos_of_posSemidef_rank_ge hMPos hrk hrankM j
  obtain ⟨U, hUNorm, hUEig, hDual⟩ :=
    normalizedLeftGramBlock_exists D lambda V hLambdaPos hVNorm hVEig
  let eta : s → ℝ := fun j => 1 - mu j
  have hQResidual : (1 - Dᵀ * D) * Q = Q * Matrix.diagonal eta := by
    calc
      (1 - Dᵀ * D) * Q = Q - (Dᵀ * D) * Q := by
        rw [Matrix.sub_mul, Matrix.one_mul]
      _ = Q - Q * Matrix.diagonal mu := by rw [hQEig]
      _ = Q * (1 - Matrix.diagonal mu) := by rw [Matrix.mul_sub, Matrix.mul_one]
      _ = Q * Matrix.diagonal eta := by
        rw [← Matrix.diagonal_one, Matrix.diagonal_sub]
  have hCross : Qᵀ * (Dᵀ * U) = 0 := by
    rw [hDual]
    calc
      Qᵀ * (V * Matrix.diagonal (fun j => Real.sqrt (lambda j))) =
          (Qᵀ * V) * Matrix.diagonal (fun j => Real.sqrt (lambda j)) := by
            rw [Matrix.mul_assoc]
      _ = 0 := by rw [hQV, Matrix.zero_mul]
  exact ⟨{
    rank_card := hrk
    complement_card := by omega
    lambda := lambda
    eta := eta
    U := U
    Q := Q
    lambda_pos := hLambdaPos
    lambda_ordered := hLambdaOrdered
    eta_ordered := fun j => by simpa [eta] using hResidualRoots j
    u_norm := hUNorm
    u_eigenvectors := hUEig
    q_norm := hQNorm
    q_residual_eigenvectors := hQResidual
    cross_orthogonal := hCross
  }⟩

/-- The two Hansen pencils become the paired rectangular Gram matrices after
coordinated positive-definite whitening. -/
private theorem hansenWhitenedGramIdentities
    {n k m : Type*}
    [Fintype n] [Fintype k] [DecidableEq k]
    [Fintype m] [DecidableEq m]
    (Xtilde : Matrix n k ℝ) (Ytilde Etilde : Matrix n m ℝ)
    (wx : PosDefWhitening (reducedRankGPencilB Xtilde))
    (wy : PosDefWhitening (reducedRankAperpPencilB Ytilde))
    (hComplement :
      reducedRankAperpPencilA Etilde =
        reducedRankAperpPencilB Ytilde -
          (Ytildeᵀ * Xtilde) * (reducedRankGPencilB Xtilde)⁻¹ *
            (Xtildeᵀ * Ytilde)) :
    let D := wx.Sᵀ * (Xtildeᵀ * Ytilde) * wy.S
    D * Dᵀ = wx.Sᵀ * reducedRankGPencilA Xtilde Ytilde * wx.S ∧
      1 - Dᵀ * D =
        wy.Sᵀ * reducedRankAperpPencilA Etilde * wy.S := by
  dsimp only
  let D : Matrix k m ℝ := wx.Sᵀ * (Xtildeᵀ * Ytilde) * wy.S
  have hXInv := wx.nonsingInv_eq
  have hYInv := wy.nonsingInv_eq
  have hYInv' : (Ytildeᵀ * Ytilde)⁻¹ = wy.S * wy.Sᵀ := by
    simpa [reducedRankAperpPencilB] using hYInv
  have hG : D * Dᵀ =
      wx.Sᵀ * reducedRankGPencilA Xtilde Ytilde * wx.S := by
    simp only [D, Matrix.transpose_mul, Matrix.transpose_transpose]
    rw [reducedRankGPencilA, hYInv']
    simp [Matrix.mul_assoc]
  have hYWhite :
      wy.Sᵀ * reducedRankAperpPencilB Ytilde * wy.S = 1 :=
    wy.whitened
  have hCross :
      wy.Sᵀ * ((Ytildeᵀ * Xtilde) *
          (reducedRankGPencilB Xtilde)⁻¹ * (Xtildeᵀ * Ytilde)) * wy.S =
        Dᵀ * D := by
    rw [hXInv]
    simp [D, Matrix.transpose_mul, Matrix.mul_assoc]
  have hR : 1 - Dᵀ * D =
      wy.Sᵀ * reducedRankAperpPencilA Etilde * wy.S := by
    calc
      1 - Dᵀ * D =
          wy.Sᵀ * reducedRankAperpPencilB Ytilde * wy.S - Dᵀ * D := by
            rw [hYWhite]
      _ = wy.Sᵀ * reducedRankAperpPencilB Ytilde * wy.S -
          wy.Sᵀ * ((Ytildeᵀ * Xtilde) *
            (reducedRankGPencilB Xtilde)⁻¹ * (Xtildeᵀ * Ytilde)) * wy.S := by
              rw [hCross]
      _ = wy.Sᵀ * (reducedRankAperpPencilB Ytilde -
          (Ytildeᵀ * Xtilde) * (reducedRankGPencilB Xtilde)⁻¹ *
            (Xtildeᵀ * Ytilde)) * wy.S := by
              rw [Matrix.mul_sub, Matrix.sub_mul]
      _ = wy.Sᵀ * reducedRankAperpPencilA Etilde * wy.S := by
            rw [← hComplement]
  exact ⟨hG, hR⟩

/-- Unconditional tie-safe spectral construction for Hansen Theorem 11.7.

Unlike the separated-roots constructor in `ReducedRank`, this theorem chooses
the G and `Aperp` blocks jointly.  It therefore permits a root tie across the
selected/omitted boundary while retaining the exact leading-root formulas,
both global determinant maxima, Hansen's cross orthogonality, positive
selected roots, roots strictly below one, and the G-side complement minimum
needed by the raw Gaussian likelihood proof.

The rank premise is the finite-sample exact-rank condition: the residualized
cross matrix must contain at least `r` nonzero canonical-correlation
directions. Positive definiteness of the unrestricted residual Gram excludes
unit selected roots when `r` is positive; it is unnecessary when `r` is empty. -/
theorem
    ReducedRankHansenIdentifiedSpectralMaximizerCertificate.exists_of_complement_pencil
    {n k m r s : Type*}
    [Fintype n]
    [Fintype k] [DecidableEq k]
    [Fintype m] [DecidableEq m]
    [Fintype r] [DecidableEq r]
    [Fintype s] [DecidableEq s]
    (Xtilde : Matrix n k ℝ) (Ytilde Etilde : Matrix n m ℝ)
    (hXGram : (Xtildeᵀ * Xtilde).PosDef)
    (hYGram : (Ytildeᵀ * Ytilde).PosDef)
    (hResidualRegular : (Etildeᵀ * Etilde).PosDef ∨ IsEmpty r)
    (hComplement :
      reducedRankAperpPencilA Etilde =
        reducedRankAperpPencilB Ytilde -
          (Ytildeᵀ * Xtilde) * (reducedRankGPencilB Xtilde)⁻¹ *
            (Xtildeᵀ * Ytilde))
    (hrk : Fintype.card r ≤ Fintype.card k)
    (hrm : Fintype.card r ≤ Fintype.card m)
    (hdim : Fintype.card s = Fintype.card m - Fintype.card r)
    (hrank : Fintype.card r ≤ (Xtildeᵀ * Ytilde).rank) :
    ∃ (G : Matrix k r ℝ) (lambda : r → ℝ)
        (Aperp : Matrix m s ℝ) (eta : s → ℝ),
      ReducedRankHansenIdentifiedSpectralMaximizerCertificate
        Xtilde Ytilde Etilde G lambda Aperp eta ∧
      (∀ j, 0 < lambda j) ∧
      (∀ j, lambda j < 1) ∧
      (∀ H : Matrix k r ℝ, reducedRankGNormalized Xtilde H →
        (1 - Gᵀ * reducedRankGPencilA Xtilde Ytilde * G).det ≤
          (1 - Hᵀ * reducedRankGPencilA Xtilde Ytilde * H).det) ∧
      ReducedRankHansenOrderedRootWitness Xtilde Ytilde lambda eta := by
  classical
  let Bx : Matrix k k ℝ := reducedRankGPencilB Xtilde
  let By : Matrix m m ℝ := reducedRankAperpPencilB Ytilde
  let Ag : Matrix k k ℝ := reducedRankGPencilA Xtilde Ytilde
  let Ar : Matrix m m ℝ := reducedRankAperpPencilA Etilde
  have hBx : Bx.PosDef := by simpa [Bx, reducedRankGPencilB] using hXGram
  have hBy : By.PosDef := by simpa [By, reducedRankAperpPencilB] using hYGram
  let wx : PosDefWhitening Bx := Classical.choice (PosDefWhitening.exists Bx hBx)
  let wy : PosDefWhitening By := Classical.choice (PosDefWhitening.exists By hBy)
  let D : Matrix k m ℝ := wx.Sᵀ * (Xtildeᵀ * Ytilde) * wy.S
  have hRankD : Fintype.card r ≤ D.rank := by
    rw [show D.rank = (Xtildeᵀ * Ytilde).rank by
      simpa [D] using whitenedCross_rank wx wy (Xtildeᵀ * Ytilde)]
    exact hrank
  have hIdentities := hansenWhitenedGramIdentities
    Xtilde Ytilde Etilde wx wy hComplement
  have hM : D * Dᵀ = wx.Sᵀ * Ag * wx.S := by
    simpa [D, Ag, Bx, By, wx, wy] using hIdentities.1
  have hN : 1 - Dᵀ * D = wy.Sᵀ * Ar * wy.S := by
    simpa [D, Ar, Bx, By, wx, wy] using hIdentities.2
  have hMPos : (D * Dᵀ).PosSemidef := by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.posSemidef_self_mul_conjTranspose D
  have hNPos : (1 - Dᵀ * D).PosSemidef := by
    have hEPos : (Etildeᵀ * Etilde).PosSemidef := by
      simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
        Matrix.posSemidef_conjTranspose_mul_self Etilde
    have hcong := hEPos.conjTranspose_mul_mul_same wy.S
    rw [hN]
    simpa [Ar, Matrix.conjTranspose_eq_transpose_of_trivial] using hcong
  have hIMPos : (1 - D * Dᵀ).PosSemidef := by
    have hAB := reducedRankGPencilA_le_pencilB_of_yGram_posDef
      Xtilde Ytilde hYGram
    have hcong := (Matrix.le_iff.mp hAB).conjTranspose_mul_mul_same wx.S
    have hXWhite : wx.Sᵀ * Bx * wx.S = 1 := wx.whitened
    have hDiff : wx.Sᵀ * (Bx - Ag) * wx.S = 1 - D * Dᵀ := by
      calc
        wx.Sᵀ * (Bx - Ag) * wx.S =
            wx.Sᵀ * Bx * wx.S - wx.Sᵀ * Ag * wx.S := by
              rw [Matrix.mul_sub, Matrix.sub_mul]
        _ = 1 - D * Dᵀ := by rw [hXWhite, hM]
    simpa [Bx, Ag, Matrix.conjTranspose_eq_transpose_of_trivial, hDiff] using hcong
  let js : RectangularJointSpectrum (r := r) (s := s) D :=
    Classical.choice (RectangularJointSpectrum.exists D hrk hrm hdim hRankD)
  let G : Matrix k r ℝ := wx.S * js.U
  let Aperp : Matrix m s ℝ := wy.S * js.Q
  have hGTransport := generalizedEigenblock_of_whitening
    Ag Bx (D * Dᵀ) wx.T wx.S wx.factor hM wx.inv_mul wx.mul_inv
      js.lambda js.U js.u_norm js.u_eigenvectors
  have hATransport := generalizedEigenblock_of_whitening
    Ar By (1 - Dᵀ * D) wy.T wy.S wy.factor hN wy.inv_mul wy.mul_inv
      js.eta js.Q js.q_norm js.q_residual_eigenvectors
  have hGEig : reducedRankHansenGEigenvectors Xtilde Ytilde js.lambda G := by
    simpa [G, Ag, Bx] using hGTransport.1
  have hGNorm : reducedRankGNormalized Xtilde G := by
    simpa [G, Bx] using hGTransport.2
  have hAEig : reducedRankHansenAperpEigenvectors Etilde Ytilde js.eta Aperp := by
    simpa [Aperp, Ar, By] using hATransport.1
  have hANorm : reducedRankAperpNormalized Ytilde Aperp := by
    simpa [Aperp, By] using hATransport.2
  have hLambdaEq : js.lambda = fun j : r =>
      hMPos.1.eigenvalues₀ (Fin.castLE hrk ((Fintype.equivFin r) j)) := by
    funext j
    exact js.lambda_ordered j
  have hEtaEq : js.eta = fun j : s =>
      hNPos.1.eigenvalues₀
        (Fin.castLE js.complement_card ((Fintype.equivFin s) j)) := by
    funext j
    exact js.eta_ordered j
  have hGFactor : Ag = wx.Tᵀ * (D * Dᵀ) * wx.T :=
    wx.factor_of_whitened Ag (D * Dᵀ) hM
  have hAFactor : Ar = wy.Tᵀ * (1 - Dᵀ * D) * wy.T :=
    wy.factor_of_whitened Ar (1 - Dᵀ * D) hN
  have hGBound : generalizedEigenDetProductUpperBound Ag Bx js.lambda := by
    have hOrd := generalizedEigenDetProductUpperBound_identity_of_posSemidef_ordered
      (D * Dᵀ) hMPos hrk
    have hWhite := generalizedEigenDetProductUpperBound_of_whitened_identity
      Ag Bx (D * Dᵀ) wx.T
      (fun j : r => hMPos.1.eigenvalues₀
        (Fin.castLE hrk ((Fintype.equivFin r) j)))
      hGFactor wx.factor hOrd
    simpa [hLambdaEq] using hWhite
  have hABound : generalizedEigenDetProductUpperBound Ar By js.eta := by
    have hOrd := generalizedEigenDetProductUpperBound_identity_of_posSemidef_ordered
      (1 - Dᵀ * D) hNPos js.complement_card
    have hWhite := generalizedEigenDetProductUpperBound_of_whitened_identity
      Ar By (1 - Dᵀ * D) wy.T
      (fun j : s => hNPos.1.eigenvalues₀
        (Fin.castLE js.complement_card ((Fintype.equivFin s) j)))
      hAFactor wy.factor hOrd
    simpa [hEtaEq] using hWhite
  have hGCert : GeneralizedEigenDetProductMaxCertificate Ag Bx G js.lambda :=
    GeneralizedEigenDetProductMaxCertificate.of_productUpperBound
      Ag Bx G js.lambda (by simpa [Ag, Bx] using hGEig)
      (by simpa [Bx] using hGNorm) hGBound
  have hACert : GeneralizedEigenDetProductMaxCertificate Ar By Aperp js.eta :=
    GeneralizedEigenDetProductMaxCertificate.of_productUpperBound
      Ar By Aperp js.eta (by simpa [Ar, By] using hAEig)
      (by simpa [By] using hANorm) hABound
  have hMax : ReducedRankHansenDetProductMaxMaxCertificate
      Xtilde Ytilde Etilde G js.lambda Aperp js.eta := by
    exact ⟨by simpa [Ag, Bx] using hGCert, by simpa [Ar, By] using hACert⟩
  have hCross : reducedRankAperpCrossOrthogonal Xtilde Ytilde G Aperp := by
    change Aperpᵀ * (Ytildeᵀ * Xtilde * G) = 0
    calc
      Aperpᵀ * (Ytildeᵀ * Xtilde * G) = js.Qᵀ * (Dᵀ * js.U) := by
        simp [Aperp, G, D, Matrix.transpose_mul, Matrix.mul_assoc]
      _ = 0 := js.cross_orthogonal
  have hComplementMin :
      ∀ H : Matrix k r ℝ, reducedRankGNormalized Xtilde H →
        (1 - Gᵀ * reducedRankGPencilA Xtilde Ytilde * G).det ≤
          (1 - Hᵀ * reducedRankGPencilA Xtilde Ytilde * H).det := by
    have hMin := generalizedEigenLeadingComplementDetMinimal_of_whitening
      Ag Bx (D * Dᵀ) wx.T hGFactor wx.factor hMPos hIMPos hrk G
      (by simpa [Ag, Bx, hLambdaEq] using hGEig)
      (by simpa [Bx] using hGNorm)
    simpa [Ag, Bx] using hMin
  have hLambdaLt : ∀ j, js.lambda j < 1 := by
    rcases hResidualRegular with hEGram | hEmpty
    · have hNDef : (1 - Dᵀ * D).PosDef := by
        have hcong := hEGram.conjTranspose_mul_mul_same wy.S_mulVec_injective
        rw [hN]
        simpa [Ar, Matrix.conjTranspose_eq_transpose_of_trivial] using hcong
      intro j
      let t : Fin (Fintype.card r) := (Fintype.equivFin r) j
      let idx : Fin (Fintype.card m) := Fin.castLE hrm t
      have htk : t.val < Fintype.card k := lt_of_lt_of_le t.isLt hrk
      have htm : t.val < Fintype.card m := lt_of_lt_of_le t.isLt hrm
      have hTransfer := mul_transpose_eigenvalues₀_eq_of_lt D t.val htk htm
      have hRight : js.lambda j =
          (transpose_mul_isHermitian D).eigenvalues₀ idx := by
        calc
          js.lambda j = (mul_transpose_isHermitian D).eigenvalues₀
              (Fin.castLE hrk t) := js.lambda_ordered j
          _ = (transpose_mul_isHermitian D).eigenvalues₀ idx := by
            simpa [idx, t] using hTransfer
      have hRoot := one_sub_ordered_eigenvalues₀_apply
        (transpose_mul_isHermitian D) (Fin.rev idx)
      have hOrderedPos : 0 < hNDef.1.eigenvalues₀ (Fin.rev idx) := by
        let e : Fin (Fintype.card m) ≃ m :=
          Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card m))
        have hp := hNDef.eigenvalues_pos (e (Fin.rev idx))
        simpa [Matrix.IsHermitian.eigenvalues, e] using hp
      have hComp : hNDef.1.eigenvalues₀ (Fin.rev idx) =
          1 - (transpose_mul_isHermitian D).eigenvalues₀ idx := by
        simpa using hRoot
      rw [hComp, ← hRight] at hOrderedPos
      linarith
    · letI : IsEmpty r := hEmpty
      exact fun j => isEmptyElim j
  have hOrdered : ReducedRankHansenOrderedRootWitness
      Xtilde Ytilde js.lambda js.eta := by
    exact ⟨hrk, js.complement_card, wx.S, wy.S, D,
      by simpa [Bx] using wx.whitened,
      by simpa [By] using wy.whitened,
      rfl, js.lambda_ordered, js.eta_ordered⟩
  exact ⟨G, js.lambda, Aperp, js.eta,
    ReducedRankHansenIdentifiedSpectralMaximizerCertificate.of_maxMax_and_cross
      hMax hCross,
    js.lambda_pos, hLambdaLt, hComplementMin, hOrdered⟩

end HansenEconometrics
