import Mathlib.Data.Matrix.ColumnRowPartitioned
import HansenEconometrics.Chapter3Projections
import HansenEconometrics.Chapter7Asymptotics.Basic
import HansenEconometrics.LinearAlgebraUtils

/-!
# Chapter 12 — instrumental-variables algebra

This file contains the deterministic estimator notation for Hansen Chapter 12:
instrument projections, reduced-form fitted regressors, IV/2SLS estimators, and
the finite-sample structural-error decomposition used in the consistency and CLT
proofs. Stochastic convergence assumptions are kept for later files.
-/

open scoped Matrix

namespace HansenEconometrics

open Matrix

variable {n k l : Type*}
variable [Fintype n] [Fintype k] [Fintype l]
variable [DecidableEq k] [DecidableEq l]

/-- Hansen equation (12.30): projection onto the instrument span,
`P_Z = Z (Z'Z)^{-1} Z'`, in the finite-sample nonsingular case. -/
noncomputable def instrumentProjection
    (Z : Matrix n l ℝ) [Invertible (Zᵀ * Z)] : Matrix n n ℝ :=
  hatMatrix Z

/-- Star version of the instrument projection, totalized through `Matrix.nonsingInv`.
It agrees with `instrumentProjection` when `Z'Z` is nonsingular. -/
noncomputable def instrumentProjectionStar (Z : Matrix n l ℝ) : Matrix n n ℝ :=
  Z * (Zᵀ * Z)⁻¹ * Zᵀ

omit [Fintype k] [DecidableEq k] in
/-- Every entry of the totalized instrument projection is measurable when all
instrument entries are measurable. -/
theorem instrumentProjectionStar_apply_measurable_of_entries
    {α : Type*} [MeasurableSpace α] {Z : α → Matrix n l ℝ}
    (hZ : ∀ i a, Measurable fun x => Z x i a) (i j : n) :
    Measurable fun x => instrumentProjectionStar (Z x) i j := by
  classical
  have hgram (a b : l) : Measurable fun x => ((Z x)ᵀ * Z x) a b :=
    gram_apply_measurable_of_entries hZ a b
  have hinv (a b : l) : Measurable fun x => (((Z x)ᵀ * Z x)⁻¹) a b :=
    matrix_inv_apply_measurable_of_entries hgram a b
  simp only [instrumentProjectionStar, Matrix.mul_apply, Matrix.transpose_apply]
  exact Finset.measurable_sum Finset.univ (fun a _ =>
    (Finset.measurable_sum Finset.univ (fun b _ => (hZ i b).mul (hinv b a))).mul
      (hZ j a))

/-- Hansen reduced-form coefficient matrix `Γ̂ = (Z'Z)^{-1} Z'X`. -/
noncomputable def reducedFormCoef
    (Z : Matrix n l ℝ) (X : Matrix n k ℝ) [Invertible (Zᵀ * Z)] : Matrix l k ℝ :=
  ⅟ (Zᵀ * Z) * Zᵀ * X

/-- Star version of the reduced-form coefficient matrix. -/
noncomputable def reducedFormCoefStar
    (Z : Matrix n l ℝ) (X : Matrix n k ℝ) : Matrix l k ℝ :=
  (Zᵀ * Z)⁻¹ * Zᵀ * X

/-- Fitted regressors from the first-stage projection, `X̂ = P_Z X`. -/
noncomputable def fittedRegressors
    (Z : Matrix n l ℝ) (X : Matrix n k ℝ) [Invertible (Zᵀ * Z)] : Matrix n k ℝ :=
  instrumentProjection Z * X

/-- Star fitted regressors `X̂* = P_Z* X`. -/
noncomputable def fittedRegressorsStar
    (Z : Matrix n l ℝ) (X : Matrix n k ℝ) : Matrix n k ℝ :=
  instrumentProjectionStar Z * X

/-- Compatibility notation for the totalized first-stage fitted regressors.
The canonical Chapter 12 API is `fittedRegressorsStar`. -/
noncomputable abbrev firstStageFitted
    (Z : Matrix n l ℝ) (X : Matrix n k ℝ) : Matrix n k ℝ :=
  fittedRegressorsStar Z X

/-- Compatibility notation for the totalized first-stage residuals.
The canonical definition used by the control-function development is
`controlFunctionResidualStar`. -/
noncomputable abbrev firstStageResidual
    (Z : Matrix n l ℝ) (X : Matrix n k ℝ) : Matrix n k ℝ :=
  X - fittedRegressorsStar Z X

/-- Just-identified IV estimator with instrument matrix `W`, regressor matrix `X`,
and scalar outcome `y`: `(W'X)^{-1} W'y`. -/
noncomputable def ivBeta
    (W : Matrix n k ℝ) (X : Matrix n k ℝ) (y : n → ℝ)
    [Invertible (Wᵀ * X)] : k → ℝ :=
  ⅟ (Wᵀ * X) *ᵥ (Wᵀ *ᵥ y)

/-- Star version of the IV estimator, totalized through `Matrix.nonsingInv`. -/
noncomputable def ivBetaStar
    (W : Matrix n k ℝ) (X : Matrix n k ℝ) (y : n → ℝ) : k → ℝ :=
  (Wᵀ * X)⁻¹ *ᵥ (Wᵀ *ᵥ y)

/-- Hansen's 2SLS sample bread matrix `X'P_Z X`. -/
noncomputable def twoSLSMomentMatrix
    (Z : Matrix n l ℝ) (X : Matrix n k ℝ) [Invertible (Zᵀ * Z)] : Matrix k k ℝ :=
  Xᵀ * instrumentProjection Z * X

/-- Star version of the 2SLS sample bread matrix. -/
noncomputable def twoSLSMomentMatrixStar
    (Z : Matrix n l ℝ) (X : Matrix n k ℝ) : Matrix k k ℝ :=
  Xᵀ * instrumentProjectionStar Z * X

/-- Hansen's 2SLS sample cross moment `X'P_Z y`. -/
noncomputable def twoSLSMomentVector
    (Z : Matrix n l ℝ) (X : Matrix n k ℝ) (y : n → ℝ)
    [Invertible (Zᵀ * Z)] : k → ℝ :=
  (Xᵀ * instrumentProjection Z) *ᵥ y

/-- Star version of the 2SLS sample cross moment. -/
noncomputable def twoSLSMomentVectorStar
    (Z : Matrix n l ℝ) (X : Matrix n k ℝ) (y : n → ℝ) : k → ℝ :=
  (Xᵀ * instrumentProjectionStar Z) *ᵥ y

/-- Hansen equation (12.31): 2SLS in projection notation,
`β̂₂ₛₗₛ = (X'P_Z X)^{-1} X'P_Z Y`. -/
noncomputable def twoSLSBeta
    (Z : Matrix n l ℝ) (X : Matrix n k ℝ) (y : n → ℝ)
    [Invertible (Zᵀ * Z)] [Invertible (twoSLSMomentMatrix Z X)] : k → ℝ :=
  ⅟ (twoSLSMomentMatrix Z X) *ᵥ twoSLSMomentVector Z X y

/-- Star primitive for 2SLS. This is the proof-engine version used by later
asymptotic statements; on nonsingular designs it agrees with `twoSLSBeta`. -/
noncomputable def twoSLSBetaStar
    (Z : Matrix n l ℝ) (X : Matrix n k ℝ) (y : n → ℝ) : k → ℝ :=
  (twoSLSMomentMatrixStar Z X)⁻¹ *ᵥ twoSLSMomentVectorStar Z X y

/-- **OrZero primitive**: textbook-facing totalization of 2SLS.

Branches explicitly on the two finite-sample nonsingularity requirements:
- `Z'Z` nonsingular, so the instrument projection is the ordinary projection;
- `X'P_Z X` nonsingular, so the 2SLS normal equations identify the coefficient.

On the nonsingular branch it returns `twoSLSBeta`; otherwise it returns `0`.
The bridge `twoSLSBetaOrZero_eq_twoSLSBetaStar` connects this textbook-facing
API to the Star proof engine used in Chapter 12 asymptotic results. -/
noncomputable def twoSLSBetaOrZero
    (Z : Matrix n l ℝ) (X : Matrix n k ℝ) (y : n → ℝ) : k → ℝ :=
  letI : Decidable (IsUnit (Zᵀ * Z).det) := Classical.propDecidable _
  if hZ : IsUnit (Zᵀ * Z).det then
    letI : Invertible (Zᵀ * Z) := Matrix.invertibleOfIsUnitDet (A := Zᵀ * Z) hZ
    letI : Decidable (IsUnit (twoSLSMomentMatrix Z X).det) := Classical.propDecidable _
    if hM : IsUnit (twoSLSMomentMatrix Z X).det then
      letI : Invertible (twoSLSMomentMatrix Z X) :=
        Matrix.invertibleOfIsUnitDet (A := twoSLSMomentMatrix Z X) hM
      twoSLSBeta Z X y
    else
      0
  else
    0

/-- Structural residual using the totalized 2SLS estimator. -/
noncomputable def twoSLSResidualStar
    (Z : Matrix n l ℝ) (X : Matrix n k ℝ) (y : n → ℝ) : n → ℝ :=
  y - X *ᵥ twoSLSBetaStar Z X y

/-- Hansen robust 2SLS middle matrix `Ω̂ = n^{-1} ∑ Z_i Z_i' ê_i^2`, using
the structural 2SLS residuals rather than second-stage OLS residuals. -/
noncomputable def twoSLSOmegaHatStar
    (Z : Matrix n l ℝ) (X : Matrix n k ℝ) (y : n → ℝ) : Matrix l l ℝ :=
  (Fintype.card n : ℝ)⁻¹ •
    ∑ i : n, (twoSLSResidualStar Z X y i) ^ 2 • Matrix.vecMulVec (Z i) (Z i)

/-- Ideal robust IV middle matrix based on true structural errors,
`n⁻¹∑ Z_i Z_i' e_i²`. -/
noncomputable def twoSLSOmegaIdeal
    (Z : Matrix n l ℝ) (e : n → ℝ) : Matrix l l ℝ :=
  (Fintype.card n : ℝ)⁻¹ •
    ∑ i : n, (e i) ^ 2 • Matrix.vecMulVec (Z i) (Z i)

/-- Cross residual-substitution remainder for the robust IV middle,
`n⁻¹∑ Z_i Z_i' e_i X_i'd`. -/
noncomputable def twoSLSOmegaCrossRemainder
    (Z : Matrix n l ℝ) (X : Matrix n k ℝ) (e : n → ℝ) (d : k → ℝ) :
    Matrix l l ℝ :=
  (Fintype.card n : ℝ)⁻¹ •
    ∑ i : n, (e i * (X i ⬝ᵥ d)) • Matrix.vecMulVec (Z i) (Z i)

/-- Quadratic residual-substitution remainder for the robust IV middle,
`n⁻¹∑ Z_i Z_i' (X_i'd)²`. -/
noncomputable def twoSLSOmegaQuadraticRemainder
    (Z : Matrix n l ℝ) (X : Matrix n k ℝ) (d : k → ℝ) : Matrix l l ℝ :=
  (Fintype.card n : ℝ)⁻¹ •
    ∑ i : n, (X i ⬝ᵥ d) ^ 2 • Matrix.vecMulVec (Z i) (Z i)

/-- Sample `Q_ZZ = n^{-1} Z'Z`. -/
noncomputable def sampleQZZ (Z : Matrix n l ℝ) : Matrix l l ℝ :=
  sampleGram Z

/-- Sample `Q_ZX = n^{-1} Z'X`. -/
noncomputable def sampleQZX (Z : Matrix n l ℝ) (X : Matrix n k ℝ) : Matrix l k ℝ :=
  (Fintype.card n : ℝ)⁻¹ • (Zᵀ * X)

/-- Sample `Q_XZ = n^{-1} X'Z`. -/
noncomputable def sampleQXZ (Z : Matrix n l ℝ) (X : Matrix n k ℝ) : Matrix k l ℝ :=
  (sampleQZX Z X)ᵀ

/-- Hansen's 2SLS population/sample bread `Q_XZ Q_ZZ^{-1} Q_ZX`. -/
noncomputable def twoSLSBread
    (QXZ : Matrix k l ℝ) (QZZ : Matrix l l ℝ) (QZX : Matrix l k ℝ) : Matrix k k ℝ :=
  QXZ * QZZ⁻¹ * QZX

omit [Fintype n] [Fintype k] [DecidableEq k] in
/-- Symmetry of Hansen's 2SLS bread under the population identities
`Q_XZ = Q_ZX'` and `Q_ZZ' = Q_ZZ`. -/
theorem twoSLSBread_transpose_of_qzz_symm
    {QXZ : Matrix k l ℝ} {QZZ : Matrix l l ℝ} {QZX : Matrix l k ℝ}
    (hQXZ : QXZ = QZXᵀ) (hQZZsymm : QZZᵀ = QZZ) :
    (twoSLSBread QXZ QZZ QZX)ᵀ = twoSLSBread QXZ QZZ QZX := by
  have hQZZinv : (QZZ⁻¹)ᵀ = QZZ⁻¹ := by
    rw [Matrix.transpose_nonsing_inv, hQZZsymm]
  simp [twoSLSBread, Matrix.transpose_mul, hQZZinv, hQXZ, Matrix.mul_assoc]

omit [Fintype n] [DecidableEq k] in
/-- Hansen Assumption 12.1 rank bridge.

If `Q_ZZ` is positive definite and `Q_ZX` has full column rank, then Hansen's
2SLS bread `Q_XZ Q_ZZ^{-1} Q_ZX` is positive definite, when `Q_XZ = Q_ZX'`.
This converts the textbook relevance condition into the nonsingularity premise
used by the CMT proof layer. -/
theorem twoSLSBread_posDef_of_qzz_posDef_rank
    {QXZ : Matrix k l ℝ} {QZZ : Matrix l l ℝ} {QZX : Matrix l k ℝ}
    (hQXZ : QXZ = QZXᵀ)
    (hQZZ : QZZ.PosDef)
    (hQZX : Function.Injective QZX.mulVec) :
    (twoSLSBread QXZ QZZ QZX).PosDef := by
  subst QXZ
  simpa [twoSLSBread, Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.mul_assoc] using
    (hQZZ.inv.conjTranspose_mul_mul_same (B := QZX) hQZX)

omit [Fintype n] in
/-- Nonsingularity form of `twoSLSBread_posDef_of_qzz_posDef_rank`. -/
theorem isUnit_twoSLSBread_det_of_qzz_posDef_rank
    {QXZ : Matrix k l ℝ} {QZZ : Matrix l l ℝ} {QZX : Matrix l k ℝ}
    (hQXZ : QXZ = QZXᵀ)
    (hQZZ : QZZ.PosDef)
    (hQZX : Function.Injective QZX.mulVec) :
    IsUnit (twoSLSBread QXZ QZZ QZX).det := by
  classical
  exact (Matrix.isUnit_iff_isUnit_det _).mp
    (twoSLSBread_posDef_of_qzz_posDef_rank hQXZ hQZZ hQZX).isUnit

/-- Hansen Theorem 12.2 asymptotic covariance formula. -/
noncomputable def twoSLSAsymptoticVariance
    (QXZ : Matrix k l ℝ) (QZZ Omega : Matrix l l ℝ) (QZX : Matrix l k ℝ) :
    Matrix k k ℝ :=
  (twoSLSBread QXZ QZZ QZX)⁻¹ *
    (QXZ * QZZ⁻¹ * Omega * QZZ⁻¹ * QZX) *
      (twoSLSBread QXZ QZZ QZX)⁻¹

/-- Hansen's homoskedastic 2SLS asymptotic covariance `σ² (Q_XZ Q_ZZ^{-1} Q_ZX)^{-1}`. -/
noncomputable def twoSLSHomoskedasticAsymptoticVariance
    (QXZ : Matrix k l ℝ) (QZZ : Matrix l l ℝ) (QZX : Matrix l k ℝ) (sigma2 : ℝ) :
    Matrix k k ℝ :=
  sigma2 • (twoSLSBread QXZ QZZ QZX)⁻¹

/-- Hansen's sample linearization matrix
`((Q̂_XZ Q̂_ZZ^{-1} Q̂_ZX)^{-1} Q̂_XZ Q̂_ZZ^{-1})`, multiplying
the instrument-error score `n^{-1} Z'e`. -/
noncomputable def twoSLSLinearizationMatrix
    (Z : Matrix n l ℝ) (X : Matrix n k ℝ) : Matrix k l ℝ :=
  (twoSLSBread (sampleQXZ Z X) (sampleQZZ Z) (sampleQZX Z X))⁻¹ *
    sampleQXZ Z X * (sampleQZZ Z)⁻¹

/-- Population counterpart of `twoSLSLinearizationMatrix`. -/
noncomputable def twoSLSPopulationLinearizationMatrix
    (QXZ : Matrix k l ℝ) (QZZ : Matrix l l ℝ) (QZX : Matrix l k ℝ) :
    Matrix k l ℝ :=
  (twoSLSBread QXZ QZZ QZX)⁻¹ * QXZ * QZZ⁻¹

omit [Fintype k] [Fintype l] [DecidableEq k] [DecidableEq l] in
/-- The instrument Gram `Q̂_ZZ` is the upper-left block of the combined sample
Gram for `[Z X]`. This is the deterministic bridge for reusing Chapter 7's
sample-Gram WLLN in IV moment proofs. -/
@[simp]
theorem sampleGram_fromCols_left_left
    (Z : Matrix n l ℝ) (X : Matrix n k ℝ) :
    (sampleGram (Matrix.fromCols Z X)).submatrix Sum.inl Sum.inl =
      sampleQZZ Z := by
  ext a b
  simp [sampleGram, sampleQZZ, Matrix.mul_apply]

omit [Fintype k] [Fintype l] [DecidableEq k] [DecidableEq l] in
/-- The instrument-regressor cross moment `Q̂_ZX` is the upper-right block of
the combined sample Gram for `[Z X]`. -/
@[simp]
theorem sampleGram_fromCols_left_right
    (Z : Matrix n l ℝ) (X : Matrix n k ℝ) :
    (sampleGram (Matrix.fromCols Z X)).submatrix Sum.inl Sum.inr =
      sampleQZX Z X := by
  ext a b
  simp [sampleGram, sampleQZX, Matrix.mul_apply]

omit [Fintype k] [Fintype l] [DecidableEq k] [DecidableEq l] in
/-- The regressor-instrument cross moment `Q̂_XZ` is the lower-left block of
the combined sample Gram for `[Z X]`. -/
@[simp]
theorem sampleGram_fromCols_right_left
    (Z : Matrix n l ℝ) (X : Matrix n k ℝ) :
    (sampleGram (Matrix.fromCols Z X)).submatrix Sum.inr Sum.inl =
      sampleQXZ Z X := by
  ext a b
  simp [sampleGram, sampleQXZ, sampleQZX, Matrix.mul_apply, mul_comm]

omit [Fintype k] [Fintype l] [DecidableEq k] [DecidableEq l] in
/-- The regressor Gram `Q̂_XX` is the lower-right block of the combined sample
Gram for `[Z X]`. -/
@[simp]
theorem sampleGram_fromCols_right_right
    (Z : Matrix n l ℝ) (X : Matrix n k ℝ) :
    (sampleGram (Matrix.fromCols Z X)).submatrix Sum.inr Sum.inr =
      sampleGram X := by
  ext a b
  simp [sampleGram, Matrix.mul_apply]

omit [Fintype k] [Fintype l] [DecidableEq k]
  [DecidableEq l] in
/-- A positive-size normalized sample Gram is nonsingular exactly when its raw
fixed-design Gram is nonsingular. -/
theorem rawGram_det_isUnit_of_sampleGram_det_isUnit
    {p : Type*} [Fintype p] [DecidableEq p] (X : Matrix n p ℝ)
    (hn : 0 < Fintype.card n) (hX : IsUnit (sampleGram X).det) :
    IsUnit ((Xᵀ * X).det) := by
  have hn_ne : (Fintype.card n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hn)
  rw [isUnit_iff_ne_zero] at hX ⊢
  rw [sampleGram, Matrix.det_smul] at hX
  exact (mul_ne_zero_iff.mp hX).2

omit [Fintype k] [Fintype l] [DecidableEq k]
  [DecidableEq l] in
/-- Converse normalized/raw Gram determinant bridge for positive sample size. -/
theorem sampleGram_det_isUnit_of_rawGram_det_isUnit
    {p : Type*} [Fintype p] [DecidableEq p] (X : Matrix n p ℝ)
    (hn : 0 < Fintype.card n) (hX : IsUnit ((Xᵀ * X).det)) :
    IsUnit (sampleGram X).det := by
  have hn_ne : (Fintype.card n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hn)
  rw [isUnit_iff_ne_zero] at hX ⊢
  rw [sampleGram, Matrix.det_smul]
  exact mul_ne_zero (pow_ne_zero _ (inv_ne_zero hn_ne)) hX

/-- Hansen structural residual variance estimator for 2SLS,
`σ̂² = n^{-1}∑ ê_i²`, using structural 2SLS residuals. -/
noncomputable def twoSLSSigmaSqHatStar
    (Z : Matrix n l ℝ) (X : Matrix n k ℝ) (y : n → ℝ) : ℝ :=
  sampleErrorSecondMoment (twoSLSResidualStar Z X y)

/-- Hansen robust plug-in covariance estimator for `√n(β̂₂ₛₗₛ - β)`,
equation (12.40), using structural residuals. -/
noncomputable def twoSLSVHatStar
    (Z : Matrix n l ℝ) (X : Matrix n k ℝ) (y : n → ℝ) : Matrix k k ℝ :=
  twoSLSAsymptoticVariance
    (sampleQXZ Z X) (sampleQZZ Z) (twoSLSOmegaHatStar Z X y) (sampleQZX Z X)

/-- Hansen homoskedastic plug-in covariance estimator for `√n(β̂₂ₛₗₛ - β)`,
using `σ̂² = n^{-1}∑ ê_i²`. -/
noncomputable def twoSLSHomoskedasticVHatStar
    (Z : Matrix n l ℝ) (X : Matrix n k ℝ) (y : n → ℝ) : Matrix k k ℝ :=
  twoSLSHomoskedasticAsymptoticVariance
    (sampleQXZ Z X) (sampleQZZ Z) (sampleQZX Z X)
    (twoSLSSigmaSqHatStar Z X y)

@[simp]
theorem instrumentProjection_eq_hatMatrix
    (Z : Matrix n l ℝ) [Invertible (Zᵀ * Z)] :
    instrumentProjection Z = hatMatrix Z :=
  rfl

@[simp]
theorem instrumentProjectionStar_eq_projection
    (Z : Matrix n l ℝ) [Invertible (Zᵀ * Z)] :
    instrumentProjectionStar Z = instrumentProjection Z := by
  unfold instrumentProjectionStar instrumentProjection hatMatrix
  rw [← invOf_eq_nonsing_inv]

theorem instrumentProjection_transpose
    (Z : Matrix n l ℝ) [Invertible (Zᵀ * Z)] :
    (instrumentProjection Z)ᵀ = instrumentProjection Z := by
  exact hatMatrix_transpose Z

theorem instrumentProjection_idempotent
    (Z : Matrix n l ℝ) [Invertible (Zᵀ * Z)] :
    instrumentProjection Z * instrumentProjection Z = instrumentProjection Z := by
  exact hatMatrix_idempotent Z

theorem instrumentProjection_mul_Z
    (Z : Matrix n l ℝ) [Invertible (Zᵀ * Z)] :
    instrumentProjection Z * Z = Z := by
  exact hat_mul_X Z

theorem instrumentProjectionStar_transpose_of_nonsingular
    (Z : Matrix n l ℝ) [Invertible (Zᵀ * Z)] :
    (instrumentProjectionStar Z)ᵀ = instrumentProjectionStar Z := by
  rw [instrumentProjectionStar_eq_projection]
  exact instrumentProjection_transpose Z

theorem instrumentProjectionStar_idempotent_of_nonsingular
    (Z : Matrix n l ℝ) [Invertible (Zᵀ * Z)] :
    instrumentProjectionStar Z * instrumentProjectionStar Z =
      instrumentProjectionStar Z := by
  rw [instrumentProjectionStar_eq_projection]
  exact instrumentProjection_idempotent Z

theorem instrumentProjectionStar_mul_Z_of_nonsingular
    (Z : Matrix n l ℝ) [Invertible (Zᵀ * Z)] :
    instrumentProjectionStar Z * Z = Z := by
  rw [instrumentProjectionStar_eq_projection]
  exact instrumentProjection_mul_Z Z

omit [Fintype k] [DecidableEq k] in
/-- First-stage fitted regressors agree with `Z Γ̂`. -/
theorem fittedRegressors_eq_Z_mul_reducedFormCoef
    (Z : Matrix n l ℝ) (X : Matrix n k ℝ) [Invertible (Zᵀ * Z)] :
    fittedRegressors Z X = Z * reducedFormCoef Z X := by
  unfold fittedRegressors instrumentProjection reducedFormCoef hatMatrix
  simp [Matrix.mul_assoc]

omit [Fintype k] [DecidableEq k] in
/-- Star first-stage fitted regressors agree with the totalized reduced-form fit. -/
theorem fittedRegressorsStar_eq_Z_mul_reducedFormCoefStar
    (Z : Matrix n l ℝ) (X : Matrix n k ℝ) :
    fittedRegressorsStar Z X = Z * reducedFormCoefStar Z X := by
  unfold fittedRegressorsStar instrumentProjectionStar reducedFormCoefStar
  simp [Matrix.mul_assoc]

omit [Fintype k] [DecidableEq k] in
/-- Projection notation equals Hansen equation (12.29)'s matrix product. -/
theorem twoSLSMomentMatrix_eq_formula
    (Z : Matrix n l ℝ) (X : Matrix n k ℝ) [Invertible (Zᵀ * Z)] :
    twoSLSMomentMatrix Z X =
      Xᵀ * Z * ⅟ (Zᵀ * Z) * Zᵀ * X := by
  unfold twoSLSMomentMatrix instrumentProjection hatMatrix
  simp [Matrix.mul_assoc]

omit [Fintype k] [DecidableEq k] in
/-- Projection notation equals Hansen equation (12.29)'s cross-product vector. -/
theorem twoSLSMomentVector_eq_formula
    (Z : Matrix n l ℝ) (X : Matrix n k ℝ) (y : n → ℝ) [Invertible (Zᵀ * Z)] :
    twoSLSMomentVector Z X y =
      (Xᵀ * Z * ⅟ (Zᵀ * Z) * Zᵀ) *ᵥ y := by
  unfold twoSLSMomentVector instrumentProjection hatMatrix
  simp [Matrix.mul_assoc]

omit [Fintype k] [DecidableEq k] in
/-- On nonsingular instrument Gram matrices, the Star 2SLS bread equals the
ordinary finite-sample bread. -/
@[simp]
theorem twoSLSMomentMatrixStar_eq_momentMatrix
    (Z : Matrix n l ℝ) (X : Matrix n k ℝ) [Invertible (Zᵀ * Z)] :
    twoSLSMomentMatrixStar Z X = twoSLSMomentMatrix Z X := by
  unfold twoSLSMomentMatrixStar twoSLSMomentMatrix
  rw [instrumentProjectionStar_eq_projection]

omit [Fintype k] [DecidableEq k] in
/-- On nonsingular instrument Gram matrices, the Star 2SLS cross moment equals
the ordinary finite-sample cross moment. -/
@[simp]
theorem twoSLSMomentVectorStar_eq_momentVector
    (Z : Matrix n l ℝ) (X : Matrix n k ℝ) (y : n → ℝ) [Invertible (Zᵀ * Z)] :
    twoSLSMomentVectorStar Z X y = twoSLSMomentVector Z X y := by
  unfold twoSLSMomentVectorStar twoSLSMomentVector
  rw [instrumentProjectionStar_eq_projection]

/-- On nonsingular finite-sample designs, Star 2SLS agrees with ordinary 2SLS. -/
theorem twoSLSBetaStar_eq_twoSLSBeta
    (Z : Matrix n l ℝ) (X : Matrix n k ℝ) (y : n → ℝ)
    [Invertible (Zᵀ * Z)] [Invertible (twoSLSMomentMatrix Z X)] :
    twoSLSBetaStar Z X y = twoSLSBeta Z X y := by
  unfold twoSLSBetaStar twoSLSBeta
  rw [twoSLSMomentMatrixStar_eq_momentMatrix,
    twoSLSMomentVectorStar_eq_momentVector]
  rw [← invOf_eq_nonsing_inv]

/-- The textbook-facing 2SLS OrZero primitive is exactly the Star proof engine. -/
@[simp]
theorem twoSLSBetaOrZero_eq_twoSLSBetaStar
    (Z : Matrix n l ℝ) (X : Matrix n k ℝ) (y : n → ℝ) :
    twoSLSBetaOrZero Z X y = twoSLSBetaStar Z X y := by
  classical
  unfold twoSLSBetaOrZero
  by_cases hZ : IsUnit (Zᵀ * Z).det
  · rw [dif_pos hZ]
    letI : Invertible (Zᵀ * Z) := Matrix.invertibleOfIsUnitDet (A := Zᵀ * Z) hZ
    by_cases hM : IsUnit (twoSLSMomentMatrix Z X).det
    · rw [dif_pos hM]
      letI : Invertible (twoSLSMomentMatrix Z X) :=
        Matrix.invertibleOfIsUnitDet (A := twoSLSMomentMatrix Z X) hM
      exact (twoSLSBetaStar_eq_twoSLSBeta Z X y).symm
    · rw [dif_neg hM]
      unfold twoSLSBetaStar
      rw [twoSLSMomentMatrixStar_eq_momentMatrix,
        twoSLSMomentVectorStar_eq_momentVector]
      rw [Matrix.nonsing_inv_apply_not_isUnit _ hM, Matrix.zero_mulVec]
  · rw [dif_neg hZ]
    unfold twoSLSBetaStar twoSLSMomentMatrixStar twoSLSMomentVectorStar
      instrumentProjectionStar
    rw [Matrix.nonsing_inv_apply_not_isUnit _ hZ]
    simp

/-- On nonsingular finite-sample designs, OrZero 2SLS agrees with ordinary 2SLS. -/
theorem twoSLSBetaOrZero_eq_twoSLSBeta
    (Z : Matrix n l ℝ) (X : Matrix n k ℝ) (y : n → ℝ)
    [Invertible (Zᵀ * Z)] [Invertible (twoSLSMomentMatrix Z X)] :
    twoSLSBetaOrZero Z X y = twoSLSBeta Z X y := by
  rw [twoSLSBetaOrZero_eq_twoSLSBetaStar, twoSLSBetaStar_eq_twoSLSBeta]

section KinalSupport

variable {k₁ k₂ l₂ : Type*}
variable [Fintype k₁] [Fintype k₂] [Fintype l₂]
variable [DecidableEq k₁] [DecidableEq k₂] [DecidableEq l₂]

/-- Endogenous-coefficient block of the textbook-facing 2SLS estimator used by
Hansen's Kinal finite-moment theorem (Theorem 12.7).  The instrument matrix is
`(X₁, Z₂)` and the regressor matrix is `(X₁, Y₂)`, so the returned coordinates
are exactly the `β₂` block. -/
noncomputable def twoSLSEndogenousBetaOrZero
    (X₁ : Matrix n k₁ ℝ) (Y₂ : Matrix n k₂ ℝ)
    (Z₂ : Matrix n l₂ ℝ) (Y₁ : n → ℝ) : k₂ → ℝ :=
  fun j =>
    twoSLSBetaOrZero
      (Matrix.fromCols X₁ Z₂)
      (Matrix.fromCols X₁ Y₂)
      Y₁ (Sum.inr j)

/-- Hansen/Kinal moment threshold for the endogenous 2SLS block:
`ℓ₂ - k₂ + 1`, expressed over `ℝ` to avoid truncating natural subtraction. -/
noncomputable def twoSLSKinalMomentThreshold (k₂ l₂ : Type*)
    [Fintype k₂] [Fintype l₂] : ℝ :=
  (Fintype.card l₂ : ℝ) - (Fintype.card k₂ : ℝ) + 1

end KinalSupport

omit [Fintype k] [DecidableEq k] in
/-- The fitted-regressor cross-product equals Hansen's `X'P_Z X`. -/
theorem fittedRegressors_transpose_mul_self_eq_twoSLSMomentMatrix
    (Z : Matrix n l ℝ) (X : Matrix n k ℝ) [Invertible (Zᵀ * Z)] :
    (fittedRegressors Z X)ᵀ * fittedRegressors Z X = twoSLSMomentMatrix Z X := by
  have hpX :
      instrumentProjection Z * (instrumentProjection Z * X) =
        instrumentProjection Z * X := by
    rw [← Matrix.mul_assoc, instrumentProjection_idempotent]
  unfold fittedRegressors twoSLSMomentMatrix
  rw [Matrix.transpose_mul, instrumentProjection_transpose]
  simpa [Matrix.mul_assoc] using
    congrArg (fun M : Matrix n k ℝ => Xᵀ * M) hpX

omit [Fintype k] [DecidableEq k] in
/-- The fitted-regressor outcome cross-product equals Hansen's `X'P_Z Y`. -/
theorem fittedRegressors_transpose_mulVec_eq_twoSLSMomentVector
    (Z : Matrix n l ℝ) (X : Matrix n k ℝ) (y : n → ℝ) [Invertible (Zᵀ * Z)] :
    (fittedRegressors Z X)ᵀ *ᵥ y = twoSLSMomentVector Z X y := by
  unfold fittedRegressors twoSLSMomentVector
  rw [Matrix.transpose_mul, instrumentProjection_transpose]

/-- Star 2SLS is the Star OLS estimator from the regression of `Y` on the fitted
first-stage regressors `X̂*`, once the Star projection is known to be idempotent
and symmetric. This is the totalized version of Hansen's two-stage computation
description following equation (12.31). -/
theorem twoSLSBetaStar_eq_olsBetaStar_fitted_of_projection_identities
    (Z : Matrix n l ℝ) (X : Matrix n k ℝ) (y : n → ℝ)
    (hidem : instrumentProjectionStar Z * instrumentProjectionStar Z = instrumentProjectionStar Z)
    (hsymm : (instrumentProjectionStar Z)ᵀ = instrumentProjectionStar Z) :
    twoSLSBetaStar Z X y = olsBetaStar (fittedRegressorsStar Z X) y := by
  have hpX :
      instrumentProjectionStar Z * (instrumentProjectionStar Z * X) =
        instrumentProjectionStar Z * X := by
    rw [← Matrix.mul_assoc, hidem]
  have hgram :
      (fittedRegressorsStar Z X)ᵀ * fittedRegressorsStar Z X =
        twoSLSMomentMatrixStar Z X := by
    unfold fittedRegressorsStar twoSLSMomentMatrixStar
    rw [Matrix.transpose_mul, hsymm]
    simpa [Matrix.mul_assoc] using
      congrArg (fun M : Matrix n k ℝ => Xᵀ * M) hpX
  have hcross :
      (fittedRegressorsStar Z X)ᵀ *ᵥ y = twoSLSMomentVectorStar Z X y := by
    unfold fittedRegressorsStar twoSLSMomentVectorStar
    rw [Matrix.transpose_mul, hsymm]
  unfold twoSLSBetaStar olsBetaStar
  rw [hgram, hcross]

/-- On nonsingular first-stage designs, Star 2SLS equals Star OLS on the fitted
regressors. -/
theorem twoSLSBetaStar_eq_olsBetaStar_fitted
    (Z : Matrix n l ℝ) (X : Matrix n k ℝ) (y : n → ℝ) [Invertible (Zᵀ * Z)] :
    twoSLSBetaStar Z X y = olsBetaStar (fittedRegressors Z X) y := by
  have hstar : instrumentProjectionStar Z = instrumentProjection Z :=
    instrumentProjectionStar_eq_projection Z
  have hfit : fittedRegressorsStar Z X = fittedRegressors Z X := by
    unfold fittedRegressorsStar fittedRegressors
    rw [hstar]
  rw [← hfit]
  exact twoSLSBetaStar_eq_olsBetaStar_fitted_of_projection_identities
    (Z := Z) (X := X) (y := y)
    (by rw [hstar]; exact instrumentProjection_idempotent Z)
    (by rw [hstar]; exact instrumentProjection_transpose Z)

omit [Fintype k] [DecidableEq k] in
/-- On nonsingular first-stage designs, the Star fitted-regressor cross-product
with the original regressor matrix is Hansen's 2SLS moment matrix. -/
theorem fittedRegressorsStar_transpose_mul_eq_twoSLSMomentMatrixStar_of_nonsingular
    (Z : Matrix n l ℝ) (X : Matrix n k ℝ) [Invertible (Zᵀ * Z)] :
    (fittedRegressorsStar Z X)ᵀ * X = twoSLSMomentMatrixStar Z X := by
  unfold fittedRegressorsStar twoSLSMomentMatrixStar
  rw [Matrix.transpose_mul, instrumentProjectionStar_transpose_of_nonsingular]

omit [Fintype k] [DecidableEq k] in
/-- On nonsingular first-stage designs, the Star fitted-regressor/outcome
cross-product is Hansen's 2SLS moment vector. -/
theorem fittedRegressorsStar_transpose_mulVec_eq_twoSLSMomentVectorStar_of_nonsingular
    (Z : Matrix n l ℝ) (X : Matrix n k ℝ) (y : n → ℝ)
    [Invertible (Zᵀ * Z)] :
    (fittedRegressorsStar Z X)ᵀ *ᵥ y =
      twoSLSMomentVectorStar Z X y := by
  unfold fittedRegressorsStar twoSLSMomentVectorStar
  rw [Matrix.transpose_mul, instrumentProjectionStar_transpose_of_nonsingular]

/-- Finite-sample 2SLS normal equation in fitted-regressor notation:
`X̂' ê = 0` on samples where the first-stage Gram and 2SLS bread are
nonsingular.  This is the deterministic orthogonality used in the subset
overidentification and FWL-style arguments. -/
theorem fittedRegressorsStar_transpose_mulVec_twoSLSResidualStar_of_nonsingular
    (Z : Matrix n l ℝ) (X : Matrix n k ℝ) (y : n → ℝ)
    [Invertible (Zᵀ * Z)]
    (hunit : IsUnit (twoSLSMomentMatrixStar Z X).det) :
    (fittedRegressorsStar Z X)ᵀ *ᵥ twoSLSResidualStar Z X y = 0 := by
  unfold twoSLSResidualStar
  rw [Matrix.mulVec_sub]
  rw [fittedRegressorsStar_transpose_mulVec_eq_twoSLSMomentVectorStar_of_nonsingular]
  have hfit :
      (fittedRegressorsStar Z X)ᵀ *ᵥ
          (X *ᵥ twoSLSBetaStar Z X y) =
        twoSLSMomentMatrixStar Z X *ᵥ twoSLSBetaStar Z X y := by
    rw [Matrix.mulVec_mulVec]
    rw [fittedRegressorsStar_transpose_mul_eq_twoSLSMomentMatrixStar_of_nonsingular]
  rw [hfit]
  unfold twoSLSBetaStar
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hunit, Matrix.one_mulVec]
  simp

omit [DecidableEq k] in
/-- The 2SLS cross moment splits into fitted signal plus structural-error score. -/
theorem twoSLSMomentVector_linear_model
    (Z : Matrix n l ℝ) (X : Matrix n k ℝ) (β : k → ℝ) (e : n → ℝ)
    [Invertible (Zᵀ * Z)] :
    twoSLSMomentVector Z X (X *ᵥ β + e) =
      twoSLSMomentMatrix Z X *ᵥ β + twoSLSMomentVector Z X e := by
  unfold twoSLSMomentVector twoSLSMomentMatrix
  rw [Matrix.mulVec_add, Matrix.mulVec_mulVec]

omit [DecidableEq k] in
/-- Star 2SLS cross moment splits into fitted signal plus structural-error score. -/
theorem twoSLSMomentVectorStar_linear_model
    (Z : Matrix n l ℝ) (X : Matrix n k ℝ) (β : k → ℝ) (e : n → ℝ) :
    twoSLSMomentVectorStar Z X (X *ᵥ β + e) =
      twoSLSMomentMatrixStar Z X *ᵥ β + twoSLSMomentVectorStar Z X e := by
  unfold twoSLSMomentVectorStar twoSLSMomentMatrixStar
  rw [Matrix.mulVec_add, Matrix.mulVec_mulVec]

/-- Hansen equation (12.39), deterministic finite-sample form. Under the
structural equation `Y = Xβ + e`, nonsingular 2SLS equals `β` plus the projected
instrument-error term. -/
@[simp]
theorem twoSLSBeta_linear_model
    (Z : Matrix n l ℝ) (X : Matrix n k ℝ) (β : k → ℝ) (e : n → ℝ)
    [Invertible (Zᵀ * Z)] [Invertible (twoSLSMomentMatrix Z X)] :
    twoSLSBeta Z X (X *ᵥ β + e) =
      β + ⅟ (twoSLSMomentMatrix Z X) *ᵥ twoSLSMomentVector Z X e := by
  unfold twoSLSBeta
  rw [twoSLSMomentVector_linear_model]
  rw [Matrix.mulVec_add, Matrix.mulVec_mulVec β (⅟ (twoSLSMomentMatrix Z X))
    (twoSLSMomentMatrix Z X), invOf_mul_self]
  simp

/-- If the projected instrument-error cross moment is zero, finite-sample 2SLS
recovers the structural coefficient. -/
theorem twoSLSBeta_eq_of_projected_error_orthogonal
    (Z : Matrix n l ℝ) (X : Matrix n k ℝ) (β : k → ℝ) (e : n → ℝ)
    [Invertible (Zᵀ * Z)] [Invertible (twoSLSMomentMatrix Z X)]
    (he : twoSLSMomentVector Z X e = 0) :
    twoSLSBeta Z X (X *ᵥ β + e) = β := by
  rw [twoSLSBeta_linear_model, he]
  simp

/-- Exact Star version of Hansen equation (12.39).

The first term is the projected structural-error score. The second term is the
explicit totalization remainder; it vanishes whenever the Star 2SLS bread
matrix is nonsingular. -/
theorem twoSLSBetaStar_sub_identity
    (Z : Matrix n l ℝ) (X : Matrix n k ℝ) (β : k → ℝ) (e : n → ℝ) :
    twoSLSBetaStar Z X (X *ᵥ β + e) - β =
      (twoSLSMomentMatrixStar Z X)⁻¹ *ᵥ twoSLSMomentVectorStar Z X e +
        (((twoSLSMomentMatrixStar Z X)⁻¹ * twoSLSMomentMatrixStar Z X) *ᵥ β - β) := by
  unfold twoSLSBetaStar
  rw [twoSLSMomentVectorStar_linear_model]
  rw [Matrix.mulVec_add, Matrix.mulVec_mulVec]
  ext a
  simp
  ring

/-- On nonsingular Star 2SLS bread matrices, the totalization remainder in the
Star version of Hansen equation (12.39) is exactly zero. -/
theorem twoSLSBetaStar_sub_identity_of_nonsingular
    (Z : Matrix n l ℝ) (X : Matrix n k ℝ) (β : k → ℝ) (e : n → ℝ)
    (hunit : IsUnit (twoSLSMomentMatrixStar Z X).det) :
    twoSLSBetaStar Z X (X *ᵥ β + e) - β =
      (twoSLSMomentMatrixStar Z X)⁻¹ *ᵥ twoSLSMomentVectorStar Z X e := by
  rw [twoSLSBetaStar_sub_identity]
  rw [Matrix.nonsing_inv_mul _ hunit]
  simp

set_option linter.flexible false in
/-- Hansen-normalized 2SLS score identity.

The unnormalized Star score
`(X'P_ZX)^{-1} X'P_Ze` is exactly Hansen's normalized expression
`((Q̂_XZ Q̂_ZZ^{-1} Q̂_ZX)^{-1} Q̂_XZ Q̂_ZZ^{-1}) (n^{-1} Z'e)`.
This is the deterministic algebra behind the linearized term used in
Theorem 12.1. -/
theorem twoSLSLinearizationMatrix_mul_sampleCrossMoment_eq_momentStar
    (Z : Matrix n l ℝ) (X : Matrix n k ℝ) (e : n → ℝ) [Nonempty n] :
    twoSLSLinearizationMatrix Z X *ᵥ sampleCrossMoment Z e =
      (twoSLSMomentMatrixStar Z X)⁻¹ *ᵥ twoSLSMomentVectorStar Z X e := by
  have hN : (Fintype.card n : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  unfold twoSLSLinearizationMatrix twoSLSBread sampleQXZ sampleQZX sampleQZZ
    sampleGram sampleCrossMoment twoSLSMomentMatrixStar twoSLSMomentVectorStar
    instrumentProjectionStar
  rw [nonsingInv_smul]
  simp [Matrix.mul_assoc, Matrix.smul_mul, Matrix.mul_smul, Matrix.mulVec_smul,
    smul_smul, hN]
  let N : ℝ := Fintype.card n
  let M : Matrix k k ℝ := Xᵀ * (Z * ((Zᵀ * Z)⁻¹ * (Zᵀ * X)))
  let A : Matrix k n ℝ := Xᵀ * (Z * ((Zᵀ * Z)⁻¹ * Zᵀ))
  change N⁻¹ • (((N⁻¹ • M)⁻¹ * A) *ᵥ e) = (M⁻¹ * A) *ᵥ e
  have hN' : N ≠ 0 := by
    exact hN
  rw [nonsingInv_smul]
  rw [inv_inv, Matrix.smul_mul, Matrix.smul_mulVec]
  rw [smul_smul, inv_mul_cancel₀ hN', one_smul]

omit [Fintype k] [DecidableEq k] in
/-- Hansen's normalized sample 2SLS bread is the unnormalized Star 2SLS moment
matrix scaled by `n⁻¹` on nonempty samples. -/
theorem twoSLSBread_sample_eq_card_inv_smul_momentMatrixStar
    (Z : Matrix n l ℝ) (X : Matrix n k ℝ) [Nonempty n] :
    twoSLSBread (sampleQXZ Z X) (sampleQZZ Z) (sampleQZX Z X) =
      (Fintype.card n : ℝ)⁻¹ • twoSLSMomentMatrixStar Z X := by
  have hN : (Fintype.card n : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  unfold twoSLSBread sampleQXZ sampleQZX sampleQZZ sampleGram
    twoSLSMomentMatrixStar instrumentProjectionStar
  rw [nonsingInv_smul]
  simp [Matrix.mul_assoc, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hN]

/-- Nonsingularity of Hansen's normalized sample 2SLS bread implies
nonsingularity of the unnormalized Star moment matrix. -/
theorem isUnit_twoSLSMomentMatrixStar_det_of_sample_bread
    (Z : Matrix n l ℝ) (X : Matrix n k ℝ) [Nonempty n]
    (h : IsUnit
      (twoSLSBread (sampleQXZ Z X) (sampleQZZ Z) (sampleQZX Z X)).det) :
    IsUnit (twoSLSMomentMatrixStar Z X).det := by
  have hN : (Fintype.card n : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hbread :
      twoSLSBread (sampleQXZ Z X) (sampleQZZ Z) (sampleQZX Z X) =
        (Fintype.card n : ℝ)⁻¹ • twoSLSMomentMatrixStar Z X :=
    twoSLSBread_sample_eq_card_inv_smul_momentMatrixStar Z X
  have hdet_ne : ((Fintype.card n : ℝ)⁻¹ • twoSLSMomentMatrixStar Z X).det ≠ 0 := by
    simpa [hbread] using h.ne_zero
  have hstar_ne : (twoSLSMomentMatrixStar Z X).det ≠ 0 := by
    rw [Matrix.det_smul] at hdet_ne
    exact right_ne_zero_of_mul hdet_ne
  exact isUnit_iff_ne_zero.mpr hstar_ne

/-- Exact Hansen-normalized finite-sample linearization on nonsingular Star
2SLS bread matrices.  This discharges the estimator-linearization premise used
by the Chapter 12.1 consistency wrapper in the ordinary high-probability
nonsingular case. -/
theorem twoSLSBetaStar_sub_eq_linearizedScore_of_nonsingular
    (Z : Matrix n l ℝ) (X : Matrix n k ℝ) (β : k → ℝ) (e : n → ℝ)
    [Nonempty n] (hunit : IsUnit (twoSLSMomentMatrixStar Z X).det) :
    twoSLSBetaStar Z X (X *ᵥ β + e) - β =
      twoSLSLinearizationMatrix Z X *ᵥ sampleCrossMoment Z e := by
  rw [twoSLSBetaStar_sub_identity_of_nonsingular (hunit := hunit)]
  exact (twoSLSLinearizationMatrix_mul_sampleCrossMoment_eq_momentStar Z X e).symm

/-- Structural 2SLS residual decomposition, pointwise form.

For `Y = Xβ + e`, each structural residual equals the true error minus the
regressor fit of the coefficient error. This is the deterministic algebra
behind the residual-substitution step in Hansen Theorem 12.3. -/
@[simp]
theorem twoSLSResidualStar_linear_model_apply
    (Z : Matrix n l ℝ) (X : Matrix n k ℝ) (β : k → ℝ) (e : n → ℝ) (i : n) :
    twoSLSResidualStar Z X (X *ᵥ β + e) i =
      e i - X i ⬝ᵥ (twoSLSBetaStar Z X (X *ᵥ β + e) - β) := by
  unfold twoSLSResidualStar
  have hrow :
      X i ⬝ᵥ (twoSLSBetaStar Z X (X *ᵥ β + e) - β) =
        (X *ᵥ (twoSLSBetaStar Z X (X *ᵥ β + e) - β)) i := by
    simp [Matrix.mulVec, dotProduct]
  rw [hrow, Matrix.mulVec_sub]
  simp
  ring

/-- Structural 2SLS residual decomposition, vector form.

For `Y = Xβ + e`, the structural residual equals the true error minus the
regressor fit of the coefficient error. This is the deterministic algebra
behind the residual-substitution step in Hansen Theorem 12.3. -/
theorem twoSLSResidualStar_linear_model
    (Z : Matrix n l ℝ) (X : Matrix n k ℝ) (β : k → ℝ) (e : n → ℝ) :
    twoSLSResidualStar Z X (X *ᵥ β + e) =
      e - X *ᵥ (twoSLSBetaStar Z X (X *ᵥ β + e) - β) := by
  ext i
  rw [twoSLSResidualStar_linear_model_apply]
  simp [Matrix.mulVec, dotProduct]

/-- Structural residual decomposition with Hansen's normalized linearized score.

On positive nonsingular samples, the residual-substitution term is exactly
`X_i' ((Q̂_XZ Q̂_ZZ^{-1} Q̂_ZX)^{-1} Q̂_XZ Q̂_ZZ^{-1})(n^{-1}Z'e)`. -/
theorem twoSLSResidualStar_linear_model_of_nonsingular
    (Z : Matrix n l ℝ) (X : Matrix n k ℝ) (β : k → ℝ) (e : n → ℝ)
    [Nonempty n] (hunit : IsUnit (twoSLSMomentMatrixStar Z X).det) :
    twoSLSResidualStar Z X (X *ᵥ β + e) =
      e - X *ᵥ (twoSLSLinearizationMatrix Z X *ᵥ sampleCrossMoment Z e) := by
  rw [twoSLSResidualStar_linear_model]
  rw [twoSLSBetaStar_sub_eq_linearizedScore_of_nonsingular (hunit := hunit)]

/-- Hansen Theorem 12.3 residual-substitution identity for the robust middle.

Under the structural equation, the feasible robust middle is the sample
instrument outer-product average weighted by
`(eᵢ - Xᵢ'(β̂₂ₛₗₛ - β))²`. This is the deterministic bridge used before the
stochastic residual perturbation argument. -/
theorem twoSLSOmegaHatStar_linear_model
    (Z : Matrix n l ℝ) (X : Matrix n k ℝ) (β : k → ℝ) (e : n → ℝ) :
    twoSLSOmegaHatStar Z X (X *ᵥ β + e) =
      (Fintype.card n : ℝ)⁻¹ •
        ∑ i : n,
          (e i - X i ⬝ᵥ (twoSLSBetaStar Z X (X *ᵥ β + e) - β)) ^ 2 •
            Matrix.vecMulVec (Z i) (Z i) := by
  unfold twoSLSOmegaHatStar
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [twoSLSResidualStar_linear_model_apply]

omit [Fintype l] [DecidableEq k] [DecidableEq l] in
/-- Generic robust-middle residual expansion.

Substituting `e - Xd` into the robust IV middle gives the ideal true-error
middle minus twice the cross remainder plus the quadratic remainder. -/
theorem twoSLSOmegaResidual_expansion
    (Z : Matrix n l ℝ) (X : Matrix n k ℝ) (e : n → ℝ) (d : k → ℝ) :
    (Fintype.card n : ℝ)⁻¹ •
        ∑ i : n, (e i - X i ⬝ᵥ d) ^ 2 • Matrix.vecMulVec (Z i) (Z i) =
      twoSLSOmegaIdeal Z e -
        (2 : ℝ) • twoSLSOmegaCrossRemainder Z X e d +
          twoSLSOmegaQuadraticRemainder Z X d := by
  ext a b
  simp only [twoSLSOmegaIdeal, twoSLSOmegaCrossRemainder,
    twoSLSOmegaQuadraticRemainder, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.sum_apply, Matrix.vecMulVec, Matrix.of_apply, smul_eq_mul]
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Hansen Theorem 12.3 robust-middle residual-substitution expansion.

The feasible robust middle equals the true-error middle plus cross and
quadratic coefficient-error remainders. -/
theorem twoSLSOmegaHatStar_linear_model_expansion
    (Z : Matrix n l ℝ) (X : Matrix n k ℝ) (β : k → ℝ) (e : n → ℝ) :
    twoSLSOmegaHatStar Z X (X *ᵥ β + e) =
      twoSLSOmegaIdeal Z e -
        (2 : ℝ) •
          twoSLSOmegaCrossRemainder Z X e
            (twoSLSBetaStar Z X (X *ᵥ β + e) - β) +
          twoSLSOmegaQuadraticRemainder Z X
            (twoSLSBetaStar Z X (X *ᵥ β + e) - β) := by
  rw [twoSLSOmegaHatStar_linear_model]
  exact twoSLSOmegaResidual_expansion Z X e
    (twoSLSBetaStar Z X (X *ᵥ β + e) - β)

/-- Hansen Theorem 12.3 residual-substitution identity for the homoskedastic
middle `σ̂²`.

This is the scalar counterpart of `twoSLSOmegaHatStar_linear_model`. -/
theorem twoSLSSigmaSqHatStar_linear_model
    (Z : Matrix n l ℝ) (X : Matrix n k ℝ) (β : k → ℝ) (e : n → ℝ) :
    twoSLSSigmaSqHatStar Z X (X *ᵥ β + e) =
      sampleErrorSecondMoment
        (e - X *ᵥ (twoSLSBetaStar Z X (X *ᵥ β + e) - β)) := by
  unfold twoSLSSigmaSqHatStar
  rw [twoSLSResidualStar_linear_model]

/-- Hansen Theorem 12.3 scalar residual-substitution expansion.

The homoskedastic middle `σ̂²` equals the true-error second moment plus the
standard cross and quadratic coefficient-error remainders. -/
theorem twoSLSSigmaSqHatStar_linear_model_expansion
    (Z : Matrix n l ℝ) (X : Matrix n k ℝ) (β : k → ℝ) (e : n → ℝ) :
    twoSLSSigmaSqHatStar Z X (X *ᵥ β + e) =
      sampleErrorSecondMoment e -
        2 * (sampleCrossMoment X e ⬝ᵥ
          (twoSLSBetaStar Z X (X *ᵥ β + e) - β)) +
          (twoSLSBetaStar Z X (X *ᵥ β + e) - β) ⬝ᵥ
            (sampleGram X *ᵥ (twoSLSBetaStar Z X (X *ᵥ β + e) - β)) := by
  rw [twoSLSSigmaSqHatStar_linear_model]
  exact sampleErrorSecondMoment_sub_mulVec X e
    (twoSLSBetaStar Z X (X *ᵥ β + e) - β)

/-- Nonsingular-sample version of the robust-middle residual substitution,
written with Hansen's normalized 2SLS linearization score. -/
theorem twoSLSOmegaHatStar_linear_model_of_nonsingular
    (Z : Matrix n l ℝ) (X : Matrix n k ℝ) (β : k → ℝ) (e : n → ℝ)
    [Nonempty n] (hunit : IsUnit (twoSLSMomentMatrixStar Z X).det) :
    twoSLSOmegaHatStar Z X (X *ᵥ β + e) =
      (Fintype.card n : ℝ)⁻¹ •
        ∑ i : n,
          (e i - X i ⬝ᵥ (twoSLSLinearizationMatrix Z X *ᵥ sampleCrossMoment Z e)) ^ 2 •
            Matrix.vecMulVec (Z i) (Z i) := by
  rw [twoSLSOmegaHatStar_linear_model]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [twoSLSBetaStar_sub_eq_linearizedScore_of_nonsingular (hunit := hunit)]

/-- Nonsingular-sample robust-middle expansion, written with Hansen's
normalized 2SLS linearized score. -/
theorem twoSLSOmegaHatStar_linear_model_expansion_of_nonsingular
    (Z : Matrix n l ℝ) (X : Matrix n k ℝ) (β : k → ℝ) (e : n → ℝ)
    [Nonempty n] (hunit : IsUnit (twoSLSMomentMatrixStar Z X).det) :
    twoSLSOmegaHatStar Z X (X *ᵥ β + e) =
      twoSLSOmegaIdeal Z e -
        (2 : ℝ) •
          twoSLSOmegaCrossRemainder Z X e
            (twoSLSLinearizationMatrix Z X *ᵥ sampleCrossMoment Z e) +
          twoSLSOmegaQuadraticRemainder Z X
            (twoSLSLinearizationMatrix Z X *ᵥ sampleCrossMoment Z e) := by
  rw [twoSLSOmegaHatStar_linear_model_expansion]
  rw [twoSLSBetaStar_sub_eq_linearizedScore_of_nonsingular (hunit := hunit)]

/-- Nonsingular-sample version of the homoskedastic residual substitution,
written with Hansen's normalized 2SLS linearization score. -/
theorem twoSLSSigmaSqHatStar_linear_model_of_nonsingular
    (Z : Matrix n l ℝ) (X : Matrix n k ℝ) (β : k → ℝ) (e : n → ℝ)
    [Nonempty n] (hunit : IsUnit (twoSLSMomentMatrixStar Z X).det) :
    twoSLSSigmaSqHatStar Z X (X *ᵥ β + e) =
      sampleErrorSecondMoment
        (e - X *ᵥ (twoSLSLinearizationMatrix Z X *ᵥ sampleCrossMoment Z e)) := by
  rw [twoSLSSigmaSqHatStar_linear_model]
  rw [twoSLSBetaStar_sub_eq_linearizedScore_of_nonsingular (hunit := hunit)]

/-- Nonsingular-sample scalar expansion of `σ̂²`, written with Hansen's
normalized 2SLS linearized score. -/
theorem twoSLSSigmaSqHatStar_linear_model_expansion_of_nonsingular
    (Z : Matrix n l ℝ) (X : Matrix n k ℝ) (β : k → ℝ) (e : n → ℝ)
    [Nonempty n] (hunit : IsUnit (twoSLSMomentMatrixStar Z X).det) :
    twoSLSSigmaSqHatStar Z X (X *ᵥ β + e) =
      sampleErrorSecondMoment e -
        2 * (sampleCrossMoment X e ⬝ᵥ
          (twoSLSLinearizationMatrix Z X *ᵥ sampleCrossMoment Z e)) +
          (twoSLSLinearizationMatrix Z X *ᵥ sampleCrossMoment Z e) ⬝ᵥ
            (sampleGram X *ᵥ
              (twoSLSLinearizationMatrix Z X *ᵥ sampleCrossMoment Z e)) := by
  rw [twoSLSSigmaSqHatStar_linear_model_expansion]
  rw [twoSLSBetaStar_sub_eq_linearizedScore_of_nonsingular (hunit := hunit)]

/-- Hansen Theorem 12.3 residual-substitution identity for the robust
covariance estimator itself. This is the covariance-sandwich wrapper around
`twoSLSOmegaHatStar_linear_model`. -/
theorem twoSLSVHatStar_linear_model
    (Z : Matrix n l ℝ) (X : Matrix n k ℝ) (β : k → ℝ) (e : n → ℝ) :
    twoSLSVHatStar Z X (X *ᵥ β + e) =
      twoSLSAsymptoticVariance
        (sampleQXZ Z X) (sampleQZZ Z)
        ((Fintype.card n : ℝ)⁻¹ •
          ∑ i : n,
            (e i - X i ⬝ᵥ (twoSLSBetaStar Z X (X *ᵥ β + e) - β)) ^ 2 •
              Matrix.vecMulVec (Z i) (Z i))
        (sampleQZX Z X) := by
  rw [twoSLSVHatStar, twoSLSOmegaHatStar_linear_model]

/-- Hansen Theorem 12.3 residual-substitution identity for the homoskedastic
covariance estimator itself. This is the covariance-sandwich wrapper around
`twoSLSSigmaSqHatStar_linear_model`. -/
theorem twoSLSHomoskedasticVHatStar_linear_model
    (Z : Matrix n l ℝ) (X : Matrix n k ℝ) (β : k → ℝ) (e : n → ℝ) :
    twoSLSHomoskedasticVHatStar Z X (X *ᵥ β + e) =
      twoSLSHomoskedasticAsymptoticVariance
        (sampleQXZ Z X) (sampleQZZ Z) (sampleQZX Z X)
        (sampleErrorSecondMoment
          (e - X *ᵥ (twoSLSBetaStar Z X (X *ᵥ β + e) - β))) := by
  rw [twoSLSHomoskedasticVHatStar, twoSLSSigmaSqHatStar_linear_model]

/-- Nonsingular-sample version of `twoSLSVHatStar_linear_model`, written with
Hansen's normalized 2SLS linearization score. -/
theorem twoSLSVHatStar_linear_model_of_nonsingular
    (Z : Matrix n l ℝ) (X : Matrix n k ℝ) (β : k → ℝ) (e : n → ℝ)
    [Nonempty n] (hunit : IsUnit (twoSLSMomentMatrixStar Z X).det) :
    twoSLSVHatStar Z X (X *ᵥ β + e) =
      twoSLSAsymptoticVariance
        (sampleQXZ Z X) (sampleQZZ Z)
        ((Fintype.card n : ℝ)⁻¹ •
          ∑ i : n,
            (e i - X i ⬝ᵥ (twoSLSLinearizationMatrix Z X *ᵥ sampleCrossMoment Z e)) ^ 2 •
              Matrix.vecMulVec (Z i) (Z i))
        (sampleQZX Z X) := by
  rw [twoSLSVHatStar, twoSLSOmegaHatStar_linear_model_of_nonsingular
    (hunit := hunit)]

/-- Nonsingular-sample version of
`twoSLSHomoskedasticVHatStar_linear_model`, written with Hansen's normalized
2SLS linearization score. -/
theorem twoSLSHomoskedasticVHatStar_linear_model_of_nonsingular
    (Z : Matrix n l ℝ) (X : Matrix n k ℝ) (β : k → ℝ) (e : n → ℝ)
    [Nonempty n] (hunit : IsUnit (twoSLSMomentMatrixStar Z X).det) :
    twoSLSHomoskedasticVHatStar Z X (X *ᵥ β + e) =
      twoSLSHomoskedasticAsymptoticVariance
        (sampleQXZ Z X) (sampleQZZ Z) (sampleQZX Z X)
        (sampleErrorSecondMoment
          (e - X *ᵥ (twoSLSLinearizationMatrix Z X *ᵥ sampleCrossMoment Z e))) := by
  rw [twoSLSHomoskedasticVHatStar, twoSLSSigmaSqHatStar_linear_model_of_nonsingular
    (hunit := hunit)]

end HansenEconometrics
