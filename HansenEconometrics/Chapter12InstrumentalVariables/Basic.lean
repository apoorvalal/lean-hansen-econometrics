import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import HansenEconometrics.LinearAlgebraUtils

/-!
# Chapter 12 - instrumental variables basics

This file contains deterministic matrix notation for Hansen's instrumental
variables chapter: instrument moments, projection onto the instrument span,
2SLS, k-class/LIML, split-sample IV, JIVE, Wald IV, and the asymptotic variance
matrices used by later theorem-facing wrappers.
-/

open scoped Matrix

namespace HansenEconometrics

open Matrix

variable {n k l q : Type*}
variable [Fintype n] [Fintype k] [Fintype l] [Fintype q]
variable [DecidableEq n] [DecidableEq k] [DecidableEq l] [DecidableEq q]

/-- Sample instrument/regressor cross moment `Z'X`. -/
noncomputable def ivCrossMoment (Z : Matrix n l ℝ) (X : Matrix n k ℝ) : Matrix l k ℝ :=
  Zᵀ * X

/-- Hansen normalized sample instrument moment `n⁻¹ Z'Z`. -/
noncomputable def ivNormalizedInstrumentMoment (Z : Matrix n l ℝ) : Matrix l l ℝ :=
  (Fintype.card n : ℝ)⁻¹ • (Zᵀ * Z)

/-- Hansen normalized sample instrument/regressor cross moment `n⁻¹ Z'X`. -/
noncomputable def ivNormalizedCrossMoment (Z : Matrix n l ℝ) (X : Matrix n k ℝ) :
    Matrix l k ℝ :=
  (Fintype.card n : ℝ)⁻¹ • (Zᵀ * X)

/-- Hansen normalized sample instrument/outcome moment `n⁻¹ Z'Y`. -/
noncomputable def ivNormalizedOutcomeMoment (Z : Matrix n l ℝ) (Y : n → ℝ) : l → ℝ :=
  (Fintype.card n : ℝ)⁻¹ • (Zᵀ *ᵥ Y)

/-- Sample instrument/error moment `Z'e`. -/
noncomputable def ivScore (Z : Matrix n l ℝ) (e : n → ℝ) : l → ℝ :=
  Zᵀ *ᵥ e

/-- Hansen normalized sample instrument/error moment `n⁻¹ Z'e`. -/
noncomputable def ivNormalizedScore (Z : Matrix n l ℝ) (e : n → ℝ) : l → ℝ :=
  (Fintype.card n : ℝ)⁻¹ • (Zᵀ *ᵥ e)

/-- Projection matrix onto the span of the instruments, using the total matrix inverse. -/
noncomputable def instrumentProjectionMatrix (Z : Matrix n l ℝ) : Matrix n n ℝ :=
  Z * (Zᵀ * Z)⁻¹ * Zᵀ

/-- Fitted first-stage regressors `P_Z X`. -/
noncomputable def firstStageFitted (Z : Matrix n l ℝ) (X : Matrix n k ℝ) : Matrix n k ℝ :=
  instrumentProjectionMatrix Z * X

/-- First-stage residuals `X - P_Z X`. -/
noncomputable def firstStageResidual (Z : Matrix n l ℝ) (X : Matrix n k ℝ) : Matrix n k ℝ :=
  X - firstStageFitted Z X

/-- Total 2SLS coefficient estimator. -/
noncomputable def twoStageLeastSquaresBeta
    (X : Matrix n k ℝ) (Z : Matrix n l ℝ) (Y : n → ℝ) : k → ℝ :=
  ((Xᵀ * instrumentProjectionMatrix Z * X)⁻¹) *ᵥ
    ((Xᵀ * instrumentProjectionMatrix Z) *ᵥ Y)

/-- Moment-form 2SLS coefficient map
`(Q_ZX' Q_ZZ⁻¹ Q_ZX)⁻¹ Q_ZX' Q_ZZ⁻¹ Q_ZY`.

This is the deterministic continuous-mapping surface used by the Chapter 12
consistency and asymptotic-normality proofs after sample moments have been
shown to converge. -/
noncomputable def twoStageLeastSquaresMomentBeta
    (QZX : Matrix l k ℝ) (QZZ : Matrix l l ℝ) (QZY : l → ℝ) : k → ℝ :=
  (QZXᵀ * QZZ⁻¹ * QZX)⁻¹ *ᵥ ((QZXᵀ * QZZ⁻¹) *ᵥ QZY)

/-- Star alias for the total 2SLS estimator, following the Chapter 7+ totalization pattern. -/
noncomputable def twoStageLeastSquaresBetaStar
    (X : Matrix n k ℝ) (Z : Matrix n l ℝ) (Y : n → ℝ) : k → ℝ :=
  twoStageLeastSquaresBeta X Z Y

/-- Textbook-facing OrZero 2SLS primitive.

The estimator branches on the rank matrix used by the displayed 2SLS formula.
On singular designs it returns zero, matching the OrZero convention for
textbook-facing estimators. -/
noncomputable def twoStageLeastSquaresBetaOrZero
    (X : Matrix n k ℝ) (Z : Matrix n l ℝ) (Y : n → ℝ) : k → ℝ := by
  classical
  exact
    if (Xᵀ * instrumentProjectionMatrix Z * X).det = 0 then
      0
    else
      twoStageLeastSquaresBeta X Z Y

omit [DecidableEq n] in
/-- The Star 2SLS alias is definitionally the displayed 2SLS estimator. -/
@[simp]
theorem twoStageLeastSquaresBetaStar_eq
    (X : Matrix n k ℝ) (Z : Matrix n l ℝ) (Y : n → ℝ) :
    twoStageLeastSquaresBetaStar X Z Y = twoStageLeastSquaresBeta X Z Y :=
  rfl

omit [Fintype n] [DecidableEq n] in
/-- Population moment identity behind Hansen Theorem 12.1.

If `Q_ZY = Q_ZX β` and the 2SLS bread matrix is nonsingular, the moment-form
2SLS map returns the structural coefficient `β`. -/
theorem twoStageLeastSquaresMomentBeta_eq_beta
    (QZX : Matrix l k ℝ) (QZZ : Matrix l l ℝ) (QZY : l → ℝ) (β : k → ℝ)
    (hQZY : QZY = QZX *ᵥ β)
    (hunit : IsUnit (QZXᵀ * QZZ⁻¹ * QZX).det) :
    twoStageLeastSquaresMomentBeta QZX QZZ QZY = β := by
  have hunit' : IsUnit (QZXᵀ * (QZZ⁻¹ * QZX)).det := by
    simpa [Matrix.mul_assoc] using hunit
  simp [twoStageLeastSquaresMomentBeta, hQZY, Matrix.mulVec_mulVec, Matrix.mul_assoc,
    Matrix.nonsing_inv_mul _ hunit']

omit [DecidableEq n] in
/-- The displayed finite-sample 2SLS formula equals the deterministic moment-form
map evaluated at the unnormalized sample moments `Z'X`, `Z'Z`, and `Z'Y`. -/
theorem twoStageLeastSquaresBeta_eq_momentBeta
    (X : Matrix n k ℝ) (Z : Matrix n l ℝ) (Y : n → ℝ) :
    twoStageLeastSquaresBeta X Z Y =
      twoStageLeastSquaresMomentBeta (Zᵀ * X) (Zᵀ * Z) (Zᵀ *ᵥ Y) := by
  simp [twoStageLeastSquaresBeta, twoStageLeastSquaresMomentBeta,
    instrumentProjectionMatrix, Matrix.mulVec_mulVec, Matrix.mul_assoc]

omit [DecidableEq n] in
/-- The finite-sample 2SLS estimator also equals the moment-form map evaluated
at Hansen's normalized sample moments. -/
theorem twoStageLeastSquaresBeta_eq_normalizedMomentBeta
    (X : Matrix n k ℝ) (Z : Matrix n l ℝ) (Y : n → ℝ) [Nonempty n] :
    twoStageLeastSquaresBeta X Z Y =
      twoStageLeastSquaresMomentBeta
        ((Fintype.card n : ℝ)⁻¹ • (Zᵀ * X))
        ((Fintype.card n : ℝ)⁻¹ • (Zᵀ * Z))
        ((Fintype.card n : ℝ)⁻¹ • (Zᵀ *ᵥ Y)) := by
  let c : ℝ := (Fintype.card n : ℝ)⁻¹
  have hcard : (Fintype.card n : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hc : c ≠ 0 := inv_ne_zero hcard
  rw [twoStageLeastSquaresBeta_eq_momentBeta]
  unfold twoStageLeastSquaresMomentBeta
  simp [nonsingInv_smul, Matrix.transpose_smul, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.smul_mulVec, Matrix.mulVec_smul, smul_smul,
    Matrix.mul_assoc]

omit [DecidableEq n] in
/-- The normalized-moment bridge in terms of the named Chapter 12 sample moments. -/
theorem twoStageLeastSquaresBeta_eq_normalizedSampleMoments
    (X : Matrix n k ℝ) (Z : Matrix n l ℝ) (Y : n → ℝ) [Nonempty n] :
    twoStageLeastSquaresBeta X Z Y =
      twoStageLeastSquaresMomentBeta
        (ivNormalizedCrossMoment Z X)
        (ivNormalizedInstrumentMoment Z)
        (ivNormalizedOutcomeMoment Z Y) := by
  simpa [ivNormalizedCrossMoment, ivNormalizedInstrumentMoment, ivNormalizedOutcomeMoment] using
    twoStageLeastSquaresBeta_eq_normalizedMomentBeta X Z Y

omit [DecidableEq n] [Fintype l] [DecidableEq k] [DecidableEq l] in
/-- Structural-equation identity for Hansen's normalized IV outcome moment:
`n⁻¹ Z'Y = (n⁻¹ Z'X)β + n⁻¹ Z'e`. -/
theorem ivNormalizedOutcomeMoment_linear_model
    (X : Matrix n k ℝ) (Z : Matrix n l ℝ) (β : k → ℝ) (e : n → ℝ) :
    ivNormalizedOutcomeMoment Z (X *ᵥ β + e) =
      ivNormalizedCrossMoment Z X *ᵥ β + ivNormalizedScore Z e := by
  unfold ivNormalizedOutcomeMoment ivNormalizedCrossMoment ivNormalizedScore
  rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, smul_add, Matrix.smul_mulVec]

omit [DecidableEq n] in
/-- On nonsingular designs, the OrZero 2SLS estimator equals the total 2SLS formula. -/
@[simp]
theorem twoStageLeastSquaresBetaOrZero_eq_of_det_ne_zero
    (X : Matrix n k ℝ) (Z : Matrix n l ℝ) (Y : n → ℝ)
    (h : (Xᵀ * instrumentProjectionMatrix Z * X).det ≠ 0) :
    twoStageLeastSquaresBetaOrZero X Z Y = twoStageLeastSquaresBeta X Z Y := by
  classical
  simp [twoStageLeastSquaresBetaOrZero, h]

omit [DecidableEq n] in
/-- On singular designs, the OrZero 2SLS estimator returns zero. -/
@[simp]
theorem twoStageLeastSquaresBetaOrZero_eq_zero_of_det_eq_zero
    (X : Matrix n k ℝ) (Z : Matrix n l ℝ) (Y : n → ℝ)
    (h : (Xᵀ * instrumentProjectionMatrix Z * X).det = 0) :
    twoStageLeastSquaresBetaOrZero X Z Y = 0 := by
  classical
  simp [twoStageLeastSquaresBetaOrZero, h]

/-- Just-identified IV estimator in moment form, with `Z'X` square. -/
noncomputable def justIdentifiedIVBeta
    (X Z : Matrix n k ℝ) (Y : n → ℝ) : k → ℝ :=
  (Zᵀ * X)⁻¹ *ᵥ (Zᵀ *ᵥ Y)

/-- Scalar Wald IV estimator `(E[Y|Z=1]-E[Y|Z=0])/(E[X|Z=1]-E[X|Z=0])`. -/
noncomputable def waldIVEstimator (Y1 Y0 X1 X0 : ℝ) : ℝ :=
  (Y1 - Y0) / (X1 - X0)

/-- k-class weight matrix `I - kappa (I - P_Z)`. -/
noncomputable def kClassWeight (kappa : ℝ) (Z : Matrix n l ℝ) : Matrix n n ℝ :=
  (1 : Matrix n n ℝ) - kappa • ((1 : Matrix n n ℝ) - instrumentProjectionMatrix Z)

/-- k-class estimator; LIML is obtained by plugging in the LIML value of `kappa`. -/
noncomputable def kClassBeta
    (kappa : ℝ) (X : Matrix n k ℝ) (Z : Matrix n l ℝ) (Y : n → ℝ) : k → ℝ :=
  ((Xᵀ * kClassWeight kappa Z * X)⁻¹) *ᵥ ((Xᵀ * kClassWeight kappa Z) *ᵥ Y)

/-- Limited-information maximum likelihood estimator surface. -/
noncomputable def limlBeta
    (kappaHat : ℝ) (X : Matrix n k ℝ) (Z : Matrix n l ℝ) (Y : n → ℝ) : k → ℝ :=
  kClassBeta kappaHat X Z Y

/-- Split-sample IV estimator surface. The cross moments may come from independent samples. -/
noncomputable def splitSampleIVBeta
    (ZX : Matrix l k ℝ) (ZY : l → ℝ) : k → ℝ :=
  (ZXᵀ * ZX)⁻¹ *ᵥ (ZXᵀ *ᵥ ZY)

/-- JIVE estimator surface, written with a supplied leave-one-out instrument weight matrix. -/
noncomputable def jiveBeta
    (J : Matrix n n ℝ) (X : Matrix n k ℝ) (Y : n → ℝ) : k → ℝ :=
  ((Xᵀ * J * X)⁻¹) *ᵥ ((Xᵀ * J) *ᵥ Y)

/-- 2SLS asymptotic bread matrix `(Q_ZX' Q_ZZ^-1 Q_ZX)^-1`. -/
noncomputable def tslsBread
    (QZX : Matrix l k ℝ) (QZZ : Matrix l l ℝ) : Matrix k k ℝ :=
  (QZXᵀ * QZZ⁻¹ * QZX)⁻¹

/-- 2SLS influence matrix multiplying the instrument score `n⁻¹/² Z'e`. -/
noncomputable def tslsInfluenceMatrix
    (QZX : Matrix l k ℝ) (QZZ : Matrix l l ℝ) : Matrix k l ℝ :=
  tslsBread QZX QZZ * QZXᵀ * QZZ⁻¹

/-- 2SLS asymptotic meat matrix. -/
noncomputable def tslsMeat
    (QZX : Matrix l k ℝ) (QZZ Omega : Matrix l l ℝ) : Matrix k k ℝ :=
  QZXᵀ * QZZ⁻¹ * Omega * QZZ⁻¹ * QZX

/-- Hansen Chapter 12 robust 2SLS asymptotic variance. -/
noncomputable def tslsAsymptoticVariance
    (QZX : Matrix l k ℝ) (QZZ Omega : Matrix l l ℝ) : Matrix k k ℝ :=
  tslsBread QZX QZZ * tslsMeat QZX QZZ Omega * tslsBread QZX QZZ

/-- Delta-method covariance for functions of 2SLS parameters. -/
noncomputable def tslsDeltaVariance
    (Vbeta : Matrix k k ℝ) (R : Matrix k q ℝ) : Matrix q q ℝ :=
  Rᵀ * Vbeta * R

/-- Homoskedastic 2SLS asymptotic variance `sigma^2 (Q_ZX' Q_ZZ^-1 Q_ZX)^-1`. -/
noncomputable def tslsHomoskedasticVariance
    (sigma2 : ℝ) (QZX : Matrix l k ℝ) (QZZ : Matrix l l ℝ) : Matrix k k ℝ :=
  sigma2 • tslsBread QZX QZZ

/-- First-stage Wald/F-statistic numerator for excluded instruments. -/
noncomputable def firstStageWaldStatistic
    (gammaHat : q → ℝ) (Vhat : Matrix q q ℝ) : ℝ :=
  gammaHat ⬝ᵥ (Vhat⁻¹ *ᵥ gammaHat)

omit [Fintype k] [DecidableEq n] [DecidableEq k] in
@[simp]
theorem firstStageFitted_eq_projection_mul
    (Z : Matrix n l ℝ) (X : Matrix n k ℝ) :
    firstStageFitted Z X = instrumentProjectionMatrix Z * X :=
  rfl

@[simp]
theorem limlBeta_eq_kClassBeta
    (kappaHat : ℝ) (X : Matrix n k ℝ) (Z : Matrix n l ℝ) (Y : n → ℝ) :
    limlBeta kappaHat X Z Y = kClassBeta kappaHat X Z Y :=
  rfl

end HansenEconometrics
