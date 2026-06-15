import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

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

/-- Sample instrument/error moment `Z'e`. -/
noncomputable def ivScore (Z : Matrix n l ℝ) (e : n → ℝ) : l → ℝ :=
  Zᵀ *ᵥ e

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
