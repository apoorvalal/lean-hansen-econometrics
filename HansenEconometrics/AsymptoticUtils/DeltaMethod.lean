import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Inv
import HansenEconometrics.AsymptoticUtils
import HansenEconometrics.AsymptoticUtils.StochasticOrder
import HansenEconometrics.ProbabilityUtils

/-!
# Delta-method and smooth-function asymptotic wrappers

This module provides the Chapter 6-facing Delta-method and smooth-function
surface.  The Delta-method statement is split into the deterministic
differentiability remainder and the stochastic Slutsky step, matching Mathlib's
Fréchet derivative API without introducing a parallel stochastic-order
framework.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology MeasureTheory ProbabilityTheory Function
open scoped Matrix MatrixOrder RealInnerProductSpace

namespace HansenEconometrics

variable {Ω Ω' E F : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {μ : Measure Ω} {ν : Measure Ω'}

section DeterministicRemainder

variable [SeminormedAddCommGroup E] [NormedSpace ℝ E]
  [SeminormedAddCommGroup F] [NormedSpace ℝ F]

/-- Deterministic Delta-method remainder from Mathlib's Fréchet derivative API.

This is the analytic core of Hansen Theorem 6.8: after subtracting the linear
approximation, the remainder is little-o of the input displacement. -/
theorem deltaMethod_remainder_isLittleO
    {g : E → F} {G : E →L[ℝ] F} {θ : E}
    (hg : HasFDerivAt g G θ) :
    (fun x => g x - g θ - G (x - θ)) =o[𝓝 θ] (fun x => x - θ) :=
  hg.isLittleO

end DeterministicRemainder

section SmoothFunctionCondition

variable {k q : Type*} [Fintype k] [Fintype q]

/-- Generic deterministic content of Hansen Assumption 7.3 for a smooth finite-dimensional
function of a parameter vector.

The matrix `R` follows Hansen's convention `R = ∂r(β)' / ∂β`, so the Fréchet derivative
acts as `v ↦ Rᵀ v`. Stochastic consistency, asymptotic normality, and covariance
estimation remain theorem-specific inputs. -/
structure SmoothFunctionCondition
    (r : (k → ℝ) → (q → ℝ)) (β : k → ℝ) (R : Matrix k q ℝ) where
  /-- Fréchet derivative of `r` at `β`. -/
  derivative : (k → ℝ) →L[ℝ] (q → ℝ)
  /-- Differentiability at the true parameter. -/
  differentiable_at : HasFDerivAt r derivative β
  /-- The derivative is represented by Hansen's transpose-oriented matrix. -/
  derivative_apply : ∀ v : k → ℝ, derivative v = Rᵀ *ᵥ v
  /-- Hansen's full-column-rank derivative condition. -/
  fullRank : Function.Injective R.mulVec

namespace SmoothFunctionCondition

/-- Hansen Assumption 7.3 supplies the continuity needed for smooth-function consistency. -/
theorem continuousAt
    {r : (k → ℝ) → (q → ℝ)} {β : k → ℝ} {R : Matrix k q ℝ}
    (h73 : SmoothFunctionCondition r β R) :
    ContinuousAt r β :=
  h73.differentiable_at.continuousAt

/-- Assumption 7.3 supplies the deterministic Delta-method little-o Taylor remainder. -/
theorem taylorRemainder_isLittleO
    {r : (k → ℝ) → (q → ℝ)} {β : k → ℝ} {R : Matrix k q ℝ}
    (h73 : SmoothFunctionCondition r β R) :
    (fun b => r b - r β - Rᵀ *ᵥ (b - β)) =o[𝓝 β] (fun b => b - β) := by
  simpa [h73.derivative_apply] using
    deltaMethod_remainder_isLittleO h73.differentiable_at

end SmoothFunctionCondition

end SmoothFunctionCondition

section ConcreteTransforms

/-- Scalar square derivative, packaged as a Fréchet derivative.

This is the deterministic derivative for the common scalar nonlinear transform
`x ↦ x²` used by Delta-method examples. -/
theorem scalarSquare_hasFDerivAt (θ : ℝ) :
    HasFDerivAt (fun x : ℝ => x ^ 2)
      (((2 : ℝ) * θ) • (ContinuousLinearMap.id ℝ ℝ)) θ := by
  simpa [two_nsmul, pow_one] using
    (hasFDerivAt_pow (𝕜 := ℝ) (𝔸 := ℝ) 2 (x := θ))

/-- Scalar square Delta-method remainder.

After subtracting the derivative image `(2θ)(x - θ)`, the square transform has a
little-o remainder relative to the scalar displacement. -/
theorem scalarSquare_deltaMethod_remainder_isLittleO (θ : ℝ) :
    (fun x : ℝ =>
      x ^ 2 - θ ^ 2 -
        (((2 : ℝ) * θ) • (ContinuousLinearMap.id ℝ ℝ)) (x - θ))
        =o[𝓝 θ] (fun x => x - θ) :=
  deltaMethod_remainder_isLittleO (scalarSquare_hasFDerivAt θ)

variable {k : Type*} [Fintype k]

set_option linter.unusedFintypeInType false in
/-- Coordinate-square derivative for a finite-dimensional parameter vector.

For a fixed coordinate `j`, the derivative of `β ↦ β_j²` is the coordinate
projection multiplied by `2 β_j`. -/
theorem coordinateSquare_hasFDerivAt (j : k) (β : k → ℝ) :
    HasFDerivAt (fun b : k → ℝ => (b j) ^ 2)
      (((2 : ℝ) * β j) •
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : k => ℝ) j)) β := by
  have hsq := scalarSquare_hasFDerivAt (β j)
  simpa [ContinuousLinearMap.comp_def, Function.comp_def] using
    hsq.comp β
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : k => ℝ) j).hasFDerivAt

/-- Coordinate-square Delta-method remainder.

This is the transform-specific Fréchet remainder for the nonlinear coefficient
map `β ↦ β_j²`. -/
theorem coordinateSquare_deltaMethod_remainder_isLittleO (j : k) (β : k → ℝ) :
    (fun b : k → ℝ =>
      (b j) ^ 2 - (β j) ^ 2 -
        (((2 : ℝ) * β j) •
          (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : k => ℝ) j))
          (b - β))
        =o[𝓝 β] (fun b => b - β) :=
  deltaMethod_remainder_isLittleO (coordinateSquare_hasFDerivAt j β)

set_option linter.unusedFintypeInType false in
/-- One-dimensional vector-valued coordinate-square derivative.

This is the finite-dimensional shape used when Chapter 7 states a nonlinear
parameter map as an `R¹`-valued transform. -/
theorem coordinateSquareVector_hasFDerivAt (j : k) (β : k → ℝ) :
    HasFDerivAt (fun b : k → ℝ => fun _ : Fin 1 => (b j) ^ 2)
      (ContinuousLinearMap.pi fun _ : Fin 1 =>
        (((2 : ℝ) * β j) •
          (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : k => ℝ) j))) β := by
  exact hasFDerivAt_pi.mpr fun _ => coordinateSquare_hasFDerivAt j β

/-- One-dimensional vector-valued coordinate-square Delta-method remainder. -/
theorem coordinateSquareVector_deltaMethod_remainder_isLittleO (j : k) (β : k → ℝ) :
    (fun b : k → ℝ =>
      (fun _ : Fin 1 => (b j) ^ 2) - (fun _ : Fin 1 => (β j) ^ 2) -
        (ContinuousLinearMap.pi fun _ : Fin 1 =>
          (((2 : ℝ) * β j) •
            (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : k => ℝ) j)))
          (b - β))
        =o[𝓝 β] (fun b => b - β) :=
  deltaMethod_remainder_isLittleO (coordinateSquareVector_hasFDerivAt j β)

/-- Matrix row for the derivative of the coordinate-square transform `β ↦ β_j²`.

The single row has coefficient `2 β_j` in coordinate `j` and zero elsewhere. -/
def coordinateSquareDerivativeMatrix {k : Type*} [DecidableEq k]
    (j : k) (β : k → ℝ) : Matrix (Fin 1) k ℝ :=
  fun _ => Pi.single j ((2 : ℝ) * β j)

/-- Applying the coordinate-square derivative row is scalar multiplication of
the selected coordinate. -/
private theorem coordinateSquareDerivativeMatrix_mulVec {k : Type*} [Fintype k] [DecidableEq k]
    (j : k) (β v : k → ℝ) :
    (coordinateSquareDerivativeMatrix j β *ᵥ v) 0 = ((2 : ℝ) * β j) * v j := by
  simp [coordinateSquareDerivativeMatrix, Matrix.mulVec]

/-- Euclidean-space application form of `coordinateSquareDerivativeMatrix_mulVec`. -/
private theorem matrixContinuousLinearMap_coordinateSquareDerivativeMatrix_apply
    {k : Type*} [Fintype k] [DecidableEq k]
    (j : k) (β : k → ℝ) (v : EuclideanSpace ℝ k) :
    (matrixContinuousLinearMap (coordinateSquareDerivativeMatrix j β) v).ofLp 0 =
      ((2 : ℝ) * β j) * v.ofLp j := by
  rw [matrixContinuousLinearMap_apply]
  exact coordinateSquareDerivativeMatrix_mulVec j β v.ofLp

/-- Gaussian image law for the coordinate-square derivative row.

This is the concrete derivative-image law used by one-dimensional nonlinear
Delta-method examples such as `β_j²`. -/
theorem coordinateSquareDerivativeMatrix_hasLaw_multivariateGaussian_zero
    {k : Type*} [Fintype k] [DecidableEq k]
    {S : Matrix k k ℝ} (hS : S.PosSemidef) (j : k) (β : k → ℝ) :
    HasLaw
      (fun z : EuclideanSpace ℝ k =>
        matrixContinuousLinearMap (coordinateSquareDerivativeMatrix j β) z)
      (multivariateGaussian 0
        (coordinateSquareDerivativeMatrix j β * S * (coordinateSquareDerivativeMatrix j β)ᵀ))
      (multivariateGaussian 0 S) := by
  simpa using
    hasLaw_multivariateGaussian_zero_linearMap (n := k) (q := Fin 1) hS
      (coordinateSquareDerivativeMatrix j β)

/-- Scalar reciprocal derivative, packaged as a Fréchet derivative. -/
theorem scalarInv_hasFDerivAt {θ : ℝ} (hθ : θ ≠ 0) :
    HasFDerivAt (fun x : ℝ => x⁻¹)
      (ContinuousLinearMap.toSpanSingleton ℝ (-(θ ^ 2)⁻¹)) θ := by
  simpa using (hasFDerivAt_inv (𝕜 := ℝ) hθ)

/-- Scalar reciprocal Delta-method remainder. -/
theorem scalarInv_deltaMethod_remainder_isLittleO {θ : ℝ} (hθ : θ ≠ 0) :
    (fun x : ℝ =>
      x⁻¹ - θ⁻¹ -
        (ContinuousLinearMap.toSpanSingleton ℝ (-(θ ^ 2)⁻¹)) (x - θ))
        =o[𝓝 θ] (fun x => x - θ) :=
  deltaMethod_remainder_isLittleO (scalarInv_hasFDerivAt hθ)

set_option linter.unusedFintypeInType false in
/-- Coordinate-reciprocal derivative for a finite-dimensional parameter vector. -/
theorem coordinateInv_hasFDerivAt (j : k) {β : k → ℝ} (hβj : β j ≠ 0) :
    HasFDerivAt (fun b : k → ℝ => (b j)⁻¹)
      ((ContinuousLinearMap.toSpanSingleton ℝ (-(β j ^ 2)⁻¹)).comp
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : k => ℝ) j)) β := by
  have hinv := scalarInv_hasFDerivAt hβj
  simpa [Function.comp_def] using
    hinv.comp β
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : k => ℝ) j).hasFDerivAt

/-- Coordinate-reciprocal Delta-method remainder. -/
theorem coordinateInv_deltaMethod_remainder_isLittleO (j : k) {β : k → ℝ}
    (hβj : β j ≠ 0) :
    (fun b : k → ℝ =>
      (b j)⁻¹ - (β j)⁻¹ -
        ((ContinuousLinearMap.toSpanSingleton ℝ (-(β j ^ 2)⁻¹)).comp
          (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : k => ℝ) j))
          (b - β))
        =o[𝓝 β] (fun b => b - β) :=
  deltaMethod_remainder_isLittleO (coordinateInv_hasFDerivAt j hβj)

set_option linter.unusedFintypeInType false in
/-- One-dimensional vector-valued coordinate-reciprocal derivative. -/
theorem coordinateInvVector_hasFDerivAt (j : k) {β : k → ℝ} (hβj : β j ≠ 0) :
    HasFDerivAt (fun b : k → ℝ => fun _ : Fin 1 => (b j)⁻¹)
      (ContinuousLinearMap.pi fun _ : Fin 1 =>
        (ContinuousLinearMap.toSpanSingleton ℝ (-(β j ^ 2)⁻¹)).comp
          (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : k => ℝ) j)) β := by
  exact hasFDerivAt_pi.mpr fun _ => coordinateInv_hasFDerivAt j hβj

/-- One-dimensional vector-valued coordinate-reciprocal Delta-method remainder. -/
theorem coordinateInvVector_deltaMethod_remainder_isLittleO (j : k) {β : k → ℝ}
    (hβj : β j ≠ 0) :
    (fun b : k → ℝ =>
      (fun _ : Fin 1 => (b j)⁻¹) - (fun _ : Fin 1 => (β j)⁻¹) -
        (ContinuousLinearMap.pi fun _ : Fin 1 =>
          (ContinuousLinearMap.toSpanSingleton ℝ (-(β j ^ 2)⁻¹)).comp
            (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : k => ℝ) j))
          (b - β))
        =o[𝓝 β] (fun b => b - β) :=
  deltaMethod_remainder_isLittleO (coordinateInvVector_hasFDerivAt j hβj)

/-- Matrix row for the derivative of the coordinate-reciprocal transform `β ↦ β_j⁻¹`. -/
noncomputable def coordinateInvDerivativeMatrix {k : Type*} [DecidableEq k]
    (j : k) (β : k → ℝ) : Matrix (Fin 1) k ℝ :=
  fun _ => Pi.single j (-(β j ^ 2)⁻¹)

/-- Applying the coordinate-reciprocal derivative row is scalar multiplication
of the selected coordinate. -/
private theorem coordinateInvDerivativeMatrix_mulVec {k : Type*} [Fintype k] [DecidableEq k]
    (j : k) (β v : k → ℝ) :
    (coordinateInvDerivativeMatrix j β *ᵥ v) 0 = (-(β j ^ 2)⁻¹) * v j := by
  simp [coordinateInvDerivativeMatrix, Matrix.mulVec]

/-- Euclidean-space application form of `coordinateInvDerivativeMatrix_mulVec`. -/
private theorem matrixContinuousLinearMap_coordinateInvDerivativeMatrix_apply
    {k : Type*} [Fintype k] [DecidableEq k]
    (j : k) (β : k → ℝ) (v : EuclideanSpace ℝ k) :
    (matrixContinuousLinearMap (coordinateInvDerivativeMatrix j β) v).ofLp 0 =
      (-(β j ^ 2)⁻¹) * v.ofLp j := by
  rw [matrixContinuousLinearMap_apply]
  exact coordinateInvDerivativeMatrix_mulVec j β v.ofLp

/-- Gaussian image law for the coordinate-reciprocal derivative row. -/
theorem coordinateInvDerivativeMatrix_hasLaw_multivariateGaussian_zero
    {k : Type*} [Fintype k] [DecidableEq k]
    {S : Matrix k k ℝ} (hS : S.PosSemidef) (j : k) (β : k → ℝ) :
    HasLaw
      (fun z : EuclideanSpace ℝ k =>
        matrixContinuousLinearMap (coordinateInvDerivativeMatrix j β) z)
      (multivariateGaussian 0
        (coordinateInvDerivativeMatrix j β * S * (coordinateInvDerivativeMatrix j β)ᵀ))
      (multivariateGaussian 0 S) := by
  simpa using
    hasLaw_multivariateGaussian_zero_linearMap (n := k) (q := Fin 1) hS
      (coordinateInvDerivativeMatrix j β)

set_option linter.unusedFintypeInType false in
/-- Coordinate-product derivative for a finite-dimensional parameter vector. -/
theorem coordinateProduct_hasFDerivAt (j l : k) (β : k → ℝ) :
    HasFDerivAt (fun b : k → ℝ => b j * b l)
      (((β j) • (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : k => ℝ) l)) +
        ((β l) • (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : k => ℝ) j))) β := by
  have hj : HasFDerivAt (fun b : k → ℝ => b j)
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : k => ℝ) j) β :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : k => ℝ) j).hasFDerivAt
  have hl : HasFDerivAt (fun b : k → ℝ => b l)
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : k => ℝ) l) β :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : k => ℝ) l).hasFDerivAt
  simpa using hj.mul hl

/-- Coordinate-product Delta-method remainder. -/
theorem coordinateProduct_deltaMethod_remainder_isLittleO (j l : k) (β : k → ℝ) :
    (fun b : k → ℝ =>
      b j * b l - β j * β l -
        ((((β j) • (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : k => ℝ) l)) +
          ((β l) • (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : k => ℝ) j)))
          (b - β)))
        =o[𝓝 β] (fun b => b - β) :=
  deltaMethod_remainder_isLittleO (coordinateProduct_hasFDerivAt j l β)

set_option linter.unusedFintypeInType false in
/-- One-dimensional vector-valued coordinate-product derivative. -/
theorem coordinateProductVector_hasFDerivAt (j l : k) (β : k → ℝ) :
    HasFDerivAt (fun b : k → ℝ => fun _ : Fin 1 => b j * b l)
      (ContinuousLinearMap.pi fun _ : Fin 1 =>
        (((β j) • (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : k => ℝ) l)) +
          ((β l) • (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : k => ℝ) j)))) β := by
  exact hasFDerivAt_pi.mpr fun _ => coordinateProduct_hasFDerivAt j l β

/-- One-dimensional vector-valued coordinate-product Delta-method remainder. -/
theorem coordinateProductVector_deltaMethod_remainder_isLittleO (j l : k) (β : k → ℝ) :
    (fun b : k → ℝ =>
      (fun _ : Fin 1 => b j * b l) - (fun _ : Fin 1 => β j * β l) -
        (ContinuousLinearMap.pi fun _ : Fin 1 =>
          (((β j) • (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : k => ℝ) l)) +
            ((β l) • (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : k => ℝ) j))))
          (b - β))
        =o[𝓝 β] (fun b => b - β) :=
  deltaMethod_remainder_isLittleO (coordinateProductVector_hasFDerivAt j l β)

/-- Matrix row for the derivative of the coordinate-product transform `β ↦ β_j β_l`. -/
def coordinateProductDerivativeMatrix {k : Type*} [DecidableEq k]
    (j l : k) (β : k → ℝ) : Matrix (Fin 1) k ℝ :=
  fun _ => Pi.single l (β j) + Pi.single j (β l)

/-- Applying the coordinate-product derivative row gives the product-rule
linearization. -/
private theorem coordinateProductDerivativeMatrix_mulVec {k : Type*} [Fintype k] [DecidableEq k]
    (j l : k) (β v : k → ℝ) :
    (coordinateProductDerivativeMatrix j l β *ᵥ v) 0 = β j * v l + β l * v j := by
  rw [Matrix.mulVec]
  change (Pi.single l (β j) + Pi.single j (β l)) ⬝ᵥ v = β j * v l + β l * v j
  rw [add_dotProduct]
  simp

/-- Euclidean-space application form of `coordinateProductDerivativeMatrix_mulVec`. -/
private theorem matrixContinuousLinearMap_coordinateProductDerivativeMatrix_apply
    {k : Type*} [Fintype k] [DecidableEq k]
    (j l : k) (β : k → ℝ) (v : EuclideanSpace ℝ k) :
    (matrixContinuousLinearMap (coordinateProductDerivativeMatrix j l β) v).ofLp 0 =
      β j * v.ofLp l + β l * v.ofLp j := by
  rw [matrixContinuousLinearMap_apply]
  exact coordinateProductDerivativeMatrix_mulVec j l β v.ofLp

/-- Gaussian image law for the coordinate-product derivative row. -/
theorem coordinateProductDerivativeMatrix_hasLaw_multivariateGaussian_zero
    {k : Type*} [Fintype k] [DecidableEq k]
    {S : Matrix k k ℝ} (hS : S.PosSemidef) (j l : k) (β : k → ℝ) :
    HasLaw
      (fun z : EuclideanSpace ℝ k =>
        matrixContinuousLinearMap (coordinateProductDerivativeMatrix j l β) z)
      (multivariateGaussian 0
        (coordinateProductDerivativeMatrix j l β * S *
          (coordinateProductDerivativeMatrix j l β)ᵀ))
      (multivariateGaussian 0 S) := by
  simpa using
    hasLaw_multivariateGaussian_zero_linearMap (n := k) (q := Fin 1) hS
      (coordinateProductDerivativeMatrix j l β)

set_option linter.unusedFintypeInType false in
/-- Coordinate-ratio derivative for a finite-dimensional parameter vector. -/
theorem coordinateRatio_hasFDerivAt (j l : k) {β : k → ℝ} (hβl : β l ≠ 0) :
    HasFDerivAt (fun b : k → ℝ => b j * (b l)⁻¹)
      (((β j) •
          ((ContinuousLinearMap.toSpanSingleton ℝ (-(β l ^ 2)⁻¹)).comp
            (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : k => ℝ) l))) +
        (((β l)⁻¹) •
          (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : k => ℝ) j))) β := by
  have hj : HasFDerivAt (fun b : k → ℝ => b j)
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : k => ℝ) j) β :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : k => ℝ) j).hasFDerivAt
  have hinv : HasFDerivAt (fun b : k → ℝ => (b l)⁻¹)
      ((ContinuousLinearMap.toSpanSingleton ℝ (-(β l ^ 2)⁻¹)).comp
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : k => ℝ) l)) β :=
    coordinateInv_hasFDerivAt l hβl
  simpa using hj.mul hinv

/-- Coordinate-ratio Delta-method remainder. -/
theorem coordinateRatio_deltaMethod_remainder_isLittleO (j l : k) {β : k → ℝ}
    (hβl : β l ≠ 0) :
    (fun b : k → ℝ =>
      b j * (b l)⁻¹ - β j * (β l)⁻¹ -
        ((((β j) •
            ((ContinuousLinearMap.toSpanSingleton ℝ (-(β l ^ 2)⁻¹)).comp
              (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : k => ℝ) l))) +
          (((β l)⁻¹) •
            (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : k => ℝ) j)))
          (b - β)))
        =o[𝓝 β] (fun b => b - β) :=
  deltaMethod_remainder_isLittleO (coordinateRatio_hasFDerivAt j l hβl)

set_option linter.unusedFintypeInType false in
/-- One-dimensional vector-valued coordinate-ratio derivative. -/
theorem coordinateRatioVector_hasFDerivAt (j l : k) {β : k → ℝ} (hβl : β l ≠ 0) :
    HasFDerivAt (fun b : k → ℝ => fun _ : Fin 1 => b j * (b l)⁻¹)
      (ContinuousLinearMap.pi fun _ : Fin 1 =>
        (((β j) •
            ((ContinuousLinearMap.toSpanSingleton ℝ (-(β l ^ 2)⁻¹)).comp
              (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : k => ℝ) l))) +
          (((β l)⁻¹) •
            (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : k => ℝ) j)))) β := by
  exact hasFDerivAt_pi.mpr fun _ => coordinateRatio_hasFDerivAt j l hβl

/-- One-dimensional vector-valued coordinate-ratio Delta-method remainder. -/
theorem coordinateRatioVector_deltaMethod_remainder_isLittleO (j l : k) {β : k → ℝ}
    (hβl : β l ≠ 0) :
    (fun b : k → ℝ =>
      (fun _ : Fin 1 => b j * (b l)⁻¹) - (fun _ : Fin 1 => β j * (β l)⁻¹) -
        (ContinuousLinearMap.pi fun _ : Fin 1 =>
          (((β j) •
              ((ContinuousLinearMap.toSpanSingleton ℝ (-(β l ^ 2)⁻¹)).comp
                (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : k => ℝ) l))) +
            (((β l)⁻¹) •
              (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : k => ℝ) j))))
          (b - β))
        =o[𝓝 β] (fun b => b - β) :=
  deltaMethod_remainder_isLittleO (coordinateRatioVector_hasFDerivAt j l hβl)

/-- Matrix row for the derivative of the coordinate-ratio transform `β ↦ β_j / β_l`. -/
noncomputable def coordinateRatioDerivativeMatrix {k : Type*} [DecidableEq k]
    (j l : k) (β : k → ℝ) : Matrix (Fin 1) k ℝ :=
  fun _ => Pi.single l (β j * (-(β l ^ 2)⁻¹)) + Pi.single j (β l)⁻¹

/-- Applying the coordinate-ratio derivative row gives the quotient-rule
linearization. -/
private theorem coordinateRatioDerivativeMatrix_mulVec {k : Type*} [Fintype k] [DecidableEq k]
    (j l : k) (β v : k → ℝ) :
    (coordinateRatioDerivativeMatrix j l β *ᵥ v) 0 =
      β j * (-(β l ^ 2)⁻¹) * v l + (β l)⁻¹ * v j := by
  rw [Matrix.mulVec]
  change (Pi.single l (β j * (-(β l ^ 2)⁻¹)) + Pi.single j (β l)⁻¹) ⬝ᵥ v =
    β j * (-(β l ^ 2)⁻¹) * v l + (β l)⁻¹ * v j
  rw [add_dotProduct]
  simp [mul_assoc]

/-- Euclidean-space application form of `coordinateRatioDerivativeMatrix_mulVec`. -/
private theorem matrixContinuousLinearMap_coordinateRatioDerivativeMatrix_apply
    {k : Type*} [Fintype k] [DecidableEq k]
    (j l : k) (β : k → ℝ) (v : EuclideanSpace ℝ k) :
    (matrixContinuousLinearMap (coordinateRatioDerivativeMatrix j l β) v).ofLp 0 =
      β j * (-(β l ^ 2)⁻¹) * v.ofLp l + (β l)⁻¹ * v.ofLp j := by
  rw [matrixContinuousLinearMap_apply]
  exact coordinateRatioDerivativeMatrix_mulVec j l β v.ofLp

/-- Gaussian image law for the coordinate-ratio derivative row. -/
theorem coordinateRatioDerivativeMatrix_hasLaw_multivariateGaussian_zero
    {k : Type*} [Fintype k] [DecidableEq k]
    {S : Matrix k k ℝ} (hS : S.PosSemidef) (j l : k) (β : k → ℝ) :
    HasLaw
      (fun z : EuclideanSpace ℝ k =>
        matrixContinuousLinearMap (coordinateRatioDerivativeMatrix j l β) z)
      (multivariateGaussian 0
        (coordinateRatioDerivativeMatrix j l β * S *
          (coordinateRatioDerivativeMatrix j l β)ᵀ))
      (multivariateGaussian 0 S) := by
  simpa using
    hasLaw_multivariateGaussian_zero_linearMap (n := k) (q := Fin 1) hS
      (coordinateRatioDerivativeMatrix j l β)

end ConcreteTransforms

section DeltaDistribution

variable [SeminormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [SeminormedAddCommGroup F] [NormedSpace ℝ F] [SecondCountableTopology F]
  [MeasurableSpace F] [BorelSpace F]

/-- Delta-method Slutsky wrapper.

If the linearized statistic `Tₙ` converges in distribution and the nonlinear
statistic differs from `G Tₙ` by an `oₚ(1)` remainder, then the nonlinear
statistic has the linear image of the limit.  The deterministic source of the
remainder is `deltaMethod_remainder_isLittleO`. -/
theorem deltaMethod_tendstoInDistribution
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {T : ℕ → Ω → E} {Z : Ω' → E} {R : ℕ → Ω → F} {G : E →L[ℝ] F}
    (hT : TendstoInDistribution T atTop Z (fun _ => μ) ν)
    (hR : TendstoInMeasure μ R atTop (fun _ => 0))
    (hR_meas : ∀ n, AEMeasurable (R n) μ) :
    TendstoInDistribution
      (fun n ω => G (T n ω) + R n ω)
      atTop (fun ω => G (Z ω)) (fun _ => μ) ν := by
  have hG :
      TendstoInDistribution
        (fun n => G ∘ T n) atTop (G ∘ Z) (fun _ => μ) ν :=
    hT.continuous_comp G.continuous
  simpa [Function.comp_def] using
    hG.add_of_tendstoInMeasure_const (c := 0) hR hR_meas

end DeltaDistribution

section SmoothConsistency

variable [IsFiniteMeasure μ]
  [PseudoEMetricSpace E] [PseudoEMetricSpace F] [TopologicalSpace.PseudoMetrizableSpace F]

/-- Hansen Theorem 6.9: smooth-function consistency from input consistency and
continuity at the target. -/
theorem smoothFunction_consistency
    {θhat : ℕ → Ω → E} {θ : E} {g : E → F}
    (hθ_meas : ∀ n, AEStronglyMeasurable (θhat n) μ)
    (hgθ_meas : ∀ n, AEStronglyMeasurable (fun ω => g (θhat n ω)) μ)
    (hθ : TendstoInMeasure μ θhat atTop (fun _ => θ))
    (hg : ContinuousAt g θ) :
    TendstoInMeasure μ (fun n ω => g (θhat n ω)) atTop (fun _ => g θ) :=
  tendstoInMeasure_continuousAt_const_comp hθ_meas hgθ_meas hθ hg

end SmoothConsistency

section GaussianSmoothFunction

variable {k q : Type*} [Fintype k] [Fintype q] [DecidableEq k] [DecidableEq q]
  {S : Matrix k k ℝ} {R : Matrix q k ℝ}

/-- Hansen Theorem 6.10, Gaussian Delta-method wrapper.

The input statistic converges to a centered multivariate Gaussian.  The nonlinear
statistic is represented as its matrix-linear Delta-method image plus an
`oₚ(1)` remainder.  The conclusion is stated directly with the named Gaussian
law of the image, using `hasLaw_multivariateGaussian_zero_linearMap`. -/
theorem smoothFunction_asymptoticNormality_gaussian
    {T : ℕ → Ω → EuclideanSpace ℝ k}
    {Y : ℕ → Ω → EuclideanSpace ℝ q}
    [IsProbabilityMeasure μ]
    (hS : S.PosSemidef)
    (hT :
      TendstoInDistribution T atTop (fun z : EuclideanSpace ℝ k => z)
        (fun _ => μ) (multivariateGaussian 0 S))
    (hrem :
      TendstoInMeasure μ
        (Y - fun n ω => matrixContinuousLinearMap R (T n ω))
        atTop (fun _ => 0))
    (hY_meas : ∀ n, AEMeasurable (Y n) μ) :
    TendstoInDistribution Y atTop (fun z : EuclideanSpace ℝ q => z)
      (fun _ => μ) (multivariateGaussian 0 (R * S * Rᵀ)) := by
  have hlin :
      TendstoInDistribution
        (fun n => matrixContinuousLinearMap R ∘ T n)
        atTop (matrixContinuousLinearMap R ∘ fun z : EuclideanSpace ℝ k => z)
        (fun _ => μ) (multivariateGaussian 0 S) :=
    hT.continuous_comp (matrixContinuousLinearMap R).continuous
  have hLaw :
      HasLaw (fun z : EuclideanSpace ℝ k => matrixContinuousLinearMap R z)
        (multivariateGaussian 0 (R * S * Rᵀ)) (multivariateGaussian 0 S) := by
    simpa [matrixContinuousLinearMap, Matrix.conjTranspose_eq_transpose_of_trivial] using
      hasLaw_multivariateGaussian_zero_linearMap (n := k) (q := q) hS R
  have htarget :
      TendstoInDistribution
        (fun n ω => matrixContinuousLinearMap R (T n ω))
        atTop (fun z : EuclideanSpace ℝ q => z)
        (fun _ => μ) (multivariateGaussian 0 (R * S * Rᵀ)) := by
    simpa [Function.comp_def] using
      tendstoInDistribution_id_of_hasLaw_limit (E := EuclideanSpace ℝ q) hlin hLaw
  exact tendstoInDistribution_of_tendstoInMeasure_sub
    (X := fun n ω => matrixContinuousLinearMap R (T n ω))
    (Y := Y)
    (Z := fun z : EuclideanSpace ℝ q => z)
    htarget hrem hY_meas

end GaussianSmoothFunction

end HansenEconometrics
