import HansenEconometrics.Chapter2LinearProjection

/-!
# Linear GMM optimization and analysis primitives

This module contains the generic weighted-moment algebra used by Chapter 13.
It keeps matrix optimization, estimator linearization, and sandwich-covariance
calculations separate from the textbook-facing GMM statements.

For a linear moment map `g - D b`, the public surface is:

* `criterion`, `gram`, and `cross` for the weighted quadratic criterion;
* `beta`, `betaStar`, and `betaOrZero` for the base and totalized estimators;
* `beta_minimizes` and `beta_eq_of_minimizer` for optimization;
* `influenceMatrix`, `beta_linear_decomposition`, and `asymptoticVariance`
  for later consistency, normality, and efficiency proofs.

The results are independent of Chapter 13 sample notation. The chapter file
specializes `D` to `Z'X` and `g` to `Z'Y`.
-/

open scoped Matrix

namespace HansenEconometrics
namespace LinearGMM

open Matrix

variable {k l : Type*}
variable [Fintype k] [Fintype l] [DecidableEq k]

/-- Weighted linear-moment criterion `(g - D b)' W (g - D b)`. -/
noncomputable def criterion (D : Matrix l k ℝ) (g : l → ℝ)
    (W : Matrix l l ℝ) (b : k → ℝ) : ℝ :=
  (g - D *ᵥ b) ⬝ᵥ (W *ᵥ (g - D *ᵥ b))

/-- Weighted moment Gram matrix `D' W D`. -/
noncomputable def gram (D : Matrix l k ℝ) (W : Matrix l l ℝ) : Matrix k k ℝ :=
  Dᵀ * W * D

/-- Weighted moment cross vector `D' W g`. -/
noncomputable def cross (D : Matrix l k ℝ) (W : Matrix l l ℝ) (g : l → ℝ) : k → ℝ :=
  (Dᵀ * W) *ᵥ g

/-- Base linear GMM coefficient `(D' W D)⁻¹ D' W g`. -/
noncomputable def beta (D : Matrix l k ℝ) (g : l → ℝ) (W : Matrix l l ℝ)
    [Invertible (gram D W)] : k → ℝ :=
  ⅟ (gram D W) *ᵥ cross D W g

/-- Star linear GMM coefficient, totalized with `Matrix.nonsingInv`. -/
noncomputable def betaStar (D : Matrix l k ℝ) (g : l → ℝ)
    (W : Matrix l l ℝ) : k → ℝ :=
  (gram D W)⁻¹ *ᵥ cross D W g

/-- Textbook-facing totalization of linear GMM.

It returns the base estimator when `D' W D` is nonsingular and `0` otherwise.
It agrees definitionally with the Star proof engine through
`betaOrZero_eq_betaStar`. -/
noncomputable def betaOrZero (D : Matrix l k ℝ) (g : l → ℝ)
    (W : Matrix l l ℝ) : k → ℝ :=
  letI : Decidable (IsUnit (gram D W).det) := Classical.propDecidable _
  if h : IsUnit (gram D W).det then
    letI : Invertible (gram D W) :=
      Matrix.invertibleOfIsUnitDet (A := gram D W) h
    beta D g W
  else
    0

omit [Fintype k] [DecidableEq k] in
/-- A positive-semidefinite weight induces a positive-semidefinite weighted
moment Gram matrix. -/
theorem gram_posSemidef (D : Matrix l k ℝ) (W : Matrix l l ℝ)
    [Finite k] (hW : W.PosSemidef) :
    (gram D W).PosSemidef := by
  simpa [gram, Matrix.conjTranspose_eq_transpose_of_trivial] using
    hW.conjTranspose_mul_mul_same D

omit [DecidableEq k] in
/-- The weighted-moment criterion is the Chapter 2 projection quadratic. -/
theorem criterion_eq_linearProjectionMSE (D : Matrix l k ℝ) (g : l → ℝ)
    (W : Matrix l l ℝ) (hW : W.PosSemidef) (b : k → ℝ) :
    criterion D g W b =
      linearProjectionMSE (gram D W) (cross D W g)
        (g ⬝ᵥ (W *ᵥ g)) b := by
  have hWsymm : Wᵀ = W :=
    (Matrix.conjTranspose_eq_transpose_of_trivial W).symm.trans hW.isHermitian.eq
  have hquad : (D *ᵥ b) ⬝ᵥ (W *ᵥ (D *ᵥ b)) =
      b ⬝ᵥ ((gram D W) *ᵥ b) := by
    simpa [gram] using quadraticForm_mulVec_eq_pullback_rect D W b
  have hcross : g ⬝ᵥ (W *ᵥ (D *ᵥ b)) =
      b ⬝ᵥ (cross D W g) := by
    have key : g ⬝ᵥ (W *ᵥ (D *ᵥ b)) = (Wᵀ *ᵥ g) ⬝ᵥ (D *ᵥ b) := by
      rw [Matrix.dotProduct_mulVec, vecMul_eq_mulVec_transpose]
    rw [key, hWsymm, Matrix.dotProduct_mulVec, vecMul_eq_mulVec_transpose,
      dotProduct_comm]
    simp [cross, Matrix.mulVec_mulVec]
  have hcross' : (D *ᵥ b) ⬝ᵥ (W *ᵥ g) =
      b ⬝ᵥ (cross D W g) := by
    rw [dotProduct_comm, Matrix.dotProduct_mulVec, vecMul_eq_mulVec_transpose,
      dotProduct_comm]
    simp [cross, Matrix.mulVec_mulVec]
  unfold criterion linearProjectionMSE
  rw [Matrix.mulVec_sub, dotProduct_sub, sub_dotProduct, sub_dotProduct,
    hquad, hcross, hcross']
  ring

/-- The generic GMM coefficient is the Chapter 2 projection coefficient. -/
theorem beta_eq_linearProjectionBeta (D : Matrix l k ℝ) (g : l → ℝ)
    (W : Matrix l l ℝ) [Invertible (gram D W)] :
    beta D g W = linearProjectionBeta (gram D W) (cross D W g) :=
  rfl

/-- The base linear GMM coefficient satisfies its weighted normal equations. -/
theorem beta_normal_equations (D : Matrix l k ℝ) (g : l → ℝ)
    (W : Matrix l l ℝ) [Invertible (gram D W)] :
    gram D W *ᵥ beta D g W = cross D W g := by
  rw [beta_eq_linearProjectionBeta]
  exact linearProjectionBeta_normal_equations (gram D W) (cross D W g)

/-- The base and Star linear GMM coefficients agree on nonsingular Gram
matrices. -/
theorem betaStar_eq_beta (D : Matrix l k ℝ) (g : l → ℝ)
    (W : Matrix l l ℝ) [Invertible (gram D W)] :
    betaStar D g W = beta D g W := by
  unfold betaStar beta
  rw [← invOf_eq_nonsing_inv]

/-- The OrZero and Star linear GMM coefficients are identical. -/
@[simp]
theorem betaOrZero_eq_betaStar (D : Matrix l k ℝ) (g : l → ℝ)
    (W : Matrix l l ℝ) :
    betaOrZero D g W = betaStar D g W := by
  classical
  unfold betaOrZero
  by_cases h : IsUnit (gram D W).det
  · rw [dif_pos h]
    letI : Invertible (gram D W) :=
      Matrix.invertibleOfIsUnitDet (A := gram D W) h
    exact (betaStar_eq_beta D g W).symm
  · rw [dif_neg h]
    unfold betaStar
    rw [Matrix.nonsing_inv_apply_not_isUnit _ h, Matrix.zero_mulVec]

/-- On a nonsingular Gram matrix, OrZero linear GMM agrees with the base
coefficient. -/
theorem betaOrZero_eq_beta (D : Matrix l k ℝ) (g : l → ℝ)
    (W : Matrix l l ℝ) [Invertible (gram D W)] :
    betaOrZero D g W = beta D g W := by
  rw [betaOrZero_eq_betaStar, betaStar_eq_beta]

/-- The base coefficient minimizes the weighted moment criterion. -/
theorem beta_minimizes (D : Matrix l k ℝ) (g : l → ℝ)
    (W : Matrix l l ℝ) (b : k → ℝ) [Invertible (gram D W)]
    (hW : W.PosSemidef) :
    criterion D g W (beta D g W) ≤ criterion D g W b := by
  have hGram := gram_posSemidef D W hW
  rw [criterion_eq_linearProjectionMSE D g W hW b,
    criterion_eq_linearProjectionMSE D g W hW (beta D g W),
    beta_eq_linearProjectionBeta]
  exact linearProjectionBeta_minimizes_MSE (gram D W) (cross D W g)
    (g ⬝ᵥ (W *ᵥ g))
    ((Matrix.conjTranspose_eq_transpose_of_trivial _).symm.trans
      hGram.isHermitian.eq)
    (by simpa using hGram.dotProduct_mulVec_nonneg) b

/-- The base coefficient is a global minimizer of the weighted moment
criterion. -/
theorem beta_isMinOn (D : Matrix l k ℝ) (g : l → ℝ)
    (W : Matrix l l ℝ) [Invertible (gram D W)] (hW : W.PosSemidef) :
    IsMinOn (criterion D g W) Set.univ (beta D g W) := by
  intro b _
  exact beta_minimizes D g W b hW

/-- Equality with the minimum identifies the base coefficient uniquely. -/
theorem beta_eq_of_minimizer (D : Matrix l k ℝ) (g : l → ℝ)
    (W : Matrix l l ℝ) (b : k → ℝ) [Invertible (gram D W)]
    (hW : W.PosSemidef)
    (hb : criterion D g W b = criterion D g W (beta D g W)) :
    b = beta D g W := by
  have hGram := gram_posSemidef D W hW
  have hGramPos : (gram D W).PosDef :=
    hGram.posDef_iff_isUnit.mpr (isUnit_of_invertible _)
  rw [criterion_eq_linearProjectionMSE D g W hW b,
    criterion_eq_linearProjectionMSE D g W hW (beta D g W),
    beta_eq_linearProjectionBeta] at hb
  rw [beta_eq_linearProjectionBeta]
  exact linearProjectionBeta_eq_of_MSE_eq (gram D W) (cross D W g)
    (g ⬝ᵥ (W *ᵥ g)) b
    ((Matrix.conjTranspose_eq_transpose_of_trivial _).symm.trans
      hGram.isHermitian.eq)
    (fun _ hv => by simpa using hGramPos.dotProduct_mulVec_pos hv) hb

/-! ## Deterministic analysis primitives -/

/-- Linear map from moments to the base GMM coefficient. -/
noncomputable def influenceMatrix (D : Matrix l k ℝ) (W : Matrix l l ℝ)
    [Invertible (gram D W)] : Matrix k l ℝ :=
  ⅟ (gram D W) * Dᵀ * W

/-- The base coefficient is the influence matrix applied to the moment
vector. -/
theorem beta_eq_influenceMatrix_mulVec (D : Matrix l k ℝ) (g : l → ℝ)
    (W : Matrix l l ℝ) [Invertible (gram D W)] :
    beta D g W = influenceMatrix D W *ᵥ g := by
  simp [beta, cross, influenceMatrix, Matrix.mulVec_mulVec, Matrix.mul_assoc]

/-- Exact linear-estimator decomposition around a coefficient `b`. -/
theorem beta_linear_decomposition (D : Matrix l k ℝ) (b : k → ℝ)
    (u : l → ℝ) (W : Matrix l l ℝ) [Invertible (gram D W)] :
    beta D (D *ᵥ b + u) W = b + influenceMatrix D W *ᵥ u := by
  have hID : influenceMatrix D W * D = (1 : Matrix k k ℝ) := by
    unfold influenceMatrix
    calc
      (⅟ (gram D W) * Dᵀ * W) * D =
          ⅟ (gram D W) * (Dᵀ * W * D) := by
            simp only [Matrix.mul_assoc]
      _ = ⅟ (gram D W) * gram D W := by rfl
      _ = 1 := invOf_mul_self _
  rw [beta_eq_influenceMatrix_mulVec, Matrix.mulVec_add,
    Matrix.mulVec_mulVec, hID, Matrix.one_mulVec]

/-- Sandwich covariance induced by a moment covariance `Omega`. -/
noncomputable def asymptoticVariance (D : Matrix l k ℝ) (W Omega : Matrix l l ℝ)
    [Invertible (gram D W)] : Matrix k k ℝ :=
  influenceMatrix D W * Omega * (influenceMatrix D W)ᵀ

/-- A positive-semidefinite moment covariance induces a positive-semidefinite
GMM asymptotic covariance. -/
theorem asymptoticVariance_posSemidef (D : Matrix l k ℝ) (W Omega : Matrix l l ℝ)
    [Invertible (gram D W)] (hOmega : Omega.PosSemidef) :
    (asymptoticVariance D W Omega).PosSemidef := by
  simpa [asymptoticVariance, Matrix.conjTranspose_eq_transpose_of_trivial] using
    hOmega.mul_mul_conjTranspose_same (influenceMatrix D W)

/-- Expanded sandwich formula before symmetry simplification. -/
theorem asymptoticVariance_eq_expanded (D : Matrix l k ℝ) (W Omega : Matrix l l ℝ)
    [Invertible (gram D W)] :
    asymptoticVariance D W Omega =
      ⅟ (gram D W) * Dᵀ * W * Omega * Wᵀ * D * (⅟ (gram D W))ᵀ := by
  simp [asymptoticVariance, influenceMatrix, Matrix.transpose_mul,
    Matrix.mul_assoc]

/-- Hansen's symmetric-weight sandwich formula. -/
theorem asymptoticVariance_eq_hansen (D : Matrix l k ℝ) (W Omega : Matrix l l ℝ)
    [Invertible (gram D W)] (hW : W.PosSemidef) :
    asymptoticVariance D W Omega =
      ⅟ (gram D W) * Dᵀ * W * Omega * W * D * ⅟ (gram D W) := by
  rw [asymptoticVariance_eq_expanded]
  have hWt : Wᵀ = W :=
    (Matrix.conjTranspose_eq_transpose_of_trivial W).symm.trans hW.isHermitian.eq
  have hGram := gram_posSemidef D W hW
  have hGramT : (gram D W)ᵀ = gram D W :=
    (Matrix.conjTranspose_eq_transpose_of_trivial _).symm.trans
      hGram.isHermitian.eq
  have hInvT : (⅟ (gram D W))ᵀ = ⅟ (gram D W) := by
    calc
      (⅟ (gram D W))ᵀ = ⅟ ((gram D W)ᵀ) := by
        simpa only using (Matrix.transpose_invOf (A := gram D W))
      _ = ⅟ (gram D W) := Invertible.congr _ _ hGramT
  rw [hWt, hInvT]

/-- If both the square moment map and weight are invertible, then the weighted
moment Gram matrix is invertible. -/
theorem gram_isUnit (D W : Matrix k k ℝ) [Invertible D] [Invertible W] :
    IsUnit (gram D W) := by
  unfold gram
  exact (((Matrix.isUnit_transpose D).mpr (isUnit_of_invertible D)).mul
    (isUnit_of_invertible W)).mul (isUnit_of_invertible D)

/-- In a just-identified system, the base GMM coefficient solves the moment
equation directly and is independent of the invertible weight. -/
theorem beta_eq_direct (D : Matrix k k ℝ) (g : k → ℝ) (W : Matrix k k ℝ)
    [Invertible D] [Invertible W] [Invertible (gram D W)] :
    beta D g W = ⅟D *ᵥ g := by
  have hDinj : Function.Injective D.mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr (isUnit_of_invertible D)
  apply hDinj
  have hBinj : Function.Injective (Dᵀ * W).mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr
      (((Matrix.isUnit_transpose D).mpr (isUnit_of_invertible D)).mul
        (isUnit_of_invertible W))
  have hnormal := beta_normal_equations D g W
  have hDirect : D *ᵥ beta D g W = g := by
    apply hBinj
    simpa [gram, cross, Matrix.mulVec_mulVec, Matrix.mul_assoc] using hnormal
  rw [hDirect, Matrix.mulVec_mulVec, mul_invOf_self, Matrix.one_mulVec]

/-- In a just-identified system, Star GMM is the direct moment-equation
solution for every invertible weight. -/
theorem betaStar_eq_direct (D : Matrix k k ℝ) (g : k → ℝ) (W : Matrix k k ℝ)
    [Invertible D] [Invertible W] :
    betaStar D g W = ⅟D *ᵥ g := by
  letI : Invertible (gram D W) := (gram_isUnit D W).invertible
  rw [betaStar_eq_beta]
  exact beta_eq_direct D g W

/-- In a just-identified system, textbook-facing OrZero GMM is the direct
moment-equation solution for every invertible weight. -/
theorem betaOrZero_eq_direct (D : Matrix k k ℝ) (g : k → ℝ) (W : Matrix k k ℝ)
    [Invertible D] [Invertible W] :
    betaOrZero D g W = ⅟D *ᵥ g := by
  rw [betaOrZero_eq_betaStar]
  exact betaStar_eq_direct D g W

end LinearGMM
end HansenEconometrics
