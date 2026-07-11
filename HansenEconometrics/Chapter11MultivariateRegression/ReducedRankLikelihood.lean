import HansenEconometrics.Chapter11MultivariateRegression.ReducedRank

/-!
# Chapter 11 — reduced-rank Gaussian likelihood

This module supplies the raw Gaussian likelihood layer missing from the
formula-oriented development of Hansen Theorem 11.7 in `ReducedRank`.
It defines sample residuals, the trace/log-determinant log-likelihood,
admissible exact-rank parameters, and a genuine global maximizer predicate
quantified over every admissible competitor.

`ReducedRankHansenTheorem11_7` remains a formula and spectral certificate: its
`mle_formula_certificate` field has type `ReducedRankMLEFormulaCertificate`
and packages displayed recovery formulas without comparing the Gaussian
likelihood with arbitrary admissible parameters.  The structure
`ReducedRankHansenTheorem11_7GaussianMLE` below records that certificate
together with positive definiteness and the separate, actual global Gaussian
MLE predicate.  No constructor from the formula certificate alone is provided.
-/

open scoped Matrix

namespace HansenEconometrics

open Matrix

variable {n k r m ell s : Type*}

section Likelihood

variable [Fintype n] [Fintype k] [Fintype r] [Fintype m] [Fintype ell]
variable [DecidableEq n] [DecidableEq r] [DecidableEq m] [DecidableEq ell]

/-- Sample residual matrix for the reduced-rank regression
`Y = X G A' + Z C + E`. -/
def reducedRankSampleResidual
    (Z : Matrix n ell ℝ) (X : Matrix n k ℝ) (Y : Matrix n m ℝ)
    (G : Matrix k r ℝ) (Acoef : Matrix m r ℝ) (C : Matrix ell m ℝ) :
    Matrix n m ℝ :=
  Y - X * G * Acoefᵀ - Z * C

/-- Gaussian sample log-likelihood for a reduced-rank regression parameter.

The covariance inverse is Mathlib's total `Matrix.nonsingInv`; admissibility
below restricts `Sigma` to be positive definite, hence nonsingular with
positive determinant.  On that domain this is the standard expression
`-nm/2 log(2π) - n/2 log(det Sigma) - 1/2 tr(Sigma⁻¹ E'E)`. -/
noncomputable def reducedRankGaussianLogLikelihood
    (Z : Matrix n ell ℝ) (X : Matrix n k ℝ) (Y : Matrix n m ℝ)
    (G : Matrix k r ℝ) (Acoef : Matrix m r ℝ) (C : Matrix ell m ℝ)
    (Sigma : Matrix m m ℝ) : ℝ :=
  -((Fintype.card n : ℝ) * (Fintype.card m : ℝ) / 2) * Real.log (2 * Real.pi)
    - ((Fintype.card n : ℝ) / 2) * Real.log Sigma.det
    - (1 / 2 : ℝ) * Matrix.trace
        (Sigma⁻¹ *
          (reducedRankSampleResidual Z X Y G Acoef C)ᵀ *
          reducedRankSampleResidual Z X Y G Acoef C)

/-- Admissible coefficient factors and covariance for the exact-rank-`r`
Gaussian reduced-rank model.

This is the likelihood parameter space: covariance is positive definite and
the factorized coefficient `G A'` has rank `r`.  Hansen's normalization of `G`
is an identification convention for the formula certificate, not a restriction
on likelihood competitors. -/
def reducedRankGaussianAdmissible
    (G : Matrix k r ℝ) (Acoef : Matrix m r ℝ) (Sigma : Matrix m m ℝ) : Prop :=
  Sigma.PosDef ∧
    (G * Acoefᵀ).rank = Fintype.card r

/-- Actual global Gaussian MLE predicate for the exact-rank-`r` model.

Unlike the formula certificate in `ReducedRank`, this predicate asserts
admissibility of the candidate and compares its raw Gaussian log-likelihood
against every admissible `(G', A', C', Sigma')` competitor. -/
def reducedRankGaussianMLE
    (Z : Matrix n ell ℝ) (X : Matrix n k ℝ) (Y : Matrix n m ℝ)
    (G : Matrix k r ℝ) (Acoef : Matrix m r ℝ) (C : Matrix ell m ℝ)
    (Sigma : Matrix m m ℝ) : Prop :=
  reducedRankGaussianAdmissible G Acoef Sigma ∧
    ∀ (G' : Matrix k r ℝ) (Acoef' : Matrix m r ℝ)
        (C' : Matrix ell m ℝ) (Sigma' : Matrix m m ℝ),
      reducedRankGaussianAdmissible G' Acoef' Sigma' →
        reducedRankGaussianLogLikelihood Z X Y G' Acoef' C' Sigma' ≤
          reducedRankGaussianLogLikelihood Z X Y G Acoef C Sigma

end Likelihood

section PositiveDefiniteLogDetTrace

open scoped MatrixOrder

variable [Fintype m] [DecidableEq m]

/-- The positive-definite log-determinant/trace inequality.

For positive-definite `S` and `Sigma`, whitening `S` by the positive square
root of `Sigma⁻¹` and applying `log x ≤ x - 1` to the whitened
eigenvalues gives
`log det S + m ≤ log det Sigma + tr(Sigma⁻¹ S)`. -/
theorem log_det_add_card_le_log_det_add_trace_inv_mul
    (S Sigma : Matrix m m ℝ) (hS : S.PosDef) (hSigma : Sigma.PosDef) :
    Real.log S.det + (Fintype.card m : ℝ) ≤
      Real.log Sigma.det + Matrix.trace (Sigma⁻¹ * S) := by
  classical
  let U : Matrix m m ℝ := CFC.sqrt Sigma⁻¹
  let B : Matrix m m ℝ := Uᵀ * S * U
  have hSigmaInv : Sigma⁻¹.PosDef := hSigma.inv
  have hU : U.PosDef := by
    simpa [U] using hSigmaInv.isStrictlyPositive.sqrt.posDef
  have hUInjective : Function.Injective U.mulVec :=
    Matrix.mulVec_injective_of_isUnit hU.isUnit
  have hB : B.PosDef := by
    have hCongruence := hS.conjTranspose_mul_mul_same hUInjective
    simpa [B, Matrix.conjTranspose_eq_transpose_of_trivial] using hCongruence
  have hUU : U * U = Sigma⁻¹ := by
    simpa [U] using
      CFC.sqrt_mul_sqrt_self Sigma⁻¹ hSigmaInv.posSemidef.nonneg
  have hUT : Uᵀ = U := by
    have hHermitian := hU.isHermitian.eq
    simpa [Matrix.conjTranspose] using hHermitian
  have hDetB : B.det = Sigma⁻¹.det * S.det := by
    calc
      B.det = U.det * S.det * U.det := by simp [B]
      _ = (U * U).det * S.det := by rw [Matrix.det_mul]; ring
      _ = Sigma⁻¹.det * S.det := by rw [hUU]
  have hTraceB : Matrix.trace B = Matrix.trace (Sigma⁻¹ * S) := by
    calc
      Matrix.trace B = Matrix.trace (Uᵀ * S * U) := rfl
      _ = Matrix.trace (U * Uᵀ * S) := Matrix.trace_mul_cycle Uᵀ S U
      _ = Matrix.trace (U * U * S) := by rw [hUT]
      _ = Matrix.trace (Sigma⁻¹ * S) := by rw [hUU]
  have hLogDetB :
      Real.log B.det = -Real.log Sigma.det + Real.log S.det := by
    rw [hDetB, Real.log_mul hSigmaInv.det_pos.ne' hS.det_pos.ne']
    simp [Real.log_inv]
  have hLogEigenvalues :
      (∑ i, Real.log (hB.1.eigenvalues i)) ≤
        ∑ i, (hB.1.eigenvalues i - 1) := by
    exact Finset.sum_le_sum fun i _ =>
      Real.log_le_sub_one_of_pos (hB.eigenvalues_pos i)
  have hLogDetB_le :
      Real.log B.det ≤ Matrix.trace B - (Fintype.card m : ℝ) := by
    calc
      Real.log B.det = ∑ i, Real.log (hB.1.eigenvalues i) := by
        rw [hB.1.det_eq_prod_eigenvalues]
        exact Real.log_prod fun i _ => (hB.eigenvalues_pos i).ne'
      _ ≤ ∑ i, (hB.1.eigenvalues i - 1) := hLogEigenvalues
      _ = Matrix.trace B - (Fintype.card m : ℝ) := by
        rw [Finset.sum_sub_distrib, hB.1.trace_eq_sum_eigenvalues]
        simp
  rw [hLogDetB, hTraceB] at hLogDetB_le
  linarith

end PositiveDefiniteLogDetTrace

section GaussianProfileValue

variable [Fintype n] [Fintype k] [Fintype r] [Fintype m] [Fintype ell]
variable [DecidableEq n] [DecidableEq r] [DecidableEq m] [DecidableEq ell]

omit [DecidableEq n] in
/-- At a positive-definite covariance profile `n⁻¹ E'E`, the Gaussian
quadratic trace term is exactly `n * m`.

This is the covariance-profile algebra behind the constant term in the raw
Gaussian log-likelihood.  It deliberately proves no log-determinant inequality
against a competing covariance. -/
theorem trace_profiledCovariance_inv_mul_crossProduct
    (E : Matrix n m ℝ) (hn : 0 < Fintype.card n)
    (hSigma : (((Fintype.card n : ℝ)⁻¹) • (Eᵀ * E)).PosDef) :
    Matrix.trace
        ((((Fintype.card n : ℝ)⁻¹) • (Eᵀ * E))⁻¹ * (Eᵀ * E)) =
      (Fintype.card n : ℝ) * (Fintype.card m : ℝ) := by
  let N : ℝ := Fintype.card n
  let S : Matrix m m ℝ := Eᵀ * E
  let Sigma : Matrix m m ℝ := N⁻¹ • S
  have hN0 : N ≠ 0 := by
    dsimp [N]
    exact_mod_cast (Nat.ne_of_gt hn)
  have hS : S = N • Sigma := by
    simp [Sigma, N, smul_smul, hN0]
  have hdet : IsUnit Sigma.det :=
    (Matrix.isUnit_iff_isUnit_det Sigma).mp hSigma.isUnit
  calc
    Matrix.trace ((N⁻¹ • S)⁻¹ * S) =
        Matrix.trace (Sigma⁻¹ * S) := by rfl
    _ = Matrix.trace (N • (Sigma⁻¹ * Sigma)) := by
      rw [hS]
      simp
    _ = Matrix.trace (N • (1 : Matrix m m ℝ)) := by
      rw [Matrix.nonsing_inv_mul Sigma hdet]
    _ = N * (Fintype.card m : ℝ) := by
      simp [Matrix.trace_smul, Matrix.trace_one, smul_eq_mul]
    _ = (Fintype.card n : ℝ) * (Fintype.card m : ℝ) := rfl

omit [DecidableEq n] [DecidableEq r] [DecidableEq ell] in
/-- The covariance profile globally maximizes the raw Gaussian likelihood at a
fixed residual matrix.

The comparison is derived from the positive-definite log-determinant/trace
inequality and ranges over every positive-definite covariance `Sigma`.  It
makes no claim about optimizing any regression coefficient. -/
theorem gaussianLogLikelihood_fixedResidual_profiledCovariance_globalMaximizer
    (E : Matrix n m ℝ) (hn : 0 < Fintype.card n)
    (hProfile :
      (((Fintype.card n : ℝ)⁻¹) • (Eᵀ * E)).PosDef) :
    ∀ Sigma : Matrix m m ℝ, Sigma.PosDef →
      -((Fintype.card n : ℝ) * (Fintype.card m : ℝ) / 2) *
            Real.log (2 * Real.pi)
          - ((Fintype.card n : ℝ) / 2) * Real.log Sigma.det
          - (1 / 2 : ℝ) * Matrix.trace (Sigma⁻¹ * Eᵀ * E) ≤
        -((Fintype.card n : ℝ) * (Fintype.card m : ℝ) / 2) *
            Real.log (2 * Real.pi)
          - ((Fintype.card n : ℝ) / 2) *
            Real.log ((((Fintype.card n : ℝ)⁻¹) • (Eᵀ * E)).det)
          - (1 / 2 : ℝ) * Matrix.trace
            (((((Fintype.card n : ℝ)⁻¹) • (Eᵀ * E))⁻¹) * Eᵀ * E) := by
  intro Sigma hSigma
  let N : ℝ := Fintype.card n
  let M : ℝ := Fintype.card m
  let S : Matrix m m ℝ := N⁻¹ • (Eᵀ * E)
  have hNPos : 0 < N := by
    dsimp [N]
    exact_mod_cast hn
  have hN0 : N ≠ 0 := hNPos.ne'
  have hCrossProduct : Eᵀ * E = N • S := by
    simp [S, smul_smul, hN0]
  have hCompetingTrace :
      Matrix.trace (Sigma⁻¹ * Eᵀ * E) =
        N * Matrix.trace (Sigma⁻¹ * S) := by
    rw [Matrix.mul_assoc, hCrossProduct]
    simp [Matrix.trace_smul, smul_eq_mul]
  have hProfileTrace :
      Matrix.trace (S⁻¹ * Eᵀ * E) = N * M := by
    rw [Matrix.mul_assoc]
    simpa [S, N, M] using
      trace_profiledCovariance_inv_mul_crossProduct E hn hProfile
  have hLogDetTrace :=
    log_det_add_card_le_log_det_add_trace_inv_mul S Sigma
      (by simpa [S, N] using hProfile) hSigma
  have hScaleNonneg : 0 ≤ N / 2 := by positivity
  have hScaled := mul_le_mul_of_nonneg_left hLogDetTrace hScaleNonneg
  have hCovariancePart :
      -(N / 2 *
          (Real.log Sigma.det + Matrix.trace (Sigma⁻¹ * S))) ≤
        -(N / 2 * (Real.log S.det + M)) := by
    simpa [M] using neg_le_neg hScaled
  change
    -(N * M / 2) * Real.log (2 * Real.pi)
          - (N / 2) * Real.log Sigma.det
          - (1 / 2 : ℝ) * Matrix.trace (Sigma⁻¹ * Eᵀ * E) ≤
      -(N * M / 2) * Real.log (2 * Real.pi)
          - (N / 2) * Real.log S.det
          - (1 / 2 : ℝ) * Matrix.trace (S⁻¹ * Eᵀ * E)
  calc
    -(N * M / 2) * Real.log (2 * Real.pi)
          - (N / 2) * Real.log Sigma.det
          - (1 / 2 : ℝ) * Matrix.trace (Sigma⁻¹ * Eᵀ * E) =
        -(N * M / 2) * Real.log (2 * Real.pi)
          - N / 2 *
            (Real.log Sigma.det + Matrix.trace (Sigma⁻¹ * S)) := by
      rw [hCompetingTrace]
      ring
    _ ≤ -(N * M / 2) * Real.log (2 * Real.pi)
          - N / 2 * (Real.log S.det + M) := by
      linarith
    _ = -(N * M / 2) * Real.log (2 * Real.pi)
          - (N / 2) * Real.log S.det
          - (1 / 2 : ℝ) * Matrix.trace (S⁻¹ * Eᵀ * E) := by
      rw [hProfileTrace]
      ring

omit [DecidableEq n] [DecidableEq r] [DecidableEq ell] in
/-- The profiled covariance globally maximizes the reduced-rank raw Gaussian
likelihood when `G`, `Acoef`, and `C` are fixed.

This is only the covariance-profile step; it does not assert optimization over
the coefficient factors or controls. -/
theorem reducedRankGaussianLogLikelihood_profiledCovariance_globalMaximizer
    (Z : Matrix n ell ℝ) (X : Matrix n k ℝ) (Y : Matrix n m ℝ)
    (G : Matrix k r ℝ) (Acoef : Matrix m r ℝ) (C : Matrix ell m ℝ)
    (hn : 0 < Fintype.card n)
    (hProfile :
      (((Fintype.card n : ℝ)⁻¹) •
        ((reducedRankSampleResidual Z X Y G Acoef C)ᵀ *
          reducedRankSampleResidual Z X Y G Acoef C)).PosDef) :
    ∀ Sigma : Matrix m m ℝ, Sigma.PosDef →
      reducedRankGaussianLogLikelihood Z X Y G Acoef C Sigma ≤
        reducedRankGaussianLogLikelihood Z X Y G Acoef C
          (((Fintype.card n : ℝ)⁻¹) •
            ((reducedRankSampleResidual Z X Y G Acoef C)ᵀ *
              reducedRankSampleResidual Z X Y G Acoef C)) := by
  intro Sigma hSigma
  simpa [reducedRankGaussianLogLikelihood] using
    gaussianLogLikelihood_fixedResidual_profiledCovariance_globalMaximizer
      (reducedRankSampleResidual Z X Y G Acoef C) hn hProfile Sigma hSigma

omit [DecidableEq n] [DecidableEq r] [DecidableEq ell] in
/-- Raw Gaussian log-likelihood evaluated at its positive-definite covariance
profile.

The quadratic term becomes `-nm/2`; the determinant term is intentionally left
as `log det(n⁻¹ E'E)`.  This theorem records the exact value implied by the raw
likelihood definition and keeps it separate from Hansen's displayed
maximized-value formula. -/
theorem reducedRankGaussianLogLikelihood_at_profiledCovariance
    (Z : Matrix n ell ℝ) (X : Matrix n k ℝ) (Y : Matrix n m ℝ)
    (G : Matrix k r ℝ) (Acoef : Matrix m r ℝ) (C : Matrix ell m ℝ)
    (hn : 0 < Fintype.card n)
    (hSigma :
      (((Fintype.card n : ℝ)⁻¹) •
        ((reducedRankSampleResidual Z X Y G Acoef C)ᵀ *
          reducedRankSampleResidual Z X Y G Acoef C)).PosDef) :
    reducedRankGaussianLogLikelihood Z X Y G Acoef C
        (((Fintype.card n : ℝ)⁻¹) •
          ((reducedRankSampleResidual Z X Y G Acoef C)ᵀ *
            reducedRankSampleResidual Z X Y G Acoef C)) =
      -((Fintype.card n : ℝ) * (Fintype.card m : ℝ) / 2) *
          Real.log (2 * Real.pi)
        - ((Fintype.card n : ℝ) / 2) *
          Real.log
            ((((Fintype.card n : ℝ)⁻¹) •
              ((reducedRankSampleResidual Z X Y G Acoef C)ᵀ *
                reducedRankSampleResidual Z X Y G Acoef C)).det)
      - ((Fintype.card n : ℝ) * (Fintype.card m : ℝ) / 2) := by
  unfold reducedRankGaussianLogLikelihood
  rw [Matrix.mul_assoc]
  rw [trace_profiledCovariance_inv_mul_crossProduct
    (reducedRankSampleResidual Z X Y G Acoef C) hn hSigma]
  ring

end GaussianProfileValue

section ProfiledCovariance

variable [Fintype n] [Fintype k] [Fintype r] [Fintype m]
variable [DecidableEq n] [DecidableEq r] [DecidableEq m]

omit [DecidableEq n] [DecidableEq m] in
/-- The concrete profiled covariance is positive definite when the sample is
nonempty, `G` is Hansen-normalized, and the displayed profiled residual matrix
has injective column map.

The proof rewrites `reducedRankSigmaHat` using
`reducedRankSigmaHat_eq_Ahat_mul_transpose_of_normalized`, identifies the
cross-product subtraction with `R'R`, and applies
`Matrix.PosDef.conjTranspose_mul_self`. -/
theorem reducedRankSigmaHat_posDef_of_normalized_of_residual_injective
    (Xtilde : Matrix n k ℝ) (Ytilde : Matrix n m ℝ) (G : Matrix k r ℝ)
    (hn : 0 < Fintype.card n)
    (hNorm : reducedRankGNormalized Xtilde G)
    (hInjective : Function.Injective
      (Ytilde - (Xtilde * G) * (Ytildeᵀ * Xtilde * G)ᵀ).mulVec) :
    (reducedRankSigmaHat Xtilde Ytilde G).PosDef := by
  classical
  let P : Matrix n r ℝ := Xtilde * G
  let R : Matrix n m ℝ := Ytilde - P * (Ytildeᵀ * P)ᵀ
  have hP : Pᵀ * P = (1 : Matrix r r ℝ) := by
    simpa [P] using reducedRankG_image_orthonormal_of_normalized Xtilde G hNorm
  have hRInjective : Function.Injective R.mulVec := by
    simpa [R, P, Matrix.mul_assoc] using hInjective
  let Q : Matrix n n ℝ := P * Pᵀ
  have hQT : Qᵀ = Q := by
    simp [Q, Matrix.transpose_mul]
  have hQIdem : Q * Q = Q := by
    simp only [Q]
    rw [Matrix.mul_assoc P Pᵀ (P * Pᵀ),
      ← Matrix.mul_assoc Pᵀ P Pᵀ, hP]
    simp
  have hR : R = Ytilde - Q * Ytilde := by
    change Ytilde - P * (Ytildeᵀ * P)ᵀ =
      Ytilde - (P * Pᵀ) * Ytilde
    rw [Matrix.transpose_mul, Matrix.transpose_transpose,
      Matrix.mul_assoc P Pᵀ Ytilde]
  have hGram :
      Ytildeᵀ * Ytilde - (Ytildeᵀ * P) * (Ytildeᵀ * P)ᵀ = Rᵀ * R := by
    rw [hR]
    simp only [Matrix.transpose_sub, Matrix.transpose_mul,
      Matrix.transpose_transpose, Matrix.mul_sub, Matrix.sub_mul]
    rw [hQT, Matrix.mul_assoc Ytildeᵀ Q (Q * Ytilde),
      ← Matrix.mul_assoc Q Q Ytilde, hQIdem]
    simp only [Q, Matrix.mul_assoc]
    abel
  have hGram' :
      Ytildeᵀ * Ytilde -
          (Ytildeᵀ * Xtilde * G) * (Ytildeᵀ * Xtilde * G)ᵀ = Rᵀ * R := by
    simpa [P, Matrix.mul_assoc] using hGram
  rw [reducedRankSigmaHat_eq_Ahat_mul_transpose_of_normalized
    Xtilde Ytilde G hNorm]
  rw [hGram']
  have hRGram : (Rᵀ * R).PosDef := by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.PosDef.conjTranspose_mul_self R hRInjective
  exact hRGram.smul (inv_pos.mpr (by exact_mod_cast hn))

end ProfiledCovariance

section TheoremCertificate

variable [Fintype n] [Fintype k] [Fintype r] [Fintype m] [Fintype ell] [Fintype s]
variable [DecidableEq n] [DecidableEq k] [DecidableEq r] [DecidableEq m]
variable [DecidableEq ell] [DecidableEq s]

/-- Hansen Theorem 11.7 formula/spectral certificate strengthened with the
conditions that distinguish an actual Gaussian MLE.

The `formula_certificate` field is the existing `ReducedRank` conclusion and
does not itself establish likelihood optimality.  The other fields separately
identify all three tilded matrices with their sample residualizations, record
covariance positive definiteness, and give the global comparison against all
admissible exact-rank Gaussian competitors.  It also records Hansen's strict
rank bound and the exact complementary width of `Aperp`.  Deliberately, this
module provides no constructor from the formula certificate alone. -/
structure ReducedRankHansenTheorem11_7GaussianMLE
    (Z : Matrix n ell ℝ) (X Xtilde : Matrix n k ℝ) (Y Ytilde Etilde : Matrix n m ℝ)
    [Invertible (Zᵀ * Z)]
    [Invertible ((Matrix.fromCols X Z)ᵀ * Matrix.fromCols X Z)]
    (G : Matrix k r ℝ) (Acoef : Matrix m r ℝ) (C : Matrix ell m ℝ)
    (Sigma : Matrix m m ℝ) (Aperp : Matrix m s ℝ)
    (lambda : r → ℝ) (eta : s → ℝ) (logLikelihood : ℝ) : Prop where
  formula_certificate :
    ReducedRankHansenTheorem11_7 Z X Xtilde Y Ytilde Etilde G Acoef C Sigma
      Aperp lambda eta logLikelihood
  x_residualized : Xtilde = reducedRankTildeX Z X
  y_residualized : Ytilde = reducedRankTildeY Z Y
  e_residualized : Etilde = reducedRankTildeE X Z Y
  aperp_dimension : Fintype.card s = Fintype.card m - Fintype.card r
  rank_dimension : Fintype.card r < min (Fintype.card k) (Fintype.card m)
  covariance_posDef : Sigma.PosDef
  gaussian_mle : reducedRankGaussianMLE Z X Y G Acoef C Sigma
  logLikelihood_eq_gaussian :
    logLikelihood = reducedRankGaussianLogLikelihood Z X Y G Acoef C Sigma

end TheoremCertificate

end HansenEconometrics
