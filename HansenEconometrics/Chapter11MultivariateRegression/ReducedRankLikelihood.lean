import HansenEconometrics.Chapter11MultivariateRegression.ReducedRankJointSpectrum

/-!
# Chapter 11 — reduced-rank Gaussian likelihood

This module supplies the raw Gaussian likelihood layer missing from the
formula-oriented development of Hansen Theorem 11.7 in `ReducedRank`.
It defines sample residuals, the trace/log-determinant log-likelihood,
admissible exact-rank parameters, and a genuine global maximizer predicate
quantified over every admissible competitor.

The fixed-`G` profiling layer proves an exact residual cross-product
decomposition, weighted-trace likelihood optimality over arbitrary coefficient
and control competitors, and joint coefficient/covariance profiling.  The
determinant layer identifies the recovered covariance with both a complement
compression and the selected-root product, and the value layer matches the raw
profiled likelihood with the corrected canonical displayed value.  Finally,
the global assembly normalizes arbitrary exact-rank competitors internally and
proves the actual unrestricted MLE predicate from a normalized profile-
determinant minimum.  A full-model residual-Gram condition derives the required
interiority uniformly over every normalized profile.  The final residualized
certificate combines these results with the identified spectral/formula
surface and the exact attained likelihood value. The theorem-facing existential
endpoint uses `ReducedRankJointSpectrum` to construct both spectral blocks
simultaneously, including when the boundary root is tied.

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

section ExactRankNormalization

open scoped MatrixOrder

variable [Fintype k] [Fintype r] [Fintype m] [DecidableEq r]

/-- Every exact-rank factorized coefficient has a representative normalized
for a positive-definite generalized-pencil denominator.

If `rank (G Aᵀ) = card r`, then `G` has full column rank.  Factoring the
positive-definite Gram `Gᵀ B G` and absorbing the factor into `A` produces
`H, D` with `Hᵀ B H = I` and exactly the same coefficient product
`H Dᵀ = G Aᵀ`.  No separate rank or invertibility assumption is imposed on
`A`. -/
theorem generalizedEigenBNormalized_factorization_exists_of_rank
    (B : Matrix k k ℝ) (hB : B.PosDef)
    (G : Matrix k r ℝ) (A : Matrix m r ℝ)
    (hRank : (G * Aᵀ).rank = Fintype.card r) :
    ∃ (H : Matrix k r ℝ) (D : Matrix m r ℝ),
      generalizedEigenvectorBNormalized B H ∧ H * Dᵀ = G * Aᵀ := by
  classical
  have hGrankLower : Fintype.card r ≤ G.rank := by
    rw [← hRank]
    exact Matrix.rank_mul_le_left G Aᵀ
  have hGrank : G.rank = Fintype.card r :=
    le_antisymm G.rank_le_card_width hGrankLower
  have hGInjective : Function.Injective G.mulVec := by
    change Function.Injective G.mulVecLin
    rw [← LinearMap.ker_eq_bot]
    apply Submodule.finrank_eq_zero.mp
    have hnullity := G.mulVecLin.finrank_range_add_finrank_ker
    change G.rank + Module.finrank ℝ (LinearMap.ker G.mulVecLin) =
      Module.finrank ℝ (r → ℝ) at hnullity
    have hsource : Module.finrank ℝ (r → ℝ) = Fintype.card r := by simp
    rw [hGrank, hsource] at hnullity
    omega
  let C : Matrix r r ℝ := Gᵀ * B * G
  have hC : C.PosDef := by
    have hcong := hB.conjTranspose_mul_mul_same hGInjective
    simpa [C, Matrix.conjTranspose_eq_transpose_of_trivial] using hcong
  have hFactor : ∃ T : Matrix r r ℝ, IsUnit T ∧ C = star T * T :=
    (CStarAlgebra.isStrictlyPositive_iff_eq_star_mul_self
      (A := Matrix r r ℝ)).mp
      (show IsStrictlyPositive C from hC.isStrictlyPositive)
  obtain ⟨T, hTunit, hCT⟩ := hFactor
  have hCT' : C = Tᵀ * T := by
    simpa [star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
      using hCT
  have hTdet : IsUnit T.det :=
    (Matrix.isUnit_iff_isUnit_det T).mp hTunit
  let Q : Matrix r r ℝ := T⁻¹
  let H : Matrix k r ℝ := G * Q
  let D : Matrix m r ℝ := A * Tᵀ
  have hNorm : generalizedEigenvectorBNormalized B H := by
    change Hᵀ * B * H = 1
    calc
      Hᵀ * B * H = Qᵀ * C * Q := by
        simp [H, C, Matrix.transpose_mul, Matrix.mul_assoc]
      _ = Qᵀ * (Tᵀ * T) * Q := by rw [← hCT']
      _ = (T * Q)ᵀ * (T * Q) := by
        simp [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = 1 := by
        rw [show T * Q = 1 from Matrix.mul_nonsing_inv T hTdet]
        simp
  have hProduct : H * Dᵀ = G * Aᵀ := by
    calc
      H * Dᵀ = (G * Q) * (A * Tᵀ)ᵀ := by rfl
      _ = G * (Q * T) * Aᵀ := by
        simp [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = G * Aᵀ := by
        rw [show Q * T = 1 from Matrix.nonsing_inv_mul T hTdet]
        simp
  exact ⟨H, D, hNorm, hProduct⟩

end ExactRankNormalization

section PencilCompression

variable [Fintype n] [Fintype k] [Fintype m] [DecidableEq m]

/-- The cross-product coefficient block compresses the reduced-rank pencil
numerator. This is the common algebra behind candidate rank and covariance
determinant calculations. -/
private theorem reducedRankCross_inv_cross_eq_pencilA_compression
    (Xtilde : Matrix n k ℝ) (Ytilde : Matrix n m ℝ) (G : Matrix k r ℝ) :
    (Ytildeᵀ * Xtilde * G)ᵀ * (Ytildeᵀ * Ytilde)⁻¹ *
        (Ytildeᵀ * Xtilde * G) =
      Gᵀ * reducedRankGPencilA Xtilde Ytilde * G := by
  simp only [reducedRankGPencilA, Matrix.transpose_mul,
    Matrix.transpose_transpose]
  simp [Matrix.mul_assoc]

end PencilCompression

section CandidateRank

variable [Fintype n] [Fintype k] [Fintype r] [Fintype m]
variable [DecidableEq r] [DecidableEq m]

/-- Positive selected generalized roots make Hansen's recovered coefficient
product have exact rank `card r`.

Normalization gives a left inverse for `G`.  The eigenvector compression with
positive diagonal roots gives a left inverse for `reducedRankAhat`; combining
them proves the matching lower rank bound, while the factorization through the
`r`-dimensional index gives the upper bound. -/
private theorem reducedRankCoefficient_rank_eq_card_of_positive_roots
    (Xtilde : Matrix n k ℝ) (Ytilde : Matrix n m ℝ)
    (G : Matrix k r ℝ) (lambda : r → ℝ)
    (hEigenvectors :
      reducedRankHansenGEigenvectors Xtilde Ytilde lambda G)
    (hNorm : reducedRankGNormalized Xtilde G)
    (hLambda : ∀ j, 0 < lambda j) :
    (G * (reducedRankAhat Xtilde Ytilde G)ᵀ).rank =
      Fintype.card r := by
  classical
  let B : Matrix k k ℝ := reducedRankGPencilB Xtilde
  let YGram : Matrix m m ℝ := Ytildeᵀ * Ytilde
  let Ahat : Matrix m r ℝ := reducedRankAhat Xtilde Ytilde G
  let Lambda : Matrix r r ℝ := Matrix.diagonal lambda
  have hLambdaUnit : IsUnit Lambda := by
    rw [Matrix.isUnit_diagonal, Pi.isUnit_iff]
    intro j
    exact isUnit_iff_ne_zero.mpr (hLambda j).ne'
  have hLambdaDet : IsUnit Lambda.det :=
    (Matrix.isUnit_iff_isUnit_det Lambda).mp hLambdaUnit
  have hGLeft : (Gᵀ * B) * G = (1 : Matrix r r ℝ) := by
    change Gᵀ * B * G = 1 at hNorm
    simpa [Matrix.mul_assoc] using hNorm
  have hAcomp : Ahatᵀ * YGram⁻¹ * Ahat = Lambda := by
    calc
      Ahatᵀ * YGram⁻¹ * Ahat =
          Gᵀ * reducedRankGPencilA Xtilde Ytilde * G := by
        rw [show Ahat = Ytildeᵀ * Xtilde * G from
          reducedRankAhat_eq_cross_of_normalized Xtilde Ytilde G hNorm]
        exact reducedRankCross_inv_cross_eq_pencilA_compression Xtilde Ytilde G
      _ = Lambda := by
        simpa [B, Lambda] using
          generalizedEigenvectorColumns_compression_eq_diagonal
            (reducedRankGPencilA Xtilde Ytilde)
            (reducedRankGPencilB Xtilde) lambda G hEigenvectors hNorm
  let R : Matrix r m ℝ := Lambda⁻¹ * Ahatᵀ * YGram⁻¹
  have hRLeft : R * Ahat = (1 : Matrix r r ℝ) := by
    calc
      R * Ahat = Lambda⁻¹ * (Ahatᵀ * YGram⁻¹ * Ahat) := by
        simp [R, Matrix.mul_assoc]
      _ = Lambda⁻¹ * Lambda := by rw [hAcomp]
      _ = 1 := Matrix.nonsing_inv_mul Lambda hLambdaDet
  have hATRight : Ahatᵀ * Rᵀ = (1 : Matrix r r ℝ) := by
    have hTranspose := congrArg Matrix.transpose hRLeft
    simpa [Matrix.transpose_mul] using hTranspose
  have hExtract :
      (Gᵀ * B) * (G * Ahatᵀ) * Rᵀ = (1 : Matrix r r ℝ) := by
    calc
      (Gᵀ * B) * (G * Ahatᵀ) * Rᵀ =
          ((Gᵀ * B) * G) * (Ahatᵀ * Rᵀ) := by
        simp [Matrix.mul_assoc]
      _ = Ahatᵀ * Rᵀ := by rw [hGLeft]; simp
      _ = 1 := hATRight
  have hLower : Fintype.card r ≤ (G * Ahatᵀ).rank := by
    calc
      Fintype.card r = (1 : Matrix r r ℝ).rank := by simp
      _ = ((Gᵀ * B) * (G * Ahatᵀ) * Rᵀ).rank := by rw [hExtract]
      _ ≤ (G * Ahatᵀ).rank :=
        (Matrix.rank_mul_le_left ((Gᵀ * B) * (G * Ahatᵀ)) Rᵀ).trans
          (Matrix.rank_mul_le_right (Gᵀ * B) (G * Ahatᵀ))
  have hUpper : (G * Ahatᵀ).rank ≤ Fintype.card r :=
    (Matrix.rank_mul_le_left G Ahatᵀ).trans G.rank_le_card_width
  change (G * Ahatᵀ).rank = Fintype.card r
  exact le_antisymm hUpper hLower

end CandidateRank

section PositiveDefiniteLogDetTrace

open scoped MatrixOrder

variable [Fintype m] [DecidableEq m]

/-- The positive-definite log-determinant/trace inequality.

For positive-definite `S` and `Sigma`, whitening `S` by the positive square
root of `Sigma⁻¹` and applying `log x ≤ x - 1` to the whitened
eigenvalues gives
`log det S + m ≤ log det Sigma + tr(Sigma⁻¹ S)`. -/
private theorem log_det_add_card_le_log_det_add_trace_inv_mul
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
private theorem trace_profiledCovariance_inv_mul_crossProduct
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
private theorem gaussianLogLikelihood_fixedResidual_profiledCovariance_globalMaximizer
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
private theorem reducedRankGaussianLogLikelihood_at_profiledCovariance
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

section FixedGCoefficientProfile

variable [Fintype n] [Fintype k] [Fintype r] [Fintype m] [Fintype ell]
variable [DecidableEq n] [DecidableEq r] [DecidableEq m] [DecidableEq ell]

omit [Fintype m] [DecidableEq r] [DecidableEq m] in
private theorem reducedRankSampleResidual_recovery_eq_residualized
    (Z : Matrix n ell ℝ) (X : Matrix n k ℝ) (Y : Matrix n m ℝ)
    (G : Matrix k r ℝ) (Acoef : Matrix m r ℝ)
    [Invertible (Zᵀ * Z)] :
    reducedRankSampleResidual Z X Y G Acoef
        (reducedRankChat Z X Y G Acoef) =
      reducedRankTildeY Z Y -
        (reducedRankTildeX Z X * G) * Acoefᵀ := by
  rw [reducedRankSampleResidual, reducedRankChat, reducedRankTildeY,
    reducedRankTildeX, residualizedRegressors]
  rw [← Matrix.invOf_eq_nonsing_inv]
  simp only [annihilatorMatrix, hatMatrix, Matrix.mul_sub, Matrix.sub_mul,
    Matrix.one_mul, Matrix.mul_assoc]
  rw [residualizedRegressors]
  simp only [annihilatorMatrix, hatMatrix, Matrix.sub_mul, Matrix.one_mul,
    Matrix.mul_assoc]
  abel

omit [Fintype m] [DecidableEq n] [DecidableEq m] [DecidableEq ell] in
private theorem reducedRankAhat_normal_equations_of_normalized
    (Xtilde : Matrix n k ℝ) (Ytilde : Matrix n m ℝ)
    (G : Matrix k r ℝ)
    (hNorm : reducedRankGNormalized Xtilde G) :
    (Xtilde * G)ᵀ *
        (Ytilde -
          (Xtilde * G) * (reducedRankAhat Xtilde Ytilde G)ᵀ) = 0 := by
  have hGram :
      (Xtilde * G)ᵀ * (Xtilde * G) = (1 : Matrix r r ℝ) :=
    reducedRankG_image_orthonormal_of_normalized Xtilde G hNorm
  rw [reducedRankAhat_eq_cross_of_normalized Xtilde Ytilde G hNorm]
  rw [Matrix.mul_sub, ← Matrix.mul_assoc, hGram, Matrix.one_mul]
  simp [Matrix.transpose_mul, Matrix.mul_assoc]

omit [Fintype m] [DecidableEq m] in
private theorem reducedRankSampleResidual_recovery_normal_equations_of_normalized
    (Z : Matrix n ell ℝ) (X : Matrix n k ℝ) (Y : Matrix n m ℝ)
    (G : Matrix k r ℝ) [Invertible (Zᵀ * Z)]
    (hNorm : reducedRankGNormalized (reducedRankTildeX Z X) G) :
    (X * G)ᵀ *
          reducedRankSampleResidual Z X Y G
            (reducedRankAhat (reducedRankTildeX Z X)
              (reducedRankTildeY Z Y) G)
            (reducedRankChat Z X Y G
              (reducedRankAhat (reducedRankTildeX Z X)
                (reducedRankTildeY Z Y) G)) = 0 ∧
      Zᵀ *
          reducedRankSampleResidual Z X Y G
            (reducedRankAhat (reducedRankTildeX Z X)
              (reducedRankTildeY Z Y) G)
            (reducedRankChat Z X Y G
              (reducedRankAhat (reducedRankTildeX Z X)
                (reducedRankTildeY Z Y) G)) = 0 := by
  let Ahat : Matrix m r ℝ :=
    reducedRankAhat (reducedRankTildeX Z X) (reducedRankTildeY Z Y) G
  let Ehat : Matrix n m ℝ :=
    reducedRankSampleResidual Z X Y G Ahat
      (reducedRankChat Z X Y G Ahat)
  have hEhat :
      Ehat = reducedRankTildeY Z Y -
        (reducedRankTildeX Z X * G) * Ahatᵀ := by
    simpa [Ahat, Ehat] using
      reducedRankSampleResidual_recovery_eq_residualized Z X Y G Ahat
  have hTildeNormal :
      (reducedRankTildeX Z X * G)ᵀ * Ehat = 0 := by
    rw [hEhat]
    simpa [Ahat] using
      reducedRankAhat_normal_equations_of_normalized
        (reducedRankTildeX Z X) (reducedRankTildeY Z Y) G hNorm
  have hZNormal : Zᵀ * Ehat = 0 := by
    rw [hEhat, Matrix.mul_sub]
    have hZY : Zᵀ * reducedRankTildeY Z Y = 0 := by
      simpa [reducedRankTildeY] using
        residualizedRegressors_orthogonal_left Z Y
    have hZX : Zᵀ * reducedRankTildeX Z X = 0 := by
      simpa [reducedRankTildeX] using
        residualizedRegressors_orthogonal_left Z X
    rw [hZY]
    simp [← Matrix.mul_assoc, hZX]
  have hAnnihilatorEhat : annihilatorMatrix Z * Ehat = Ehat := by
    rw [hEhat]
    simp only [reducedRankTildeY, reducedRankTildeX,
      residualizedRegressors, Matrix.mul_sub, ← Matrix.mul_assoc,
      annihilatorMatrix_idempotent]
  have hRawNormal : (X * G)ᵀ * Ehat = 0 := by
    calc
      (X * G)ᵀ * Ehat = Gᵀ * Xᵀ * Ehat := by
        rw [Matrix.transpose_mul]
      _ = Gᵀ * Xᵀ * (annihilatorMatrix Z * Ehat) := by
        rw [hAnnihilatorEhat]
      _ = Gᵀ * Xᵀ * annihilatorMatrix Z * Ehat := by
        simp only [Matrix.mul_assoc]
      _ = (annihilatorMatrix Z * X * G)ᵀ * Ehat := by
        rw [Matrix.transpose_mul, Matrix.transpose_mul,
          annihilatorMatrix_transpose]
        simp [Matrix.mul_assoc]
      _ = (reducedRankTildeX Z X * G)ᵀ * Ehat := by rfl
      _ = 0 := hTildeNormal
  simpa [Ahat, Ehat] using And.intro hRawNormal hZNormal

omit [Fintype k] [Fintype r] [Fintype m] [Fintype ell]
    [DecidableEq n] [DecidableEq r] [DecidableEq m] [DecidableEq ell] in
/-- Matrix Pythagoras: orthogonal summands have additive Gram matrices. -/
private theorem transpose_mul_add_self_of_orthogonal
    (E D : Matrix n m ℝ) (hCross : Eᵀ * D = 0) :
    (E + D)ᵀ * (E + D) = Eᵀ * E + Dᵀ * D := by
  have hCrossTranspose : Dᵀ * E = 0 := by
    have hTranspose := congrArg Matrix.transpose hCross
    simpa [Matrix.transpose_mul] using hTranspose
  rw [Matrix.transpose_add, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add,
    hCross, hCrossTranspose]
  simp

omit [Fintype m] [DecidableEq n] [DecidableEq r] [DecidableEq m]
    [DecidableEq ell] in
/-- Exact residual cross-product decomposition at any fixed-`G` coefficient
candidate satisfying the raw normal equations.

The competing `Acoef` and `C` are arbitrary.  Their residual cross product is
the candidate residual cross product plus the Gram matrix of the fitted-value
difference.  No normalization or rank condition is imposed on a competitor;
normalization only enters the recovery-formula specialization below. -/
private theorem reducedRankSampleResidual_crossProduct_eq_profiled_add_of_normalEquations
    (Z : Matrix n ell ℝ) (X : Matrix n k ℝ) (Y : Matrix n m ℝ)
    (G : Matrix k r ℝ) (Ahat : Matrix m r ℝ) (Chat : Matrix ell m ℝ)
    (hXNormal :
      (X * G)ᵀ * reducedRankSampleResidual Z X Y G Ahat Chat = 0)
    (hZNormal : Zᵀ * reducedRankSampleResidual Z X Y G Ahat Chat = 0)
    (Acoef : Matrix m r ℝ) (C : Matrix ell m ℝ) :
    (reducedRankSampleResidual Z X Y G Acoef C)ᵀ *
        reducedRankSampleResidual Z X Y G Acoef C =
      (reducedRankSampleResidual Z X Y G Ahat Chat)ᵀ *
          reducedRankSampleResidual Z X Y G Ahat Chat +
        (X * G * (Ahat - Acoef)ᵀ + Z * (Chat - C))ᵀ *
          (X * G * (Ahat - Acoef)ᵀ + Z * (Chat - C)) := by
  let Ehat : Matrix n m ℝ :=
    reducedRankSampleResidual Z X Y G Ahat Chat
  let D : Matrix n m ℝ :=
    X * G * (Ahat - Acoef)ᵀ + Z * (Chat - C)
  have hXCross : Ehatᵀ * (X * G) = 0 := by
    have hTranspose := congrArg Matrix.transpose hXNormal
    simpa [Ehat, Matrix.transpose_mul] using hTranspose
  have hZCross : Ehatᵀ * Z = 0 := by
    have hTranspose := congrArg Matrix.transpose hZNormal
    simpa [Ehat, Matrix.transpose_mul] using hTranspose
  have hCross : Ehatᵀ * D = 0 := by
    simp [D, Matrix.mul_add, ← Matrix.mul_assoc, hXCross, hZCross]
  have hResidual :
      reducedRankSampleResidual Z X Y G Acoef C = Ehat + D := by
    simp only [Ehat, D, reducedRankSampleResidual, Matrix.transpose_sub,
      Matrix.mul_sub]
    abel
  rw [hResidual]
  simpa [Ehat, D] using
    transpose_mul_add_self_of_orthogonal Ehat D hCross

omit [Fintype m] [DecidableEq m] in
/-- Hansen's fixed-`G` recovery formulas give an exact least-squares
cross-product profile over every competing coefficient matrix and control
coefficient.

`Xtilde` and `Ytilde` are required to be the actual residualizations.  Hansen's
normalization is assumed only for the fixed candidate `G`, where it reduces
`reducedRankAhat` to the normal-equation solution.  The arbitrary competitors
`Acoef` and `C` carry no normalization or rank restriction. -/
theorem reducedRankSampleResidual_crossProduct_eq_profiled_add_of_recovery
    (Z : Matrix n ell ℝ) (X : Matrix n k ℝ) (Y : Matrix n m ℝ)
    (Xtilde : Matrix n k ℝ) (Ytilde : Matrix n m ℝ)
    (G : Matrix k r ℝ) (Ahat : Matrix m r ℝ) (Chat : Matrix ell m ℝ)
    [Invertible (Zᵀ * Z)]
    (hXtilde : Xtilde = reducedRankTildeX Z X)
    (hYtilde : Ytilde = reducedRankTildeY Z Y)
    (hNorm : reducedRankGNormalized Xtilde G)
    (hRecovery :
      reducedRankLeastSquaresRecovery Z X Y Xtilde Ytilde G Ahat Chat)
    (Acoef : Matrix m r ℝ) (C : Matrix ell m ℝ) :
    (reducedRankSampleResidual Z X Y G Acoef C)ᵀ *
        reducedRankSampleResidual Z X Y G Acoef C =
      (reducedRankSampleResidual Z X Y G Ahat Chat)ᵀ *
          reducedRankSampleResidual Z X Y G Ahat Chat +
        (X * G * (Ahat - Acoef)ᵀ + Z * (Chat - C))ᵀ *
          (X * G * (Ahat - Acoef)ᵀ + Z * (Chat - C)) := by
  subst Xtilde
  subst Ytilde
  rcases hRecovery with ⟨hAhat, hChat⟩
  subst Ahat
  subst Chat
  have hNormal :=
    reducedRankSampleResidual_recovery_normal_equations_of_normalized
      Z X Y G hNorm
  exact
    reducedRankSampleResidual_crossProduct_eq_profiled_add_of_normalEquations
      Z X Y G _ _ hNormal.1 hNormal.2 Acoef C

omit [DecidableEq n] [DecidableEq r] [DecidableEq ell] in
private theorem trace_inv_mul_transpose_mul_nonneg
    (Sigma : Matrix m m ℝ) (D : Matrix n m ℝ) (hSigma : Sigma.PosDef) :
    0 ≤ Matrix.trace (Sigma⁻¹ * Dᵀ * D) := by
  rw [Matrix.trace_mul_cycle]
  have hPosSemidef : (D * Sigma⁻¹ * Dᵀ).PosSemidef := by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
      hSigma.inv.posSemidef.mul_mul_conjTranspose_same D
  exact hPosSemidef.trace_nonneg

omit [Fintype m] [DecidableEq n] [DecidableEq m] [DecidableEq ell] in
private theorem residual_crossProduct_eq_sub_crossGram_of_orthonormal
    (P : Matrix n r ℝ) (Y : Matrix n m ℝ)
    (hP : Pᵀ * P = (1 : Matrix r r ℝ)) :
    (Y - P * (Yᵀ * P)ᵀ)ᵀ * (Y - P * (Yᵀ * P)ᵀ) =
      Yᵀ * Y - (Yᵀ * P) * (Yᵀ * P)ᵀ := by
  let A : Matrix m r ℝ := Yᵀ * P
  change (Y - P * Aᵀ)ᵀ * (Y - P * Aᵀ) = Yᵀ * Y - A * Aᵀ
  have hYP : Yᵀ * P = A := rfl
  have hPY : Pᵀ * Y = Aᵀ := by
    simp [A, Matrix.transpose_mul]
  rw [Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub]
  rw [← Matrix.mul_assoc Yᵀ P Aᵀ, hYP]
  rw [Matrix.mul_assoc A Pᵀ Y, hPY]
  rw [Matrix.mul_assoc A Pᵀ (P * Aᵀ),
    ← Matrix.mul_assoc Pᵀ P Aᵀ, hP, Matrix.one_mul]
  abel

omit [Fintype m] [DecidableEq n] [DecidableEq m] [DecidableEq ell] in
private theorem reducedRankAhat_residual_crossProduct_of_normalized
    (Xtilde : Matrix n k ℝ) (Ytilde : Matrix n m ℝ)
    (G : Matrix k r ℝ) (hNorm : reducedRankGNormalized Xtilde G) :
    (Ytilde -
        (Xtilde * G) * (reducedRankAhat Xtilde Ytilde G)ᵀ)ᵀ *
        (Ytilde -
          (Xtilde * G) * (reducedRankAhat Xtilde Ytilde G)ᵀ) =
      Ytildeᵀ * Ytilde -
        (Ytildeᵀ * Xtilde * G) * (Ytildeᵀ * Xtilde * G)ᵀ := by
  have hP :
      (Xtilde * G)ᵀ * (Xtilde * G) = (1 : Matrix r r ℝ) :=
    reducedRankG_image_orthonormal_of_normalized Xtilde G hNorm
  rw [reducedRankAhat_eq_cross_of_normalized Xtilde Ytilde G hNorm]
  simpa [Matrix.mul_assoc] using
    residual_crossProduct_eq_sub_crossGram_of_orthonormal
      (Xtilde * G) Ytilde hP

omit [Fintype m] [DecidableEq m] in
/-- Hansen's covariance recovery is exactly the residual cross-product profile
at the recovered fixed-`G` coefficients.

The assumptions identify `Xtilde` and `Ytilde` with their raw-sample FWL
residualizations and require Hansen's normalization only for the fixed
candidate `G`. -/
private theorem reducedRankSigmaHat_eq_profiledResidual_crossProduct_of_recovery
    (Z : Matrix n ell ℝ) (X : Matrix n k ℝ) (Y : Matrix n m ℝ)
    (Xtilde : Matrix n k ℝ) (Ytilde : Matrix n m ℝ)
    (G : Matrix k r ℝ) (Ahat : Matrix m r ℝ) (Chat : Matrix ell m ℝ)
    [Invertible (Zᵀ * Z)]
    (hXtilde : Xtilde = reducedRankTildeX Z X)
    (hYtilde : Ytilde = reducedRankTildeY Z Y)
    (hNorm : reducedRankGNormalized Xtilde G)
    (hRecovery :
      reducedRankLeastSquaresRecovery Z X Y Xtilde Ytilde G Ahat Chat) :
    reducedRankSigmaHat Xtilde Ytilde G =
      ((Fintype.card n : ℝ)⁻¹) •
        ((reducedRankSampleResidual Z X Y G Ahat Chat)ᵀ *
          reducedRankSampleResidual Z X Y G Ahat Chat) := by
  subst Xtilde
  subst Ytilde
  rcases hRecovery with ⟨hAhat, hChat⟩
  subst Ahat
  subst Chat
  rw [reducedRankSigmaHat_eq_Ahat_mul_transpose_of_normalized
    (reducedRankTildeX Z X) (reducedRankTildeY Z Y) G hNorm]
  rw [reducedRankSampleResidual_recovery_eq_residualized]
  congr 1
  exact
    (reducedRankAhat_residual_crossProduct_of_normalized
      (reducedRankTildeX Z X) (reducedRankTildeY Z Y) G hNorm).symm

/-- For fixed `G` and fixed positive-definite covariance, Hansen's recovered
`Ahat` and `Chat` globally maximize the raw Gaussian likelihood over every
competing `Acoef` and `C`.

The covariance is held fixed on both sides.  Only the candidate `G` is
Hansen-normalized; the quantified coefficient and control competitors are
arbitrary. -/
private theorem
    fixedG_fixedCovariance_coefficients_max
    (Z : Matrix n ell ℝ) (X : Matrix n k ℝ) (Y : Matrix n m ℝ)
    (Xtilde : Matrix n k ℝ) (Ytilde : Matrix n m ℝ)
    (G : Matrix k r ℝ) (Ahat : Matrix m r ℝ) (Chat : Matrix ell m ℝ)
    [Invertible (Zᵀ * Z)]
    (hXtilde : Xtilde = reducedRankTildeX Z X)
    (hYtilde : Ytilde = reducedRankTildeY Z Y)
    (hNorm : reducedRankGNormalized Xtilde G)
    (hRecovery :
      reducedRankLeastSquaresRecovery Z X Y Xtilde Ytilde G Ahat Chat)
    (Sigma : Matrix m m ℝ) (hSigma : Sigma.PosDef) :
    ∀ (Acoef : Matrix m r ℝ) (C : Matrix ell m ℝ),
      reducedRankGaussianLogLikelihood Z X Y G Acoef C Sigma ≤
        reducedRankGaussianLogLikelihood Z X Y G Ahat Chat Sigma := by
  intro Acoef C
  let E : Matrix n m ℝ := reducedRankSampleResidual Z X Y G Acoef C
  let Ehat : Matrix n m ℝ := reducedRankSampleResidual Z X Y G Ahat Chat
  let D : Matrix n m ℝ :=
    X * G * (Ahat - Acoef)ᵀ + Z * (Chat - C)
  have hCross : Eᵀ * E = Ehatᵀ * Ehat + Dᵀ * D := by
    simpa [E, Ehat, D] using
      reducedRankSampleResidual_crossProduct_eq_profiled_add_of_recovery
        Z X Y Xtilde Ytilde G Ahat Chat hXtilde hYtilde hNorm hRecovery Acoef C
  have hDifferenceNonneg :
      0 ≤ Matrix.trace (Sigma⁻¹ * Dᵀ * D) :=
    trace_inv_mul_transpose_mul_nonneg Sigma D hSigma
  have hTraceDecomposition :
      Matrix.trace (Sigma⁻¹ * Eᵀ * E) =
        Matrix.trace (Sigma⁻¹ * Ehatᵀ * Ehat) +
          Matrix.trace (Sigma⁻¹ * Dᵀ * D) := by
    calc
      Matrix.trace (Sigma⁻¹ * Eᵀ * E) =
          Matrix.trace (Sigma⁻¹ * (Eᵀ * E)) := by
            rw [Matrix.mul_assoc]
      _ = Matrix.trace (Sigma⁻¹ * (Ehatᵀ * Ehat + Dᵀ * D)) := by
            rw [hCross]
      _ = Matrix.trace (Sigma⁻¹ * Ehatᵀ * Ehat) +
          Matrix.trace (Sigma⁻¹ * Dᵀ * D) := by
            simp only [Matrix.mul_add, Matrix.trace_add, ← Matrix.mul_assoc]
  have hTrace :
      Matrix.trace (Sigma⁻¹ * Ehatᵀ * Ehat) ≤
        Matrix.trace (Sigma⁻¹ * Eᵀ * E) := by
    rw [hTraceDecomposition]
    exact le_add_of_nonneg_right hDifferenceNonneg
  unfold reducedRankGaussianLogLikelihood
  change
    -((Fintype.card n : ℝ) * (Fintype.card m : ℝ) / 2) *
          Real.log (2 * Real.pi)
        - ((Fintype.card n : ℝ) / 2) * Real.log Sigma.det
        - (1 / 2 : ℝ) * Matrix.trace (Sigma⁻¹ * Eᵀ * E) ≤
      -((Fintype.card n : ℝ) * (Fintype.card m : ℝ) / 2) *
          Real.log (2 * Real.pi)
        - ((Fintype.card n : ℝ) / 2) * Real.log Sigma.det
        - (1 / 2 : ℝ) * Matrix.trace (Sigma⁻¹ * Ehatᵀ * Ehat)
  linarith

/-- Full fixed-`G` profiling theorem for the raw Gaussian likelihood.

Assuming the recovered residual covariance is positive definite, the recovered
coefficients and their covariance profile dominate every arbitrary competing
`Acoef`, `C`, and positive-definite `Sigma` for the same fixed `G`.  This does
not compare different `G` matrices and therefore is not a global reduced-rank
MLE statement. -/
theorem reducedRankGaussianLogLikelihood_fixedG_profiled_globalMaximizer
    (Z : Matrix n ell ℝ) (X : Matrix n k ℝ) (Y : Matrix n m ℝ)
    (Xtilde : Matrix n k ℝ) (Ytilde : Matrix n m ℝ)
    (G : Matrix k r ℝ) (Ahat : Matrix m r ℝ) (Chat : Matrix ell m ℝ)
    [Invertible (Zᵀ * Z)]
    (hXtilde : Xtilde = reducedRankTildeX Z X)
    (hYtilde : Ytilde = reducedRankTildeY Z Y)
    (hNorm : reducedRankGNormalized Xtilde G)
    (hRecovery :
      reducedRankLeastSquaresRecovery Z X Y Xtilde Ytilde G Ahat Chat)
    (hn : 0 < Fintype.card n)
    (hProfile :
      (((Fintype.card n : ℝ)⁻¹) •
        ((reducedRankSampleResidual Z X Y G Ahat Chat)ᵀ *
          reducedRankSampleResidual Z X Y G Ahat Chat)).PosDef) :
    ∀ (Acoef : Matrix m r ℝ) (C : Matrix ell m ℝ)
        (Sigma : Matrix m m ℝ), Sigma.PosDef →
      reducedRankGaussianLogLikelihood Z X Y G Acoef C Sigma ≤
        reducedRankGaussianLogLikelihood Z X Y G Ahat Chat
          (((Fintype.card n : ℝ)⁻¹) •
            ((reducedRankSampleResidual Z X Y G Ahat Chat)ᵀ *
              reducedRankSampleResidual Z X Y G Ahat Chat)) := by
  intro Acoef C Sigma hSigma
  calc
    reducedRankGaussianLogLikelihood Z X Y G Acoef C Sigma ≤
        reducedRankGaussianLogLikelihood Z X Y G Ahat Chat Sigma :=
      fixedG_fixedCovariance_coefficients_max
        Z X Y Xtilde Ytilde G Ahat Chat hXtilde hYtilde hNorm hRecovery
          Sigma hSigma Acoef C
    _ ≤ reducedRankGaussianLogLikelihood Z X Y G Ahat Chat
          (((Fintype.card n : ℝ)⁻¹) •
            ((reducedRankSampleResidual Z X Y G Ahat Chat)ᵀ *
              reducedRankSampleResidual Z X Y G Ahat Chat)) :=
      reducedRankGaussianLogLikelihood_profiledCovariance_globalMaximizer
        Z X Y G Ahat Chat hn hProfile Sigma hSigma

/-- Fixed-`G` raw Gaussian likelihood comparison stated entirely through
Hansen's coefficient and covariance recovery predicates.

For the same fixed normalized `G`, the recovered `(Ahat, Chat, Sigmahat)`
dominates every arbitrary `Acoef`, `C`, and positive-definite `Sigma`.
Different `G` matrices are not compared, so this theorem is a fixed-`G`
profile result, not an MLE certificate. -/
theorem reducedRankGaussianLogLikelihood_fixedG_recovery_globalMaximizer
    (Z : Matrix n ell ℝ) (X : Matrix n k ℝ) (Y : Matrix n m ℝ)
    (Xtilde : Matrix n k ℝ) (Ytilde : Matrix n m ℝ)
    (G : Matrix k r ℝ) (Ahat : Matrix m r ℝ) (Chat : Matrix ell m ℝ)
    (Sigmahat : Matrix m m ℝ) [Invertible (Zᵀ * Z)]
    (hXtilde : Xtilde = reducedRankTildeX Z X)
    (hYtilde : Ytilde = reducedRankTildeY Z Y)
    (hNorm : reducedRankGNormalized Xtilde G)
    (hLeastSquaresRecovery :
      reducedRankLeastSquaresRecovery Z X Y Xtilde Ytilde G Ahat Chat)
    (hCovarianceRecovery :
      reducedRankCovarianceRecovery Xtilde Ytilde G Sigmahat)
    (hn : 0 < Fintype.card n) (hSigmahat : Sigmahat.PosDef) :
    ∀ (Acoef : Matrix m r ℝ) (C : Matrix ell m ℝ)
        (Sigma : Matrix m m ℝ), Sigma.PosDef →
      reducedRankGaussianLogLikelihood Z X Y G Acoef C Sigma ≤
        reducedRankGaussianLogLikelihood Z X Y G Ahat Chat Sigmahat := by
  have hSigmahatEq :
      Sigmahat = ((Fintype.card n : ℝ)⁻¹) •
        ((reducedRankSampleResidual Z X Y G Ahat Chat)ᵀ *
          reducedRankSampleResidual Z X Y G Ahat Chat) :=
    hCovarianceRecovery.trans
      (reducedRankSigmaHat_eq_profiledResidual_crossProduct_of_recovery
        Z X Y Xtilde Ytilde G Ahat Chat hXtilde hYtilde hNorm
          hLeastSquaresRecovery)
  have hProfile :
      (((Fintype.card n : ℝ)⁻¹) •
        ((reducedRankSampleResidual Z X Y G Ahat Chat)ᵀ *
          reducedRankSampleResidual Z X Y G Ahat Chat)).PosDef := by
    rw [← hSigmahatEq]
    exact hSigmahat
  simpa [← hSigmahatEq] using
    reducedRankGaussianLogLikelihood_fixedG_profiled_globalMaximizer
      Z X Y Xtilde Ytilde G Ahat Chat hXtilde hYtilde hNorm
        hLeastSquaresRecovery hn hProfile

/-- The raw likelihood at any recovered interior covariance has the universal
profiled value expressed in terms of that covariance determinant. -/
private theorem reducedRankGaussianLogLikelihood_at_recovery_value
    (Z : Matrix n ell ℝ) (X : Matrix n k ℝ) (Y : Matrix n m ℝ)
    (Xtilde : Matrix n k ℝ) (Ytilde : Matrix n m ℝ)
    (G : Matrix k r ℝ) (Ahat : Matrix m r ℝ) (Chat : Matrix ell m ℝ)
    (Sigmahat : Matrix m m ℝ) [Invertible (Zᵀ * Z)]
    (hXtilde : Xtilde = reducedRankTildeX Z X)
    (hYtilde : Ytilde = reducedRankTildeY Z Y)
    (hNorm : reducedRankGNormalized Xtilde G)
    (hLeastSquaresRecovery :
      reducedRankLeastSquaresRecovery Z X Y Xtilde Ytilde G Ahat Chat)
    (hCovarianceRecovery :
      reducedRankCovarianceRecovery Xtilde Ytilde G Sigmahat)
    (hn : 0 < Fintype.card n) (hSigmahat : Sigmahat.PosDef) :
    reducedRankGaussianLogLikelihood Z X Y G Ahat Chat Sigmahat =
      -((Fintype.card n : ℝ) * (Fintype.card m : ℝ) / 2) *
          Real.log (2 * Real.pi)
        - ((Fintype.card n : ℝ) / 2) * Real.log Sigmahat.det
        - ((Fintype.card n : ℝ) * (Fintype.card m : ℝ) / 2) := by
  have hSigmahatEq :
      Sigmahat = ((Fintype.card n : ℝ)⁻¹) •
        ((reducedRankSampleResidual Z X Y G Ahat Chat)ᵀ *
          reducedRankSampleResidual Z X Y G Ahat Chat) :=
    hCovarianceRecovery.trans
      (reducedRankSigmaHat_eq_profiledResidual_crossProduct_of_recovery
        Z X Y Xtilde Ytilde G Ahat Chat hXtilde hYtilde hNorm
          hLeastSquaresRecovery)
  have hProfilePos :
      (((Fintype.card n : ℝ)⁻¹) •
        ((reducedRankSampleResidual Z X Y G Ahat Chat)ᵀ *
          reducedRankSampleResidual Z X Y G Ahat Chat)).PosDef := by
    rw [← hSigmahatEq]
    exact hSigmahat
  have hValue := reducedRankGaussianLogLikelihood_at_profiledCovariance
    Z X Y G Ahat Chat hn hProfilePos
  rw [← hSigmahatEq] at hValue
  exact hValue

end FixedGCoefficientProfile

section ProfileDeterminant

variable [Fintype n] [Fintype k] [Fintype r] [Fintype m]
variable [DecidableEq n] [DecidableEq r] [DecidableEq m]

omit [DecidableEq n] in
/-- Determinant of Hansen's recovered covariance through the complement of a
compressed generalized-pencil numerator.

For every fixed Hansen-normalized `G`, positive definiteness of the
residualized outcome Gram gives
`det Sigmahat = n⁻ᵐ det(Ytilde'Ytilde) det(I - G' A_G G)`.
No generalized-eigenvector or selected-root assumption is used.  This is the
determinant surface needed to compare different normalized `G` blocks; it does
not itself assert that any block is optimal. -/
theorem reducedRankSigmaHat_det_eq_complementCompression
    (Xtilde : Matrix n k ℝ) (Ytilde : Matrix n m ℝ)
    (G : Matrix k r ℝ)
    (hYGram : (Ytildeᵀ * Ytilde).PosDef)
    (hNorm : reducedRankGNormalized Xtilde G) :
    (reducedRankSigmaHat Xtilde Ytilde G).det =
      ((Fintype.card n : ℝ)⁻¹) ^ Fintype.card m *
        (Ytildeᵀ * Ytilde).det *
          (1 - Gᵀ * reducedRankGPencilA Xtilde Ytilde * G).det := by
  classical
  let YGram : Matrix m m ℝ := Ytildeᵀ * Ytilde
  let Ahat : Matrix m r ℝ := Ytildeᵀ * Xtilde * G
  have hYdet : IsUnit YGram.det :=
    (Matrix.isUnit_iff_isUnit_det YGram).mp hYGram.isUnit
  have hAcomp :
      Ahatᵀ * YGram⁻¹ * Ahat =
        Gᵀ * reducedRankGPencilA Xtilde Ytilde * G := by
    exact reducedRankCross_inv_cross_eq_pencilA_compression Xtilde Ytilde G
  have hResidualFactor :
      YGram - Ahat * Ahatᵀ =
        YGram * (1 - YGram⁻¹ * Ahat * Ahatᵀ) := by
    calc
      YGram - Ahat * Ahatᵀ = YGram * 1 - Ahat * Ahatᵀ := by simp
      _ = YGram * 1 - (YGram * YGram⁻¹) * (Ahat * Ahatᵀ) := by
        rw [Matrix.mul_nonsing_inv YGram hYdet]
        simp
      _ = YGram * (1 - YGram⁻¹ * Ahat * Ahatᵀ) := by
        simp [Matrix.mul_sub, Matrix.mul_assoc]
  have hResidualDet :
      (YGram - Ahat * Ahatᵀ).det =
        YGram.det *
          (1 - Gᵀ * reducedRankGPencilA Xtilde Ytilde * G).det := by
    rw [hResidualFactor, Matrix.det_mul]
    congr 1
    calc
      (1 - YGram⁻¹ * Ahat * Ahatᵀ).det =
          (1 - Ahatᵀ * (YGram⁻¹ * Ahat)).det := by
        simpa using Matrix.det_one_sub_mul_comm (YGram⁻¹ * Ahat) Ahatᵀ
      _ = (1 - Gᵀ * reducedRankGPencilA Xtilde Ytilde * G).det := by
        rw [← Matrix.mul_assoc, hAcomp]
  rw [reducedRankSigmaHat_eq_Ahat_mul_transpose_of_normalized
    Xtilde Ytilde G hNorm]
  rw [Matrix.det_smul]
  change
    (Fintype.card n : ℝ)⁻¹ ^ Fintype.card m *
        (YGram - Ahat * Ahatᵀ).det = _
  rw [hResidualDet]
  dsimp [YGram]
  ring

omit [DecidableEq n] in
/-- Exact determinant of Hansen's recovered fixed-`G` covariance.

If the residualized outcome Gram is positive definite and the fixed candidate
`G` is both Hansen-normalized and a generalized-eigenvector block with roots
`lambda`, then
`det Sigmahat = n⁻ᵐ det(Ytilde'Ytilde) ∏ⱼ (1 - lambdaⱼ)`.
This is a formula identity only; it does not assert likelihood optimality. -/
theorem reducedRankSigmaHat_det_eq_eigenvalueProduct
    (Xtilde : Matrix n k ℝ) (Ytilde : Matrix n m ℝ)
    (G : Matrix k r ℝ) (lambda : r → ℝ)
    (hYGram : (Ytildeᵀ * Ytilde).PosDef)
    (hNorm : reducedRankGNormalized Xtilde G)
    (hEigenvectors :
      reducedRankHansenGEigenvectors Xtilde Ytilde lambda G) :
    (reducedRankSigmaHat Xtilde Ytilde G).det =
      ((Fintype.card n : ℝ)⁻¹) ^ Fintype.card m *
        (Ytildeᵀ * Ytilde).det * ∏ j, (1 - lambda j) := by
  classical
  have hCompression :
      Gᵀ * reducedRankGPencilA Xtilde Ytilde * G =
        Matrix.diagonal lambda :=
    generalizedEigenvectorColumns_compression_eq_diagonal
      (reducedRankGPencilA Xtilde Ytilde)
      (reducedRankGPencilB Xtilde) lambda G hEigenvectors hNorm
  have hComplementDet :
      (1 - Gᵀ * reducedRankGPencilA Xtilde Ytilde * G).det =
        ∏ j, (1 - lambda j) := by
    rw [hCompression]
    rw [← Matrix.diagonal_one, Matrix.diagonal_sub, Matrix.det_diagonal]
  rw [reducedRankSigmaHat_det_eq_complementCompression
    Xtilde Ytilde G hYGram hNorm, hComplementDet]

omit [DecidableEq n] in
/-- Complement-compression determinant minimality implies minimality of
Hansen's recovered covariance determinant over normalized `G` blocks.

Both covariance determinants share the nonnegative factor
`n⁻ᵐ det(Ytildeᵀ Ytilde)`.  Positive definiteness of the outcome Gram makes
its determinant positive; no profile-covariance positive-definiteness is
needed for this algebraic comparison. -/
theorem reducedRankSigmaHat_det_minimal_of_complementDetMinimal
    (Xtilde : Matrix n k ℝ) (Ytilde : Matrix n m ℝ)
    (G : Matrix k r ℝ)
    (hYGram : (Ytildeᵀ * Ytilde).PosDef)
    (hNorm : reducedRankGNormalized Xtilde G)
    (hComplementMin :
      ∀ H : Matrix k r ℝ, reducedRankGNormalized Xtilde H →
        (1 - Gᵀ * reducedRankGPencilA Xtilde Ytilde * G).det ≤
          (1 - Hᵀ * reducedRankGPencilA Xtilde Ytilde * H).det) :
    ∀ H : Matrix k r ℝ, reducedRankGNormalized Xtilde H →
      (reducedRankSigmaHat Xtilde Ytilde G).det ≤
        (reducedRankSigmaHat Xtilde Ytilde H).det := by
  intro H hHNorm
  rw [reducedRankSigmaHat_det_eq_complementCompression
      Xtilde Ytilde G hYGram hNorm,
    reducedRankSigmaHat_det_eq_complementCompression
      Xtilde Ytilde H hYGram hHNorm]
  have hCardNonneg : 0 ≤ (Fintype.card n : ℝ) := by positivity
  have hCommonNonneg :
      0 ≤ ((Fintype.card n : ℝ)⁻¹) ^ Fintype.card m *
        (Ytildeᵀ * Ytilde).det :=
    mul_nonneg (pow_nonneg (inv_nonneg.mpr hCardNonneg) _)
      hYGram.det_pos.le
  exact mul_le_mul_of_nonneg_left (hComplementMin H hHNorm) hCommonNonneg

end ProfileDeterminant

section GlobalMLEAssembly

variable [Fintype n] [Fintype k] [Fintype r] [Fintype m] [Fintype ell]
variable [DecidableEq n] [DecidableEq r] [DecidableEq m] [DecidableEq ell]

/-- Conditional global Gaussian MLE assembly from normalized covariance-profile
determinant minimality.

The global likelihood parameter space remains the unrestricted admissible
space in `reducedRankGaussianMLE`.  Each exact-rank competing product
`G' A'ᵀ` is internally refactorized as `H Dᵀ` with normalized `H`; no
normalization is imposed on the competitor itself.  The recovered fixed-`H`
likelihood optimum then reduces the comparison to recovered covariance
determinants.

`hProfileMin` and `hAllProfilePos` are deliberately explicit.  Thus this is a
conditional global assembly theorem, not a claim that Hansen's regular sample
assumptions already imply every covariance-interiority obligation. -/
theorem reducedRankGaussianMLE_of_normalized_profileDet_minimal
    (Z : Matrix n ell ℝ) (X : Matrix n k ℝ) (Y : Matrix n m ℝ)
    (Xtilde : Matrix n k ℝ) (Ytilde : Matrix n m ℝ)
    (G : Matrix k r ℝ) (Ahat : Matrix m r ℝ) (Chat : Matrix ell m ℝ)
    (Sigmahat : Matrix m m ℝ) [Invertible (Zᵀ * Z)]
    (hXtilde : Xtilde = reducedRankTildeX Z X)
    (hYtilde : Ytilde = reducedRankTildeY Z Y)
    (hn : 0 < Fintype.card n)
    (hXGram : (Xtildeᵀ * Xtilde).PosDef)
    (hNorm : reducedRankGNormalized Xtilde G)
    (hLeastSquaresRecovery :
      reducedRankLeastSquaresRecovery Z X Y Xtilde Ytilde G Ahat Chat)
    (hCovarianceRecovery :
      reducedRankCovarianceRecovery Xtilde Ytilde G Sigmahat)
    (hSigmahat : Sigmahat.PosDef)
    (hRank : (G * Ahatᵀ).rank = Fintype.card r)
    (hProfileMin :
      ∀ H : Matrix k r ℝ, reducedRankGNormalized Xtilde H →
        (reducedRankSigmaHat Xtilde Ytilde G).det ≤
          (reducedRankSigmaHat Xtilde Ytilde H).det)
    (hAllProfilePos :
      ∀ H : Matrix k r ℝ, reducedRankGNormalized Xtilde H →
        (reducedRankSigmaHat Xtilde Ytilde H).PosDef) :
    reducedRankGaussianMLE Z X Y G Ahat Chat Sigmahat := by
  refine ⟨⟨hSigmahat, hRank⟩, ?_⟩
  intro G' Acoef' C' Sigma' hAdmissible'
  rcases hAdmissible' with ⟨hSigma', hRank'⟩
  have hPencilB : (reducedRankGPencilB Xtilde).PosDef := by
    simpa [reducedRankGPencilB] using hXGram
  obtain ⟨H, D, hHNorm, hProduct⟩ :=
    generalizedEigenBNormalized_factorization_exists_of_rank
      (reducedRankGPencilB Xtilde) hPencilB G' Acoef' hRank'
  have hHNormalized : reducedRankGNormalized Xtilde H := hHNorm
  let AH : Matrix m r ℝ := reducedRankAhat Xtilde Ytilde H
  let CH : Matrix ell m ℝ := reducedRankChat Z X Y H AH
  let SigmaH : Matrix m m ℝ := reducedRankSigmaHat Xtilde Ytilde H
  have hHRecovery :
      reducedRankLeastSquaresRecovery Z X Y Xtilde Ytilde H AH CH := by
    exact ⟨rfl, rfl⟩
  have hHCovarianceRecovery :
      reducedRankCovarianceRecovery Xtilde Ytilde H SigmaH := rfl
  have hSigmaH : SigmaH.PosDef := by
    simpa [SigmaH] using hAllProfilePos H hHNormalized
  have hResidualEq :
      reducedRankSampleResidual Z X Y G' Acoef' C' =
        reducedRankSampleResidual Z X Y H D C' := by
    unfold reducedRankSampleResidual
    rw [Matrix.mul_assoc X G' Acoef'ᵀ, Matrix.mul_assoc X H Dᵀ,
      hProduct]
  have hLikelihoodEq :
      reducedRankGaussianLogLikelihood Z X Y G' Acoef' C' Sigma' =
        reducedRankGaussianLogLikelihood Z X Y H D C' Sigma' := by
    unfold reducedRankGaussianLogLikelihood
    rw [hResidualEq]
  have hFixedH :
      reducedRankGaussianLogLikelihood Z X Y H D C' Sigma' ≤
        reducedRankGaussianLogLikelihood Z X Y H AH CH SigmaH :=
    reducedRankGaussianLogLikelihood_fixedG_recovery_globalMaximizer
      Z X Y Xtilde Ytilde H AH CH SigmaH hXtilde hYtilde hHNormalized
        hHRecovery hHCovarianceRecovery hn hSigmaH D C' Sigma' hSigma'
  have hGProfileValue :
      reducedRankGaussianLogLikelihood Z X Y G Ahat Chat Sigmahat =
        -((Fintype.card n : ℝ) * (Fintype.card m : ℝ) / 2) *
            Real.log (2 * Real.pi)
          - ((Fintype.card n : ℝ) / 2) * Real.log Sigmahat.det
          - ((Fintype.card n : ℝ) * (Fintype.card m : ℝ) / 2) :=
    reducedRankGaussianLogLikelihood_at_recovery_value
      Z X Y Xtilde Ytilde G Ahat Chat Sigmahat hXtilde hYtilde hNorm
        hLeastSquaresRecovery hCovarianceRecovery hn hSigmahat
  have hHProfileValue :
      reducedRankGaussianLogLikelihood Z X Y H AH CH SigmaH =
        -((Fintype.card n : ℝ) * (Fintype.card m : ℝ) / 2) *
            Real.log (2 * Real.pi)
          - ((Fintype.card n : ℝ) / 2) * Real.log SigmaH.det
          - ((Fintype.card n : ℝ) * (Fintype.card m : ℝ) / 2) :=
    reducedRankGaussianLogLikelihood_at_recovery_value
      Z X Y Xtilde Ytilde H AH CH SigmaH hXtilde hYtilde hHNormalized
        hHRecovery hHCovarianceRecovery hn hSigmaH
  have hDet : Sigmahat.det ≤ SigmaH.det := by
    calc
      Sigmahat.det = (reducedRankSigmaHat Xtilde Ytilde G).det :=
        congrArg Matrix.det hCovarianceRecovery
      _ ≤ (reducedRankSigmaHat Xtilde Ytilde H).det :=
        hProfileMin H hHNormalized
      _ = SigmaH.det := rfl
  have hLog : Real.log Sigmahat.det ≤ Real.log SigmaH.det :=
    Real.log_le_log hSigmahat.det_pos hDet
  have hProfileLikelihood :
      reducedRankGaussianLogLikelihood Z X Y H AH CH SigmaH ≤
        reducedRankGaussianLogLikelihood Z X Y G Ahat Chat Sigmahat := by
    rw [hHProfileValue, hGProfileValue]
    have hNNonneg : 0 ≤ (Fintype.card n : ℝ) / 2 := by positivity
    have hScaled := mul_le_mul_of_nonneg_left hLog hNNonneg
    linarith
  calc
    reducedRankGaussianLogLikelihood Z X Y G' Acoef' C' Sigma' =
        reducedRankGaussianLogLikelihood Z X Y H D C' Sigma' := hLikelihoodEq
    _ ≤ reducedRankGaussianLogLikelihood Z X Y H AH CH SigmaH := hFixedH
    _ ≤ reducedRankGaussianLogLikelihood Z X Y G Ahat Chat Sigmahat :=
      hProfileLikelihood

/-- Positive-root specialization of the conditional global Gaussian MLE
assembly.

The Hansen generalized-eigenvector equations and `0 < lambda j` derive exact
rank of the recovered candidate coefficient product internally.  The
determinant-minimality and universal profile-positive-definiteness assumptions
remain explicit, and likelihood competitors remain unrestricted by Hansen's
normalization. -/
private theorem gaussianMLE_of_positive_roots_profile_min
    (Z : Matrix n ell ℝ) (X : Matrix n k ℝ) (Y : Matrix n m ℝ)
    (Xtilde : Matrix n k ℝ) (Ytilde : Matrix n m ℝ)
    (G : Matrix k r ℝ) (Ahat : Matrix m r ℝ) (Chat : Matrix ell m ℝ)
    (Sigmahat : Matrix m m ℝ) (lambda : r → ℝ)
    [Invertible (Zᵀ * Z)]
    (hXtilde : Xtilde = reducedRankTildeX Z X)
    (hYtilde : Ytilde = reducedRankTildeY Z Y)
    (hn : 0 < Fintype.card n)
    (hXGram : (Xtildeᵀ * Xtilde).PosDef)
    (hNorm : reducedRankGNormalized Xtilde G)
    (hEigenvectors :
      reducedRankHansenGEigenvectors Xtilde Ytilde lambda G)
    (hLambda : ∀ j, 0 < lambda j)
    (hLeastSquaresRecovery :
      reducedRankLeastSquaresRecovery Z X Y Xtilde Ytilde G Ahat Chat)
    (hCovarianceRecovery :
      reducedRankCovarianceRecovery Xtilde Ytilde G Sigmahat)
    (hSigmahat : Sigmahat.PosDef)
    (hProfileMin :
      ∀ H : Matrix k r ℝ, reducedRankGNormalized Xtilde H →
        (reducedRankSigmaHat Xtilde Ytilde G).det ≤
          (reducedRankSigmaHat Xtilde Ytilde H).det)
    (hAllProfilePos :
      ∀ H : Matrix k r ℝ, reducedRankGNormalized Xtilde H →
        (reducedRankSigmaHat Xtilde Ytilde H).PosDef) :
    reducedRankGaussianMLE Z X Y G Ahat Chat Sigmahat := by
  have hAhat : Ahat = reducedRankAhat Xtilde Ytilde G :=
    hLeastSquaresRecovery.1
  have hRank : (G * Ahatᵀ).rank = Fintype.card r := by
    rw [hAhat]
    exact reducedRankCoefficient_rank_eq_card_of_positive_roots
      Xtilde Ytilde G lambda hEigenvectors hNorm hLambda
  exact reducedRankGaussianMLE_of_normalized_profileDet_minimal
    Z X Y Xtilde Ytilde G Ahat Chat Sigmahat hXtilde hYtilde hn hXGram
      hNorm hLeastSquaresRecovery hCovarianceRecovery hSigmahat hRank
      hProfileMin hAllProfilePos

/-- Conditional global Gaussian MLE assembly from positive selected roots and
complement-compression determinant minimality.

Positive roots provide candidate exact rank, while the common-factor
determinant identity transfers `hComplementMin` to the recovered covariance
determinant minimum.  Universal positive definiteness of normalized recovered
covariances remains an explicit assumption. -/
theorem reducedRankGaussianMLE_of_positive_roots_of_complementDet_minimal
    (Z : Matrix n ell ℝ) (X : Matrix n k ℝ) (Y : Matrix n m ℝ)
    (Xtilde : Matrix n k ℝ) (Ytilde : Matrix n m ℝ)
    (G : Matrix k r ℝ) (Ahat : Matrix m r ℝ) (Chat : Matrix ell m ℝ)
    (Sigmahat : Matrix m m ℝ) (lambda : r → ℝ)
    [Invertible (Zᵀ * Z)]
    (hXtilde : Xtilde = reducedRankTildeX Z X)
    (hYtilde : Ytilde = reducedRankTildeY Z Y)
    (hn : 0 < Fintype.card n)
    (hXGram : (Xtildeᵀ * Xtilde).PosDef)
    (hYGram : (Ytildeᵀ * Ytilde).PosDef)
    (hNorm : reducedRankGNormalized Xtilde G)
    (hEigenvectors :
      reducedRankHansenGEigenvectors Xtilde Ytilde lambda G)
    (hLambda : ∀ j, 0 < lambda j)
    (hLeastSquaresRecovery :
      reducedRankLeastSquaresRecovery Z X Y Xtilde Ytilde G Ahat Chat)
    (hCovarianceRecovery :
      reducedRankCovarianceRecovery Xtilde Ytilde G Sigmahat)
    (hSigmahat : Sigmahat.PosDef)
    (hComplementMin :
      ∀ H : Matrix k r ℝ, reducedRankGNormalized Xtilde H →
        (1 - Gᵀ * reducedRankGPencilA Xtilde Ytilde * G).det ≤
          (1 - Hᵀ * reducedRankGPencilA Xtilde Ytilde * H).det)
    (hAllProfilePos :
      ∀ H : Matrix k r ℝ, reducedRankGNormalized Xtilde H →
        (reducedRankSigmaHat Xtilde Ytilde H).PosDef) :
    reducedRankGaussianMLE Z X Y G Ahat Chat Sigmahat := by
  have hProfileMin :=
    reducedRankSigmaHat_det_minimal_of_complementDetMinimal
      Xtilde Ytilde G hYGram hNorm hComplementMin
  exact
    gaussianMLE_of_positive_roots_profile_min
      Z X Y Xtilde Ytilde G Ahat Chat Sigmahat lambda hXtilde hYtilde hn
        hXGram hNorm hEigenvectors hLambda hLeastSquaresRecovery
        hCovarianceRecovery hSigmahat hProfileMin hAllProfilePos

end GlobalMLEAssembly

section ProfiledLikelihoodValue

variable [Fintype n] [Fintype k] [Fintype r] [Fintype m] [Fintype ell]
variable [DecidableEq n] [DecidableEq r] [DecidableEq m] [DecidableEq ell]

omit [Fintype n] [Fintype k] [Fintype m] [Fintype ell]
    [DecidableEq n] [DecidableEq r] [DecidableEq m] [DecidableEq ell] in
private theorem log_scaled_det_product
    (N d : ℝ) (M : ℕ) (c : r → ℝ)
    (hN : 0 < N) (hd : 0 < d) (hc : ∀ j, 0 < c j) :
    Real.log (N⁻¹ ^ M * d * ∏ j, c j) =
      -(M : ℝ) * Real.log N + Real.log d + ∑ j, Real.log (c j) := by
  have hN0 : N ≠ 0 := hN.ne'
  have hd0 : d ≠ 0 := hd.ne'
  have hc0 : ∀ j, c j ≠ 0 := fun j => (hc j).ne'
  have hprod0 : (∏ j, c j) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun j _ => hc0 j
  rw [Real.log_mul (mul_ne_zero (pow_ne_zero M (inv_ne_zero hN0)) hd0) hprod0,
    Real.log_mul (pow_ne_zero M (inv_ne_zero hN0)) hd0,
    Real.log_pow, Real.log_inv,
    Real.log_prod (fun j _ => hc0 j)]
  ring

/-- Exact raw Gaussian likelihood value at Hansen's recovered fixed-`G`
coefficients and covariance.

Under actual FWL residualization, positive residualized outcome Gram, Hansen
normalization and generalized-eigenvector equations, the least-squares and
covariance recovery equalities, covariance interiority, and `lambda j < 1`,
the raw likelihood equals the corrected canonical
`reducedRankMaximizedLogLikelihood`.  This is an attained-value identity for a
fixed candidate, not a likelihood comparison or MLE statement. -/
theorem reducedRankGaussianLogLikelihood_at_recovery_eq_maximizedLogLikelihood
    (Z : Matrix n ell ℝ) (X : Matrix n k ℝ) (Y : Matrix n m ℝ)
    (Xtilde : Matrix n k ℝ) (Ytilde : Matrix n m ℝ)
    (G : Matrix k r ℝ) (Ahat : Matrix m r ℝ) (Chat : Matrix ell m ℝ)
    (Sigmahat : Matrix m m ℝ) (lambda : r → ℝ)
    [Invertible (Zᵀ * Z)]
    (hXtilde : Xtilde = reducedRankTildeX Z X)
    (hYtilde : Ytilde = reducedRankTildeY Z Y)
    (hn : 0 < Fintype.card n)
    (hYGram : (Ytildeᵀ * Ytilde).PosDef)
    (hNorm : reducedRankGNormalized Xtilde G)
    (hEigenvectors :
      reducedRankHansenGEigenvectors Xtilde Ytilde lambda G)
    (hLeastSquaresRecovery :
      reducedRankLeastSquaresRecovery Z X Y Xtilde Ytilde G Ahat Chat)
    (hCovarianceRecovery :
      reducedRankCovarianceRecovery Xtilde Ytilde G Sigmahat)
    (hSigmahat : Sigmahat.PosDef) (hLambda : ∀ j, lambda j < 1) :
    reducedRankGaussianLogLikelihood Z X Y G Ahat Chat Sigmahat =
      reducedRankMaximizedLogLikelihood Ytilde lambda := by
  let N : ℝ := Fintype.card n
  let M : ℝ := Fintype.card m
  let SigmaProfile : Matrix m m ℝ :=
    N⁻¹ •
      ((reducedRankSampleResidual Z X Y G Ahat Chat)ᵀ *
        reducedRankSampleResidual Z X Y G Ahat Chat)
  have hN : 0 < N := by
    dsimp [N]
    exact_mod_cast hn
  have hSigmahatEq : Sigmahat = SigmaProfile := by
    simpa [SigmaProfile, N] using
      hCovarianceRecovery.trans
        (reducedRankSigmaHat_eq_profiledResidual_crossProduct_of_recovery
          Z X Y Xtilde Ytilde G Ahat Chat hXtilde hYtilde hNorm
            hLeastSquaresRecovery)
  have hProfileDet :
      SigmaProfile.det =
        N⁻¹ ^ Fintype.card m * (Ytildeᵀ * Ytilde).det *
          ∏ j, (1 - lambda j) := by
    rw [← hSigmahatEq, hCovarianceRecovery]
    simpa [N] using
      reducedRankSigmaHat_det_eq_eigenvalueProduct
        Xtilde Ytilde G lambda hYGram hNorm hEigenvectors
  have hFactors : ∀ j, 0 < 1 - lambda j := by
    intro j
    linarith [hLambda j]
  have hLogDet :
      Real.log SigmaProfile.det =
        -M * Real.log N + Real.log (Ytildeᵀ * Ytilde).det +
          ∑ j, Real.log (1 - lambda j) := by
    rw [hProfileDet]
    simpa [M] using
      log_scaled_det_product N (Ytildeᵀ * Ytilde).det
        (Fintype.card m) (fun j => 1 - lambda j) hN hYGram.det_pos hFactors
  have hLogDetSigmahat :
      Real.log Sigmahat.det =
        -M * Real.log N + Real.log (Ytildeᵀ * Ytilde).det +
          ∑ j, Real.log (1 - lambda j) := by
    rw [hSigmahatEq]
    exact hLogDet
  calc
    reducedRankGaussianLogLikelihood Z X Y G Ahat Chat Sigmahat =
        -(N * M / 2) * Real.log (2 * Real.pi)
          - (N / 2) * Real.log Sigmahat.det - N * M / 2 := by
      simpa [N, M] using
        reducedRankGaussianLogLikelihood_at_recovery_value
          Z X Y Xtilde Ytilde G Ahat Chat Sigmahat hXtilde hYtilde hNorm
            hLeastSquaresRecovery hCovarianceRecovery hn hSigmahat
    _ = reducedRankMaximizedLogLikelihood Ytilde lambda := by
      rw [hLogDetSigmahat]
      simp only [reducedRankMaximizedLogLikelihood]
      dsimp [N, M]
      ring

end ProfiledLikelihoodValue

section ProfiledCovariance

variable [Fintype n] [Fintype k] [Fintype r] [Fintype m]
variable [DecidableEq n] [DecidableEq k] [DecidableEq r] [DecidableEq m]

omit [DecidableEq n] [DecidableEq k] [DecidableEq m] in
/-- The concrete profiled covariance is positive definite when the sample is
nonempty, `G` is Hansen-normalized, and the displayed profiled residual matrix
has injective column map.

The proof rewrites `reducedRankSigmaHat` using
`reducedRankSigmaHat_eq_Ahat_mul_transpose_of_normalized`, identifies the
cross-product subtraction with `R'R`, and applies
`Matrix.PosDef.conjTranspose_mul_self`. -/
private theorem reducedRankSigmaHat_posDef_of_normalized_of_residual_injective
    (Xtilde : Matrix n k ℝ) (Ytilde : Matrix n m ℝ) (G : Matrix k r ℝ)
    (hn : 0 < Fintype.card n)
    (hNorm : reducedRankGNormalized Xtilde G)
    (hInjective : Function.Injective
      (Ytilde - (Xtilde * G) * (Ytildeᵀ * Xtilde * G)ᵀ).mulVec) :
    (reducedRankSigmaHat Xtilde Ytilde G).PosDef := by
  classical
  let P : Matrix n r ℝ := Xtilde * G
  let R : Matrix n m ℝ := Ytilde - P * (Ytildeᵀ * P)ᵀ
  have hRInjective : Function.Injective R.mulVec := by
    simpa [R, P, Matrix.mul_assoc] using hInjective
  have hGram' :
      Ytildeᵀ * Ytilde -
          (Ytildeᵀ * Xtilde * G) * (Ytildeᵀ * Xtilde * G)ᵀ = Rᵀ * R := by
    simpa [R, P, Matrix.mul_assoc,
      reducedRankAhat_eq_cross_of_normalized Xtilde Ytilde G hNorm] using
      (reducedRankAhat_residual_crossProduct_of_normalized
        Xtilde Ytilde G hNorm).symm
  rw [reducedRankSigmaHat_eq_Ahat_mul_transpose_of_normalized
    Xtilde Ytilde G hNorm]
  rw [hGram']
  have hRGram : (Rᵀ * R).PosDef := by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.PosDef.conjTranspose_mul_self R hRInjective
  exact hRGram.smul (inv_pos.mpr (by exact_mod_cast hn))

omit [Fintype m] [DecidableEq m] in
private theorem matrixFullResidual_eq_annihilator_mul
    (D : Matrix n k ℝ) (V : Matrix n m ℝ) [Invertible (Dᵀ * D)] :
    V - D * ((Dᵀ * D)⁻¹ * Dᵀ * V) = annihilatorMatrix D * V := by
  simp [annihilatorMatrix, hatMatrix, Matrix.invOf_eq_nonsing_inv,
    Matrix.sub_mul, Matrix.mul_assoc]

omit [Fintype m] [DecidableEq n] [DecidableEq m] in
private theorem matrixFullResidual_crossProduct_eq_complement
    (D : Matrix n k ℝ) (V : Matrix n m ℝ) [Invertible (Dᵀ * D)] :
    (V - D * ((Dᵀ * D)⁻¹ * Dᵀ * V))ᵀ *
        (V - D * ((Dᵀ * D)⁻¹ * Dᵀ * V)) =
      Vᵀ * V - (Vᵀ * D) * (Dᵀ * D)⁻¹ * (Dᵀ * V) := by
  classical
  rw [matrixFullResidual_eq_annihilator_mul]
  rw [Matrix.transpose_mul, annihilatorMatrix_transpose, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (annihilatorMatrix D) (annihilatorMatrix D) V,
    annihilatorMatrix_idempotent]
  simp [annihilatorMatrix, hatMatrix, Matrix.invOf_eq_nonsing_inv,
    Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]

omit [DecidableEq m] in
private theorem fwlLeftResidual_eq_fullResidual
    [Fintype ell] [DecidableEq ell]
    (X : Matrix n k ℝ) (Z : Matrix n ell ℝ) (y : n → ℝ)
    [Invertible (Zᵀ * Z)]
    [Invertible ((Matrix.fromCols X Z)ᵀ * Matrix.fromCols X Z)]
    [Invertible ((residualizedRegressors Z X)ᵀ *
      residualizedRegressors Z X)] :
    residual (residualizedRegressors Z X) (annihilatorMatrix Z *ᵥ y) =
      residual (Matrix.fromCols X Z) y := by
  have hcoef := fromColsLeftBeta_eq_fwlLeftBeta X Z y
  unfold residual fitted fwlLeftBeta at *
  rw [← hcoef]
  rw [fwl_left_auxiliary_residual_eq_annihilator_full_residual]
  exact annihilator_mulVec_eq_self_of_regressors_orthogonal Z
    (residual (Matrix.fromCols X Z) y)
    (normal_equations_fromCols_right X Z y)

omit [Fintype m] [DecidableEq m] in
/-- The full OLS residual from regressing `Ytilde = M_Z Y` on
`Xtilde = M_Z X` is Hansen's unrestricted residual `Etilde = M_[X,Z] Y`.

This is the matrix-valued Chapter 11 bridge to the left-block residual form of
the Chapter 3 Frisch-Waugh-Lovell theorem. -/
theorem reducedRankFullResidual_eq_tildeE
    [Fintype ell] [DecidableEq ell]
    (Z : Matrix n ell ℝ) (X : Matrix n k ℝ) (Y : Matrix n m ℝ)
    [Invertible (Zᵀ * Z)]
    [Invertible ((Matrix.fromCols X Z)ᵀ * Matrix.fromCols X Z)] :
    reducedRankTildeY Z Y -
        reducedRankTildeX Z X *
          (((reducedRankTildeX Z X)ᵀ * reducedRankTildeX Z X)⁻¹ *
            (reducedRankTildeX Z X)ᵀ * reducedRankTildeY Z Y) =
      reducedRankTildeE X Z Y := by
  have hXGram := reducedRankTildeX_gram_posDef Z X
  have hXdet : IsUnit
      ((reducedRankTildeX Z X)ᵀ * reducedRankTildeX Z X).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp hXGram.isUnit
  letI : Invertible
      ((reducedRankTildeX Z X)ᵀ * reducedRankTildeX Z X) :=
    Matrix.invertibleOfIsUnitDet
      (A := (reducedRankTildeX Z X)ᵀ * reducedRankTildeX Z X) hXdet
  letI : Invertible
      ((residualizedRegressors Z X)ᵀ * residualizedRegressors Z X) := by
    simpa [reducedRankTildeX] using
      (inferInstance : Invertible
        ((reducedRankTildeX Z X)ᵀ * reducedRankTildeX Z X))
  rw [matrixFullResidual_eq_annihilator_mul]
  simp only [reducedRankTildeX, reducedRankTildeY, reducedRankTildeE,
    residualizedRegressors]
  rw [← Matrix.mul_assoc]
  ext i j
  let yj : n → ℝ := fun a => Y a j
  have h := fwlLeftResidual_eq_fullResidual X Z yj
  rw [residual_eq_annihilator_mul_y, residual_eq_annihilator_mul_y] at h
  rw [Matrix.mulVec_mulVec] at h
  exact congrFun h i

omit [Fintype m] [DecidableEq m] in
/-- The unrestricted residual Gram is the Schur complement of `Xtilde'Xtilde`
in the residualized `(X,Y)` cross-product matrix.

This is the FWL bridge that identifies Hansen's two Theorem 11.7 pencils. -/
theorem reducedRankTildeE_crossProduct_eq_complement
    [Fintype ell] [DecidableEq ell]
    (Z : Matrix n ell ℝ) (X : Matrix n k ℝ) (Y : Matrix n m ℝ)
    [Invertible (Zᵀ * Z)]
    [Invertible ((Matrix.fromCols X Z)ᵀ * Matrix.fromCols X Z)] :
    (reducedRankTildeE X Z Y)ᵀ * reducedRankTildeE X Z Y =
      (reducedRankTildeY Z Y)ᵀ * reducedRankTildeY Z Y -
        ((reducedRankTildeY Z Y)ᵀ * reducedRankTildeX Z X) *
          ((reducedRankTildeX Z X)ᵀ * reducedRankTildeX Z X)⁻¹ *
            ((reducedRankTildeX Z X)ᵀ * reducedRankTildeY Z Y) := by
  have hXGram := reducedRankTildeX_gram_posDef Z X
  have hXdet : IsUnit
      ((reducedRankTildeX Z X)ᵀ * reducedRankTildeX Z X).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp hXGram.isUnit
  letI : Invertible
      ((reducedRankTildeX Z X)ᵀ * reducedRankTildeX Z X) :=
    Matrix.invertibleOfIsUnitDet
      (A := (reducedRankTildeX Z X)ᵀ * reducedRankTildeX Z X) hXdet
  rw [← reducedRankFullResidual_eq_tildeE Z X Y]
  exact matrixFullResidual_crossProduct_eq_complement
    (reducedRankTildeX Z X) (reducedRankTildeY Z Y)

omit [Fintype m] [DecidableEq m] in
/-- The residualized FWL identity in Hansen's Theorem 11.7 pencil notation. -/
theorem reducedRankAperpPencilA_tildeE_eq_complement
    [Fintype ell] [DecidableEq ell]
    (Z : Matrix n ell ℝ) (X : Matrix n k ℝ) (Y : Matrix n m ℝ)
    [Invertible (Zᵀ * Z)]
    [Invertible ((Matrix.fromCols X Z)ᵀ * Matrix.fromCols X Z)] :
    reducedRankAperpPencilA (reducedRankTildeE X Z Y) =
      reducedRankAperpPencilB (reducedRankTildeY Z Y) -
        ((reducedRankTildeY Z Y)ᵀ * reducedRankTildeX Z X) *
          (reducedRankGPencilB (reducedRankTildeX Z X))⁻¹ *
            ((reducedRankTildeX Z X)ᵀ * reducedRankTildeY Z Y) := by
  simpa [reducedRankAperpPencilA, reducedRankAperpPencilB,
    reducedRankGPencilB] using reducedRankTildeE_crossProduct_eq_complement Z X Y

omit [Fintype m] [DecidableEq n] [DecidableEq r] [DecidableEq m] in
private theorem profileResidual_crossProduct_posDef_of_fullResidual
    [Finite m]
    (X : Matrix n k ℝ) (Y : Matrix n m ℝ)
    (H : Matrix k r ℝ) (A : Matrix m r ℝ)
    (hXGram : (Xᵀ * X).PosDef)
    (hFull :
      ((Y - X * ((Xᵀ * X)⁻¹ * Xᵀ * Y))ᵀ *
        (Y - X * ((Xᵀ * X)⁻¹ * Xᵀ * Y))).PosDef) :
    ((Y - (X * H) * Aᵀ)ᵀ * (Y - (X * H) * Aᵀ)).PosDef := by
  letI := Fintype.ofFinite m
  classical
  let K : Matrix k k ℝ := Xᵀ * X
  let Bfull : Matrix k m ℝ := K⁻¹ * Xᵀ * Y
  let Efull : Matrix n m ℝ := Y - X * Bfull
  let D : Matrix n m ℝ := X * (Bfull - H * Aᵀ)
  have hKdet : IsUnit K.det :=
    (Matrix.isUnit_iff_isUnit_det K).mp (by simpa [K] using hXGram.isUnit)
  have hNormal : Xᵀ * Efull = 0 := by
    calc
      Xᵀ * Efull = Xᵀ * Y - (Xᵀ * X) * Bfull := by
        simp only [Efull, Matrix.mul_sub]
        rw [← Matrix.mul_assoc]
      _ = Xᵀ * Y - K * (K⁻¹ * Xᵀ * Y) := by simp [K, Bfull]
      _ = Xᵀ * Y - (K * K⁻¹) * (Xᵀ * Y) := by
        simp only [Matrix.mul_assoc]
      _ = 0 := by
        rw [Matrix.mul_nonsing_inv K hKdet]
        simp
  have hCross : Efullᵀ * D = 0 := by
    have hTranspose := congrArg Matrix.transpose hNormal
    have hEX : Efullᵀ * X = 0 := by
      simpa [Matrix.transpose_mul] using hTranspose
    simp [D, ← Matrix.mul_assoc, hEX]
  have hResidual : Y - (X * H) * Aᵀ = Efull + D := by
    simp only [Efull, D, Bfull, Matrix.mul_sub]
    simp [Matrix.mul_assoc]
  have hGram :
      (Y - (X * H) * Aᵀ)ᵀ * (Y - (X * H) * Aᵀ) =
        Efullᵀ * Efull + Dᵀ * D := by
    rw [hResidual]
    exact transpose_mul_add_self_of_orthogonal Efull D hCross
  have hEfull : (Efullᵀ * Efull).PosDef := by
    simpa [Efull, Bfull, K] using hFull
  have hD : (Dᵀ * D).PosSemidef := by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
      posSemidef_conjTranspose_mul_self D
  rw [hGram]
  exact hEfull.add_posSemidef hD

omit [Fintype m] [DecidableEq n] [DecidableEq m] in
/-- A positive-definite unrestricted OLS residual Gram makes every normalized
reduced-rank covariance profile interior.

The unrestricted residual is from regressing `Ytilde` on all columns of
`Xtilde`.  Every rank-`r` fitted value is nested in that full model, so its
residual Gram is the unrestricted Gram plus a positive-semidefinite square.
This supplies the uniform profile-interiority premise needed by the global MLE
assembly from one concrete sample condition. -/
theorem reducedRankSigmaHat_posDef_of_fullResidual_posDef
    [Finite m]
    (Xtilde : Matrix n k ℝ) (Ytilde : Matrix n m ℝ)
    (H : Matrix k r ℝ)
    (hn : 0 < Fintype.card n)
    (hXGram : (Xtildeᵀ * Xtilde).PosDef)
    (hNorm : reducedRankGNormalized Xtilde H)
    (hFull :
      ((Ytilde - Xtilde * ((Xtildeᵀ * Xtilde)⁻¹ * Xtildeᵀ * Ytilde))ᵀ *
        (Ytilde - Xtilde *
          ((Xtildeᵀ * Xtilde)⁻¹ * Xtildeᵀ * Ytilde))).PosDef) :
    (reducedRankSigmaHat Xtilde Ytilde H).PosDef := by
  letI := Fintype.ofFinite m
  let Ahat : Matrix m r ℝ := reducedRankAhat Xtilde Ytilde H
  let P : Matrix n r ℝ := Xtilde * H
  let Ehat : Matrix n m ℝ := Ytilde - P * Ahatᵀ
  have hEhatGram :
      Ehatᵀ * Ehat = Ytildeᵀ * Ytilde - Ahat * Ahatᵀ := by
    simpa [Ehat, P, Ahat, Matrix.mul_assoc,
      reducedRankAhat_eq_cross_of_normalized Xtilde Ytilde H hNorm] using
      reducedRankAhat_residual_crossProduct_of_normalized
        Xtilde Ytilde H hNorm
  have hEhat : (Ehatᵀ * Ehat).PosDef := by
    exact profileResidual_crossProduct_posDef_of_fullResidual
      Xtilde Ytilde H Ahat hXGram hFull
  have hSigmaEq :
      reducedRankSigmaHat Xtilde Ytilde H =
        ((Fintype.card n : ℝ)⁻¹) • (Ehatᵀ * Ehat) := by
    have hAhatCross : Ahat = Ytildeᵀ * Xtilde * H := by
      simpa [Ahat] using
        reducedRankAhat_eq_cross_of_normalized Xtilde Ytilde H hNorm
    rw [reducedRankSigmaHat_eq_Ahat_mul_transpose_of_normalized
      Xtilde Ytilde H hNorm, hEhatGram, hAhatCross]
  rw [hSigmaEq]
  exact hEhat.smul (inv_pos.mpr (by exact_mod_cast hn))

/-- Hansen's positive-root, complement-minimal candidate is an unrestricted
Gaussian MLE under a single full-model residual-interiority condition.

Compared with `reducedRankGaussianMLE_of_positive_roots_of_complementDet_minimal`,
this theorem derives both candidate covariance positivity and positivity of
every normalized covariance profile from the positive-definite unrestricted
OLS residual Gram. -/
private theorem gaussianMLE_of_positive_roots_complement_min_fullResidual
    [Fintype ell] [DecidableEq ell]
    (Z : Matrix n ell ℝ) (X : Matrix n k ℝ) (Y : Matrix n m ℝ)
    (Xtilde : Matrix n k ℝ) (Ytilde : Matrix n m ℝ)
    (G : Matrix k r ℝ) (Ahat : Matrix m r ℝ) (Chat : Matrix ell m ℝ)
    (Sigmahat : Matrix m m ℝ) (lambda : r → ℝ)
    [Invertible (Zᵀ * Z)]
    (hXtilde : Xtilde = reducedRankTildeX Z X)
    (hYtilde : Ytilde = reducedRankTildeY Z Y)
    (hn : 0 < Fintype.card n)
    (hXGram : (Xtildeᵀ * Xtilde).PosDef)
    (hYGram : (Ytildeᵀ * Ytilde).PosDef)
    (hNorm : reducedRankGNormalized Xtilde G)
    (hEigenvectors :
      reducedRankHansenGEigenvectors Xtilde Ytilde lambda G)
    (hLambda : ∀ j, 0 < lambda j)
    (hLeastSquaresRecovery :
      reducedRankLeastSquaresRecovery Z X Y Xtilde Ytilde G Ahat Chat)
    (hCovarianceRecovery :
      reducedRankCovarianceRecovery Xtilde Ytilde G Sigmahat)
    (hComplementMin :
      ∀ H : Matrix k r ℝ, reducedRankGNormalized Xtilde H →
        (1 - Gᵀ * reducedRankGPencilA Xtilde Ytilde * G).det ≤
          (1 - Hᵀ * reducedRankGPencilA Xtilde Ytilde * H).det)
    (hFull :
      ((Ytilde - Xtilde * ((Xtildeᵀ * Xtilde)⁻¹ * Xtildeᵀ * Ytilde))ᵀ *
        (Ytilde - Xtilde *
          ((Xtildeᵀ * Xtilde)⁻¹ * Xtildeᵀ * Ytilde))).PosDef) :
    reducedRankGaussianMLE Z X Y G Ahat Chat Sigmahat := by
  have hAllProfilePos :
      ∀ H : Matrix k r ℝ, reducedRankGNormalized Xtilde H →
        (reducedRankSigmaHat Xtilde Ytilde H).PosDef := by
    intro H hHNorm
    exact reducedRankSigmaHat_posDef_of_fullResidual_posDef
      Xtilde Ytilde H hn hXGram hHNorm hFull
  have hSigmahat : Sigmahat.PosDef := by
    rw [hCovarianceRecovery]
    exact hAllProfilePos G hNorm
  exact reducedRankGaussianMLE_of_positive_roots_of_complementDet_minimal
    Z X Y Xtilde Ytilde G Ahat Chat Sigmahat lambda hXtilde hYtilde hn
      hXGram hYGram hNorm hEigenvectors hLambda hLeastSquaresRecovery
      hCovarianceRecovery hSigmahat hComplementMin hAllProfilePos

/-- Residualized Hansen-facing global MLE endpoint for Theorem 11.7.

Full sample-Gram regularity supplies positive-definite `Xtilde` and `Ytilde`
Grams. Positive definiteness of Hansen's unrestricted residual Gram
`Etilde' Etilde` supplies interiority for every normalized covariance profile.
Thus a complement-minimizing normalized generalized-eigenblock with positive
selected roots makes the displayed `Ahat`, `Chat`, and `Sigmahat` the actual
Gaussian MLE against every admissible exact-rank competitor. -/
private theorem residualized_gaussianMLE_of_positive_roots_complement_min
    [Fintype ell] [DecidableEq ell]
    (Z : Matrix n ell ℝ) (X : Matrix n k ℝ) (Y : Matrix n m ℝ)
    (G : Matrix k r ℝ) (lambda : r → ℝ)
    [Invertible (Zᵀ * Z)]
    [Invertible ((Matrix.fromCols X Z)ᵀ * Matrix.fromCols X Z)]
    [Invertible ((Matrix.fromCols Y Z)ᵀ * Matrix.fromCols Y Z)]
    (hn : 0 < Fintype.card n)
    (hNorm : reducedRankGNormalized (reducedRankTildeX Z X) G)
    (hEigenvectors : reducedRankHansenGEigenvectors
      (reducedRankTildeX Z X) (reducedRankTildeY Z Y) lambda G)
    (hLambda : ∀ j, 0 < lambda j)
    (hComplementMin :
      ∀ H : Matrix k r ℝ, reducedRankGNormalized (reducedRankTildeX Z X) H →
        (1 - Gᵀ * reducedRankGPencilA
          (reducedRankTildeX Z X) (reducedRankTildeY Z Y) * G).det ≤
          (1 - Hᵀ * reducedRankGPencilA
            (reducedRankTildeX Z X) (reducedRankTildeY Z Y) * H).det)
    (hEGram :
      ((reducedRankTildeE X Z Y)ᵀ * reducedRankTildeE X Z Y).PosDef) :
    reducedRankGaussianMLE Z X Y G
      (reducedRankAhat (reducedRankTildeX Z X) (reducedRankTildeY Z Y) G)
      (reducedRankChat Z X Y G
        (reducedRankAhat (reducedRankTildeX Z X) (reducedRankTildeY Z Y) G))
      (reducedRankSigmaHat
        (reducedRankTildeX Z X) (reducedRankTildeY Z Y) G) := by
  let Xtilde : Matrix n k ℝ := reducedRankTildeX Z X
  let Ytilde : Matrix n m ℝ := reducedRankTildeY Z Y
  let Ahat : Matrix m r ℝ := reducedRankAhat Xtilde Ytilde G
  let Chat : Matrix ell m ℝ := reducedRankChat Z X Y G Ahat
  let Sigmahat : Matrix m m ℝ := reducedRankSigmaHat Xtilde Ytilde G
  have hXGram : (Xtildeᵀ * Xtilde).PosDef := by
    simpa [Xtilde] using reducedRankTildeX_gram_posDef Z X
  have hYGram : (Ytildeᵀ * Ytilde).PosDef := by
    simpa [Ytilde] using reducedRankTildeY_gram_posDef Z Y
  have hXdet : IsUnit (Xtildeᵀ * Xtilde).det :=
    (Matrix.isUnit_iff_isUnit_det (Xtildeᵀ * Xtilde)).mp hXGram.isUnit
  letI : Invertible (Xtildeᵀ * Xtilde) :=
    Matrix.invertibleOfIsUnitDet (A := Xtildeᵀ * Xtilde) hXdet
  have hFull :
      ((Ytilde - Xtilde * ((Xtildeᵀ * Xtilde)⁻¹ * Xtildeᵀ * Ytilde))ᵀ *
        (Ytilde - Xtilde *
          ((Xtildeᵀ * Xtilde)⁻¹ * Xtildeᵀ * Ytilde))).PosDef := by
    rw [show Ytilde - Xtilde *
          ((Xtildeᵀ * Xtilde)⁻¹ * Xtildeᵀ * Ytilde) =
        reducedRankTildeE X Z Y by
      simpa [Xtilde, Ytilde] using reducedRankFullResidual_eq_tildeE Z X Y]
    exact hEGram
  have hRecovery :
      reducedRankLeastSquaresRecovery Z X Y Xtilde Ytilde G Ahat Chat :=
    ⟨rfl, rfl⟩
  have hCovarianceRecovery :
      reducedRankCovarianceRecovery Xtilde Ytilde G Sigmahat := rfl
  have hResult :=
    gaussianMLE_of_positive_roots_complement_min_fullResidual
      Z X Y Xtilde Ytilde G Ahat Chat Sigmahat lambda rfl rfl hn hXGram
        hYGram (by simpa [Xtilde] using hNorm)
        (by simpa [Xtilde, Ytilde] using hEigenvectors) hLambda hRecovery
        hCovarianceRecovery
        (by simpa [Xtilde, Ytilde] using hComplementMin) hFull
  simpa [Xtilde, Ytilde, Ahat, Chat, Sigmahat] using hResult

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
  ordered_roots :
    ReducedRankHansenOrderedRootWitness Xtilde Ytilde lambda eta
  covariance_posDef : Sigma.PosDef
  gaussian_mle : reducedRankGaussianMLE Z X Y G Acoef C Sigma
  logLikelihood_eq_gaussian :
    logLikelihood = reducedRankGaussianLogLikelihood Z X Y G Acoef C Sigma

/-- Complete residualized Hansen Theorem 11.7 certificate under explicit
identified spectral and regular-sample conditions.

The identified max/max certificate supplies Hansen's `G` and `Aperp` formulas.
Positive selected roots and complement-determinant minimality supply the exact-
rank global MLE. For positive rank, positive `Etilde' Etilde` supplies covariance
interiority; the rank-zero case instead reduces every covariance profile to
the positive-definite residualized outcome Gram. Roots below one identify the
corrected displayed likelihood with the raw Gaussian likelihood. The joint
tie-safe spectral construction in `ReducedRankJointSpectrum` supplies this
theorem's identified certificate and its exact ordered-root witness. -/
private theorem hansen11_7_gaussianMLE_of_identified
    (Z : Matrix n ell ℝ) (X : Matrix n k ℝ) (Y : Matrix n m ℝ)
    (G : Matrix k r ℝ) (lambda : r → ℝ)
    (Aperp : Matrix m s ℝ) (eta : s → ℝ)
    [Invertible (Zᵀ * Z)]
    [Invertible ((Matrix.fromCols X Z)ᵀ * Matrix.fromCols X Z)]
    [Invertible ((Matrix.fromCols Y Z)ᵀ * Matrix.fromCols Y Z)]
    (hn : 0 < Fintype.card n)
    (hSpec : ReducedRankHansenIdentifiedSpectralMaximizerCertificate
      (reducedRankTildeX Z X) (reducedRankTildeY Z Y) (reducedRankTildeE X Z Y)
      G lambda Aperp eta)
    (hLambdaPos : ∀ j, 0 < lambda j)
    (hLambdaLtOne : ∀ j, lambda j < 1)
    (hComplementMin :
      ∀ H : Matrix k r ℝ, reducedRankGNormalized (reducedRankTildeX Z X) H →
        (1 - Gᵀ * reducedRankGPencilA
          (reducedRankTildeX Z X) (reducedRankTildeY Z Y) * G).det ≤
          (1 - Hᵀ * reducedRankGPencilA
            (reducedRankTildeX Z X) (reducedRankTildeY Z Y) * H).det)
    (hResidualRegular :
      ((reducedRankTildeE X Z Y)ᵀ * reducedRankTildeE X Z Y).PosDef ∨
        IsEmpty r)
    (hAperpDimension : Fintype.card s = Fintype.card m - Fintype.card r)
    (hRankDimension : Fintype.card r < min (Fintype.card k) (Fintype.card m))
    (hOrdered : ReducedRankHansenOrderedRootWitness
      (reducedRankTildeX Z X) (reducedRankTildeY Z Y) lambda eta) :
    ReducedRankHansenTheorem11_7GaussianMLE
      Z X (reducedRankTildeX Z X) Y (reducedRankTildeY Z Y) (reducedRankTildeE X Z Y)
      G ((reducedRankTildeY Z Y)ᵀ * reducedRankTildeX Z X * G)
      (reducedRankChat Z X Y G
        ((reducedRankTildeY Z Y)ᵀ * reducedRankTildeX Z X * G))
      ((Fintype.card n : ℝ)⁻¹ •
        ((reducedRankTildeY Z Y)ᵀ * reducedRankTildeY Z Y -
          ((reducedRankTildeY Z Y)ᵀ * reducedRankTildeX Z X * G) *
            ((reducedRankTildeY Z Y)ᵀ * reducedRankTildeX Z X * G)ᵀ))
      Aperp lambda eta
      (reducedRankMaximizedLogLikelihood (reducedRankTildeY Z Y) lambda) := by
  let Xtilde : Matrix n k ℝ := reducedRankTildeX Z X
  let Ytilde : Matrix n m ℝ := reducedRankTildeY Z Y
  let Etilde : Matrix n m ℝ := reducedRankTildeE X Z Y
  let Acoef : Matrix m r ℝ := Ytildeᵀ * Xtilde * G
  let C : Matrix ell m ℝ := reducedRankChat Z X Y G Acoef
  let Sigma : Matrix m m ℝ :=
    (Fintype.card n : ℝ)⁻¹ • (Ytildeᵀ * Ytilde - Acoef * Acoefᵀ)
  let logLikelihood : ℝ := reducedRankMaximizedLogLikelihood Ytilde lambda
  have hNorm : reducedRankGNormalized Xtilde G := by
    simpa [Xtilde, Ytilde, Etilde] using
      hSpec.spectral_maximizers.g_max.normalized
  have hFormula : ReducedRankHansenTheorem11_7
      Z X Xtilde Y Ytilde Etilde G Acoef C Sigma Aperp lambda eta logLikelihood := by
    simpa [Xtilde, Ytilde, Etilde, Acoef, C, Sigma, logLikelihood] using
      reducedRankHansenTheorem11_7_of_identified_spectral_maximizer_certificate
        Z X Xtilde Y Ytilde Etilde G lambda Aperp eta
          (by simpa [Xtilde, Ytilde, Etilde] using hSpec)
  have hXGram : (Xtildeᵀ * Xtilde).PosDef := by
    simpa [Xtilde] using reducedRankTildeX_gram_posDef Z X
  have hYGram : (Ytildeᵀ * Ytilde).PosDef := by
    simpa [Ytilde] using reducedRankTildeY_gram_posDef Z Y
  have hMLE : reducedRankGaussianMLE Z X Y G Acoef C Sigma := by
    rcases hResidualRegular with hEGram | hEmpty
    · have hMLE0 :=
        residualized_gaussianMLE_of_positive_roots_complement_min
          Z X Y G lambda hn (by simpa [Xtilde] using hNorm)
            (by simpa [Xtilde, Ytilde, Etilde] using
              hSpec.spectral_maximizers.g_max.eigenvectors)
            hLambdaPos hComplementMin hEGram
      rw [reducedRankAhat_eq_cross_of_normalized Xtilde Ytilde G hNorm,
        reducedRankSigmaHat_eq_Ahat_mul_transpose_of_normalized
          Xtilde Ytilde G hNorm] at hMLE0
      simpa [Xtilde, Ytilde, Acoef, C, Sigma] using hMLE0
    · letI : IsEmpty r := hEmpty
      have hSigmaEq (H : Matrix k r ℝ)
          (hHNorm : reducedRankGNormalized Xtilde H) :
          reducedRankSigmaHat Xtilde Ytilde H =
            (Fintype.card n : ℝ)⁻¹ • (Ytildeᵀ * Ytilde) := by
        rw [reducedRankSigmaHat_eq_Ahat_mul_transpose_of_normalized
          Xtilde Ytilde H hHNorm]
        have hcross : Ytildeᵀ * Xtilde * H = 0 := by
          ext i j
          exact isEmptyElim j
        have hzero :
            (Ytildeᵀ * Xtilde * H) * (Ytildeᵀ * Xtilde * H)ᵀ = 0 := by
          rw [hcross, Matrix.zero_mul]
        rw [hzero, sub_zero]
      have hScalePos : 0 < (Fintype.card n : ℝ)⁻¹ :=
        inv_pos.mpr (by exact_mod_cast hn)
      have hAllProfilePos :
          ∀ H : Matrix k r ℝ, reducedRankGNormalized Xtilde H →
            (reducedRankSigmaHat Xtilde Ytilde H).PosDef := by
        intro H hHNorm
        rw [hSigmaEq H hHNorm]
        exact hYGram.smul hScalePos
      have hSigma : Sigma.PosDef := by
        rw [hFormula.covariance_recovery]
        exact hAllProfilePos G hNorm
      have hProfileMin :
          ∀ H : Matrix k r ℝ, reducedRankGNormalized Xtilde H →
            (reducedRankSigmaHat Xtilde Ytilde G).det ≤
              (reducedRankSigmaHat Xtilde Ytilde H).det := by
        intro H hHNorm
        rw [hSigmaEq G hNorm, hSigmaEq H hHNorm]
      exact gaussianMLE_of_positive_roots_profile_min
        Z X Y Xtilde Ytilde G Acoef C Sigma lambda rfl rfl hn hXGram hNorm
          (by simpa [Xtilde, Ytilde, Etilde] using
            hSpec.spectral_maximizers.g_max.eigenvectors)
          hLambdaPos hFormula.least_squares_recovery
          hFormula.covariance_recovery hSigma hProfileMin hAllProfilePos
  have hValue :=
    reducedRankGaussianLogLikelihood_at_recovery_eq_maximizedLogLikelihood
      Z X Y Xtilde Ytilde G Acoef C Sigma lambda rfl rfl hn hYGram hNorm
        (by simpa [Xtilde, Ytilde, Etilde] using
          hSpec.spectral_maximizers.g_max.eigenvectors)
        hFormula.least_squares_recovery hFormula.covariance_recovery hMLE.1.1
        hLambdaLtOne
  refine {
    formula_certificate := hFormula
    x_residualized := rfl
    y_residualized := rfl
    e_residualized := rfl
    aperp_dimension := hAperpDimension
    rank_dimension := hRankDimension
    ordered_roots := hOrdered
    covariance_posDef := hMLE.1.1
    gaussian_mle := hMLE
    logLikelihood_eq_gaussian := ?_
  }
  simpa [Xtilde, Ytilde, Acoef, C, Sigma, logLikelihood] using hValue.symm

omit [Fintype s] [DecidableEq s] in
/-- Hansen Theorem 11.7 for residualized multivariate regression, including
existence of the jointly selected primal and dual spectral blocks and the
actual global Gaussian MLE conclusion.

The construction is tie-safe: no separation is assumed between the last
selected root and the first omitted root. The selected-rank premise is the
finite-sample condition ensuring that the positive exact-rank parameter space
has a maximizer rather than only a lower-rank boundary supremum. Positive
definiteness of the unrestricted residual Gram is required only for positive
rank; the rank-zero case is handled directly from the residualized outcome
Gram. -/
theorem reducedRankHansenTheorem11_7GaussianMLE_residualized_exists
    (Z : Matrix n ell ℝ) (X : Matrix n k ℝ) (Y : Matrix n m ℝ)
    [Invertible (Zᵀ * Z)]
    [Invertible ((Matrix.fromCols X Z)ᵀ * Matrix.fromCols X Z)]
    [Invertible ((Matrix.fromCols Y Z)ᵀ * Matrix.fromCols Y Z)]
    (hn : 0 < Fintype.card n)
    (hResidualRegular :
      ((reducedRankTildeE X Z Y)ᵀ * reducedRankTildeE X Z Y).PosDef ∨
        IsEmpty r)
    (hRankDimension : Fintype.card r < min (Fintype.card k) (Fintype.card m))
    (hSelectedRank : Fintype.card r ≤
      ((reducedRankTildeX Z X)ᵀ * reducedRankTildeY Z Y).rank) :
    ∃ (G : Matrix k r ℝ) (lambda : r → ℝ)
        (Aperp : Matrix m (reducedRankAperpIndex m r) ℝ)
        (eta : reducedRankAperpIndex m r → ℝ),
      ReducedRankHansenTheorem11_7GaussianMLE
        Z X (reducedRankTildeX Z X) Y (reducedRankTildeY Z Y)
        (reducedRankTildeE X Z Y)
        G ((reducedRankTildeY Z Y)ᵀ * reducedRankTildeX Z X * G)
        (reducedRankChat Z X Y G
          ((reducedRankTildeY Z Y)ᵀ * reducedRankTildeX Z X * G))
        ((Fintype.card n : ℝ)⁻¹ •
          ((reducedRankTildeY Z Y)ᵀ * reducedRankTildeY Z Y -
            ((reducedRankTildeY Z Y)ᵀ * reducedRankTildeX Z X * G) *
              ((reducedRankTildeY Z Y)ᵀ * reducedRankTildeX Z X * G)ᵀ))
        Aperp lambda eta
        (reducedRankMaximizedLogLikelihood (reducedRankTildeY Z Y) lambda) := by
  have hXGram :
      ((reducedRankTildeX Z X)ᵀ * reducedRankTildeX Z X).PosDef :=
    reducedRankTildeX_gram_posDef Z X
  have hYGram :
      ((reducedRankTildeY Z Y)ᵀ * reducedRankTildeY Z Y).PosDef :=
    reducedRankTildeY_gram_posDef Z Y
  have hComplement := reducedRankAperpPencilA_tildeE_eq_complement Z X Y
  have hrk : Fintype.card r ≤ Fintype.card k := by omega
  have hrm : Fintype.card r ≤ Fintype.card m := by omega
  obtain ⟨G, lambda, Aperp, eta, hSpec, hLambdaPos, hLambdaLtOne,
      hComplementMin, hOrdered⟩ :=
    ReducedRankHansenIdentifiedSpectralMaximizerCertificate.exists_of_complement_pencil
      (s := reducedRankAperpIndex m r)
      (reducedRankTildeX Z X) (reducedRankTildeY Z Y)
      (reducedRankTildeE X Z Y) hXGram hYGram hResidualRegular hComplement hrk hrm
      (reducedRankAperpDimension_canonical (m := m) (r := r)) hSelectedRank
  refine ⟨G, lambda, Aperp, eta, ?_⟩
  exact hansen11_7_gaussianMLE_of_identified
    Z X Y G lambda Aperp eta hn hSpec hLambdaPos hLambdaLtOne
      hComplementMin hResidualRegular
      (reducedRankAperpDimension_canonical (m := m) (r := r)) hRankDimension
      hOrdered

end TheoremCertificate

end HansenEconometrics
