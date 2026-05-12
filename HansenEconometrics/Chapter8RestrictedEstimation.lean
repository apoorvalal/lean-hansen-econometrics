import HansenEconometrics.Chapter4LeastSquaresRegression
import HansenEconometrics.StudentT

open MeasureTheory ProbabilityTheory
open scoped Matrix ENNReal Topology MeasureTheory ProbabilityTheory

namespace HansenEconometrics

open Matrix

/-!
# Chapter 8: restricted estimation, finite-sample layer

This module provides a Chapter 8 constrained least-squares surface.  The deterministic and
stochastic results below are deliberately stated as wrappers over explicit lower-level algebraic,
conditional-moment, and law inputs when the full textbook derivation is not yet available in the
repository.
-/

variable {n k q : Type*}
variable [Fintype n] [Fintype k] [Fintype q]
variable [DecidableEq n] [DecidableEq k] [DecidableEq q]

/-- Hansen Chapter 8 restriction Gram matrix, `R'(X'X)⁻¹R`. -/
noncomputable def clsConstraintGram
    (X : Matrix n k ℝ) (R : Matrix k q ℝ) [Invertible (Xᵀ * X)] : Matrix q q ℝ :=
  Rᵀ * ⅟ (Xᵀ * X) * R

/-- Matrix mapping restriction gaps into coefficient corrections. -/
noncomputable def clsRestrictionAdjustmentMatrix
    (X : Matrix n k ℝ) (R : Matrix k q ℝ) [Invertible (Xᵀ * X)]
    [Invertible (clsConstraintGram X R)] : Matrix k q ℝ :=
  ⅟ (Xᵀ * X) * R * ⅟ (clsConstraintGram X R)

/-- CLS covariance correction matrix, `G⁻¹R(R'G⁻¹R)⁻¹R'G⁻¹`. -/
noncomputable def clsCorrectionMatrix
    (X : Matrix n k ℝ) (R : Matrix k q ℝ) [Invertible (Xᵀ * X)]
    [Invertible (clsConstraintGram X R)] : Matrix k k ℝ :=
  clsRestrictionAdjustmentMatrix X R * Rᵀ * ⅟ (Xᵀ * X)

/-- Hansen constrained least-squares coefficient estimator. -/
noncomputable def clsBeta
    (X : Matrix n k ℝ) (y : n → ℝ) (R : Matrix k q ℝ) (c : q → ℝ)
    [Invertible (Xᵀ * X)] [Invertible (clsConstraintGram X R)] : k → ℝ :=
  olsBeta X y - clsRestrictionAdjustmentMatrix X R *ᵥ (Rᵀ *ᵥ olsBeta X y - c)

/-- CLS residual vector. -/
noncomputable def clsResidual
    (X : Matrix n k ℝ) (y : n → ℝ) (R : Matrix k q ℝ) (c : q → ℝ)
    [Invertible (Xᵀ * X)] [Invertible (clsConstraintGram X R)] : n → ℝ :=
  y - X *ᵥ clsBeta X y R c

/-- CLS residual-maker matrix. -/
noncomputable def clsProjectionMatrix
    (X : Matrix n k ℝ) (R : Matrix k q ℝ) [Invertible (Xᵀ * X)]
    [Invertible (clsConstraintGram X R)] : Matrix n n ℝ :=
  annihilatorMatrix X + X * clsCorrectionMatrix X R * Xᵀ

/-- CLS residual-variance estimator with `n - k + q` degrees of freedom. -/
noncomputable def clsResidualVariance
    (X : Matrix n k ℝ) (y : n → ℝ) (R : Matrix k q ℝ) (c : q → ℝ)
    [Invertible (Xᵀ * X)] [Invertible (clsConstraintGram X R)] : ℝ :=
  ((Fintype.card n : ℝ) - Fintype.card k + Fintype.card q)⁻¹ *
    dotProduct (clsResidual X y R c) (clsResidual X y R c)

/-- Conditional covariance matrix for the linear CLS coefficient transform. -/
noncomputable def clsConditionalVarianceMatrix
    (X : Matrix n k ℝ) (R : Matrix k q ℝ) (D : Matrix n n ℝ)
    [Invertible (Xᵀ * X)] [Invertible (clsConstraintGram X R)] : Matrix k k ℝ :=
  let B : Matrix k n ℝ := ⅟ (Xᵀ * X) * Xᵀ - clsCorrectionMatrix X R * Xᵀ
  B * D * Bᵀ

/-- Homoskedastic CLS covariance formula. -/
noncomputable def clsHomoskedasticVarianceMatrix
    (X : Matrix n k ℝ) (R : Matrix k q ℝ) (σ2 : ℝ)
    [Invertible (Xᵀ * X)] [Invertible (clsConstraintGram X R)] : Matrix k k ℝ :=
  σ2 • (⅟ (Xᵀ * X) - clsCorrectionMatrix X R)

/-- Plug-in homoskedastic CLS covariance estimator. -/
noncomputable def clsHomoskedasticVarianceEstimator
    (X : Matrix n k ℝ) (y : n → ℝ) (R : Matrix k q ℝ) (c : q → ℝ)
    [Invertible (Xᵀ * X)] [Invertible (clsConstraintGram X R)] : Matrix k k ℝ :=
  clsHomoskedasticVarianceMatrix X R (clsResidualVariance X y R c)

/-- Hansen Theorem 8.1 restriction-gap identity in the linear model. -/
theorem cls_restriction_gap_linear_model
    (X : Matrix n k ℝ) (β : k → ℝ) (e : n → ℝ) (R : Matrix k q ℝ) (c : q → ℝ)
    [Invertible (Xᵀ * X)] (hrestrict : Rᵀ *ᵥ β = c) :
    Rᵀ *ᵥ olsBeta X (X *ᵥ β + e) - c =
      Rᵀ *ᵥ (⅟ (Xᵀ * X) *ᵥ (Xᵀ *ᵥ e)) := by
  rw [olsBeta_linear_decomposition]
  ext j
  simp [Matrix.mulVec_add, hrestrict]

/-- Hansen Theorem 8.1 coefficient decomposition in the linear model. -/
theorem clsBeta_linear_model
    (X : Matrix n k ℝ) (β : k → ℝ) (e : n → ℝ) (R : Matrix k q ℝ) (c : q → ℝ)
    [Invertible (Xᵀ * X)] [Invertible (clsConstraintGram X R)]
    (hrestrict : Rᵀ *ᵥ β = c) :
    clsBeta X (X *ᵥ β + e) R c =
      β + (⅟ (Xᵀ * X) * Xᵀ - clsCorrectionMatrix X R * Xᵀ) *ᵥ e := by
  unfold clsBeta clsCorrectionMatrix clsRestrictionAdjustmentMatrix
  rw [olsBeta_linear_decomposition]
  ext i
  simp [Matrix.mulVec_add, Matrix.add_mulVec, Matrix.neg_mulVec, Matrix.mulVec_mulVec,
    Matrix.mul_assoc, hrestrict, sub_eq_add_neg, add_assoc]

/-- Hansen Theorem 8.1 residual decomposition in the linear model. -/
theorem clsResidual_linear_model
    (X : Matrix n k ℝ) (β : k → ℝ) (e : n → ℝ) (R : Matrix k q ℝ) (c : q → ℝ)
    [Invertible (Xᵀ * X)] [Invertible (clsConstraintGram X R)]
    (hrestrict : Rᵀ *ᵥ β = c) :
    clsResidual X (X *ᵥ β + e) R c = clsProjectionMatrix X R *ᵥ e := by
  unfold clsResidual clsProjectionMatrix annihilatorMatrix
  rw [clsBeta_linear_model X β e R c hrestrict]
  ext i
  simp [hatMatrix, clsCorrectionMatrix, Matrix.mulVec_add, Matrix.add_mulVec,
    Matrix.neg_mulVec, Matrix.mulVec_neg, Matrix.mulVec_mulVec, Matrix.mul_assoc,
    sub_eq_add_neg, add_assoc, add_comm, add_left_comm]
  ring

/-- The restriction Gram matrix is symmetric. -/
@[simp]
theorem clsConstraintGram_transpose
    (X : Matrix n k ℝ) (R : Matrix k q ℝ) [Invertible (Xᵀ * X)] :
    (clsConstraintGram X R)ᵀ = clsConstraintGram X R := by
  unfold clsConstraintGram
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
    inv_gram_transpose]
  simp [Matrix.mul_assoc]

/-- The inverse of the symmetric restriction Gram matrix is symmetric. -/
@[simp]
theorem inv_clsConstraintGram_transpose
    (X : Matrix n k ℝ) (R : Matrix k q ℝ) [Invertible (Xᵀ * X)]
    [Invertible (clsConstraintGram X R)] :
    (⅟ (clsConstraintGram X R))ᵀ = ⅟ (clsConstraintGram X R) := by
  simpa [clsConstraintGram_transpose (X := X) (R := R)] using
    (Matrix.transpose_invOf (A := clsConstraintGram X R))

/-- The CLS covariance correction matrix is symmetric. -/
@[simp]
theorem clsCorrectionMatrix_transpose
    (X : Matrix n k ℝ) (R : Matrix k q ℝ) [Invertible (Xᵀ * X)]
    [Invertible (clsConstraintGram X R)] :
    (clsCorrectionMatrix X R)ᵀ = clsCorrectionMatrix X R := by
  unfold clsCorrectionMatrix clsRestrictionAdjustmentMatrix
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_mul,
    Matrix.transpose_transpose, inv_gram_transpose, inv_clsConstraintGram_transpose]
  simp [Matrix.mul_assoc]

omit [DecidableEq n] in
private lemma clsCorrectionMatrix_gram_mul_self
    (X : Matrix n k ℝ) (R : Matrix k q ℝ) [Invertible (Xᵀ * X)]
    [Invertible (clsConstraintGram X R)] :
    clsCorrectionMatrix X R * (Xᵀ * X) * clsCorrectionMatrix X R =
      clsCorrectionMatrix X R := by
  have hCG :
      clsCorrectionMatrix X R * (Xᵀ * X) =
        ⅟ (Xᵀ * X) * R * ⅟ (clsConstraintGram X R) * Rᵀ := by
    unfold clsCorrectionMatrix clsRestrictionAdjustmentMatrix
    simp [Matrix.mul_assoc]
  rw [hCG]
  unfold clsCorrectionMatrix clsRestrictionAdjustmentMatrix
  calc
    ⅟ (Xᵀ * X) * R * ⅟ (clsConstraintGram X R) * Rᵀ *
        (⅟ (Xᵀ * X) * R * ⅟ (clsConstraintGram X R) * Rᵀ * ⅟ (Xᵀ * X)) =
        ⅟ (Xᵀ * X) * R *
          (⅟ (clsConstraintGram X R) * clsConstraintGram X R *
            ⅟ (clsConstraintGram X R)) * Rᵀ * ⅟ (Xᵀ * X) := by
      simp [clsConstraintGram, Matrix.mul_assoc]
    _ = ⅟ (Xᵀ * X) * R * ⅟ (clsConstraintGram X R) * Rᵀ * ⅟ (Xᵀ * X) := by
      rw [invOf_mul_self]
      simp [Matrix.mul_assoc]

/-- Hansen Theorem 8.1: symmetry of the CLS residual-maker matrix. -/
theorem clsProjectionMatrix_transpose
    (X : Matrix n k ℝ) (R : Matrix k q ℝ) [Invertible (Xᵀ * X)]
    [Invertible (clsConstraintGram X R)] :
    (clsProjectionMatrix X R)ᵀ = clsProjectionMatrix X R := by
  unfold clsProjectionMatrix
  rw [Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_mul,
    Matrix.transpose_transpose, annihilatorMatrix_transpose, clsCorrectionMatrix_transpose]
  simp [Matrix.mul_assoc]

/-- Hansen Theorem 8.1: the CLS residual-maker matrix is idempotent. -/
theorem clsProjectionMatrix_idempotent
    (X : Matrix n k ℝ) (R : Matrix k q ℝ) [Invertible (Xᵀ * X)]
    [Invertible (clsConstraintGram X R)] :
    clsProjectionMatrix X R * clsProjectionMatrix X R = clsProjectionMatrix X R := by
  let K : Matrix n n ℝ := X * clsCorrectionMatrix X R * Xᵀ
  have hMX : annihilatorMatrix X * X = 0 := annihilator_mul_X X
  have hXM : Xᵀ * annihilatorMatrix X = 0 := by
    have h := congrArg Matrix.transpose (annihilator_mul_X (X := X))
    simpa [Matrix.transpose_mul, annihilatorMatrix_transpose] using h
  have hMK : annihilatorMatrix X * K = 0 := by
    calc
      annihilatorMatrix X * K =
          (annihilatorMatrix X * X) * (clsCorrectionMatrix X R * Xᵀ) := by
        simp [K, Matrix.mul_assoc]
      _ = 0 := by simp [hMX]
  have hKM : K * annihilatorMatrix X = 0 := by
    calc
      K * annihilatorMatrix X = X * clsCorrectionMatrix X R * (Xᵀ * annihilatorMatrix X) := by
        simp [K, Matrix.mul_assoc]
      _ = 0 := by simp [hXM]
  have hKK : K * K = K := by
    calc
      K * K = X * (clsCorrectionMatrix X R * (Xᵀ * X) * clsCorrectionMatrix X R) * Xᵀ := by
        simp [K, Matrix.mul_assoc]
      _ = K := by
        rw [clsCorrectionMatrix_gram_mul_self]
  change (annihilatorMatrix X + K) * (annihilatorMatrix X + K) = annihilatorMatrix X + K
  simp [Matrix.add_mul, Matrix.mul_add, annihilatorMatrix_idempotent, hMK, hKM, hKK]

/-- Hansen Theorem 8.1: trace of the CLS residual-maker matrix. -/
theorem clsProjectionMatrix_trace
    (X : Matrix n k ℝ) (R : Matrix k q ℝ) [Invertible (Xᵀ * X)]
    [Invertible (clsConstraintGram X R)] :
    Matrix.trace (clsProjectionMatrix X R) =
      (Fintype.card n : ℝ) - Fintype.card k + Fintype.card q := by
  unfold clsProjectionMatrix
  rw [Matrix.trace_add, annihilatorMatrix_trace]
  have hK : Matrix.trace (X * clsCorrectionMatrix X R * Xᵀ) = (Fintype.card q : ℝ) := by
    calc
      Matrix.trace (X * clsCorrectionMatrix X R * Xᵀ) =
          Matrix.trace (Xᵀ * X * clsCorrectionMatrix X R) := by
        rw [Matrix.trace_mul_cycle]
      _ = Matrix.trace (R * ⅟ (clsConstraintGram X R) * Rᵀ * ⅟ (Xᵀ * X)) := by
        unfold clsCorrectionMatrix clsRestrictionAdjustmentMatrix
        simp [Matrix.mul_assoc]
      _ = Matrix.trace (R * (⅟ (clsConstraintGram X R) * Rᵀ * ⅟ (Xᵀ * X))) := by
        simp only [← Matrix.mul_assoc]
      _ = Matrix.trace ((⅟ (clsConstraintGram X R) * Rᵀ * ⅟ (Xᵀ * X)) * R) := by
        rw [Matrix.trace_mul_comm]
      _ = Matrix.trace (⅟ (clsConstraintGram X R) * clsConstraintGram X R) := by
        unfold clsConstraintGram
        simp [Matrix.mul_assoc]
      _ = Matrix.trace (1 : Matrix q q ℝ) := by
        rw [invOf_mul_self]
      _ = (Fintype.card q : ℝ) := by
        rw [Matrix.trace_one]
  rw [hK]

/-- Hansen Theorem 8.2 conditional-unbiasedness bridge for CLS.

The stochastic input is the conditional mean of the linear CLS error term, while the theorem
rewrites the estimator itself using `clsBeta_linear_model`. -/
theorem cls_condExp_unbiased
    {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω}
    (X : Matrix n k ℝ) (β : k → ℝ) (e : Ω → n → ℝ) (R : Matrix k q ℝ) (c : q → ℝ)
    [Invertible (Xᵀ * X)] [Invertible (clsConstraintGram X R)]
    (hrestrict : Rᵀ *ᵥ β = c)
    (hmean : μ[(fun ω =>
      β + (⅟(Xᵀ * X) * Xᵀ - clsCorrectionMatrix X R * Xᵀ) *ᵥ e ω) | m] =ᵐ[μ]
        fun _ => β) :
    μ[(fun ω => clsBeta X (X *ᵥ β + e ω) R c) | m] =ᵐ[μ] fun _ => β := by
  have hfun :
      (fun ω => clsBeta X (X *ᵥ β + e ω) R c) =
        fun ω => β + (⅟(Xᵀ * X) * Xᵀ - clsCorrectionMatrix X R * Xᵀ) *ᵥ e ω := by
    funext ω
    exact clsBeta_linear_model X β (e ω) R c hrestrict
  simpa [hfun] using hmean

omit [DecidableEq n] in
/-- Lean-only deterministic bridge for Hansen Theorem 8.3's homoskedastic sandwich core. -/
theorem cls_sandwichCore_eq
    (X : Matrix n k ℝ) (R : Matrix k q ℝ) [Invertible (Xᵀ * X)]
    [Invertible (clsConstraintGram X R)] :
    (let B : Matrix k n ℝ := ⅟ (Xᵀ * X) * Xᵀ - clsCorrectionMatrix X R * Xᵀ
     B * Bᵀ) = ⅟ (Xᵀ * X) - clsCorrectionMatrix X R := by
  classical
  have hAGA : ⅟ (Xᵀ * X) * Xᵀ * X * ⅟ (Xᵀ * X) = ⅟ (Xᵀ * X) := by
    calc
      ⅟ (Xᵀ * X) * Xᵀ * X * ⅟ (Xᵀ * X) =
          ⅟ (Xᵀ * X) * (Xᵀ * X) * ⅟ (Xᵀ * X) := by
        simp [Matrix.mul_assoc]
      _ = ⅟ (Xᵀ * X) := by
        rw [invOf_mul_self, Matrix.one_mul]
  have hCGA : clsCorrectionMatrix X R * Xᵀ * X * ⅟ (Xᵀ * X) =
      clsCorrectionMatrix X R := by
    calc
      clsCorrectionMatrix X R * Xᵀ * X * ⅟ (Xᵀ * X) =
          clsCorrectionMatrix X R * (Xᵀ * X) * ⅟ (Xᵀ * X) := by
        simp [Matrix.mul_assoc]
      _ = clsCorrectionMatrix X R := by
        rw [Matrix.mul_assoc, mul_invOf_self, Matrix.mul_one]
  have hAGC : ⅟ (Xᵀ * X) * Xᵀ * X * clsCorrectionMatrix X R =
      clsCorrectionMatrix X R := by
    calc
      ⅟ (Xᵀ * X) * Xᵀ * X * clsCorrectionMatrix X R =
          ⅟ (Xᵀ * X) * (Xᵀ * X) * clsCorrectionMatrix X R := by
        simp [Matrix.mul_assoc]
      _ = clsCorrectionMatrix X R := by
        rw [invOf_mul_self, Matrix.one_mul]
  have hCGC : clsCorrectionMatrix X R * Xᵀ * X * clsCorrectionMatrix X R =
      clsCorrectionMatrix X R := by
    calc
      clsCorrectionMatrix X R * Xᵀ * X * clsCorrectionMatrix X R =
          clsCorrectionMatrix X R * (Xᵀ * X) * clsCorrectionMatrix X R := by
        simp [Matrix.mul_assoc]
      _ = clsCorrectionMatrix X R := clsCorrectionMatrix_gram_mul_self X R
  simp only [Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_transpose,
    inv_gram_transpose, clsCorrectionMatrix_transpose]
  simp only [Matrix.sub_mul, Matrix.mul_sub]
  simp only [← Matrix.mul_assoc]
  rw [hAGA, hCGA, hAGC, hCGC]
  simp

/-- Hansen Theorem 8.3 homoskedastic covariance bridge from the deterministic sandwich core. -/
theorem cls_conditionalVariance_homoskedastic
    (X : Matrix n k ℝ) (R : Matrix k q ℝ) (σ2 : ℝ)
    [Invertible (Xᵀ * X)] [Invertible (clsConstraintGram X R)]
    (hBB :
      (let B : Matrix k n ℝ := ⅟ (Xᵀ * X) * Xᵀ - clsCorrectionMatrix X R * Xᵀ
       B * Bᵀ) = ⅟ (Xᵀ * X) - clsCorrectionMatrix X R) :
    clsConditionalVarianceMatrix X R (σ2 • (1 : Matrix n n ℝ)) =
      clsHomoskedasticVarianceMatrix X R σ2 := by
  let B : Matrix k n ℝ := ⅟(Xᵀ * X) * Xᵀ - clsCorrectionMatrix X R * Xᵀ
  change B * (σ2 • (1 : Matrix n n ℝ)) * Bᵀ = σ2 • (⅟(Xᵀ * X) - clsCorrectionMatrix X R)
  calc
    B * (σ2 • (1 : Matrix n n ℝ)) * Bᵀ = σ2 • (B * Bᵀ) := by
      simp
    _ = σ2 • (⅟(Xᵀ * X) - clsCorrectionMatrix X R) := by
      rw [hBB]

/-- Hansen Theorem 8.4 residual-variance conditional expectation bridge.

The stochastic input is stated for the quadratic form of the structural error after applying the
CLS residual-maker. -/
theorem cls_residualVariance_condExp_eq_sigmaSq
    {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω}
    (X : Matrix n k ℝ) (β : k → ℝ) (e : Ω → n → ℝ) (R : Matrix k q ℝ) (c : q → ℝ)
    (σ2 : ℝ) [Invertible (Xᵀ * X)] [Invertible (clsConstraintGram X R)]
    (hrestrict : Rᵀ *ᵥ β = c)
    (hmean : μ[(fun ω =>
      ((Fintype.card n : ℝ) - Fintype.card k + Fintype.card q)⁻¹ *
        dotProduct (clsProjectionMatrix X R *ᵥ e ω) (clsProjectionMatrix X R *ᵥ e ω)) | m]
        =ᵐ[μ] fun _ => σ2) :
    μ[(fun ω => clsResidualVariance X (X *ᵥ β + e ω) R c) | m] =ᵐ[μ] fun _ => σ2 := by
  have hfun :
      (fun ω => clsResidualVariance X (X *ᵥ β + e ω) R c) =
        fun ω => ((Fintype.card n : ℝ) - Fintype.card k + Fintype.card q)⁻¹ *
          dotProduct (clsProjectionMatrix X R *ᵥ e ω) (clsProjectionMatrix X R *ᵥ e ω) := by
    funext ω
    unfold clsResidualVariance
    rw [clsResidual_linear_model X β (e ω) R c hrestrict]
  simpa [hfun] using hmean

/-- CLS coefficient Gaussian-law bridge from the law of its affine linear-model representation. -/
theorem clsBeta_hasGaussianLaw_of_error
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (X : Matrix n k ℝ) (β : k → ℝ) (e : Ω → n → ℝ) (R : Matrix k q ℝ) (c : q → ℝ)
    [Invertible (Xᵀ * X)] [Invertible (clsConstraintGram X R)]
    (hrestrict : Rᵀ *ᵥ β = c)
    (h : HasGaussianLaw (fun ω =>
      β + (⅟(Xᵀ * X) * Xᵀ - clsCorrectionMatrix X R * Xᵀ) *ᵥ e ω) μ) :
    HasGaussianLaw (fun ω => clsBeta X (X *ᵥ β + e ω) R c) μ := by
  have hfun :
      (fun ω => clsBeta X (X *ᵥ β + e ω) R c) =
        fun ω => β + (⅟(Xᵀ * X) * Xᵀ - clsCorrectionMatrix X R * Xᵀ) *ᵥ e ω := by
    funext ω
    exact clsBeta_linear_model X β (e ω) R c hrestrict
  simpa [hfun] using h

/-- Scaled CLS residual-variance statistic. -/
noncomputable def scaledClsResidualVarianceStatistic
    {Ω : Type*} (X : Matrix n k ℝ) (β : k → ℝ) (σ2 : ℝ) (R : Matrix k q ℝ) (c : q → ℝ)
    [Invertible (Xᵀ * X)] [Invertible (clsConstraintGram X R)] (e : Ω → n → ℝ) : Ω → ℝ :=
  fun ω =>
    (((Fintype.card n : ℝ) - Fintype.card k + Fintype.card q) *
      clsResidualVariance X (X *ᵥ β + e ω) R c) / σ2

/-- Hansen Theorem 8.5 chi-square law bridge for the scaled CLS residual statistic.

The law input is stated for the residual-maker quadratic form of the structural error; the theorem
transfers it to the named CLS residual-variance statistic using `clsResidual_linear_model`. -/
theorem scaledClsResidualVarianceStatistic_hasChiSquareLaw
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (X : Matrix n k ℝ) (β : k → ℝ) (σ2 : ℝ) (R : Matrix k q ℝ) (c : q → ℝ)
    [Invertible (Xᵀ * X)] [Invertible (clsConstraintGram X R)]
    (e : Ω → n → ℝ) (ν : ℕ) (hrestrict : Rᵀ *ᵥ β = c)
    (h : HasLaw
      (fun ω =>
        (((Fintype.card n : ℝ) - Fintype.card k + Fintype.card q) *
          (((Fintype.card n : ℝ) - Fintype.card k + Fintype.card q)⁻¹ *
            dotProduct (clsProjectionMatrix X R *ᵥ e ω) (clsProjectionMatrix X R *ᵥ e ω))) /
          σ2)
      (chiSquared ν) μ) :
    HasLaw (scaledClsResidualVarianceStatistic X β σ2 R c e) (chiSquared ν) μ := by
  have hfun :
      scaledClsResidualVarianceStatistic X β σ2 R c e =
        fun ω =>
          (((Fintype.card n : ℝ) - Fintype.card k + Fintype.card q) *
            (((Fintype.card n : ℝ) - Fintype.card k + Fintype.card q)⁻¹ *
              dotProduct (clsProjectionMatrix X R *ᵥ e ω) (clsProjectionMatrix X R *ᵥ e ω))) /
            σ2 := by
    funext ω
    unfold scaledClsResidualVarianceStatistic clsResidualVariance
    rw [clsResidual_linear_model X β (e ω) R c hrestrict]
  simpa [hfun] using h

/-- CLS t-statistic assembled from a standardized numerator and a chi-square statistic. -/
noncomputable def clsTStatFromComponents (z qstat : ℝ) (ν : ℕ) : ℝ :=
  z * (Real.sqrt (ν : ℝ) / Real.sqrt qstat)

/-- Hansen Theorem 8.5 Student-t bridge from the standard-normal numerator, chi-square
studentizer, and independence inputs. -/
theorem clsTStat_hasStudentTLaw
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (Z Q : Ω → ℝ) (ν : ℕ) (hν : 0 < ν)
    (hZ : HasLaw Z (gaussianReal 0 1) μ) (hQ : HasLaw Q (chiSquared ν) μ)
    (hInd : Z ⟂ᵢ[μ] Q) :
    HasLaw (fun ω => clsTStatFromComponents (Z ω) (Q ω) ν) (studentT ν) μ := by
  simpa [clsTStatFromComponents] using
    hasLaw_ratio_standardNormal_chiSquared_studentT hν hZ hQ hInd

end HansenEconometrics
