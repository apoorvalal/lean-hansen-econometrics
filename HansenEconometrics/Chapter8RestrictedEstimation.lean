import HansenEconometrics.Chapter4LeastSquaresRegression
import HansenEconometrics.ChiSquared
import HansenEconometrics.ProbabilityUtils
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

omit [Fintype q] [DecidableEq n] [DecidableEq q] in
/-- Hansen Theorem 8.1 restriction-gap identity in the linear model. -/
theorem cls_restriction_gap_linear_model
    (X : Matrix n k ℝ) (β : k → ℝ) (e : n → ℝ) (R : Matrix k q ℝ) (c : q → ℝ)
    [Invertible (Xᵀ * X)] (hrestrict : Rᵀ *ᵥ β = c) :
    Rᵀ *ᵥ olsBeta X (X *ᵥ β + e) - c =
      Rᵀ *ᵥ (⅟ (Xᵀ * X) *ᵥ (Xᵀ *ᵥ e)) := by
  rw [olsBeta_linear_decomposition]
  ext j
  simp [Matrix.mulVec_add, hrestrict]

omit [DecidableEq n] in
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

omit [Fintype q] [DecidableEq n] [DecidableEq q] in
/-- The restriction Gram matrix is symmetric. -/
@[simp]
theorem clsConstraintGram_transpose
    (X : Matrix n k ℝ) (R : Matrix k q ℝ) [Invertible (Xᵀ * X)] :
    (clsConstraintGram X R)ᵀ = clsConstraintGram X R := by
  unfold clsConstraintGram
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
    inv_gram_transpose]
  simp [Matrix.mul_assoc]

omit [DecidableEq n] in
/-- The inverse of the symmetric restriction Gram matrix is symmetric. -/
@[simp]
theorem inv_clsConstraintGram_transpose
    (X : Matrix n k ℝ) (R : Matrix k q ℝ) [Invertible (Xᵀ * X)]
    [Invertible (clsConstraintGram X R)] :
    (⅟ (clsConstraintGram X R))ᵀ = ⅟ (clsConstraintGram X R) := by
  simpa [clsConstraintGram_transpose (X := X) (R := R)] using
    (Matrix.transpose_invOf (A := clsConstraintGram X R))

omit [DecidableEq n] in
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

/-- The CLS residual-maker matrix is Hermitian (equivalently, symmetric for real matrices). -/
theorem clsProjectionMatrix_isHermitian
    (X : Matrix n k ℝ) (R : Matrix k q ℝ) [Invertible (Xᵀ * X)]
    [Invertible (clsConstraintGram X R)] :
    (clsProjectionMatrix X R).IsHermitian :=
  (Matrix.conjTranspose_eq_transpose_of_trivial _).trans (clsProjectionMatrix_transpose X R)

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

/-- The rank of the CLS residual-maker plus the number of coefficients equals
observations plus the number of restrictions. Equivalent to rank(Pcls) = n − k + q. -/
theorem clsProjectionMatrix_rank_add
    (X : Matrix n k ℝ) (R : Matrix k q ℝ) [Invertible (Xᵀ * X)]
    [Invertible (clsConstraintGram X R)] :
    (clsProjectionMatrix X R).rank + Fintype.card k = Fintype.card n + Fintype.card q := by
  have h := rank_eq_natCast_trace_of_isHermitian_idempotent
    (clsProjectionMatrix_isHermitian X R) (clsProjectionMatrix_idempotent X R)
  rw [clsProjectionMatrix_trace] at h
  exact_mod_cast show ((clsProjectionMatrix X R).rank : ℝ) + (Fintype.card k : ℝ) =
      (Fintype.card n : ℝ) + (Fintype.card q : ℝ) by
    linarith

/-- Hansen Theorem 8.1: the rank of the CLS residual-maker is `n - k + q`. -/
theorem clsProjectionMatrix_rank
    (X : Matrix n k ℝ) (R : Matrix k q ℝ) [Invertible (Xᵀ * X)]
    [Invertible (clsConstraintGram X R)] :
    (clsProjectionMatrix X R).rank = Fintype.card n - Fintype.card k + Fintype.card q := by
  have hbase : (clsProjectionMatrix X R).rank =
      Fintype.card n + Fintype.card q - Fintype.card k :=
    Nat.eq_sub_of_add_eq (clsProjectionMatrix_rank_add X R)
  have hkn : Fintype.card k ≤ Fintype.card n := by
    have hle := Matrix.rank_le_card_height (hatMatrix X)
    simpa [rank_hatMatrix X] using hle
  omega

omit [DecidableEq n] in
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
/-- Hansen Theorem 8.2 conditional unbiasedness from coordinatewise mean-zero errors. -/
theorem cls_condExp_unbiased_of_error_zero
    {Ω : Type*} {m m₀ : MeasurableSpace Ω} {μ : Measure Ω}
    (X : Matrix n k ℝ) (β : k → ℝ) (e : Ω → n → ℝ) (R : Matrix k q ℝ) (c : q → ℝ)
    [Invertible (Xᵀ * X)] [Invertible (clsConstraintGram X R)] [IsProbabilityMeasure μ]
    (hrestrict : Rᵀ *ᵥ β = c)
    (hm : m ≤ m₀) [SigmaFinite (μ.trim hm)]
    (he_int : ∀ i, Integrable (fun ω => e ω i) μ)
    (hmean : ∀ i, μ[fun ω => e ω i | m] =ᵐ[μ] fun _ => 0) :
    μ[(fun ω => clsBeta X (X *ᵥ β + e ω) R c) | m] =ᵐ[μ] fun _ => β := by
  let B : Matrix k n ℝ := ⅟(Xᵀ * X) * Xᵀ - clsCorrectionMatrix X R * Xᵀ
  let f : Ω → k → ℝ := fun ω => β + B *ᵥ e ω
  have hf_int : Integrable f μ := by
    refine Integrable.of_eval ?_
    intro j
    have hrepr : (fun ω => f ω j) = fun ω => β j + ∑ i, B j i * e ω i := by
      funext ω
      simp [f, B, Matrix.mulVec, dotProduct]
    rw [hrepr]
    have hsum_int : Integrable (fun ω => ∑ i, B j i * e ω i) μ := by
      simpa using MeasureTheory.integrable_finset_sum (s := Finset.univ)
        (f := fun i ω => B j i * e ω i)
        (fun i _ => (he_int i).const_mul (B j i))
    exact (integrable_const (β j)).add hsum_int
  have hcoord : ∀ j : k, μ[(fun ω => f ω j) | m] =ᵐ[μ] fun _ => β j := by
    intro j
    have hrepr : (fun ω => f ω j) = fun ω => β j + ∑ i, B j i * e ω i := by
      funext ω
      simp [f, B, Matrix.mulVec, dotProduct]
    rw [hrepr]
    have hsum_int : Integrable (fun ω => ∑ i, B j i * e ω i) μ := by
      simpa using MeasureTheory.integrable_finset_sum (s := Finset.univ)
        (f := fun i ω => B j i * e ω i)
        (fun i _ => (he_int i).const_mul (B j i))
    have hconst : μ[(fun _ : Ω => β j) | m] = fun _ => β j := by
      simpa using MeasureTheory.condExp_const (μ := μ) (m := m) (m₀ := m₀) hm (β j)
    have hsum_repr : (fun ω => ∑ i, B j i * e ω i) = ∑ i, fun ω => B j i * e ω i := by
      funext ω
      simp
    have hsum_ce : μ[(fun ω => ∑ i, B j i * e ω i) | m] =ᵐ[μ]
        ∑ i, μ[(fun ω => B j i * e ω i) | m] := by
      rw [hsum_repr]
      simpa using MeasureTheory.condExp_finset_sum (μ := μ) (m := m)
        (s := Finset.univ) (f := fun i ω => B j i * e ω i)
        (fun i _ => (he_int i).const_mul (B j i))
    have hsum_smul : (∑ i, μ[(fun ω => B j i * e ω i) | m]) =ᵐ[μ]
        ∑ i, (fun ω => B j i * μ[fun ω => e ω i | m] ω) := by
      classical
      refine Finset.induction_on (Finset.univ : Finset n) ?_ ?_
      · simp
      · intro a s ha ih
        have ha' : μ[(fun ω => B j a * e ω a) | m] =ᵐ[μ]
            fun ω => B j a * μ[fun ω => e ω a | m] ω := by
          simpa [Pi.smul_apply, smul_eq_mul] using
            (MeasureTheory.condExp_smul (μ := μ) (m := m) (B j a) (fun ω => e ω a))
        simpa [Finset.sum_insert, ha] using ha'.add ih
    have hsum_zero : (∑ i, (fun ω => B j i * μ[fun ω => e ω i | m] ω)) =ᵐ[μ] 0 := by
      classical
      refine Finset.induction_on (Finset.univ : Finset n) ?_ ?_
      · simp
      · intro a s ha ih
        have hzeroa : (fun ω => B j a * μ[fun ω => e ω a | m] ω) =ᵐ[μ] 0 := by
          filter_upwards [hmean a] with ω hω
          simp [hω]
        simpa [Finset.sum_insert, ha] using hzeroa.add ih
    have hsum_final : μ[(fun ω => ∑ i, B j i * e ω i) | m] =ᵐ[μ] 0 :=
      hsum_ce.trans (hsum_smul.trans hsum_zero)
    calc
      μ[(fun ω => β j + ∑ i, B j i * e ω i) | m]
          =ᵐ[μ] μ[(fun _ : Ω => β j) | m] +
              μ[(fun ω => ∑ i, B j i * e ω i) | m] := by
            simpa using MeasureTheory.condExp_add (μ := μ) (m := m)
              (integrable_const (β j)) hsum_int
      _ =ᵐ[μ] (fun _ => β j) + 0 := by
            rw [hconst]
            exact Filter.EventuallyEq.add Filter.EventuallyEq.rfl hsum_final
      _ =ᵐ[μ] fun _ => β j := by simp
  have hmean_vec : μ[f | m] =ᵐ[μ] fun _ => β := by
    rw [Filter.EventuallyEq]
    change ∀ᵐ ω ∂μ, μ[f | m] ω = β
    have hcoord' : ∀ j : k, ∀ᵐ ω ∂μ, μ[f | m] ω j = β j := by
      intro j
      exact (condExp_apply (m := m) (μ := μ) (f := f) hf_int j).trans (hcoord j)
    have hall : ∀ᵐ ω ∂μ, ∀ j : k, μ[f | m] ω j = β j := ae_all_iff.2 hcoord'
    exact hall.mono fun ω hω => by
      funext j
      exact hω j
  have hfun : (fun ω => clsBeta X (X *ᵥ β + e ω) R c) = f := by
    funext ω
    exact clsBeta_linear_model X β (e ω) R c hrestrict
  simpa [hfun, f, B] using hmean_vec

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

/-- Hansen Theorem 8.3: composed homoskedastic CLS covariance formula. -/
theorem cls_conditionalVariance_homoskedastic_composed
    (X : Matrix n k ℝ) (R : Matrix k q ℝ) (σ2 : ℝ)
    [Invertible (Xᵀ * X)] [Invertible (clsConstraintGram X R)] :
    clsConditionalVarianceMatrix X R (σ2 • (1 : Matrix n n ℝ)) =
      clsHomoskedasticVarianceMatrix X R σ2 :=
  cls_conditionalVariance_homoskedastic X R σ2 (cls_sandwichCore_eq X R)

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

/-- Hansen Theorem 8.4 residual-variance conditional expectation from homoskedastic second
moments. The explicit degrees-of-freedom nonzero assumption is needed because
`clsResidualVariance` uses a totalized inverse. -/
theorem cls_residualVariance_condExp_eq_sigmaSq_of_homoskedastic
    {Ω : Type*} {m m₀ : MeasurableSpace Ω} {μ : Measure Ω}
    (X : Matrix n k ℝ) (β : k → ℝ) (e : Ω → n → ℝ) (R : Matrix k q ℝ) (c : q → ℝ)
    (σ2 : ℝ) [Invertible (Xᵀ * X)] [Invertible (clsConstraintGram X R)]
    [IsProbabilityMeasure μ]
    (hrestrict : Rᵀ *ᵥ β = c)
    (hm : m ≤ m₀) [SigmaFinite (μ.trim hm)]
    (hee_int : ∀ i j, Integrable (fun ω => e ω i * e ω j) μ)
    (hhomo : ∀ i j,
      μ[fun ω => e ω i * e ω j | m] =ᵐ[μ]
        fun _ => σ2 * (1 : Matrix n n ℝ) i j)
    (hdf : ((Fintype.card n : ℝ) - Fintype.card k + Fintype.card q) ≠ 0) :
    μ[(fun ω => clsResidualVariance X (X *ᵥ β + e ω) R c) | m] =ᵐ[μ] fun _ => σ2 := by
  let P : Matrix n n ℝ := clsProjectionMatrix X R
  let df : ℝ := (Fintype.card n : ℝ) - Fintype.card k + Fintype.card q
  have hquad_repr :
      (fun ω => dotProduct (P *ᵥ e ω) (P *ᵥ e ω)) =
        fun ω => e ω ⬝ᵥ P *ᵥ e ω := by
    funext ω
    calc
      dotProduct (P *ᵥ e ω) (P *ᵥ e ω) = (P *ᵥ e ω) ᵥ* P ⬝ᵥ e ω := by
        rw [Matrix.dotProduct_mulVec]
      _ = e ω ᵥ* (Pᵀ * P) ⬝ᵥ e ω := by
        rw [Matrix.vecMul_mulVec]
      _ = e ω ᵥ* P ⬝ᵥ e ω := by
        rw [show Pᵀ = P by simp [P, clsProjectionMatrix_transpose],
          show P * P = P by simp [P, clsProjectionMatrix_idempotent]]
      _ = e ω ⬝ᵥ P *ᵥ e ω := by
        rw [← Matrix.dotProduct_mulVec]
  have hquad := condExp_quadratic_form_eq_sum (μ := μ) (m := m) (m₀ := m₀)
    P e (σ2 • (1 : Matrix n n ℝ)) hm hee_int (by
      intro i j
      simpa using hhomo i j)
  have hsum : (∑ i, ∑ j, P i j * (σ2 • (1 : Matrix n n ℝ)) i j) = σ2 * df := by
    calc
      (∑ i, ∑ j, P i j * (σ2 • (1 : Matrix n n ℝ)) i j) =
          ∑ i, ∑ j, P i j * (σ2 * (1 : Matrix n n ℝ) i j) := by
        simp
      _ = σ2 * Matrix.trace P := sum_quadratic_homoskedastic_eq_trace P σ2
      _ = σ2 * df := by
        simp [P, df, clsProjectionMatrix_trace]
  have hscaled : μ[(fun ω => df⁻¹ * (e ω ⬝ᵥ P *ᵥ e ω)) | m] =ᵐ[μ] fun _ => σ2 := by
    calc
      μ[(fun ω => df⁻¹ * (e ω ⬝ᵥ P *ᵥ e ω)) | m]
          =ᵐ[μ] df⁻¹ • μ[(fun ω => e ω ⬝ᵥ P *ᵥ e ω) | m] := by
            simpa [smul_eq_mul] using MeasureTheory.condExp_smul (μ := μ) (m := m)
              df⁻¹ (fun ω => e ω ⬝ᵥ P *ᵥ e ω)
      _ =ᵐ[μ] fun _ : Ω => df⁻¹ *
          (∑ i, ∑ j, P i j * (σ2 • (1 : Matrix n n ℝ)) i j) := by
            filter_upwards [hquad] with ω hω
            simp [Pi.smul_apply, smul_eq_mul, hω]
      _ =ᵐ[μ] fun _ : Ω => df⁻¹ * (σ2 * df) := by
            rw [hsum]
      _ =ᵐ[μ] fun _ : Ω => σ2 := by
            filter_upwards [] with ω
            field_simp [df, hdf]
  have hmean : μ[(fun ω => df⁻¹ * dotProduct (P *ᵥ e ω) (P *ᵥ e ω)) | m]
      =ᵐ[μ] fun _ => σ2 := by
    have hscaled_input :
        (fun ω => df⁻¹ * dotProduct (P *ᵥ e ω) (P *ᵥ e ω)) =
          fun ω => df⁻¹ * (e ω ⬝ᵥ P *ᵥ e ω) := by
      funext ω
      rw [congrFun hquad_repr ω]
    rw [hscaled_input]
    exact hscaled
  have hfun : (fun ω => clsResidualVariance X (X *ᵥ β + e ω) R c) =
      fun ω => df⁻¹ * dotProduct (P *ᵥ e ω) (P *ᵥ e ω) := by
    funext ω
    unfold clsResidualVariance
    rw [clsResidual_linear_model X β (e ω) R c hrestrict]
  simpa [hfun] using hmean

omit [DecidableEq n] in
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

omit [DecidableEq n] in
/-- If the error vector has a Gaussian law, then the CLS coefficient vector is Gaussian as an
affine image of the error vector. -/
theorem clsBeta_hasGaussianLaw_of_gaussian_error
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (X : Matrix n k ℝ) (β : k → ℝ) (e : Ω → n → ℝ) (R : Matrix k q ℝ) (c : q → ℝ)
    [Invertible (Xᵀ * X)] [Invertible (clsConstraintGram X R)]
    (hrestrict : Rᵀ *ᵥ β = c)
    (he : HasGaussianLaw e μ) :
    HasGaussianLaw (fun ω => clsBeta X (X *ᵥ β + e ω) R c) μ := by
  classical
  let B : Matrix k n ℝ := ⅟(Xᵀ * X) * Xᵀ - clsCorrectionMatrix X R * Xᵀ
  let L : (n → ℝ) →L[ℝ] (k → ℝ) := (Matrix.toLin' B).toContinuousLinearMap
  have hLin : HasGaussianLaw (fun ω => L (e ω)) μ := he.map_fun L
  have hAff : HasGaussianLaw (fun ω => β + L (e ω)) μ := by
    refine ⟨?_⟩
    have hmap : (μ.map fun ω => L (e ω)).map (fun x => β + x) =
        μ.map (fun ω => β + L (e ω)) := by
      simpa using
        (AEMeasurable.map_map_of_aemeasurable
          (μ := μ)
          (f := fun ω => L (e ω))
          (g := fun x => β + x)
          (Measurable.aemeasurable <| by fun_prop)
          hLin.aemeasurable)
    rw [← hmap]
    letI : IsGaussian (μ.map fun ω => L (e ω)) := hLin.isGaussian_map
    infer_instance
  exact clsBeta_hasGaussianLaw_of_error X β e R c hrestrict (by
    refine hAff.congr ?_
    filter_upwards with ω
    simp [L, B, Matrix.sub_mulVec])

/-- Scaled CLS residual-variance statistic. -/
noncomputable def scaledClsResidualVarianceStatistic
    {Ω : Type*} (X : Matrix n k ℝ) (β : k → ℝ) (σ2 : ℝ) (R : Matrix k q ℝ) (c : q → ℝ)
    [Invertible (Xᵀ * X)] [Invertible (clsConstraintGram X R)] (e : Ω → n → ℝ) : Ω → ℝ :=
  fun ω =>
    (((Fintype.card n : ℝ) - Fintype.card k + Fintype.card q) *
      clsResidualVariance X (X *ᵥ β + e ω) R c) / σ2

set_option maxHeartbeats 800000 in
-- The deterministic normalization and eigenspace rewrite expand several large `let`-bound terms.
/-- The scaled CLS residual statistic is the sum of squared standardized Gaussian coordinates on
 the `1`-eigenspace of the CLS residual-maker. This is the deterministic bridge for Hansen
Theorem 8.5. -/
theorem scaledClsResVarStat_eq_sum_sq_eigenvector_coords
    {Ω : Type*} [MeasurableSpace Ω]
    (X : Matrix n k ℝ) (β : k → ℝ) {σ2 : ℝ} (hσ2 : 0 < σ2)
    (R : Matrix k q ℝ) (c : q → ℝ)
    [Invertible (Xᵀ * X)] [Invertible (clsConstraintGram X R)]
    (hrestrict : Rᵀ *ᵥ β = c) (hdf : Fintype.card k < Fintype.card n + Fintype.card q)
    (ε : Ω → EuclideanSpace ℝ n) :
    let P := clsProjectionMatrix X R
    let hP : P.IsHermitian := clsProjectionMatrix_isHermitian X R
    let b : OrthonormalBasis n ℝ (EuclideanSpace ℝ n) := hP.eigenvectorBasis
    scaledClsResidualVarianceStatistic X β σ2 R c (WithLp.ofLp ∘ ε) =
      sumSquaresRV
        (restrictedStandardizedCoords b
          (fun i : {j : n // hP.eigenvalues j = 1} => i.1) σ2 ε) := by
  classical
  let P : Matrix n n ℝ := clsProjectionMatrix X R
  let hP : P.IsHermitian := clsProjectionMatrix_isHermitian X R
  let b : OrthonormalBasis n ℝ (EuclideanSpace ℝ n) := hP.eigenvectorBasis
  funext ω
  let df : ℝ := (Fintype.card n : ℝ) - Fintype.card k + Fintype.card q
  let e : n → ℝ := WithLp.ofLp (ε ω)
  have hneq_df : df ≠ 0 := by
    dsimp [df]
    have hne : ((Fintype.card n + Fintype.card q : ℝ) - Fintype.card k) ≠ 0 := by
      exact sub_ne_zero.mpr (by exact_mod_cast (Nat.ne_of_gt hdf))
    have hrewrite :
        ((Fintype.card n : ℝ) - Fintype.card k + Fintype.card q) =
          (Fintype.card n + Fintype.card q : ℝ) - Fintype.card k := by
      ring
    rwa [hrewrite]
  have hquad :
      e ⬝ᵥ P *ᵥ e = ∑ i : {j : n // hP.eigenvalues j = 1}, (b.repr (ε ω) i.1)^2 := by
    simpa [P, hP, b, e] using
      isHermitian_idempotent_quadratic_form_eq_sum_sq_eigenvector_coords hP
        (clsProjectionMatrix_idempotent X R) e
  have hdot : dotProduct (P *ᵥ e) (P *ᵥ e) = e ⬝ᵥ P *ᵥ e := by
    have hPt : Pᵀ = P := by simp [P, clsProjectionMatrix_transpose]
    exact (quadratic_form_eq_dotProduct_of_symm_idempotent P hPt
      (clsProjectionMatrix_idempotent X R) e).symm
  have hscaled :
      scaledClsResidualVarianceStatistic X β σ2 R c (WithLp.ofLp ∘ ε) ω =
        (df * (df⁻¹ * dotProduct (P *ᵥ e) (P *ᵥ e))) / σ2 := by
    simp [scaledClsResidualVarianceStatistic, clsResidualVariance, df, e, P,
      clsResidual_linear_model X β e R c hrestrict]
  have hcancel : df * (df⁻¹ * dotProduct (P *ᵥ e) (P *ᵥ e)) =
      dotProduct (P *ᵥ e) (P *ᵥ e) := by
    field_simp [hneq_df]
  calc
    scaledClsResidualVarianceStatistic X β σ2 R c (WithLp.ofLp ∘ ε) ω
        = (df * (df⁻¹ * dotProduct (P *ᵥ e) (P *ᵥ e))) / σ2 := hscaled
    _ = dotProduct (P *ᵥ e) (P *ᵥ e) / σ2 := by rw [hcancel]
    _ = (e ⬝ᵥ P *ᵥ e) / σ2 := by rw [hdot]
    _ = (∑ i : {j : n // hP.eigenvalues j = 1}, (b.repr (ε ω) i.1)^2) / σ2 := by
          rw [hquad]
    _ = ∑ i : {j : n // hP.eigenvalues j = 1},
          ((b.repr (ε ω) i.1) / Real.sqrt σ2)^2 := by
          rw [Finset.sum_div]
          refine Finset.sum_congr rfl ?_
          intro i hi
          field_simp [Real.sq_sqrt hσ2.le, hσ2.ne']
          rw [Real.sq_sqrt hσ2.le]
    _ = sumSquaresRV
          (restrictedStandardizedCoords b
            (fun i : {j : n // hP.eigenvalues j = 1} => i.1) σ2 ε) ω := by
          simp [sumSquaresRV, restrictedStandardizedCoords, standardizedCoords]

/-- Hansen Theorem 8.5, chi-square component: under homoskedastic Gaussian structural errors,
the scaled CLS residual variance statistic has a chi-square law with `n - k + q` degrees of
freedom. -/
theorem scaledClsResidualVarianceStatistic_hasLaw_chiSquared
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (X : Matrix n k ℝ) (β : k → ℝ) {σ2 : ℝ} (hσ2 : 0 < σ2)
    (R : Matrix k q ℝ) (c : q → ℝ)
    [Invertible (Xᵀ * X)] [Invertible (clsConstraintGram X R)]
    (hrestrict : Rᵀ *ᵥ β = c) (hdf : Fintype.card k < Fintype.card n + Fintype.card q)
    (ε : Ω → EuclideanSpace ℝ n)
    (hε : HasLaw ε (multivariateGaussian 0 ((σ2 : ℝ) • (1 : Matrix n n ℝ))) μ) :
    HasLaw (scaledClsResidualVarianceStatistic X β σ2 R c (WithLp.ofLp ∘ ε))
      (chiSquared (Fintype.card n - Fintype.card k + Fintype.card q)) μ := by
  classical
  let P : Matrix n n ℝ := clsProjectionMatrix X R
  let hP : P.IsHermitian := clsProjectionMatrix_isHermitian X R
  let W : {j : n // hP.eigenvalues j = 1} → Ω → ℝ :=
    restrictedStandardizedCoords hP.eigenvectorBasis
      (fun i : {j : n // hP.eigenvalues j = 1} => i.1) σ2 ε
  have hRankEqCard :
      P.rank = Fintype.card {j : n // hP.eigenvalues j = 1} := by
    simpa [P, hP] using rank_eq_card_eigenvalues_eq_one_of_isHermitian_idempotent hP
      (clsProjectionMatrix_idempotent X R)
  have hkn : Fintype.card k ≤ Fintype.card n := by
    have hle := Matrix.rank_le_card_height (hatMatrix X)
    simpa [rank_hatMatrix X] using hle
  have hCardPos : 0 < Fintype.card {j : n // hP.eigenvalues j = 1} := by
    rw [← hRankEqCard]
    change 0 < (clsProjectionMatrix X R).rank
    rw [clsProjectionMatrix_rank X R]
    omega
  have hcoords := orthonormalBasis_coords_div_sqrt_iIndep_standardGaussian
    (b := hP.eigenvectorBasis) hσ2 ε hε
  have hLawW : ∀ i, HasLaw (W i) (gaussianReal 0 1) μ := by
    intro i
    simpa [W, restrictedStandardizedCoords, standardizedCoords] using hcoords.1 i.1
  have hIndepW : ProbabilityTheory.iIndepFun W μ := by
    simpa [W, restrictedStandardizedCoords, standardizedCoords] using
      hcoords.2.precomp Subtype.val_injective
  letI : MeasureSpace Ω := ⟨μ⟩
  have hLawSumSq : HasLaw (sumSquaresRV W)
      (chiSquared (Fintype.card {j : n // hP.eigenvalues j = 1})) μ := by
    simpa [W, sumSquaresRV] using hasLaw_sum_sq_chiSquared_fintype hCardPos hLawW hIndepW
  have hEq := scaledClsResVarStat_eq_sum_sq_eigenvector_coords X β hσ2 R c hrestrict hdf ε
  convert hLawSumSq.congr ?_ using 1
  · rw [← hRankEqCard]
    change chiSquared (Fintype.card n - Fintype.card k + Fintype.card q) =
      chiSquared (clsProjectionMatrix X R).rank
    rw [clsProjectionMatrix_rank X R]
  · simp [W]

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

/-- Hansen Theorem 8.5 exact finite-sample normal-regression laws for CLS.

This is a result package, not an assumption interface: constructors below prove its fields from
Gaussian-error and independence inputs. -/
structure ClsNormalRegressionFiniteSampleLaws
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : Matrix n k ℝ) (β : k → ℝ) (σ2 : ℝ) (R : Matrix k q ℝ) (c : q → ℝ)
    [Invertible (Xᵀ * X)] [Invertible (clsConstraintGram X R)]
    (ε : Ω → EuclideanSpace ℝ n) (Z : Ω → ℝ) where
  beta_gaussian :
    HasGaussianLaw
      (fun ω => clsBeta X (X *ᵥ β + WithLp.ofLp (ε ω)) R c) μ
  scaled_residual_variance_chiSquared :
    HasLaw
      (scaledClsResidualVarianceStatistic X β σ2 R c (WithLp.ofLp ∘ ε))
      (chiSquared (Fintype.card n - Fintype.card k + Fintype.card q)) μ
  t_student :
    HasLaw
      (fun ω => clsTStatFromComponents (Z ω)
        (scaledClsResidualVarianceStatistic X β σ2 R c (WithLp.ofLp ∘ ε) ω)
        (Fintype.card n - Fintype.card k + Fintype.card q))
      (studentT (Fintype.card n - Fintype.card k + Fintype.card q)) μ

/-- Hansen Theorem 8.5: exact finite-sample Gaussian, chi-square, and Student-t laws for CLS. -/
theorem clsNormalRegressionFiniteSampleLaws
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (X : Matrix n k ℝ) (β : k → ℝ) {σ2 : ℝ} (hσ2 : 0 < σ2)
    (R : Matrix k q ℝ) (c : q → ℝ)
    [Invertible (Xᵀ * X)] [Invertible (clsConstraintGram X R)]
    (hrestrict : Rᵀ *ᵥ β = c) (hdf : Fintype.card k < Fintype.card n + Fintype.card q)
    (ε : Ω → EuclideanSpace ℝ n)
    (hε : HasLaw ε (multivariateGaussian 0 ((σ2 : ℝ) • (1 : Matrix n n ℝ))) μ)
    (he : HasGaussianLaw (WithLp.ofLp ∘ ε : Ω → n → ℝ) μ)
    (Z : Ω → ℝ) (hZ : HasLaw Z (gaussianReal 0 1) μ)
    (hInd : Z ⟂ᵢ[μ] scaledClsResidualVarianceStatistic X β σ2 R c (WithLp.ofLp ∘ ε)) :
    ClsNormalRegressionFiniteSampleLaws μ X β σ2 R c ε Z := by
  have hBeta :
      HasGaussianLaw
        (fun ω => clsBeta X (X *ᵥ β + WithLp.ofLp (ε ω)) R c) μ := by
    simpa [Function.comp_def] using
      clsBeta_hasGaussianLaw_of_gaussian_error X β (WithLp.ofLp ∘ ε) R c hrestrict he
  have hQ :
      HasLaw
        (scaledClsResidualVarianceStatistic X β σ2 R c (WithLp.ofLp ∘ ε))
        (chiSquared (Fintype.card n - Fintype.card k + Fintype.card q)) μ :=
    scaledClsResidualVarianceStatistic_hasLaw_chiSquared X β hσ2 R c hrestrict hdf ε hε
  have hν : 0 < Fintype.card n - Fintype.card k + Fintype.card q := by
    omega
  exact
    { beta_gaussian := hBeta
      scaled_residual_variance_chiSquared := hQ
      t_student :=
        clsTStat_hasStudentTLaw Z
          (scaledClsResidualVarianceStatistic X β σ2 R c (WithLp.ofLp ∘ ε))
          (Fintype.card n - Fintype.card k + Fintype.card q) hν hZ hQ hInd }

end HansenEconometrics
