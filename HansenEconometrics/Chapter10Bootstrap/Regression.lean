import HansenEconometrics.Chapter8Asymptotics
import HansenEconometrics.Chapter10Bootstrap.Covariance
import HansenEconometrics.Chapter10Bootstrap.Studentization

/-!
# Chapter 10 — Bootstrap regression

Finite-resample OLS score bootstrap statistics, linearized coefficient
statistics, and linear-restriction test statistics, with the finite OLS
bootstrap regression CLT wrappers (Hansen Theorem 10.18).
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology MeasureTheory ProbabilityTheory Matrix
open scoped Matrix.Norms.Elementwise Function

namespace HansenEconometrics

variable {Ω Ωs Ωlim E F k : Type*}
variable {mΩ : MeasurableSpace Ω} {mΩs : MeasurableSpace Ωs}
variable {mΩlim : MeasurableSpace Ωlim}
variable {μ : Measure Ω} {ν : Measure Ωlim}

section BootstrapRegression

theorem heteroAsymCov_posSemidef_of_scoreCLTConditions
    [IsProbabilityMeasure μ]
    {k : Type*} [Fintype k] [DecidableEq k]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ}
    (h : ScoreCLTConditions μ X e) :
    (heteroAsymCov μ X e).PosSemidef :=
  -- Reuse Chapter 8's canonical OLS sandwich PosSemidef result rather than
  -- re-proving it (the inline proof was byte-for-byte identical).
  heteroAsymCov_posSemidef h

/-- Ordinary finite-resample regression score bootstrap statistic.

For a sample path `ω` and resampling map `ωs : Fin (n+1) → Fin (n+1)`, this is
`sqrt(n+1)` times the centered nonparametric bootstrap mean of the score vectors
`e_i X_i`, represented as a Euclidean vector. -/
noncomputable def regressionBootstrapScoreFinSucc
    {k : Type*} [Fintype k]
    (X : ℕ → Ω → (k → ℝ)) (e : ℕ → Ω → ℝ)
    (n : ℕ) (ω : Ω) (ωs : Fin (n + 1) → Fin (n + 1)) :
    EuclideanSpace ℝ k :=
  WithLp.toLp 2
    (fun a =>
      Real.sqrt (n + 1 : ℝ) *
        (empiricalBootstrapResampleMean
            (fun i : Fin (n + 1) => e i.val ω • X i.val ω)
            (fun ωs t => ωs t) ωs a -
          empiricalMean
            (fun i : Fin (n + 1) => e i.val ω • X i.val ω) a))

/-- Ordinary finite-resample linearized regression coefficient bootstrap
statistic.

This applies the population Gram inverse to
`regressionBootstrapScoreFinSucc`; it is the linearized coefficient statistic
used in Hansen Theorem 10.18 before the nonlinear OLS inversion remainder is
controlled. -/
noncomputable def regressionLinearizedScoreFinSucc
    {k : Type*} [Fintype k] [DecidableEq k]
    (μ : Measure Ω) (X : ℕ → Ω → (k → ℝ)) (e : ℕ → Ω → ℝ)
    (n : ℕ) (ω : Ω) (ωs : Fin (n + 1) → Fin (n + 1)) :
    EuclideanSpace ℝ k :=
  matrixContinuousLinearMap ((popGram μ X)⁻¹)
    (regressionBootstrapScoreFinSucc (Ω := Ω) X e n ω ωs)

/-- Ordinary finite-resample bootstrap regression design matrix.

For a fixed sample path `ω` and resampling map
`ωs : Fin (n+1) → Fin (n+1)`, this stacks the resampled regressors
`X_{ωs(t)}` into the bootstrap design matrix. -/
def regressionBootstrapRegressorsFinSucc
    {k : Type*}
    (X : ℕ → Ω → (k → ℝ))
    (n : ℕ) (ω : Ω) (ωs : Fin (n + 1) → Fin (n + 1)) :
    Matrix (Fin (n + 1)) k ℝ :=
  Matrix.of fun i j => X (ωs i).val ω j

/-- Ordinary finite-resample bootstrap regression outcome vector. -/
def regressionBootstrapOutcomesFinSucc
    (y : ℕ → Ω → ℝ)
    (n : ℕ) (ω : Ω) (ωs : Fin (n + 1) → Fin (n + 1)) :
    Fin (n + 1) → ℝ :=
  fun i => y (ωs i).val ω

/-- Ordinary finite-resample bootstrap structural-error vector. -/
def regressionBootstrapErrorsFinSucc
    (e : ℕ → Ω → ℝ)
    (n : ℕ) (ω : Ω) (ωs : Fin (n + 1) → Fin (n + 1)) :
    Fin (n + 1) → ℝ :=
  fun i => e (ωs i).val ω

omit [MeasurableSpace Ω] in
/-- A pointwise linear model remains linear after ordinary finite resampling. -/
theorem regressionBootstrapOutcomesFinSucc_linear_model
    {k : Type*} [Fintype k]
    (X : ℕ → Ω → (k → ℝ)) (e : ℕ → Ω → ℝ) (y : ℕ → Ω → ℝ)
    (β : k → ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (n : ℕ) (ω : Ω) (ωs : Fin (n + 1) → Fin (n + 1)) :
    regressionBootstrapOutcomesFinSucc y n ω ωs =
      regressionBootstrapRegressorsFinSucc X n ω ωs *ᵥ β +
        regressionBootstrapErrorsFinSucc e n ω ωs := by
  funext i
  simp [regressionBootstrapOutcomesFinSucc, regressionBootstrapRegressorsFinSucc,
    regressionBootstrapErrorsFinSucc, Matrix.mulVec, Matrix.of_apply, dotProduct,
    hmodel (ωs i).val ω]

omit [MeasurableSpace Ω] in
/-- The resampled score cross moment is the bootstrap resample mean of
`e_i X_i`. -/
private theorem regressionBootstrap_sampleCrossMoment_errors_finSucc_eq_resampleMean
    {k : Type*} [Fintype k]
    (X : ℕ → Ω → (k → ℝ)) (e : ℕ → Ω → ℝ)
    (n : ℕ) (ω : Ω) (ωs : Fin (n + 1) → Fin (n + 1)) :
    sampleCrossMoment (regressionBootstrapRegressorsFinSucc X n ω ωs)
        (regressionBootstrapErrorsFinSucc e n ω ωs) =
      empiricalBootstrapResampleMean
        (fun i : Fin (n + 1) => e i.val ω • X i.val ω)
        (fun ωs t => ωs t) ωs := by
  funext a
  simp [sampleCrossMoment, regressionBootstrapRegressorsFinSucc,
    regressionBootstrapErrorsFinSucc, empiricalBootstrapResampleMean,
    Matrix.mulVec, dotProduct, smul_eq_mul, mul_comm]

omit [MeasurableSpace Ω] in
/-- The original-sample score cross moment is the empirical mean of `e_i X_i`. -/
private theorem sampleCrossMoment_stackRegressors_stackErrors_finSucc_eq_empiricalMean
    {k : Type*} [Fintype k]
    (X : ℕ → Ω → (k → ℝ)) (e : ℕ → Ω → ℝ)
    (n : ℕ) (ω : Ω) :
  sampleCrossMoment (stackRegressors X (n + 1) ω) (stackErrors e (n + 1) ω) =
      empiricalMean (fun i : Fin (n + 1) => e i.val ω • X i.val ω) := by
  rw [sampleCrossMoment_stackRegressors_stackErrors_eq_avg]
  simp only [empiricalMean, Fintype.card_fin, ENNReal.toReal_inv, sum_fin_eq_sum_range_smul]
  have htoReal : ((n : ℝ≥0∞) + 1).toReal = (n : ℝ) + 1 := by
    rw [ENNReal.toReal_add (by simp) (by simp)]
    simp [ENNReal.toReal_natCast]
  simp [htoReal, Nat.cast_add, Nat.cast_one]

omit [MeasurableSpace Ω] in
/-- The ordinary finite-resample score statistic is exactly the centered
resampled score cross moment, scaled by `sqrt(n+1)`. -/
private theorem regressionBootstrapScoreFinSucc_eq_sqrt_smul_sampleCrossMoment_sub
    {k : Type*} [Fintype k]
    (X : ℕ → Ω → (k → ℝ)) (e : ℕ → Ω → ℝ)
    (n : ℕ) (ω : Ω) (ωs : Fin (n + 1) → Fin (n + 1)) :
    regressionBootstrapScoreFinSucc (Ω := Ω) X e n ω ωs =
      WithLp.toLp 2
        (Real.sqrt (n + 1 : ℝ) •
          (sampleCrossMoment (regressionBootstrapRegressorsFinSucc X n ω ωs)
              (regressionBootstrapErrorsFinSucc e n ω ωs) -
            sampleCrossMoment (stackRegressors X (n + 1) ω)
              (stackErrors e (n + 1) ω))) := by
  rw [regressionBootstrap_sampleCrossMoment_errors_finSucc_eq_resampleMean,
    sampleCrossMoment_stackRegressors_stackErrors_finSucc_eq_empiricalMean]
  change WithLp.toLp 2
      (fun a =>
        Real.sqrt (n + 1 : ℝ) *
          (empiricalBootstrapResampleMean
              (fun i : Fin (n + 1) => e i.val ω • X i.val ω)
              (fun ωs t => ωs t) ωs a -
            empiricalMean
              (fun i : Fin (n + 1) => e i.val ω • X i.val ω) a)) =
    WithLp.toLp 2
      (Real.sqrt (n + 1 : ℝ) •
        (empiricalBootstrapResampleMean
            (fun i : Fin (n + 1) => e i.val ω • X i.val ω)
            (fun ωs t => ωs t) ωs -
          empiricalMean
            (fun i : Fin (n + 1) => e i.val ω • X i.val ω)))
  apply congrArg (WithLp.toLp 2)
  funext a
  simp [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]

/-- Ordinary finite-resample bootstrap OLS coefficient, totalized by
`olsBetaOrZero`. -/
noncomputable def regressionBootstrapBetaFinSucc
    {k : Type*} [Fintype k] [DecidableEq k]
    (X : ℕ → Ω → (k → ℝ)) (y : ℕ → Ω → ℝ)
    (n : ℕ) (ω : Ω) (ωs : Fin (n + 1) → Fin (n + 1)) :
    k → ℝ :=
  olsBetaOrZero (regressionBootstrapRegressorsFinSucc X n ω ωs)
    (regressionBootstrapOutcomesFinSucc y n ω ωs)

/-- Hansen Theorem 10.18 concrete ordinary-bootstrap coefficient statistic:
`sqrt(n+1) (β̂* - β̂)`, using the project-wide `olsBetaOrZero`
totalization for both the resampled and original sample coefficients. -/
noncomputable def regressionBootstrapBetaStatisticFinSucc
    {k : Type*} [Fintype k] [DecidableEq k]
    (X : ℕ → Ω → (k → ℝ)) (y : ℕ → Ω → ℝ)
    (n : ℕ) (ω : Ω) (ωs : Fin (n + 1) → Fin (n + 1)) :
    EuclideanSpace ℝ k :=
  WithLp.toLp 2
    (Real.sqrt (n + 1 : ℝ) •
      (regressionBootstrapBetaFinSucc X y n ω ωs -
        olsBetaOrZero (stackRegressors X (n + 1) ω)
          (stackOutcomes y (n + 1) ω)))

/-- Transformed concrete ordinary-bootstrap regression statistic
`Rᵀ sqrt(n+1) (β̂* - β̂)`. -/
noncomputable def regressionBootstrapThetaStatisticFinSucc
    {k q : Type*} [Fintype k] [Fintype q] [DecidableEq k] [DecidableEq q]
    (R : Matrix k q ℝ) (X : ℕ → Ω → (k → ℝ)) (y : ℕ → Ω → ℝ)
    (n : ℕ) (ω : Ω) (ωs : Fin (n + 1) → Fin (n + 1)) :
    EuclideanSpace ℝ q :=
  matrixContinuousLinearMap Rᵀ
    (regressionBootstrapBetaStatisticFinSucc X y n ω ωs)

/-- Scalar ordinary-bootstrap linear-restriction numerator
`sqrt(n+1) (R βhat* - R βhat)` in the Chapter 7 one-row restriction
notation. -/
noncomputable def regressionBootstrapLinearRestrictionStatisticFinSucc
    {k : Type*} [Fintype k] [DecidableEq k]
    (R : Matrix Unit k ℝ) (X : ℕ → Ω → (k → ℝ)) (y : ℕ → Ω → ℝ)
    (n : ℕ) (ω : Ω) (ωs : Fin (n + 1) → Fin (n + 1)) : ℝ :=
  Real.sqrt (n + 1 : ℝ) *
    (linearRestrictionEstimate R (regressionBootstrapBetaFinSucc X y n ω ωs) -
      linearRestrictionEstimate R
        (olsBetaOrZero (stackRegressors X (n + 1) ω)
          (stackOutcomes y (n + 1) ω)))

omit [MeasurableSpace Ω] in
/-- The scalar ordinary-bootstrap restriction statistic is the `Unit`
coordinate of the transformed coefficient statistic. -/
private theorem regressionBootstrapLinearRestrictionStatisticFinSucc_eq_theta_apply
    {k : Type*} [Fintype k] [DecidableEq k]
    (R : Matrix Unit k ℝ) (X : ℕ → Ω → (k → ℝ)) (y : ℕ → Ω → ℝ)
    (n : ℕ) (ω : Ω) (ωs : Fin (n + 1) → Fin (n + 1)) :
    regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs =
      ((regressionBootstrapThetaStatisticFinSucc Rᵀ X y n ω ωs :
        EuclideanSpace ℝ Unit) : Unit → ℝ) () := by
  simp [regressionBootstrapLinearRestrictionStatisticFinSucc,
    regressionBootstrapThetaStatisticFinSucc, regressionBootstrapBetaStatisticFinSucc,
    linearRestrictionEstimate, matrixContinuousLinearMap_apply, smul_eq_mul,
    dotProduct]

omit [MeasurableSpace Ω] in
/-- The scalar ordinary-bootstrap restriction statistic is bounded by the
operator norm of the one-row restriction applied to the coefficient statistic.

This bridge turns bounded concrete coefficient-statistic paths into the
scalar numerator bound required by the bounded studentization and
critical-value wrappers. -/
private theorem regressionBootstrapLinearRestrictionStatisticFinSucc_abs_le_beta_norm
    {k : Type*} [Fintype k] [DecidableEq k]
    (R : Matrix Unit k ℝ) (X : ℕ → Ω → (k → ℝ)) (y : ℕ → Ω → ℝ)
    (n : ℕ) (ω : Ω) (ωs : Fin (n + 1) → Fin (n + 1)) :
    |regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs| ≤
      ‖PiLp.proj (p := (2 : ℝ≥0∞)) (𝕜 := ℝ)
          (β := fun _ : Unit => ℝ) ()‖ *
        (‖matrixContinuousLinearMap R‖ *
          ‖regressionBootstrapBetaStatisticFinSucc X y n ω ωs‖) := by
  rw [regressionBootstrapLinearRestrictionStatisticFinSucc_eq_theta_apply]
  simpa [regressionBootstrapThetaStatisticFinSucc] using
    abs_matrixContinuousLinearMap_coord_le_opNorm_mul_norm
      (G := R) () (regressionBootstrapBetaStatisticFinSucc X y n ω ωs)

omit [MeasurableSpace Ω] in
/-- Eventual boundedness of the concrete coefficient statistic supplies the
scalar numerator bound for the one-row ordinary-bootstrap restriction. -/
theorem regressionBootstrapLinearRestrictionStatisticFinSucc_eventually_abs_bound_of_beta_bound
    {k : Type*} [Fintype k] [DecidableEq k]
    {X : ℕ → Ω → (k → ℝ)} {y : ℕ → Ω → ℝ}
    (R : Matrix Unit k ℝ) {Cbeta : ℝ}
    (hBetaBound : ∀ᶠ n in atTop,
      ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
        ‖regressionBootstrapBetaStatisticFinSucc X y n ω ωs‖ ≤ Cbeta) :
    ∀ᶠ n in atTop,
      ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
        |regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs| ≤
          ‖PiLp.proj (p := (2 : ℝ≥0∞)) (𝕜 := ℝ)
              (β := fun _ : Unit => ℝ) ()‖ *
            (‖matrixContinuousLinearMap R‖ * Cbeta) := by
  filter_upwards [hBetaBound] with n hn
  intro ω ωs
  have hbase :=
    regressionBootstrapLinearRestrictionStatisticFinSucc_abs_le_beta_norm
      (R := R) (X := X) (y := y) n ω ωs
  have hlin :
      ‖matrixContinuousLinearMap R‖ *
          ‖regressionBootstrapBetaStatisticFinSucc X y n ω ωs‖ ≤
        ‖matrixContinuousLinearMap R‖ * Cbeta :=
    mul_le_mul_of_nonneg_left (hn ω ωs) (norm_nonneg _)
  exact hbase.trans
    (mul_le_mul_of_nonneg_left hlin (norm_nonneg _))

/-- Eventual boundedness of the linearized coefficient statistic supplies an
eventual bound after applying the transformed-regression linear map `Rᵀ`. -/
theorem regressionLinearizedScoreFinSucc_transformed_eventually_norm_bound_of_bound
    {k q : Type*} [Fintype k] [Fintype q] [DecidableEq k]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ}
    (R : Matrix k q ℝ) {Clin : ℝ}
    (hLinBound : ∀ᶠ n in atTop,
      ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
        ‖regressionLinearizedScoreFinSucc μ X e n ω ωs‖ ≤ Clin) :
    ∀ᶠ n in atTop,
      ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
        ‖matrixContinuousLinearMap Rᵀ
          (regressionLinearizedScoreFinSucc μ X e n ω ωs)‖ ≤
          ‖matrixContinuousLinearMap Rᵀ‖ * Clin := by
  filter_upwards [hLinBound] with n hn
  intro ω ωs
  have hbase :=
    (matrixContinuousLinearMap Rᵀ).le_opNorm
      (regressionLinearizedScoreFinSucc μ X e n ω ωs)
  exact hbase.trans
    (mul_le_mul_of_nonneg_left (hn ω ωs) (norm_nonneg _))

omit [MeasurableSpace Ω] in
/-- Eventual boundedness of the concrete coefficient statistic supplies an
eventual bound for the transformed ordinary-bootstrap statistic. -/
theorem regressionBootstrapThetaStatisticFinSucc_eventually_norm_bound_of_beta_bound
    {k q : Type*} [Fintype k] [Fintype q] [DecidableEq k] [DecidableEq q]
    {X : ℕ → Ω → (k → ℝ)} {y : ℕ → Ω → ℝ}
    (R : Matrix k q ℝ) {Cbeta : ℝ}
    (hBetaBound : ∀ᶠ n in atTop,
      ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
        ‖regressionBootstrapBetaStatisticFinSucc X y n ω ωs‖ ≤ Cbeta) :
    ∀ᶠ n in atTop,
      ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
        ‖regressionBootstrapThetaStatisticFinSucc R X y n ω ωs‖ ≤
          ‖matrixContinuousLinearMap Rᵀ‖ * Cbeta := by
  filter_upwards [hBetaBound] with n hn
  intro ω ωs
  have hbase :=
    (matrixContinuousLinearMap Rᵀ).le_opNorm
      (regressionBootstrapBetaStatisticFinSucc X y n ω ωs)
  have hstep :
      ‖matrixContinuousLinearMap Rᵀ
          (regressionBootstrapBetaStatisticFinSucc X y n ω ωs)‖ ≤
        ‖matrixContinuousLinearMap Rᵀ‖ * Cbeta :=
    hbase.trans
      (mul_le_mul_of_nonneg_left (hn ω ωs) (norm_nonneg _))
  simpa [regressionBootstrapThetaStatisticFinSucc] using hstep

omit [MeasurableSpace Ω] in
/-- The scalar ordinary-bootstrap restriction statistic is exactly the Chapter
7 totalized OLS linear-restriction numerator on the resampled design, centered
at the original-sample `olsBetaOrZero`. -/
theorem regressionBootstrapLinearRestrictionStatisticFinSucc_eq_olsLinearTNumeratorOrZero
    {k : Type*} [Fintype k] [DecidableEq k]
    (R : Matrix Unit k ℝ) (X : ℕ → Ω → (k → ℝ)) (y : ℕ → Ω → ℝ)
    (n : ℕ) (ω : Ω) (ωs : Fin (n + 1) → Fin (n + 1)) :
    regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs =
      olsLinearTNumeratorOrZero R
        (regressionBootstrapRegressorsFinSucc X n ω ωs)
        (regressionBootstrapOutcomesFinSucc y n ω ωs)
        (olsBetaOrZero (stackRegressors X (n + 1) ω)
          (stackOutcomes y (n + 1) ω))
        (Real.sqrt (n + 1 : ℝ)) := by
  rw [regressionBootstrapLinearRestrictionStatisticFinSucc,
    olsLinearTNumeratorOrZero, linearMapUnit_smul_sub_dot_one]
  rfl

theorem regressionLinearizedScoreFinSucc_ofLp_eq_popGramInv_sqrt_smul_sampleCrossMoment_sub
    {k : Type*} [Fintype k] [DecidableEq k]
    (μ : Measure Ω) (X : ℕ → Ω → (k → ℝ)) (e : ℕ → Ω → ℝ)
    (n : ℕ) (ω : Ω) (ωs : Fin (n + 1) → Fin (n + 1)) :
    (regressionLinearizedScoreFinSucc μ X e n ω ωs).ofLp =
      (popGram μ X)⁻¹ *ᵥ
        (Real.sqrt (n + 1 : ℝ) •
          (sampleCrossMoment (regressionBootstrapRegressorsFinSucc X n ω ωs)
              (regressionBootstrapErrorsFinSucc e n ω ωs) -
            sampleCrossMoment (stackRegressors X (n + 1) ω)
              (stackErrors e (n + 1) ω))) := by
  rw [regressionLinearizedScoreFinSucc, matrixContinuousLinearMap_apply,
    regressionBootstrapScoreFinSucc_eq_sqrt_smul_sampleCrossMoment_sub]

omit [MeasurableSpace Ω] in
/-- Bootstrap OLS coefficient error as sample-Gram-inverse score plus the
singular-design totalization remainder. -/
theorem regressionBootstrapBetaFinSucc_sub_beta_eq_sampleGramInv_score_add_remainder
    {k : Type*} [Fintype k] [DecidableEq k]
    (X : ℕ → Ω → (k → ℝ)) (e y : ℕ → Ω → ℝ) (β : k → ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (n : ℕ) (ω : Ω) (ωs : Fin (n + 1) → Fin (n + 1)) :
    regressionBootstrapBetaFinSucc X y n ω ωs - β =
      ((sampleGram (regressionBootstrapRegressorsFinSucc X n ω ωs))⁻¹ *
          sampleGram (regressionBootstrapRegressorsFinSucc X n ω ωs) - 1) *ᵥ β +
        (sampleGram (regressionBootstrapRegressorsFinSucc X n ω ωs))⁻¹ *ᵥ
          sampleCrossMoment (regressionBootstrapRegressorsFinSucc X n ω ωs)
            (regressionBootstrapErrorsFinSucc e n ω ωs) := by
  unfold regressionBootstrapBetaFinSucc
  rw [regressionBootstrapOutcomesFinSucc_linear_model X e y β hmodel]
  have hident := olsBetaOrZero_sub_identity_matrix
    (X := regressionBootstrapRegressorsFinSucc X n ω ωs)
    (β := β) (e := regressionBootstrapErrorsFinSucc e n ω ωs)
  rw [← hident]
  abel

omit [MeasurableSpace Ω] in
/-- Original-sample OLS coefficient error in the same sample-Gram-inverse score
plus singular-remainder form used for bootstrap centering. -/
theorem olsBetaOrZero_stack_finSucc_sub_beta_eq_sampleGramInv_score_add_remainder
    {k : Type*} [Fintype k] [DecidableEq k]
    (X : ℕ → Ω → (k → ℝ)) (e y : ℕ → Ω → ℝ) (β : k → ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (n : ℕ) (ω : Ω) :
    olsBetaOrZero (stackRegressors X (n + 1) ω)
        (stackOutcomes y (n + 1) ω) - β =
      ((sampleGram (stackRegressors X (n + 1) ω))⁻¹ *
          sampleGram (stackRegressors X (n + 1) ω) - 1) *ᵥ β +
        (sampleGram (stackRegressors X (n + 1) ω))⁻¹ *ᵥ
          sampleCrossMoment (stackRegressors X (n + 1) ω)
            (stackErrors e (n + 1) ω) := by
  rw [stack_linear_model X e y β hmodel]
  have hident := olsBetaOrZero_sub_identity_matrix
    (X := stackRegressors X (n + 1) ω)
    (β := β) (e := stackErrors e (n + 1) ω)
  rw [← hident]
  abel

omit [MeasurableSpace Ω] in
/-- Exact finite-resample decomposition of Hansen's concrete
`sqrt(n+1) (β̂* - β̂)` ordinary-bootstrap statistic.

The leading pieces are the bootstrap and original sample-Gram-inverse score
terms. The remaining two terms are the singular-design totalization remainders
from `olsBetaOrZero`. -/
theorem regressionBootstrapBetaStatisticFinSucc_ofLp_eq_sqrt_smul_decomposition
    {k : Type*} [Fintype k] [DecidableEq k]
    (X : ℕ → Ω → (k → ℝ)) (e y : ℕ → Ω → ℝ) (β : k → ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (n : ℕ) (ω : Ω) (ωs : Fin (n + 1) → Fin (n + 1)) :
    (regressionBootstrapBetaStatisticFinSucc X y n ω ωs).ofLp =
      Real.sqrt (n + 1 : ℝ) •
        ((((sampleGram (regressionBootstrapRegressorsFinSucc X n ω ωs))⁻¹ *
              sampleGram (regressionBootstrapRegressorsFinSucc X n ω ωs) - 1) *ᵥ β +
            (sampleGram (regressionBootstrapRegressorsFinSucc X n ω ωs))⁻¹ *ᵥ
              sampleCrossMoment (regressionBootstrapRegressorsFinSucc X n ω ωs)
                (regressionBootstrapErrorsFinSucc e n ω ωs)) -
          (((sampleGram (stackRegressors X (n + 1) ω))⁻¹ *
                sampleGram (stackRegressors X (n + 1) ω) - 1) *ᵥ β +
            (sampleGram (stackRegressors X (n + 1) ω))⁻¹ *ᵥ
              sampleCrossMoment (stackRegressors X (n + 1) ω)
                (stackErrors e (n + 1) ω))) := by
  change
    Real.sqrt (n + 1 : ℝ) •
        (regressionBootstrapBetaFinSucc X y n ω ωs -
          olsBetaOrZero (stackRegressors X (n + 1) ω)
            (stackOutcomes y (n + 1) ω)) =
      Real.sqrt (n + 1 : ℝ) •
        ((((sampleGram (regressionBootstrapRegressorsFinSucc X n ω ωs))⁻¹ *
              sampleGram (regressionBootstrapRegressorsFinSucc X n ω ωs) - 1) *ᵥ β +
            (sampleGram (regressionBootstrapRegressorsFinSucc X n ω ωs))⁻¹ *ᵥ
              sampleCrossMoment (regressionBootstrapRegressorsFinSucc X n ω ωs)
                (regressionBootstrapErrorsFinSucc e n ω ωs)) -
          (((sampleGram (stackRegressors X (n + 1) ω))⁻¹ *
                sampleGram (stackRegressors X (n + 1) ω) - 1) *ᵥ β +
            (sampleGram (stackRegressors X (n + 1) ω))⁻¹ *ᵥ
              sampleCrossMoment (stackRegressors X (n + 1) ω)
                (stackErrors e (n + 1) ω)))
  rw [← regressionBootstrapBetaFinSucc_sub_beta_eq_sampleGramInv_score_add_remainder
      X e y β hmodel n ω ωs,
    ← olsBetaOrZero_stack_finSucc_sub_beta_eq_sampleGramInv_score_add_remainder
      X e y β hmodel n ω]
  congr 1
  abel

/-- Exact difference between the concrete bootstrap OLS statistic and the
population-inverse linearized score. This is the deterministic algebra behind
the remaining Theorem 10.18 conditional-closeness premise. -/
theorem regressionBootstrapBetaStatisticFinSucc_sub_linearizedScore_ofLp_eq
    {k : Type*} [Fintype k] [DecidableEq k]
    (μ : Measure Ω) (X : ℕ → Ω → (k → ℝ)) (e y : ℕ → Ω → ℝ) (β : k → ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (n : ℕ) (ω : Ω) (ωs : Fin (n + 1) → Fin (n + 1)) :
    (regressionBootstrapBetaStatisticFinSucc X y n ω ωs).ofLp -
        (regressionLinearizedScoreFinSucc μ X e n ω ωs).ofLp =
      Real.sqrt (n + 1 : ℝ) •
        (((((sampleGram (regressionBootstrapRegressorsFinSucc X n ω ωs))⁻¹ *
                sampleGram (regressionBootstrapRegressorsFinSucc X n ω ωs) - 1) *ᵥ β +
              (sampleGram (regressionBootstrapRegressorsFinSucc X n ω ωs))⁻¹ *ᵥ
                sampleCrossMoment (regressionBootstrapRegressorsFinSucc X n ω ωs)
                  (regressionBootstrapErrorsFinSucc e n ω ωs)) -
            (((sampleGram (stackRegressors X (n + 1) ω))⁻¹ *
                  sampleGram (stackRegressors X (n + 1) ω) - 1) *ᵥ β +
              (sampleGram (stackRegressors X (n + 1) ω))⁻¹ *ᵥ
                sampleCrossMoment (stackRegressors X (n + 1) ω)
                  (stackErrors e (n + 1) ω))) -
          (popGram μ X)⁻¹ *ᵥ
            (sampleCrossMoment (regressionBootstrapRegressorsFinSucc X n ω ωs)
                (regressionBootstrapErrorsFinSucc e n ω ωs) -
              sampleCrossMoment (stackRegressors X (n + 1) ω)
                (stackErrors e (n + 1) ω))) := by
  rw [regressionBootstrapBetaStatisticFinSucc_ofLp_eq_sqrt_smul_decomposition
      X e y β hmodel,
    regressionLinearizedScoreFinSucc_ofLp_eq_popGramInv_sqrt_smul_sampleCrossMoment_sub]
  rw [Matrix.mulVec_smul, ← smul_sub]

/-- Named finite-resample vector gap between Hansen's concrete OLS bootstrap
coefficient statistic and its population-inverse linearized score.

The first two blocks are the bootstrap and original-sample `olsBetaOrZero`
sample-Gram-inverse score decompositions, including the singular-design
totalization remainders.  The final block subtracts the population-inverse
linearized score. -/
noncomputable def regressionBootstrapBetaLinearizedGapVectorFinSucc
    {k : Type*} [Fintype k] [DecidableEq k]
    (μ : Measure Ω) (X : ℕ → Ω → (k → ℝ)) (e : ℕ → Ω → ℝ) (β : k → ℝ)
    (n : ℕ) (ω : Ω) (ωs : Fin (n + 1) → Fin (n + 1)) :
    k → ℝ :=
  Real.sqrt (n + 1 : ℝ) •
    (((((sampleGram (regressionBootstrapRegressorsFinSucc X n ω ωs))⁻¹ *
            sampleGram (regressionBootstrapRegressorsFinSucc X n ω ωs) - 1) *ᵥ β +
          (sampleGram (regressionBootstrapRegressorsFinSucc X n ω ωs))⁻¹ *ᵥ
            sampleCrossMoment (regressionBootstrapRegressorsFinSucc X n ω ωs)
              (regressionBootstrapErrorsFinSucc e n ω ωs)) -
        (((sampleGram (stackRegressors X (n + 1) ω))⁻¹ *
              sampleGram (stackRegressors X (n + 1) ω) - 1) *ᵥ β +
          (sampleGram (stackRegressors X (n + 1) ω))⁻¹ *ᵥ
            sampleCrossMoment (stackRegressors X (n + 1) ω)
              (stackErrors e (n + 1) ω))) -
      (popGram μ X)⁻¹ *ᵥ
        (sampleCrossMoment (regressionBootstrapRegressorsFinSucc X n ω ωs)
            (regressionBootstrapErrorsFinSucc e n ω ωs) -
          sampleCrossMoment (stackRegressors X (n + 1) ω)
            (stackErrors e (n + 1) ω)))

/-- Euclidean norm envelope for the finite-resample OLS-linearization gap. -/
noncomputable def regressionBootstrapBetaLinearizedGapEnvelopeFinSucc
    {k : Type*} [Fintype k] [DecidableEq k]
    (μ : Measure Ω) (X : ℕ → Ω → (k → ℝ)) (e : ℕ → Ω → ℝ) (β : k → ℝ)
    (n : ℕ) (ω : Ω) (ωs : Fin (n + 1) → Fin (n + 1)) :
    ℝ :=
  ‖(WithLp.toLp 2
      (regressionBootstrapBetaLinearizedGapVectorFinSucc μ X e β n ω ωs) :
      EuclideanSpace ℝ k)‖

/-- The exact `.ofLp` OLS-linearization difference is the named finite
gap vector. -/
theorem regressionBootstrapBetaStatisticFinSucc_sub_linearizedScore_ofLp_eq_gapVector
    {k : Type*} [Fintype k] [DecidableEq k]
    (μ : Measure Ω) (X : ℕ → Ω → (k → ℝ)) (e y : ℕ → Ω → ℝ) (β : k → ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (n : ℕ) (ω : Ω) (ωs : Fin (n + 1) → Fin (n + 1)) :
    (regressionBootstrapBetaStatisticFinSucc X y n ω ωs).ofLp -
        (regressionLinearizedScoreFinSucc μ X e n ω ωs).ofLp =
      regressionBootstrapBetaLinearizedGapVectorFinSucc μ X e β n ω ωs := by
  rw [regressionBootstrapBetaLinearizedGapVectorFinSucc]
  exact regressionBootstrapBetaStatisticFinSucc_sub_linearizedScore_ofLp_eq
    μ X e y β hmodel n ω ωs

/-- The named gap envelope pointwise bounds the distance from Hansen's concrete
OLS bootstrap coefficient statistic to the population-inverse linearized
score. -/
theorem regressionBootstrapBetaStatisticFinSucc_dist_linearizedScore_le_gapEnvelope
    {k : Type*} [Fintype k] [DecidableEq k]
    (μ : Measure Ω) (X : ℕ → Ω → (k → ℝ)) (e y : ℕ → Ω → ℝ) (β : k → ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (n : ℕ) (ω : Ω) (ωs : Fin (n + 1) → Fin (n + 1)) :
    dist (regressionBootstrapBetaStatisticFinSucc X y n ω ωs)
        (regressionLinearizedScoreFinSucc μ X e n ω ωs) ≤
      regressionBootstrapBetaLinearizedGapEnvelopeFinSucc μ X e β n ω ωs := by
  have hvec :=
    regressionBootstrapBetaStatisticFinSucc_sub_linearizedScore_ofLp_eq_gapVector
      μ X e y β hmodel n ω ωs
  have hdiff :
      regressionBootstrapBetaStatisticFinSucc X y n ω ωs -
          regressionLinearizedScoreFinSucc μ X e n ω ωs =
        (WithLp.toLp 2
          (regressionBootstrapBetaLinearizedGapVectorFinSucc μ X e β n ω ωs) :
          EuclideanSpace ℝ k) := by
    apply WithLp.ofLp_injective (p := (2 : ℝ≥0∞))
    simpa using hvec
  rw [dist_eq_norm, hdiff, regressionBootstrapBetaLinearizedGapEnvelopeFinSucc]

set_option linter.style.longLine false in
/-- Hansen Theorem 10.18 score-level ordinary-bootstrap CLT.

The ordinary `Fin (n+1)` nonparametric bootstrap CLT applied to the regression
score vectors `e_i X_i` gives a Euclidean score Gaussian with covariance
`scoreCovMat`. -/
theorem chapter10_indexed_bootstrap_score_gaussian_finSucc_resampleMean
    [IsProbabilityMeasure μ]
    {k : Type*} [Fintype k] [DecidableEq k]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ}
    (h : ScoreCLTConditions μ X e)
    (hΩ : (scoreCovMat μ X e).PosDef) :
    TendstoInBootstrapWeakDistributionIndexed μ
      (fun n _ =>
        (ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))))
      (fun n ω ωs =>
        regressionBootstrapScoreFinSucc (Ω := Ω) X e n ω ωs)
      (multivariateGaussian (0 : EuclideanSpace ℝ k) (scoreCovMat μ X e))
      (fun z : EuclideanSpace ℝ k => z) := by
  have hVec :
      TendstoInBootstrapWeakDistributionIndexed μ
        (fun n _ =>
          (ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
              Measure (Fin (n + 1) → Fin (n + 1))))
        (fun n ω ωs a =>
          Real.sqrt (n + 1 : ℝ) *
            (empiricalBootstrapResampleMean
                (fun i : Fin (n + 1) => e i.val ω • X i.val ω)
                (fun ωs t => ωs t) ωs a -
              empiricalMean
                (fun i : Fin (n + 1) => e i.val ω • X i.val ω) a))
        (multivariateGaussian (0 : EuclideanSpace ℝ k) (scoreCovMat μ X e))
        (fun z : EuclideanSpace ℝ k => (z : k → ℝ)) := by
    simpa [scoreCovMat] using
      (chapter10_indexed_bootstrap_weak_clt_gaussian_finSucc_resampleMean_of_iIndep_covMat_tail_posDef
        (μ := μ) (Y := fun i ω => e i ω • X i ω)
        (fun a =>
          scoreCoordinate_memLp_two (μ := μ) (X := X) (e := e)
            h.toSampleCLTAssumption72 a)
        h.iIndep_cross h.ident_cross
        (by simpa [scoreCovMat] using hΩ))
  have hEuclid :
      TendstoInBootstrapWeakDistributionIndexed μ
        (fun n _ =>
          (ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
              Measure (Fin (n + 1) → Fin (n + 1))))
        (fun n ω ωs =>
          WithLp.toLp 2
            (fun a =>
              Real.sqrt (n + 1 : ℝ) *
                (empiricalBootstrapResampleMean
                    (fun i : Fin (n + 1) => e i.val ω • X i.val ω)
                    (fun ωs t => ωs t) ωs a -
                  empiricalMean
                    (fun i : Fin (n + 1) => e i.val ω • X i.val ω) a)))
        (multivariateGaussian (0 : EuclideanSpace ℝ k) (scoreCovMat μ X e))
        (fun z : EuclideanSpace ℝ k =>
          WithLp.toLp 2 ((z : EuclideanSpace ℝ k) : k → ℝ)) :=
    chapter10_indexed_bootstrap_continuous_mapping_distribution
      (μ := μ)
      (Pstar := fun n _ =>
        (ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))))
      (Zstar := fun n ω ωs a =>
        Real.sqrt (n + 1 : ℝ) *
          (empiricalBootstrapResampleMean
              (fun i : Fin (n + 1) => e i.val ω • X i.val ω)
              (fun ωs t => ωs t) ωs a -
            empiricalMean
              (fun i : Fin (n + 1) => e i.val ω • X i.val ω) a))
      (ν := multivariateGaussian (0 : EuclideanSpace ℝ k) (scoreCovMat μ X e))
      (Z := fun z : EuclideanSpace ℝ k => (z : k → ℝ))
      (g := (WithLp.toLp 2 : (k → ℝ) → EuclideanSpace ℝ k))
      hVec (PiLp.continuous_toLp 2 (fun _ : k => ℝ))
  refine hEuclid.congr ?_ ?_
  · intro n ω ωs
    rfl
  intro z
  simp

/-- Hansen Theorem 10.18 linearized ordinary-bootstrap coefficient CLT.

Applying the population Gram inverse to the ordinary bootstrap score CLT gives
the linearized regression coefficient statistic with covariance
`heteroAsymCov`. -/
theorem
    chapter10_indexed_bootstrap_regression_linearizedScore_gaussian_finSucc_resampleMean
    [IsProbabilityMeasure μ]
    {k : Type*} [Fintype k] [DecidableEq k]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ}
    (h : ScoreCLTConditions μ X e)
    (hΩ : (scoreCovMat μ X e).PosDef) :
    TendstoInBootstrapWeakDistributionIndexed μ
      (fun n _ =>
        (ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))))
      (fun n ω ωs =>
        regressionLinearizedScoreFinSucc μ X e n ω ωs)
      (multivariateGaussian (0 : EuclideanSpace ℝ k) (heteroAsymCov μ X e))
      (fun z : EuclideanSpace ℝ k => z) := by
  have hScore :=
    chapter10_indexed_bootstrap_score_gaussian_finSucc_resampleMean
      (μ := μ) (X := X) (e := e) h hΩ
  have hDelta :=
    chapter10_indexed_bootstrap_delta_method_gaussian
      (μ := μ)
      (Pstar := fun n _ =>
        (ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))))
      (Tstar := fun n ω ωs =>
        WithLp.toLp 2
          (fun a =>
            Real.sqrt (n + 1 : ℝ) *
              (empiricalBootstrapResampleMean
                  (fun i : Fin (n + 1) => e i.val ω • X i.val ω)
                  (fun ωs t => ωs t) ωs a -
                empiricalMean
                  (fun i : Fin (n + 1) => e i.val ω • X i.val ω) a)))
      (V := scoreCovMat μ X e) ((popGram μ X)⁻¹) hΩ.posSemidef hScore
  have hQinv_transpose : ((popGram μ X)⁻¹)ᵀ = (popGram μ X)⁻¹ := by
    simpa using
      (popGram_inv_isSymm (μ := μ) (X := X)
        h.toSampleMomentAssumption71.int_outer).eq
  have hcov :
      (popGram μ X)⁻¹ * scoreCovMat μ X e * ((popGram μ X)⁻¹)ᵀ =
        heteroAsymCov μ X e := by
    simp [heteroAsymCov, hQinv_transpose]
  simpa [regressionLinearizedScoreFinSucc, regressionBootstrapScoreFinSucc, hcov]
    using hDelta

set_option linter.style.longLine false in
/-- Robust-feasible HC face of the ordinary finite-resample regression score
bootstrap CLT.

The Chapter 7 robust-feasible condition package supplies the score CLT
conditions; positive definiteness of the score covariance remains explicit. -/
theorem
    chapter10_indexed_bootstrap_score_gaussian_finSucc_resampleMean_of_robustFeasibleHCMomentConditions
    [IsProbabilityMeasure μ]
    {k : Type*} [Fintype k] [DecidableEq k]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    (β : k → ℝ)
    (hm : RobustFeasibleHCMomentConditions μ X e y β)
    (hΩ : (scoreCovMat μ X e).PosDef) :
    TendstoInBootstrapWeakDistributionIndexed μ
      (fun n _ =>
        (ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))))
      (fun n ω ωs =>
        regressionBootstrapScoreFinSucc (Ω := Ω) X e n ω ωs)
      (multivariateGaussian (0 : EuclideanSpace ℝ k) (scoreCovMat μ X e))
      (fun z : EuclideanSpace ℝ k => z) :=
  chapter10_indexed_bootstrap_score_gaussian_finSucc_resampleMean
    (μ := μ) (X := X) (e := e) hm.toScoreCLTConditions hΩ

set_option linter.style.longLine false in
/-- Robust-feasible HC face of the ordinary finite-resample linearized
regression coefficient CLT. -/
theorem
    chapter10_indexed_bootstrap_regression_linearizedScore_gaussian_finSucc_resampleMean_of_robustFeasibleHCMomentConditions
    [IsProbabilityMeasure μ]
    {k : Type*} [Fintype k] [DecidableEq k]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    (β : k → ℝ)
    (hm : RobustFeasibleHCMomentConditions μ X e y β)
    (hΩ : (scoreCovMat μ X e).PosDef) :
    TendstoInBootstrapWeakDistributionIndexed μ
      (fun n _ =>
        (ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))))
      (fun n ω ωs =>
        regressionLinearizedScoreFinSucc μ X e n ω ωs)
      (multivariateGaussian (0 : EuclideanSpace ℝ k) (heteroAsymCov μ X e))
      (fun z : EuclideanSpace ℝ k => z) :=
  chapter10_indexed_bootstrap_regression_linearizedScore_gaussian_finSucc_resampleMean
    (μ := μ) (X := X) (e := e) hm.toScoreCLTConditions hΩ

/-- Hansen Theorem 10.18 nonlinear ordinary-bootstrap coefficient CLT from the
linearized score route.

This is the regression-facing inversion-transfer wrapper: once a concrete
bootstrap coefficient statistic is conditionally close to
`regressionLinearizedScoreFinSucc`, and both statistics have asymptotic
compact-tail control, the statistic inherits the ordinary-bootstrap Gaussian
coefficient limit with covariance `heteroAsymCov`. -/
theorem
    chapter10_indexed_bootstrap_regression_beta_gaussian_finSucc_of_linearizedScore_tight
    [IsProbabilityMeasure μ]
    {k : Type*} [Fintype k] [DecidableEq k]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ}
    {TbetaStar :
      ∀ n, Ω → (Fin (n + 1) → Fin (n + 1)) → EuclideanSpace ℝ k}
    (h : ScoreCLTConditions μ X e)
    (hΩ : (scoreCovMat μ X e).PosDef)
    (hTbetaStar : ∀ n ω, Measurable (TbetaStar n ω))
    (hTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set (EuclideanSpace ℝ k), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω =>
            ((ProbabilityTheory.uniformOn
              (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                Measure (Fin (n + 1) → Fin (n + 1)))).real
              {ωs | regressionLinearizedScoreFinSucc μ X e n ω ωs ∉ K})
          atTop (fun _ => 0) ∧
        TendstoInMeasure μ
          (fun n ω =>
            ((ProbabilityTheory.uniformOn
              (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                Measure (Fin (n + 1) → Fin (n + 1)))).real
              {ωs | TbetaStar n ω ωs ∉ K})
          atTop (fun _ => 0))
    (hclose : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          ((ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
              Measure (Fin (n + 1) → Fin (n + 1)))).real
            {ωs |
              δ ≤ dist (TbetaStar n ω ωs)
                (regressionLinearizedScoreFinSucc μ X e n ω ωs)})
        atTop (fun _ => 0)) :
    TendstoInBootstrapWeakDistributionIndexed μ
      (fun n _ =>
        (ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))))
      TbetaStar
      (multivariateGaussian (0 : EuclideanSpace ℝ k) (heteroAsymCov μ X e))
      (fun z : EuclideanSpace ℝ k => z) := by
  letI : ∀ n, Ω → IsProbabilityMeasure
      (ProbabilityTheory.uniformOn
        (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
          Measure (Fin (n + 1) → Fin (n + 1))) := fun n _ => by
    infer_instance
  refine TendstoInBootstrapWeakDistributionIndexed.of_bootstrap_dist_tendsto_zero_tight
    (μ := μ)
    (Pstar := fun n _ =>
      (ProbabilityTheory.uniformOn
        (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
          Measure (Fin (n + 1) → Fin (n + 1))))
    (Zstar := fun n ω ωs => regressionLinearizedScoreFinSucc μ X e n ω ωs)
    (Zstar' := TbetaStar)
    (ν := multivariateGaussian (0 : EuclideanSpace ℝ k) (heteroAsymCov μ X e))
    (Z := fun z : EuclideanSpace ℝ k => z)
    (chapter10_indexed_bootstrap_regression_linearizedScore_gaussian_finSucc_resampleMean
      (μ := μ) (X := X) (e := e) h hΩ)
    (fun n ω => inferInstance) ?_ hTbetaStar hTail hclose
  intro n ω
  exact measurable_of_finite _

set_option linter.style.longLine false in
/-- Concrete ordinary-bootstrap OLS coefficient version of
`chapter10_indexed_bootstrap_regression_beta_gaussian_finSucc_of_linearizedScore_tight`.

The statistic is Hansen's `sqrt(n+1) (β̂* - β̂)` with `olsBetaOrZero`
totalization.  The model-specific work remains the conditional closeness to
`regressionLinearizedScoreFinSucc` and the shared compact-tail control. -/
theorem
    chapter10_indexed_bootstrap_regression_beta_gaussian_finSucc_olsBetaOrZero_of_linearizedScore_tight
    [IsProbabilityMeasure μ]
    {k : Type*} [Fintype k] [DecidableEq k]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    (h : ScoreCLTConditions μ X e)
    (hΩ : (scoreCovMat μ X e).PosDef)
    (hTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set (EuclideanSpace ℝ k), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω =>
            ((ProbabilityTheory.uniformOn
              (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                Measure (Fin (n + 1) → Fin (n + 1)))).real
              {ωs | regressionLinearizedScoreFinSucc μ X e n ω ωs ∉ K})
          atTop (fun _ => 0) ∧
        TendstoInMeasure μ
          (fun n ω =>
            ((ProbabilityTheory.uniformOn
              (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                Measure (Fin (n + 1) → Fin (n + 1)))).real
              {ωs | regressionBootstrapBetaStatisticFinSucc X y n ω ωs ∉ K})
          atTop (fun _ => 0))
    (hclose : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          ((ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
              Measure (Fin (n + 1) → Fin (n + 1)))).real
            {ωs |
              δ ≤ dist (regressionBootstrapBetaStatisticFinSucc X y n ω ωs)
                (regressionLinearizedScoreFinSucc μ X e n ω ωs)})
        atTop (fun _ => 0)) :
    TendstoInBootstrapWeakDistributionIndexed μ
      (fun n _ =>
        (ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))))
      (fun n ω ωs => regressionBootstrapBetaStatisticFinSucc X y n ω ωs)
      (multivariateGaussian (0 : EuclideanSpace ℝ k) (heteroAsymCov μ X e))
      (fun z : EuclideanSpace ℝ k => z) :=
  chapter10_indexed_bootstrap_regression_beta_gaussian_finSucc_of_linearizedScore_tight
    (μ := μ) (X := X) (e := e)
    (TbetaStar := fun n ω ωs =>
      regressionBootstrapBetaStatisticFinSucc X y n ω ωs)
    h hΩ (fun _ _ => measurable_of_finite _) hTail hclose

set_option linter.style.longLine false in
/-- Concrete ordinary-bootstrap OLS coefficient transfer from the explicit
finite OLS-linearization gap envelope.

This wrapper replaces the raw conditional-closeness premise by the tail
condition for `regressionBootstrapBetaLinearizedGapEnvelopeFinSucc`, whose
pointwise bound is supplied by the finite matrix decomposition above. -/
theorem
    chapter10_indexed_bootstrap_regression_beta_gaussian_finSucc_olsBetaOrZero_of_gapEnvelope_tight
    [IsProbabilityMeasure μ]
    {k : Type*} [Fintype k] [DecidableEq k]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    (β : k → ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (h : ScoreCLTConditions μ X e)
    (hΩ : (scoreCovMat μ X e).PosDef)
    (hTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set (EuclideanSpace ℝ k), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω =>
            ((ProbabilityTheory.uniformOn
              (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                Measure (Fin (n + 1) → Fin (n + 1)))).real
              {ωs | regressionLinearizedScoreFinSucc μ X e n ω ωs ∉ K})
          atTop (fun _ => 0) ∧
        TendstoInMeasure μ
          (fun n ω =>
            ((ProbabilityTheory.uniformOn
              (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                Measure (Fin (n + 1) → Fin (n + 1)))).real
              {ωs | regressionBootstrapBetaStatisticFinSucc X y n ω ωs ∉ K})
          atTop (fun _ => 0))
    (hGapTail : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          ((ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
              Measure (Fin (n + 1) → Fin (n + 1)))).real
            {ωs |
              δ ≤ regressionBootstrapBetaLinearizedGapEnvelopeFinSucc
                μ X e β n ω ωs})
        atTop (fun _ => 0)) :
    TendstoInBootstrapWeakDistributionIndexed μ
      (fun n _ =>
        (ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))))
      (fun n ω ωs => regressionBootstrapBetaStatisticFinSucc X y n ω ωs)
      (multivariateGaussian (0 : EuclideanSpace ℝ k) (heteroAsymCov μ X e))
      (fun z : EuclideanSpace ℝ k => z) :=
  chapter10_indexed_bootstrap_regression_beta_gaussian_finSucc_olsBetaOrZero_of_linearizedScore_tight
    (μ := μ) (X := X) (e := e) (y := y) h hΩ hTail
    (TendstoInBootstrapWeakDistributionIndexed.bootstrap_dist_tendsto_zero_of_dist_bound
      (μ := μ)
      (Pstar := fun n _ =>
        (ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))))
      (Zstar := fun n ω ωs => regressionLinearizedScoreFinSucc μ X e n ω ωs)
      (Zstar' := fun n ω ωs => regressionBootstrapBetaStatisticFinSucc X y n ω ωs)
      (R := fun n ω ωs =>
        regressionBootstrapBetaLinearizedGapEnvelopeFinSucc μ X e β n ω ωs)
      (fun n ω => by infer_instance)
      hGapTail
      (fun n ω ωs =>
        regressionBootstrapBetaStatisticFinSucc_dist_linearizedScore_le_gapEnvelope
          μ X e y β hmodel n ω ωs))

set_option linter.style.longLine false in
/-- Robust-feasible HC specialization of the explicit gap-envelope concrete
ordinary-bootstrap OLS coefficient transfer. -/
theorem
    chapter10_indexed_bootstrap_regression_beta_gaussian_finSucc_olsBetaOrZero_of_gapEnvelope_tight_of_robustFeasibleHCMomentConditions
    [IsProbabilityMeasure μ]
    {k : Type*} [Fintype k] [DecidableEq k]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    (β : k → ℝ)
    (hm : RobustFeasibleHCMomentConditions μ X e y β)
    (hΩ : (scoreCovMat μ X e).PosDef)
    (hTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set (EuclideanSpace ℝ k), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω =>
            ((ProbabilityTheory.uniformOn
              (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                Measure (Fin (n + 1) → Fin (n + 1)))).real
              {ωs | regressionLinearizedScoreFinSucc μ X e n ω ωs ∉ K})
          atTop (fun _ => 0) ∧
        TendstoInMeasure μ
          (fun n ω =>
            ((ProbabilityTheory.uniformOn
              (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                Measure (Fin (n + 1) → Fin (n + 1)))).real
              {ωs | regressionBootstrapBetaStatisticFinSucc X y n ω ωs ∉ K})
          atTop (fun _ => 0))
    (hGapTail : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          ((ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
              Measure (Fin (n + 1) → Fin (n + 1)))).real
            {ωs |
              δ ≤ regressionBootstrapBetaLinearizedGapEnvelopeFinSucc
                μ X e β n ω ωs})
        atTop (fun _ => 0)) :
    TendstoInBootstrapWeakDistributionIndexed μ
      (fun n _ =>
        (ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))))
      (fun n ω ωs => regressionBootstrapBetaStatisticFinSucc X y n ω ωs)
      (multivariateGaussian (0 : EuclideanSpace ℝ k) (heteroAsymCov μ X e))
      (fun z : EuclideanSpace ℝ k => z) :=
  chapter10_indexed_bootstrap_regression_beta_gaussian_finSucc_olsBetaOrZero_of_gapEnvelope_tight
    (μ := μ) (X := X) (e := e) (y := y)
    β hm.model hm.toScoreCLTConditions hΩ hTail hGapTail

set_option linter.style.longLine false in
/-- Robust-feasible HC specialization of the concrete ordinary-bootstrap OLS
coefficient transfer. -/
theorem
    chapter10_indexed_bootstrap_regression_beta_gaussian_finSucc_olsBetaOrZero_of_linearizedScore_tight_of_robustFeasibleHCMomentConditions
    [IsProbabilityMeasure μ]
    {k : Type*} [Fintype k] [DecidableEq k]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    (β : k → ℝ)
    (hm : RobustFeasibleHCMomentConditions μ X e y β)
    (hΩ : (scoreCovMat μ X e).PosDef)
    (hTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set (EuclideanSpace ℝ k), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω =>
            ((ProbabilityTheory.uniformOn
              (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                Measure (Fin (n + 1) → Fin (n + 1)))).real
              {ωs | regressionLinearizedScoreFinSucc μ X e n ω ωs ∉ K})
          atTop (fun _ => 0) ∧
        TendstoInMeasure μ
          (fun n ω =>
            ((ProbabilityTheory.uniformOn
              (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                Measure (Fin (n + 1) → Fin (n + 1)))).real
              {ωs | regressionBootstrapBetaStatisticFinSucc X y n ω ωs ∉ K})
          atTop (fun _ => 0))
    (hclose : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          ((ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
              Measure (Fin (n + 1) → Fin (n + 1)))).real
            {ωs |
              δ ≤ dist (regressionBootstrapBetaStatisticFinSucc X y n ω ωs)
                (regressionLinearizedScoreFinSucc μ X e n ω ωs)})
        atTop (fun _ => 0)) :
    TendstoInBootstrapWeakDistributionIndexed μ
      (fun n _ =>
        (ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))))
      (fun n ω ωs => regressionBootstrapBetaStatisticFinSucc X y n ω ωs)
      (multivariateGaussian (0 : EuclideanSpace ℝ k) (heteroAsymCov μ X e))
      (fun z : EuclideanSpace ℝ k => z) :=
  chapter10_indexed_bootstrap_regression_beta_gaussian_finSucc_olsBetaOrZero_of_linearizedScore_tight
    (μ := μ) (X := X) (e := e) (y := y)
    hm.toScoreCLTConditions hΩ hTail hclose

set_option linter.style.longLine false in
/-- Concrete ordinary-bootstrap OLS coefficient transfer with compact-tail
control discharged by deterministic eventual norm bounds.

This is the bounded-statistic face of the Hansen Theorem 10.18 nonlinear
coefficient route: model-specific work is reduced to norm bounds for the
linearized and nonlinear coefficient statistics plus conditional closeness. -/
theorem
    chapter10_indexed_bootstrap_regression_beta_gaussian_finSucc_olsBetaOrZero_of_linearizedScore_bounds
    [IsProbabilityMeasure μ]
    {k : Type*} [Fintype k] [DecidableEq k]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    {Clin Cbeta : ℝ}
    (h : ScoreCLTConditions μ X e)
    (hΩ : (scoreCovMat μ X e).PosDef)
    (hLinBound : ∀ᶠ n in atTop,
      ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
        ‖regressionLinearizedScoreFinSucc μ X e n ω ωs‖ ≤ Clin)
    (hBetaBound : ∀ᶠ n in atTop,
      ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
        ‖regressionBootstrapBetaStatisticFinSucc X y n ω ωs‖ ≤ Cbeta)
    (hclose : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          ((ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
              Measure (Fin (n + 1) → Fin (n + 1)))).real
            {ωs |
              δ ≤ dist (regressionBootstrapBetaStatisticFinSucc X y n ω ωs)
                (regressionLinearizedScoreFinSucc μ X e n ω ωs)})
        atTop (fun _ => 0)) :
    TendstoInBootstrapWeakDistributionIndexed μ
      (fun n _ =>
        (ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))))
      (fun n ω ωs => regressionBootstrapBetaStatisticFinSucc X y n ω ωs)
      (multivariateGaussian (0 : EuclideanSpace ℝ k) (heteroAsymCov μ X e))
      (fun z : EuclideanSpace ℝ k => z) :=
  chapter10_indexed_bootstrap_regression_beta_gaussian_finSucc_olsBetaOrZero_of_linearizedScore_tight
    (μ := μ) (X := X) (e := e) (y := y) h hΩ
    (chapter10_indexed_bootstrap_euclidean_pair_compactTail_of_eventually_norm_bound
      (μ := μ)
      (Pstar := fun n _ =>
        (ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))))
      (Zstar := fun n ω ωs => regressionLinearizedScoreFinSucc μ X e n ω ωs)
      (Zstar' := fun n ω ωs => regressionBootstrapBetaStatisticFinSucc X y n ω ωs)
      hLinBound hBetaBound)
    hclose

set_option linter.style.longLine false in
/-- Robust-feasible HC specialization of the bounded concrete
ordinary-bootstrap OLS coefficient transfer. -/
theorem
    chapter10_indexed_bootstrap_regression_beta_gaussian_finSucc_olsBetaOrZero_of_linearizedScore_bounds_of_robustFeasibleHCMomentConditions
    [IsProbabilityMeasure μ]
    {k : Type*} [Fintype k] [DecidableEq k]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    {Clin Cbeta : ℝ}
    (β : k → ℝ)
    (hm : RobustFeasibleHCMomentConditions μ X e y β)
    (hΩ : (scoreCovMat μ X e).PosDef)
    (hLinBound : ∀ᶠ n in atTop,
      ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
        ‖regressionLinearizedScoreFinSucc μ X e n ω ωs‖ ≤ Clin)
    (hBetaBound : ∀ᶠ n in atTop,
      ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
        ‖regressionBootstrapBetaStatisticFinSucc X y n ω ωs‖ ≤ Cbeta)
    (hclose : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          ((ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
              Measure (Fin (n + 1) → Fin (n + 1)))).real
            {ωs |
              δ ≤ dist (regressionBootstrapBetaStatisticFinSucc X y n ω ωs)
                (regressionLinearizedScoreFinSucc μ X e n ω ωs)})
        atTop (fun _ => 0)) :
    TendstoInBootstrapWeakDistributionIndexed μ
      (fun n _ =>
        (ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))))
      (fun n ω ωs => regressionBootstrapBetaStatisticFinSucc X y n ω ωs)
      (multivariateGaussian (0 : EuclideanSpace ℝ k) (heteroAsymCov μ X e))
      (fun z : EuclideanSpace ℝ k => z) :=
  chapter10_indexed_bootstrap_regression_beta_gaussian_finSucc_olsBetaOrZero_of_linearizedScore_bounds
    (μ := μ) (X := X) (e := e) (y := y)
    hm.toScoreCLTConditions hΩ hLinBound hBetaBound hclose

set_option linter.style.longLine false in
/-- Concrete ordinary-bootstrap OLS coefficient gap-envelope transfer with
compact-tail control discharged by deterministic eventual norm bounds.

This is the bounded-statistic face of
`chapter10_indexed_bootstrap_regression_beta_gaussian_finSucc_olsBetaOrZero_of_gapEnvelope_tight`:
model-specific nonlinear-inversion work is reduced to norm bounds for the
linearized and nonlinear coefficient statistics plus the named finite
OLS-linearization gap-envelope tail. -/
theorem
    chapter10_indexed_bootstrap_regression_beta_gaussian_finSucc_olsBetaOrZero_of_gapEnvelope_bounds
    [IsProbabilityMeasure μ]
    {k : Type*} [Fintype k] [DecidableEq k]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    {Clin Cbeta : ℝ}
    (β : k → ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (h : ScoreCLTConditions μ X e)
    (hΩ : (scoreCovMat μ X e).PosDef)
    (hLinBound : ∀ᶠ n in atTop,
      ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
        ‖regressionLinearizedScoreFinSucc μ X e n ω ωs‖ ≤ Clin)
    (hBetaBound : ∀ᶠ n in atTop,
      ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
        ‖regressionBootstrapBetaStatisticFinSucc X y n ω ωs‖ ≤ Cbeta)
    (hGapTail : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          ((ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
              Measure (Fin (n + 1) → Fin (n + 1)))).real
            {ωs |
              δ ≤ regressionBootstrapBetaLinearizedGapEnvelopeFinSucc
                μ X e β n ω ωs})
        atTop (fun _ => 0)) :
    TendstoInBootstrapWeakDistributionIndexed μ
      (fun n _ =>
        (ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))))
      (fun n ω ωs => regressionBootstrapBetaStatisticFinSucc X y n ω ωs)
      (multivariateGaussian (0 : EuclideanSpace ℝ k) (heteroAsymCov μ X e))
      (fun z : EuclideanSpace ℝ k => z) :=
  chapter10_indexed_bootstrap_regression_beta_gaussian_finSucc_olsBetaOrZero_of_gapEnvelope_tight
    (μ := μ) (X := X) (e := e) (y := y) β hmodel h hΩ
    (chapter10_indexed_bootstrap_euclidean_pair_compactTail_of_eventually_norm_bound
      (μ := μ)
      (Pstar := fun n _ =>
        (ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))))
      (Zstar := fun n ω ωs => regressionLinearizedScoreFinSucc μ X e n ω ωs)
      (Zstar' := fun n ω ωs => regressionBootstrapBetaStatisticFinSucc X y n ω ωs)
      hLinBound hBetaBound)
    hGapTail

set_option linter.style.longLine false in
/-- Robust-feasible HC specialization of the bounded concrete
ordinary-bootstrap OLS coefficient gap-envelope transfer. -/
theorem
    chapter10_indexed_bootstrap_regression_beta_gaussian_finSucc_olsBetaOrZero_of_gapEnvelope_bounds_of_robustFeasibleHCMomentConditions
    [IsProbabilityMeasure μ]
    {k : Type*} [Fintype k] [DecidableEq k]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    {Clin Cbeta : ℝ}
    (β : k → ℝ)
    (hm : RobustFeasibleHCMomentConditions μ X e y β)
    (hΩ : (scoreCovMat μ X e).PosDef)
    (hLinBound : ∀ᶠ n in atTop,
      ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
        ‖regressionLinearizedScoreFinSucc μ X e n ω ωs‖ ≤ Clin)
    (hBetaBound : ∀ᶠ n in atTop,
      ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
        ‖regressionBootstrapBetaStatisticFinSucc X y n ω ωs‖ ≤ Cbeta)
    (hGapTail : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          ((ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
              Measure (Fin (n + 1) → Fin (n + 1)))).real
            {ωs |
              δ ≤ regressionBootstrapBetaLinearizedGapEnvelopeFinSucc
                μ X e β n ω ωs})
        atTop (fun _ => 0)) :
    TendstoInBootstrapWeakDistributionIndexed μ
      (fun n _ =>
        (ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))))
      (fun n ω ωs => regressionBootstrapBetaStatisticFinSucc X y n ω ωs)
      (multivariateGaussian (0 : EuclideanSpace ℝ k) (heteroAsymCov μ X e))
      (fun z : EuclideanSpace ℝ k => z) :=
  chapter10_indexed_bootstrap_regression_beta_gaussian_finSucc_olsBetaOrZero_of_gapEnvelope_bounds
    (μ := μ) (X := X) (e := e) (y := y)
    β hm.model hm.toScoreCLTConditions hΩ hLinBound hBetaBound hGapTail

/-- Hansen Theorem 10.18, nonlinear-regression delta-method Gaussian wrapper.

If the bootstrap regression coefficient statistic converges weakly to
`N(0,Vβ)`, then the derivative-linearized statistic for a smooth transformation
with Jacobian `R` converges weakly to `N(0,R' Vβ R)`.  This is the regression
surface of the bootstrap Delta method; the concrete OLS bootstrap constructor
supplies the coefficient-level bootstrap CLT premise. -/
theorem chapter10_bootstrap_regression_theta_gaussian
    {k q : Type*} [Fintype k] [Fintype q] [DecidableEq k] [DecidableEq q]
    {Pstar : ℕ → Ω → Measure Ωs}
    {TbetaStar : ℕ → Ω → Ωs → EuclideanSpace ℝ k}
    {Vβ : Matrix k k ℝ} (R : Matrix k q ℝ)
    (hVβ : Vβ.PosSemidef)
    (hβ :
      TendstoInBootstrapWeakDistribution μ Pstar TbetaStar
        (multivariateGaussian (0 : EuclideanSpace ℝ k) Vβ)
        (fun z : EuclideanSpace ℝ k => z)) :
    TendstoInBootstrapWeakDistribution μ Pstar
      (fun n ω ωs => matrixContinuousLinearMap Rᵀ (TbetaStar n ω ωs))
      (multivariateGaussian (0 : EuclideanSpace ℝ q) (Rᵀ * Vβ * R))
      (fun z : EuclideanSpace ℝ q => z) := by
  simpa [Matrix.transpose_transpose] using
    chapter10_bootstrap_delta_method_gaussian (μ := μ) (Pstar := Pstar)
      (Tstar := TbetaStar) (V := Vβ) (G := Rᵀ) hVβ hβ

/-- Hansen Theorem 10.18, regression Gaussian CDF wrapper.

This is the Hansen Definition 10.2 face of
`chapter10_bootstrap_regression_theta_gaussian`: after the coefficient-level
bootstrap CLT and the delta-method linear map, coordinate CDF convergence
follows at transformed Gaussian continuity points whose lower-orthant
frontiers are null. -/
theorem chapter10_bootstrap_regression_theta_gaussian_distribution
    {k q : Type*} [Fintype k] [Fintype q] [DecidableEq k] [DecidableEq q]
    {Pstar : ℕ → Ω → Measure Ωs}
    {TbetaStar : ℕ → Ω → Ωs → EuclideanSpace ℝ k}
    {Vβ : Matrix k k ℝ} (R : Matrix k q ℝ)
    (hVβ : Vβ.PosSemidef)
    (hβ :
      TendstoInBootstrapWeakDistribution μ Pstar TbetaStar
        (multivariateGaussian (0 : EuclideanSpace ℝ k) Vβ)
        (fun z : EuclideanSpace ℝ k => z))
    (hPstar : ∀ n ω, IsFiniteMeasure (Pstar n ω))
    (hTbetaStar : ∀ n ω, Measurable (TbetaStar n ω))
    (hfrontier : ∀ x : q → ℝ,
      ContinuousAt
          (fun y =>
            vectorCDF
              (multivariateGaussian (0 : EuclideanSpace ℝ q) (Rᵀ * Vβ * R))
              (fun z : EuclideanSpace ℝ q => (z : q → ℝ)) y) x →
        ((multivariateGaussian (0 : EuclideanSpace ℝ q) (Rᵀ * Vβ * R)).map
            (fun z : EuclideanSpace ℝ q => (z : q → ℝ)))
          (frontier {z : q → ℝ | coordinateLE z x}) = 0) :
    TendstoInBootstrapDistribution μ Pstar
      (fun n ω ωs =>
        ((matrixContinuousLinearMap Rᵀ (TbetaStar n ω ωs) :
          EuclideanSpace ℝ q) : q → ℝ))
      (multivariateGaussian (0 : EuclideanSpace ℝ q) (Rᵀ * Vβ * R))
      (fun z : EuclideanSpace ℝ q => (z : q → ℝ)) := by
  simpa [Matrix.transpose_transpose] using
    chapter10_bootstrap_delta_method_gaussian_distribution
      (μ := μ) (Pstar := Pstar) (Tstar := TbetaStar) (V := Vβ)
      (G := Rᵀ) hVβ hβ hPstar hTbetaStar
      (by simpa [Matrix.transpose_transpose] using hfrontier)

/-- Hansen Theorem 10.18, regression Gaussian CDF wrapper with positive
definite transformed covariance.

When `R' Vβ R` is positive definite, the transformed Gaussian lower-orthant
null-frontier premise in `chapter10_bootstrap_regression_theta_gaussian_distribution`
is automatic. -/
theorem chapter10_bootstrap_regression_theta_gaussian_distribution_posDef
    {k q : Type*} [Fintype k] [Fintype q] [DecidableEq k] [DecidableEq q]
    {Pstar : ℕ → Ω → Measure Ωs}
    {TbetaStar : ℕ → Ω → Ωs → EuclideanSpace ℝ k}
    {Vβ : Matrix k k ℝ} (R : Matrix k q ℝ)
    (hVβ : Vβ.PosSemidef)
    (hRVR : (Rᵀ * Vβ * R).PosDef)
    (hβ :
      TendstoInBootstrapWeakDistribution μ Pstar TbetaStar
        (multivariateGaussian (0 : EuclideanSpace ℝ k) Vβ)
        (fun z : EuclideanSpace ℝ k => z))
    (hPstar : ∀ n ω, IsFiniteMeasure (Pstar n ω))
    (hTbetaStar : ∀ n ω, Measurable (TbetaStar n ω)) :
    TendstoInBootstrapDistribution μ Pstar
      (fun n ω ωs =>
        ((matrixContinuousLinearMap Rᵀ (TbetaStar n ω ωs) :
          EuclideanSpace ℝ q) : q → ℝ))
      (multivariateGaussian (0 : EuclideanSpace ℝ q) (Rᵀ * Vβ * R))
      (fun z : EuclideanSpace ℝ q => (z : q → ℝ)) :=
  chapter10_bootstrap_regression_theta_gaussian_distribution
    (μ := μ) (Pstar := Pstar) (TbetaStar := TbetaStar) (Vβ := Vβ)
    R hVβ hβ hPstar hTbetaStar
    (fun x _hx => multivariateGaussian_coordinateLE_frontier_null_of_posDef hRVR x)

set_option linter.style.longLine false

/-- Hansen Theorem 10.18 regression Gaussian wrapper under the Chapter 7
robust feasible HC condition package.

This discharges positive semidefiniteness of the heteroskedastic coefficient
covariance from `RobustFeasibleHCMomentConditions`.  The coefficient-level
bootstrap CLT remains the model-specific premise. -/
theorem
chapter10_bootstrap_regression_theta_gaussian_of_robustFeasibleHCMomentConditions
    [IsProbabilityMeasure μ]
    {k q : Type*} [Fintype k] [Fintype q] [DecidableEq k] [DecidableEq q]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    {Pstar : ℕ → Ω → Measure Ωs}
    {TbetaStar : ℕ → Ω → Ωs → EuclideanSpace ℝ k}
    (β : k → ℝ) (R : Matrix k q ℝ)
    (hm : RobustFeasibleHCMomentConditions μ X e y β)
    (hβ :
      TendstoInBootstrapWeakDistribution μ Pstar TbetaStar
        (multivariateGaussian (0 : EuclideanSpace ℝ k)
          (heteroAsymCov μ X e))
        (fun z : EuclideanSpace ℝ k => z)) :
    TendstoInBootstrapWeakDistribution μ Pstar
      (fun n ω ωs => matrixContinuousLinearMap Rᵀ (TbetaStar n ω ωs))
      (multivariateGaussian (0 : EuclideanSpace ℝ q)
        (Rᵀ * heteroAsymCov μ X e * R))
      (fun z : EuclideanSpace ℝ q => z) :=
  chapter10_bootstrap_regression_theta_gaussian
    (μ := μ) (Pstar := Pstar) (TbetaStar := TbetaStar)
    (Vβ := heteroAsymCov μ X e) R
    (heteroAsymCov_posSemidef_of_scoreCLTConditions
      (μ := μ) (X := X) (e := e) hm.toScoreCLTConditions)
    hβ

/-- Hansen Definition 10.2 face of
`chapter10_bootstrap_regression_theta_gaussian_of_robustFeasibleHCMomentConditions`.

The transformed Gaussian frontier premise is left explicit; use the `_posDef`
variant when `R' Vβ R` is positive definite. -/
theorem
chapter10_bootstrap_regression_theta_gaussian_distribution_of_robustFeasibleHCMomentConditions
    [IsProbabilityMeasure μ]
    {k q : Type*} [Fintype k] [Fintype q] [DecidableEq k] [DecidableEq q]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    {Pstar : ℕ → Ω → Measure Ωs}
    {TbetaStar : ℕ → Ω → Ωs → EuclideanSpace ℝ k}
    (β : k → ℝ) (R : Matrix k q ℝ)
    (hm : RobustFeasibleHCMomentConditions μ X e y β)
    (hβ :
      TendstoInBootstrapWeakDistribution μ Pstar TbetaStar
        (multivariateGaussian (0 : EuclideanSpace ℝ k)
          (heteroAsymCov μ X e))
        (fun z : EuclideanSpace ℝ k => z))
    (hPstar : ∀ n ω, IsFiniteMeasure (Pstar n ω))
    (hTbetaStar : ∀ n ω, Measurable (TbetaStar n ω))
    (hfrontier : ∀ x : q → ℝ,
      ContinuousAt
          (fun y =>
            vectorCDF
              (multivariateGaussian (0 : EuclideanSpace ℝ q)
                (Rᵀ * heteroAsymCov μ X e * R))
              (fun z : EuclideanSpace ℝ q => (z : q → ℝ)) y) x →
        ((multivariateGaussian (0 : EuclideanSpace ℝ q)
            (Rᵀ * heteroAsymCov μ X e * R)).map
            (fun z : EuclideanSpace ℝ q => (z : q → ℝ)))
          (frontier {z : q → ℝ | coordinateLE z x}) = 0) :
    TendstoInBootstrapDistribution μ Pstar
      (fun n ω ωs =>
        ((matrixContinuousLinearMap Rᵀ (TbetaStar n ω ωs) :
          EuclideanSpace ℝ q) : q → ℝ))
      (multivariateGaussian (0 : EuclideanSpace ℝ q)
        (Rᵀ * heteroAsymCov μ X e * R))
      (fun z : EuclideanSpace ℝ q => (z : q → ℝ)) :=
  chapter10_bootstrap_regression_theta_gaussian_distribution
    (μ := μ) (Pstar := Pstar) (TbetaStar := TbetaStar)
    (Vβ := heteroAsymCov μ X e) R
    (heteroAsymCov_posSemidef_of_scoreCLTConditions
      (μ := μ) (X := X) (e := e) hm.toScoreCLTConditions)
    hβ hPstar hTbetaStar hfrontier

/-- Positive-definite transformed-covariance version of
`chapter10_bootstrap_regression_theta_gaussian_distribution_of_robustFeasibleHCMomentConditions`. -/
theorem
chapter10_bootstrap_regression_theta_gaussian_distribution_posDef_of_robustFeasibleHCMomentConditions
    [IsProbabilityMeasure μ]
    {k q : Type*} [Fintype k] [Fintype q] [DecidableEq k] [DecidableEq q]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    {Pstar : ℕ → Ω → Measure Ωs}
    {TbetaStar : ℕ → Ω → Ωs → EuclideanSpace ℝ k}
    (β : k → ℝ) (R : Matrix k q ℝ)
    (hm : RobustFeasibleHCMomentConditions μ X e y β)
    (hRVR : (Rᵀ * heteroAsymCov μ X e * R).PosDef)
    (hβ :
      TendstoInBootstrapWeakDistribution μ Pstar TbetaStar
        (multivariateGaussian (0 : EuclideanSpace ℝ k)
          (heteroAsymCov μ X e))
        (fun z : EuclideanSpace ℝ k => z))
    (hPstar : ∀ n ω, IsFiniteMeasure (Pstar n ω))
    (hTbetaStar : ∀ n ω, Measurable (TbetaStar n ω)) :
    TendstoInBootstrapDistribution μ Pstar
      (fun n ω ωs =>
        ((matrixContinuousLinearMap Rᵀ (TbetaStar n ω ωs) :
          EuclideanSpace ℝ q) : q → ℝ))
      (multivariateGaussian (0 : EuclideanSpace ℝ q)
        (Rᵀ * heteroAsymCov μ X e * R))
      (fun z : EuclideanSpace ℝ q => (z : q → ℝ)) :=
  chapter10_bootstrap_regression_theta_gaussian_distribution_posDef
    (μ := μ) (Pstar := Pstar) (TbetaStar := TbetaStar)
    (Vβ := heteroAsymCov μ X e) R
    (heteroAsymCov_posSemidef_of_scoreCLTConditions
      (μ := μ) (X := X) (e := e) hm.toScoreCLTConditions)
    hRVR hβ hPstar hTbetaStar

/-- Indexed Hansen Theorem 10.18, nonlinear-regression delta-method Gaussian
wrapper for sample-size-dependent bootstrap spaces. -/
theorem chapter10_indexed_bootstrap_regression_theta_gaussian
    {k q : Type*} [Fintype k] [Fintype q] [DecidableEq k] [DecidableEq q]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {TbetaStar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ k}
    {Vβ : Matrix k k ℝ} (R : Matrix k q ℝ)
    (hVβ : Vβ.PosSemidef)
    (hβ :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar TbetaStar
        (multivariateGaussian (0 : EuclideanSpace ℝ k) Vβ)
        (fun z : EuclideanSpace ℝ k => z)) :
    TendstoInBootstrapWeakDistributionIndexed μ Pstar
      (fun n ω ωs => matrixContinuousLinearMap Rᵀ (TbetaStar n ω ωs))
      (multivariateGaussian (0 : EuclideanSpace ℝ q) (Rᵀ * Vβ * R))
      (fun z : EuclideanSpace ℝ q => z) := by
  simpa [Matrix.transpose_transpose] using
    chapter10_indexed_bootstrap_delta_method_gaussian
      (μ := μ) (Pstar := Pstar) (Tstar := TbetaStar) (V := Vβ)
      (G := Rᵀ) hVβ hβ

/-- Hansen Theorem 10.18 transformed-regression ordinary-bootstrap CLT from the
linearized score route.

This composes the concrete ordinary bootstrap score CLT with the population
Gram inverse and the regression delta map `Rᵀ`, yielding the transformed
statistic covariance `Rᵀ Vβ R` with `Vβ = heteroAsymCov`. -/
theorem chapter10_indexed_bootstrap_regression_theta_gaussian_finSucc_linearizedScore
    [IsProbabilityMeasure μ]
    {k q : Type*} [Fintype k] [Fintype q] [DecidableEq k] [DecidableEq q]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ}
    (R : Matrix k q ℝ)
    (h : ScoreCLTConditions μ X e)
    (hΩ : (scoreCovMat μ X e).PosDef) :
    TendstoInBootstrapWeakDistributionIndexed μ
      (fun n _ =>
        (ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))))
      (fun n ω ωs =>
        matrixContinuousLinearMap Rᵀ
          (regressionLinearizedScoreFinSucc μ X e n ω ωs))
      (multivariateGaussian (0 : EuclideanSpace ℝ q)
        (Rᵀ * heteroAsymCov μ X e * R))
      (fun z : EuclideanSpace ℝ q => z) :=
  chapter10_indexed_bootstrap_regression_theta_gaussian
    (μ := μ)
    (Pstar := fun n _ =>
      (ProbabilityTheory.uniformOn
        (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
          Measure (Fin (n + 1) → Fin (n + 1))))
    (TbetaStar := fun n ω ωs =>
      regressionLinearizedScoreFinSucc μ X e n ω ωs)
    (Vβ := heteroAsymCov μ X e) R
    (heteroAsymCov_posSemidef_of_scoreCLTConditions
      (μ := μ) (X := X) (e := e) h)
    (chapter10_indexed_bootstrap_regression_linearizedScore_gaussian_finSucc_resampleMean
      (μ := μ) (X := X) (e := e) h hΩ)

/-- Hansen Definition 10.2 face of the ordinary-bootstrap linearized
regression score route.

This is the CDF counterpart of
`chapter10_indexed_bootstrap_regression_theta_gaussian_finSucc_linearizedScore`:
the finite ordinary-bootstrap score CLT is mapped through the population Gram
inverse and `Rᵀ`, then converted to coordinate CDF convergence at transformed
Gaussian continuity points. -/
theorem
    chapter10_indexed_bootstrap_regression_theta_gaussian_distribution_finSucc_linearizedScore
    [IsProbabilityMeasure μ]
    {k q : Type*} [Fintype k] [Fintype q] [DecidableEq k] [DecidableEq q]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ}
    (R : Matrix k q ℝ)
    (h : ScoreCLTConditions μ X e)
    (hΩ : (scoreCovMat μ X e).PosDef)
    (hfrontier : ∀ x : q → ℝ,
      ContinuousAt
          (fun y =>
            vectorCDF
              (multivariateGaussian (0 : EuclideanSpace ℝ q)
                (Rᵀ * heteroAsymCov μ X e * R))
              (fun z : EuclideanSpace ℝ q => (z : q → ℝ)) y) x →
        ((multivariateGaussian (0 : EuclideanSpace ℝ q)
            (Rᵀ * heteroAsymCov μ X e * R)).map
            (fun z : EuclideanSpace ℝ q => (z : q → ℝ)))
          (frontier {z : q → ℝ | coordinateLE z x}) = 0) :
    TendstoInBootstrapDistributionIndexed μ
      (fun n _ =>
        (ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))))
      (fun n ω ωs =>
        ((matrixContinuousLinearMap Rᵀ
          (regressionLinearizedScoreFinSucc μ X e n ω ωs) :
            EuclideanSpace ℝ q) : q → ℝ))
      (multivariateGaussian (0 : EuclideanSpace ℝ q)
        (Rᵀ * heteroAsymCov μ X e * R))
      (fun z : EuclideanSpace ℝ q => (z : q → ℝ)) := by
  simpa [Matrix.transpose_transpose] using
    chapter10_indexed_bootstrap_delta_method_gaussian_distribution
      (μ := μ)
      (Pstar := fun n _ =>
        (ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))))
      (Tstar := fun n ω ωs =>
        regressionLinearizedScoreFinSucc μ X e n ω ωs)
      (V := heteroAsymCov μ X e) (G := Rᵀ)
      (heteroAsymCov_posSemidef_of_scoreCLTConditions
        (μ := μ) (X := X) (e := e) h)
      (chapter10_indexed_bootstrap_regression_linearizedScore_gaussian_finSucc_resampleMean
        (μ := μ) (X := X) (e := e) h hΩ)
      (fun n ω => inferInstance) (fun n ω => measurable_of_finite _)
      (by simpa [Matrix.transpose_transpose] using hfrontier)

/-- Positive-definite transformed-covariance CDF face of the
ordinary-bootstrap linearized regression score route. -/
theorem
    chapter10_indexed_bootstrap_regression_theta_gaussian_distribution_posDef_finSucc_linearizedScore
    [IsProbabilityMeasure μ]
    {k q : Type*} [Fintype k] [Fintype q] [DecidableEq k] [DecidableEq q]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ}
    (R : Matrix k q ℝ)
    (h : ScoreCLTConditions μ X e)
    (hΩ : (scoreCovMat μ X e).PosDef)
    (hRVR : (Rᵀ * heteroAsymCov μ X e * R).PosDef) :
    TendstoInBootstrapDistributionIndexed μ
      (fun n _ =>
        (ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))))
      (fun n ω ωs =>
        ((matrixContinuousLinearMap Rᵀ
          (regressionLinearizedScoreFinSucc μ X e n ω ωs) :
            EuclideanSpace ℝ q) : q → ℝ))
      (multivariateGaussian (0 : EuclideanSpace ℝ q)
        (Rᵀ * heteroAsymCov μ X e * R))
      (fun z : EuclideanSpace ℝ q => (z : q → ℝ)) :=
  chapter10_indexed_bootstrap_regression_theta_gaussian_distribution_finSucc_linearizedScore
    (μ := μ) R h hΩ
    (fun x _hx => multivariateGaussian_coordinateLE_frontier_null_of_posDef hRVR x)

/-- Hansen Theorem 10.18 transformed-regression ordinary-bootstrap CLT after
nonlinear coefficient inversion.

This composes the nonlinear coefficient transfer from
`regressionLinearizedScoreFinSucc` with the regression delta map `Rᵀ`.  The
model-specific OLS work is exactly the conditional closeness and compact-tail
premises for the concrete coefficient statistic `TbetaStar`. -/
theorem
    chapter10_indexed_bootstrap_regression_theta_gaussian_finSucc_of_linearizedScore_tight
    [IsProbabilityMeasure μ]
    {k q : Type*} [Fintype k] [Fintype q] [DecidableEq k] [DecidableEq q]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ}
    {TbetaStar :
      ∀ n, Ω → (Fin (n + 1) → Fin (n + 1)) → EuclideanSpace ℝ k}
    (R : Matrix k q ℝ)
    (h : ScoreCLTConditions μ X e)
    (hΩ : (scoreCovMat μ X e).PosDef)
    (hTbetaStar : ∀ n ω, Measurable (TbetaStar n ω))
    (hTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set (EuclideanSpace ℝ k), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω =>
            ((ProbabilityTheory.uniformOn
              (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                Measure (Fin (n + 1) → Fin (n + 1)))).real
              {ωs | regressionLinearizedScoreFinSucc μ X e n ω ωs ∉ K})
          atTop (fun _ => 0) ∧
        TendstoInMeasure μ
          (fun n ω =>
            ((ProbabilityTheory.uniformOn
              (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                Measure (Fin (n + 1) → Fin (n + 1)))).real
              {ωs | TbetaStar n ω ωs ∉ K})
          atTop (fun _ => 0))
    (hclose : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          ((ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
              Measure (Fin (n + 1) → Fin (n + 1)))).real
            {ωs |
              δ ≤ dist (TbetaStar n ω ωs)
                (regressionLinearizedScoreFinSucc μ X e n ω ωs)})
        atTop (fun _ => 0)) :
    TendstoInBootstrapWeakDistributionIndexed μ
      (fun n _ =>
        (ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))))
      (fun n ω ωs => matrixContinuousLinearMap Rᵀ (TbetaStar n ω ωs))
      (multivariateGaussian (0 : EuclideanSpace ℝ q)
        (Rᵀ * heteroAsymCov μ X e * R))
      (fun z : EuclideanSpace ℝ q => z) :=
  chapter10_indexed_bootstrap_regression_theta_gaussian
    (μ := μ)
    (Pstar := fun n _ =>
      (ProbabilityTheory.uniformOn
        (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
          Measure (Fin (n + 1) → Fin (n + 1))))
    (TbetaStar := TbetaStar)
    (Vβ := heteroAsymCov μ X e) R
    (heteroAsymCov_posSemidef_of_scoreCLTConditions
      (μ := μ) (X := X) (e := e) h)
    (chapter10_indexed_bootstrap_regression_beta_gaussian_finSucc_of_linearizedScore_tight
      (μ := μ) (X := X) (e := e) h hΩ hTbetaStar hTail hclose)

set_option linter.style.longLine false in
/-- Concrete transformed ordinary-bootstrap OLS statistic version of Hansen
Theorem 10.18. -/
theorem
    chapter10_indexed_bootstrap_regression_theta_gaussian_finSucc_olsBetaOrZero_of_linearizedScore_tight
    [IsProbabilityMeasure μ]
    {k q : Type*} [Fintype k] [Fintype q] [DecidableEq k] [DecidableEq q]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    (R : Matrix k q ℝ)
    (h : ScoreCLTConditions μ X e)
    (hΩ : (scoreCovMat μ X e).PosDef)
    (hTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set (EuclideanSpace ℝ k), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω =>
            ((ProbabilityTheory.uniformOn
              (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                Measure (Fin (n + 1) → Fin (n + 1)))).real
              {ωs | regressionLinearizedScoreFinSucc μ X e n ω ωs ∉ K})
          atTop (fun _ => 0) ∧
        TendstoInMeasure μ
          (fun n ω =>
            ((ProbabilityTheory.uniformOn
              (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                Measure (Fin (n + 1) → Fin (n + 1)))).real
              {ωs | regressionBootstrapBetaStatisticFinSucc X y n ω ωs ∉ K})
          atTop (fun _ => 0))
    (hclose : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          ((ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
              Measure (Fin (n + 1) → Fin (n + 1)))).real
            {ωs |
              δ ≤ dist (regressionBootstrapBetaStatisticFinSucc X y n ω ωs)
                (regressionLinearizedScoreFinSucc μ X e n ω ωs)})
        atTop (fun _ => 0)) :
    TendstoInBootstrapWeakDistributionIndexed μ
      (fun n _ =>
        (ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))))
      (fun n ω ωs => regressionBootstrapThetaStatisticFinSucc R X y n ω ωs)
      (multivariateGaussian (0 : EuclideanSpace ℝ q)
        (Rᵀ * heteroAsymCov μ X e * R))
      (fun z : EuclideanSpace ℝ q => z) := by
  simpa [regressionBootstrapThetaStatisticFinSucc] using
    chapter10_indexed_bootstrap_regression_theta_gaussian_finSucc_of_linearizedScore_tight
      (μ := μ) (X := X) (e := e)
      (TbetaStar := fun n ω ωs =>
        regressionBootstrapBetaStatisticFinSucc X y n ω ωs)
      R h hΩ (fun _ _ => measurable_of_finite _) hTail hclose

set_option linter.style.longLine false in
/-- Robust-feasible HC specialization of the concrete transformed
ordinary-bootstrap OLS statistic route. -/
theorem
    chapter10_indexed_bootstrap_regression_theta_gaussian_finSucc_olsBetaOrZero_of_linearizedScore_tight_of_robustFeasibleHCMomentConditions
    [IsProbabilityMeasure μ]
    {k q : Type*} [Fintype k] [Fintype q] [DecidableEq k] [DecidableEq q]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    (β : k → ℝ) (R : Matrix k q ℝ)
    (hm : RobustFeasibleHCMomentConditions μ X e y β)
    (hΩ : (scoreCovMat μ X e).PosDef)
    (hTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set (EuclideanSpace ℝ k), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω =>
            ((ProbabilityTheory.uniformOn
              (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                Measure (Fin (n + 1) → Fin (n + 1)))).real
              {ωs | regressionLinearizedScoreFinSucc μ X e n ω ωs ∉ K})
          atTop (fun _ => 0) ∧
        TendstoInMeasure μ
          (fun n ω =>
            ((ProbabilityTheory.uniformOn
              (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                Measure (Fin (n + 1) → Fin (n + 1)))).real
              {ωs | regressionBootstrapBetaStatisticFinSucc X y n ω ωs ∉ K})
          atTop (fun _ => 0))
    (hclose : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          ((ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
              Measure (Fin (n + 1) → Fin (n + 1)))).real
            {ωs |
              δ ≤ dist (regressionBootstrapBetaStatisticFinSucc X y n ω ωs)
                (regressionLinearizedScoreFinSucc μ X e n ω ωs)})
        atTop (fun _ => 0)) :
    TendstoInBootstrapWeakDistributionIndexed μ
      (fun n _ =>
        (ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))))
      (fun n ω ωs => regressionBootstrapThetaStatisticFinSucc R X y n ω ωs)
      (multivariateGaussian (0 : EuclideanSpace ℝ q)
        (Rᵀ * heteroAsymCov μ X e * R))
      (fun z : EuclideanSpace ℝ q => z) :=
  chapter10_indexed_bootstrap_regression_theta_gaussian_finSucc_olsBetaOrZero_of_linearizedScore_tight
    (μ := μ) (X := X) (e := e) (y := y)
    R hm.toScoreCLTConditions hΩ hTail hclose

set_option linter.style.longLine false in
/-- Concrete transformed ordinary-bootstrap OLS statistic transfer from the
explicit finite OLS-linearization gap envelope.

This is the transformed-statistic counterpart of
`chapter10_indexed_bootstrap_regression_beta_gaussian_finSucc_olsBetaOrZero_of_gapEnvelope_tight`. -/
theorem
    chapter10_indexed_bootstrap_regression_theta_gaussian_finSucc_olsBetaOrZero_of_gapEnvelope_tight
    [IsProbabilityMeasure μ]
    {k q : Type*} [Fintype k] [Fintype q] [DecidableEq k] [DecidableEq q]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    (β : k → ℝ) (R : Matrix k q ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (h : ScoreCLTConditions μ X e)
    (hΩ : (scoreCovMat μ X e).PosDef)
    (hTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set (EuclideanSpace ℝ k), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω =>
            ((ProbabilityTheory.uniformOn
              (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                Measure (Fin (n + 1) → Fin (n + 1)))).real
              {ωs | regressionLinearizedScoreFinSucc μ X e n ω ωs ∉ K})
          atTop (fun _ => 0) ∧
        TendstoInMeasure μ
          (fun n ω =>
            ((ProbabilityTheory.uniformOn
              (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                Measure (Fin (n + 1) → Fin (n + 1)))).real
              {ωs | regressionBootstrapBetaStatisticFinSucc X y n ω ωs ∉ K})
          atTop (fun _ => 0))
    (hGapTail : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          ((ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
              Measure (Fin (n + 1) → Fin (n + 1)))).real
            {ωs |
              δ ≤ regressionBootstrapBetaLinearizedGapEnvelopeFinSucc
                μ X e β n ω ωs})
        atTop (fun _ => 0)) :
    TendstoInBootstrapWeakDistributionIndexed μ
      (fun n _ =>
        (ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))))
      (fun n ω ωs => regressionBootstrapThetaStatisticFinSucc R X y n ω ωs)
      (multivariateGaussian (0 : EuclideanSpace ℝ q)
        (Rᵀ * heteroAsymCov μ X e * R))
      (fun z : EuclideanSpace ℝ q => z) := by
  simpa [regressionBootstrapThetaStatisticFinSucc] using
    chapter10_indexed_bootstrap_regression_theta_gaussian
      (μ := μ)
      (Pstar := fun n _ =>
        (ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))))
      (TbetaStar := fun n ω ωs =>
        regressionBootstrapBetaStatisticFinSucc X y n ω ωs)
      (Vβ := heteroAsymCov μ X e) R
      (heteroAsymCov_posSemidef_of_scoreCLTConditions
        (μ := μ) (X := X) (e := e) h)
      (chapter10_indexed_bootstrap_regression_beta_gaussian_finSucc_olsBetaOrZero_of_gapEnvelope_tight
        (μ := μ) (X := X) (e := e) (y := y)
        β hmodel h hΩ hTail hGapTail)

set_option linter.style.longLine false in
/-- Robust-feasible HC specialization of the transformed ordinary-bootstrap
OLS gap-envelope transfer. -/
theorem
    chapter10_indexed_bootstrap_regression_theta_gaussian_finSucc_olsBetaOrZero_of_gapEnvelope_tight_of_robustFeasibleHCMomentConditions
    [IsProbabilityMeasure μ]
    {k q : Type*} [Fintype k] [Fintype q] [DecidableEq k] [DecidableEq q]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    (β : k → ℝ) (R : Matrix k q ℝ)
    (hm : RobustFeasibleHCMomentConditions μ X e y β)
    (hΩ : (scoreCovMat μ X e).PosDef)
    (hTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set (EuclideanSpace ℝ k), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω =>
            ((ProbabilityTheory.uniformOn
              (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                Measure (Fin (n + 1) → Fin (n + 1)))).real
              {ωs | regressionLinearizedScoreFinSucc μ X e n ω ωs ∉ K})
          atTop (fun _ => 0) ∧
        TendstoInMeasure μ
          (fun n ω =>
            ((ProbabilityTheory.uniformOn
              (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                Measure (Fin (n + 1) → Fin (n + 1)))).real
              {ωs | regressionBootstrapBetaStatisticFinSucc X y n ω ωs ∉ K})
          atTop (fun _ => 0))
    (hGapTail : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          ((ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
              Measure (Fin (n + 1) → Fin (n + 1)))).real
            {ωs |
              δ ≤ regressionBootstrapBetaLinearizedGapEnvelopeFinSucc
                μ X e β n ω ωs})
        atTop (fun _ => 0)) :
    TendstoInBootstrapWeakDistributionIndexed μ
      (fun n _ =>
        (ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))))
      (fun n ω ωs => regressionBootstrapThetaStatisticFinSucc R X y n ω ωs)
      (multivariateGaussian (0 : EuclideanSpace ℝ q)
        (Rᵀ * heteroAsymCov μ X e * R))
      (fun z : EuclideanSpace ℝ q => z) :=
  chapter10_indexed_bootstrap_regression_theta_gaussian_finSucc_olsBetaOrZero_of_gapEnvelope_tight
    (μ := μ) (X := X) (e := e) (y := y)
    β R hm.model hm.toScoreCLTConditions hΩ hTail hGapTail

set_option linter.style.longLine false in
/-- Concrete transformed ordinary-bootstrap OLS gap-envelope transfer with
coefficient compact-tail control discharged by deterministic eventual norm
bounds. -/
theorem
    chapter10_indexed_bootstrap_regression_theta_gaussian_finSucc_olsBetaOrZero_of_gapEnvelope_bounds
    [IsProbabilityMeasure μ]
    {k q : Type*} [Fintype k] [Fintype q] [DecidableEq k] [DecidableEq q]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    {Clin Cbeta : ℝ}
    (β : k → ℝ) (R : Matrix k q ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (h : ScoreCLTConditions μ X e)
    (hΩ : (scoreCovMat μ X e).PosDef)
    (hLinBound : ∀ᶠ n in atTop,
      ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
        ‖regressionLinearizedScoreFinSucc μ X e n ω ωs‖ ≤ Clin)
    (hBetaBound : ∀ᶠ n in atTop,
      ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
        ‖regressionBootstrapBetaStatisticFinSucc X y n ω ωs‖ ≤ Cbeta)
    (hGapTail : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          ((ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
              Measure (Fin (n + 1) → Fin (n + 1)))).real
            {ωs |
              δ ≤ regressionBootstrapBetaLinearizedGapEnvelopeFinSucc
                μ X e β n ω ωs})
        atTop (fun _ => 0)) :
    TendstoInBootstrapWeakDistributionIndexed μ
      (fun n _ =>
        (ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))))
      (fun n ω ωs => regressionBootstrapThetaStatisticFinSucc R X y n ω ωs)
      (multivariateGaussian (0 : EuclideanSpace ℝ q)
        (Rᵀ * heteroAsymCov μ X e * R))
      (fun z : EuclideanSpace ℝ q => z) := by
  simpa [regressionBootstrapThetaStatisticFinSucc] using
    chapter10_indexed_bootstrap_regression_theta_gaussian
      (μ := μ)
      (Pstar := fun n _ =>
        (ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))))
      (TbetaStar := fun n ω ωs =>
        regressionBootstrapBetaStatisticFinSucc X y n ω ωs)
      (Vβ := heteroAsymCov μ X e) R
      (heteroAsymCov_posSemidef_of_scoreCLTConditions
        (μ := μ) (X := X) (e := e) h)
      (chapter10_indexed_bootstrap_regression_beta_gaussian_finSucc_olsBetaOrZero_of_gapEnvelope_bounds
        (μ := μ) (X := X) (e := e) (y := y)
        β hmodel h hΩ hLinBound hBetaBound hGapTail)

set_option linter.style.longLine false in
/-- Robust-feasible HC specialization of the bounded transformed
ordinary-bootstrap OLS gap-envelope transfer. -/
theorem
    chapter10_indexed_bootstrap_regression_theta_gaussian_finSucc_olsBetaOrZero_of_gapEnvelope_bounds_of_robustFeasibleHCMomentConditions
    [IsProbabilityMeasure μ]
    {k q : Type*} [Fintype k] [Fintype q] [DecidableEq k] [DecidableEq q]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    {Clin Cbeta : ℝ}
    (β : k → ℝ) (R : Matrix k q ℝ)
    (hm : RobustFeasibleHCMomentConditions μ X e y β)
    (hΩ : (scoreCovMat μ X e).PosDef)
    (hLinBound : ∀ᶠ n in atTop,
      ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
        ‖regressionLinearizedScoreFinSucc μ X e n ω ωs‖ ≤ Clin)
    (hBetaBound : ∀ᶠ n in atTop,
      ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
        ‖regressionBootstrapBetaStatisticFinSucc X y n ω ωs‖ ≤ Cbeta)
    (hGapTail : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          ((ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
              Measure (Fin (n + 1) → Fin (n + 1)))).real
            {ωs |
              δ ≤ regressionBootstrapBetaLinearizedGapEnvelopeFinSucc
                μ X e β n ω ωs})
        atTop (fun _ => 0)) :
    TendstoInBootstrapWeakDistributionIndexed μ
      (fun n _ =>
        (ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))))
      (fun n ω ωs => regressionBootstrapThetaStatisticFinSucc R X y n ω ωs)
      (multivariateGaussian (0 : EuclideanSpace ℝ q)
        (Rᵀ * heteroAsymCov μ X e * R))
      (fun z : EuclideanSpace ℝ q => z) :=
  chapter10_indexed_bootstrap_regression_theta_gaussian_finSucc_olsBetaOrZero_of_gapEnvelope_bounds
    (μ := μ) (X := X) (e := e) (y := y)
    β R hm.model hm.toScoreCLTConditions hΩ hLinBound hBetaBound hGapTail

private theorem regressionBootstrapLinearRestrictionStatisticFinSucc_tendsto_of_theta
    {k : Type*} [Fintype k] [DecidableEq k]
    {X : ℕ → Ω → (k → ℝ)} {y : ℕ → Ω → ℝ}
    (R : Matrix Unit k ℝ)
    {Pstar : ∀ n, Ω → Measure (Fin (n + 1) → Fin (n + 1))}
    {ν : Measure (EuclideanSpace ℝ Unit)}
    (hθ :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar
        (fun n ω ωs => regressionBootstrapThetaStatisticFinSucc Rᵀ X y n ω ωs)
        ν (fun z : EuclideanSpace ℝ Unit => z)) :
    TendstoInBootstrapWeakDistributionIndexed μ Pstar
      (fun n ω ωs => regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs)
      ν (fun z : EuclideanSpace ℝ Unit => (z : Unit → ℝ) ()) := by
  have hcoord :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar
        (fun n ω ωs =>
          ((regressionBootstrapThetaStatisticFinSucc Rᵀ X y n ω ωs :
            EuclideanSpace ℝ Unit) : Unit → ℝ) ())
        ν (fun z : EuclideanSpace ℝ Unit => (z : Unit → ℝ) ()) :=
    chapter10_indexed_bootstrap_continuous_mapping_distribution
      (μ := μ) (Pstar := Pstar)
      (Zstar := fun n ω ωs => regressionBootstrapThetaStatisticFinSucc Rᵀ X y n ω ωs)
      (ν := ν) (Z := fun z : EuclideanSpace ℝ Unit => z)
      (g := fun z : EuclideanSpace ℝ Unit => (z : Unit → ℝ) ()) hθ
      (by
        simpa using
          ((continuous_apply ()).comp
            (PiLp.continuous_ofLp 2 (fun _ : Unit => ℝ))))
  refine hcoord.congr ?_ ?_
  · intro n ω ωs
    exact (regressionBootstrapLinearRestrictionStatisticFinSucc_eq_theta_apply
      R X y n ω ωs).symm
  intro z
  rfl

set_option linter.style.longLine false in
/-- Scalar one-row ordinary-bootstrap OLS restriction transfer from the
explicit finite OLS-linearization gap envelope.

This is the `Unit`-coordinate face of the transformed-statistic theorem, in
the Chapter 7 scalar restriction notation
`sqrt(n+1) (R βhat* - R βhat)`. -/
theorem
    chapter10_indexed_bootstrap_regression_linearRestriction_gaussian_finSucc_olsBetaOrZero_of_gapEnvelope_tight
    [IsProbabilityMeasure μ]
    {k : Type*} [Fintype k] [DecidableEq k]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    (β : k → ℝ) (R : Matrix Unit k ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (h : ScoreCLTConditions μ X e)
    (hΩ : (scoreCovMat μ X e).PosDef)
    (hTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set (EuclideanSpace ℝ k), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω =>
            ((ProbabilityTheory.uniformOn
              (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                Measure (Fin (n + 1) → Fin (n + 1)))).real
              {ωs | regressionLinearizedScoreFinSucc μ X e n ω ωs ∉ K})
          atTop (fun _ => 0) ∧
        TendstoInMeasure μ
          (fun n ω =>
            ((ProbabilityTheory.uniformOn
              (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                Measure (Fin (n + 1) → Fin (n + 1)))).real
              {ωs | regressionBootstrapBetaStatisticFinSucc X y n ω ωs ∉ K})
          atTop (fun _ => 0))
    (hGapTail : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          ((ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
              Measure (Fin (n + 1) → Fin (n + 1)))).real
            {ωs |
              δ ≤ regressionBootstrapBetaLinearizedGapEnvelopeFinSucc
                μ X e β n ω ωs})
        atTop (fun _ => 0)) :
    TendstoInBootstrapWeakDistributionIndexed μ
      (fun n _ =>
        (ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))))
      (fun n ω ωs => regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs)
      (multivariateGaussian (0 : EuclideanSpace ℝ Unit)
        (R * heteroAsymCov μ X e * Rᵀ))
      (fun z : EuclideanSpace ℝ Unit => (z : Unit → ℝ) ()) := by
  have hθ :
      TendstoInBootstrapWeakDistributionIndexed μ
        (fun n _ =>
          (ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
              Measure (Fin (n + 1) → Fin (n + 1))))
        (fun n ω ωs => regressionBootstrapThetaStatisticFinSucc Rᵀ X y n ω ωs)
        (multivariateGaussian (0 : EuclideanSpace ℝ Unit)
          ((Rᵀ)ᵀ * heteroAsymCov μ X e * Rᵀ))
        (fun z : EuclideanSpace ℝ Unit => z) :=
    chapter10_indexed_bootstrap_regression_theta_gaussian_finSucc_olsBetaOrZero_of_gapEnvelope_tight
      (μ := μ) (X := X) (e := e) (y := y)
      β Rᵀ hmodel h hΩ hTail hGapTail
  have hscalar :=
    regressionBootstrapLinearRestrictionStatisticFinSucc_tendsto_of_theta
      (μ := μ) (X := X) (y := y) R hθ
  simpa [Matrix.transpose_transpose] using hscalar

set_option linter.style.longLine false in
/-- Robust-feasible HC specialization of the scalar one-row OLS
gap-envelope transfer. -/
theorem
    chapter10_indexed_bootstrap_regression_linearRestriction_gaussian_finSucc_olsBetaOrZero_of_gapEnvelope_tight_of_robustFeasibleHCMomentConditions
    [IsProbabilityMeasure μ]
    {k : Type*} [Fintype k] [DecidableEq k]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    (β : k → ℝ) (R : Matrix Unit k ℝ)
    (hm : RobustFeasibleHCMomentConditions μ X e y β)
    (hΩ : (scoreCovMat μ X e).PosDef)
    (hTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set (EuclideanSpace ℝ k), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω =>
            ((ProbabilityTheory.uniformOn
              (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                Measure (Fin (n + 1) → Fin (n + 1)))).real
              {ωs | regressionLinearizedScoreFinSucc μ X e n ω ωs ∉ K})
          atTop (fun _ => 0) ∧
        TendstoInMeasure μ
          (fun n ω =>
            ((ProbabilityTheory.uniformOn
              (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                Measure (Fin (n + 1) → Fin (n + 1)))).real
              {ωs | regressionBootstrapBetaStatisticFinSucc X y n ω ωs ∉ K})
          atTop (fun _ => 0))
    (hGapTail : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          ((ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
              Measure (Fin (n + 1) → Fin (n + 1)))).real
            {ωs |
              δ ≤ regressionBootstrapBetaLinearizedGapEnvelopeFinSucc
                μ X e β n ω ωs})
        atTop (fun _ => 0)) :
    TendstoInBootstrapWeakDistributionIndexed μ
      (fun n _ =>
        (ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))))
      (fun n ω ωs => regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs)
      (multivariateGaussian (0 : EuclideanSpace ℝ Unit)
        (R * heteroAsymCov μ X e * Rᵀ))
      (fun z : EuclideanSpace ℝ Unit => (z : Unit → ℝ) ()) :=
  chapter10_indexed_bootstrap_regression_linearRestriction_gaussian_finSucc_olsBetaOrZero_of_gapEnvelope_tight
    (μ := μ) (X := X) (e := e) (y := y)
    β R hm.model hm.toScoreCLTConditions hΩ hTail hGapTail

set_option linter.style.longLine false in
/-- Scalar one-row ordinary-bootstrap OLS restriction transfer with
coefficient compact-tail control discharged by deterministic eventual norm
bounds. -/
theorem
    chapter10_indexed_bootstrap_regression_linearRestriction_gaussian_finSucc_olsBetaOrZero_of_gapEnvelope_bounds
    [IsProbabilityMeasure μ]
    {k : Type*} [Fintype k] [DecidableEq k]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    {Clin Cbeta : ℝ}
    (β : k → ℝ) (R : Matrix Unit k ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (h : ScoreCLTConditions μ X e)
    (hΩ : (scoreCovMat μ X e).PosDef)
    (hLinBound : ∀ᶠ n in atTop,
      ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
        ‖regressionLinearizedScoreFinSucc μ X e n ω ωs‖ ≤ Clin)
    (hBetaBound : ∀ᶠ n in atTop,
      ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
        ‖regressionBootstrapBetaStatisticFinSucc X y n ω ωs‖ ≤ Cbeta)
    (hGapTail : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          ((ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
              Measure (Fin (n + 1) → Fin (n + 1)))).real
            {ωs |
              δ ≤ regressionBootstrapBetaLinearizedGapEnvelopeFinSucc
                μ X e β n ω ωs})
        atTop (fun _ => 0)) :
    TendstoInBootstrapWeakDistributionIndexed μ
      (fun n _ =>
        (ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))))
      (fun n ω ωs => regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs)
      (multivariateGaussian (0 : EuclideanSpace ℝ Unit)
        (R * heteroAsymCov μ X e * Rᵀ))
      (fun z : EuclideanSpace ℝ Unit => (z : Unit → ℝ) ()) := by
  have hθ :
      TendstoInBootstrapWeakDistributionIndexed μ
        (fun n _ =>
          (ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
              Measure (Fin (n + 1) → Fin (n + 1))))
        (fun n ω ωs => regressionBootstrapThetaStatisticFinSucc Rᵀ X y n ω ωs)
        (multivariateGaussian (0 : EuclideanSpace ℝ Unit)
          ((Rᵀ)ᵀ * heteroAsymCov μ X e * Rᵀ))
        (fun z : EuclideanSpace ℝ Unit => z) :=
    chapter10_indexed_bootstrap_regression_theta_gaussian_finSucc_olsBetaOrZero_of_gapEnvelope_bounds
      (μ := μ) (X := X) (e := e) (y := y)
      β Rᵀ hmodel h hΩ hLinBound hBetaBound hGapTail
  have hscalar :=
    regressionBootstrapLinearRestrictionStatisticFinSucc_tendsto_of_theta
      (μ := μ) (X := X) (y := y) R hθ
  simpa [Matrix.transpose_transpose] using hscalar

set_option linter.style.longLine false in
/-- Robust-feasible HC specialization of the bounded scalar one-row OLS
gap-envelope transfer. -/
theorem
    chapter10_indexed_bootstrap_regression_linearRestriction_gaussian_finSucc_olsBetaOrZero_of_gapEnvelope_bounds_of_robustFeasibleHCMomentConditions
    [IsProbabilityMeasure μ]
    {k : Type*} [Fintype k] [DecidableEq k]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    {Clin Cbeta : ℝ}
    (β : k → ℝ) (R : Matrix Unit k ℝ)
    (hm : RobustFeasibleHCMomentConditions μ X e y β)
    (hΩ : (scoreCovMat μ X e).PosDef)
    (hLinBound : ∀ᶠ n in atTop,
      ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
        ‖regressionLinearizedScoreFinSucc μ X e n ω ωs‖ ≤ Clin)
    (hBetaBound : ∀ᶠ n in atTop,
      ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
        ‖regressionBootstrapBetaStatisticFinSucc X y n ω ωs‖ ≤ Cbeta)
    (hGapTail : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          ((ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
              Measure (Fin (n + 1) → Fin (n + 1)))).real
            {ωs |
              δ ≤ regressionBootstrapBetaLinearizedGapEnvelopeFinSucc
                μ X e β n ω ωs})
        atTop (fun _ => 0)) :
    TendstoInBootstrapWeakDistributionIndexed μ
      (fun n _ =>
        (ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))))
      (fun n ω ωs => regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs)
      (multivariateGaussian (0 : EuclideanSpace ℝ Unit)
        (R * heteroAsymCov μ X e * Rᵀ))
      (fun z : EuclideanSpace ℝ Unit => (z : Unit → ℝ) ()) :=
  chapter10_indexed_bootstrap_regression_linearRestriction_gaussian_finSucc_olsBetaOrZero_of_gapEnvelope_bounds
    (μ := μ) (X := X) (e := e) (y := y)
    β R hm.model hm.toScoreCLTConditions hΩ hLinBound hBetaBound hGapTail

private theorem
    regressionBootstrapLinearRestrictionStatisticFinSucc_tendsto_standardNormal_of_gaussian
    [IsProbabilityMeasure μ]
    {k : Type*} [Fintype k] [DecidableEq k]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    (R : Matrix Unit k ℝ)
    (h : ScoreCLTConditions μ X e)
    {Pstar : ∀ n, Ω → Measure (Fin (n + 1) → Fin (n + 1))}
    (hT :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar
        (fun n ω ωs => regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs)
        (multivariateGaussian (0 : EuclideanSpace ℝ Unit)
          (R * heteroAsymCov μ X e * Rᵀ))
        (fun z : EuclideanSpace ℝ Unit => (z : Unit → ℝ) ())) :
    TendstoInBootstrapWeakDistributionIndexed μ Pstar
      (fun n ω ωs => regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs)
      (gaussianReal 0 1)
      (fun z : ℝ => linearRestrictionStdError R (heteroAsymCov μ X e) * z) := by
  let Vβ : Matrix k k ℝ := heteroAsymCov μ X e
  let S : Matrix Unit Unit ℝ := R * Vβ * Rᵀ
  have hVβ : Vβ.PosSemidef := by
    simpa [Vβ] using
      heteroAsymCov_posSemidef_of_scoreCLTConditions
        (μ := μ) (X := X) (e := e) h
  have hS : S.PosSemidef := by
    simpa [S, Vβ, Matrix.conjTranspose] using
      Matrix.PosSemidef.conjTranspose_mul_mul_same hVβ Rᵀ
  have hcoordLaw :
      HasLaw (fun z : EuclideanSpace ℝ Unit => (z : Unit → ℝ) ())
        (gaussianReal 0 (S () ()).toNNReal)
        (multivariateGaussian (0 : EuclideanSpace ℝ Unit) S) := by
    simpa using (multivariateGaussian_eval_hasLaw (μ := (0 : EuclideanSpace ℝ Unit))
      (S := S) hS ())
  have hσ :
      S () () = linearRestrictionStdError R (heteroAsymCov μ X e) ^ 2 := by
    simpa [S, Vβ, linearRestrictionStdError] using
      (Real.sq_sqrt (hS.diag_nonneg (i := ()))).symm
  have hstdLaw :
      HasLaw
        (fun z : ℝ => linearRestrictionStdError R (heteroAsymCov μ X e) * z)
        (gaussianReal 0 (S () ()).toNNReal) (gaussianReal 0 1) :=
    hasLaw_const_mul_id_gaussianReal_of_variance_eq hσ
  simpa [S, Vβ] using hT.congr_limit_law hcoordLaw hstdLaw

set_option linter.style.longLine false in
/-- Scalar one-row ordinary-bootstrap OLS restriction transfer in the scaled
standard-normal form used by the studentization wrappers.

The limit map is `seθ * Z` with
`seθ = linearRestrictionStdError R (heteroAsymCov μ X e)`. -/
theorem
    chapter10_indexed_bootstrap_regression_linearRestriction_standardNormal_finSucc_olsBetaOrZero_of_gapEnvelope_tight
    [IsProbabilityMeasure μ]
    {k : Type*} [Fintype k] [DecidableEq k]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    (β : k → ℝ) (R : Matrix Unit k ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (h : ScoreCLTConditions μ X e)
    (hΩ : (scoreCovMat μ X e).PosDef)
    (hTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set (EuclideanSpace ℝ k), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω =>
            ((ProbabilityTheory.uniformOn
              (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                Measure (Fin (n + 1) → Fin (n + 1)))).real
              {ωs | regressionLinearizedScoreFinSucc μ X e n ω ωs ∉ K})
          atTop (fun _ => 0) ∧
        TendstoInMeasure μ
          (fun n ω =>
            ((ProbabilityTheory.uniformOn
              (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                Measure (Fin (n + 1) → Fin (n + 1)))).real
              {ωs | regressionBootstrapBetaStatisticFinSucc X y n ω ωs ∉ K})
          atTop (fun _ => 0))
    (hGapTail : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          ((ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
              Measure (Fin (n + 1) → Fin (n + 1)))).real
            {ωs |
              δ ≤ regressionBootstrapBetaLinearizedGapEnvelopeFinSucc
                μ X e β n ω ωs})
        atTop (fun _ => 0)) :
    TendstoInBootstrapWeakDistributionIndexed μ
      (fun n _ =>
        (ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))))
      (fun n ω ωs => regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs)
      (gaussianReal 0 1)
      (fun z : ℝ => linearRestrictionStdError R (heteroAsymCov μ X e) * z) :=
  regressionBootstrapLinearRestrictionStatisticFinSucc_tendsto_standardNormal_of_gaussian
    (μ := μ) (X := X) (e := e) (y := y) R h
    (chapter10_indexed_bootstrap_regression_linearRestriction_gaussian_finSucc_olsBetaOrZero_of_gapEnvelope_tight
      (μ := μ) (X := X) (e := e) (y := y)
      β R hmodel h hΩ hTail hGapTail)

set_option linter.style.longLine false in
/-- Robust-feasible HC specialization of the scalar one-row OLS
standard-normal numerator transfer. -/
theorem
    chapter10_indexed_bootstrap_regression_linearRestriction_standardNormal_finSucc_olsBetaOrZero_of_gapEnvelope_tight_of_robustFeasibleHCMomentConditions
    [IsProbabilityMeasure μ]
    {k : Type*} [Fintype k] [DecidableEq k]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    (β : k → ℝ) (R : Matrix Unit k ℝ)
    (hm : RobustFeasibleHCMomentConditions μ X e y β)
    (hΩ : (scoreCovMat μ X e).PosDef)
    (hTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set (EuclideanSpace ℝ k), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω =>
            ((ProbabilityTheory.uniformOn
              (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                Measure (Fin (n + 1) → Fin (n + 1)))).real
              {ωs | regressionLinearizedScoreFinSucc μ X e n ω ωs ∉ K})
          atTop (fun _ => 0) ∧
        TendstoInMeasure μ
          (fun n ω =>
            ((ProbabilityTheory.uniformOn
              (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                Measure (Fin (n + 1) → Fin (n + 1)))).real
              {ωs | regressionBootstrapBetaStatisticFinSucc X y n ω ωs ∉ K})
          atTop (fun _ => 0))
    (hGapTail : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          ((ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
              Measure (Fin (n + 1) → Fin (n + 1)))).real
            {ωs |
              δ ≤ regressionBootstrapBetaLinearizedGapEnvelopeFinSucc
                μ X e β n ω ωs})
        atTop (fun _ => 0)) :
    TendstoInBootstrapWeakDistributionIndexed μ
      (fun n _ =>
        (ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))))
      (fun n ω ωs => regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs)
      (gaussianReal 0 1)
      (fun z : ℝ => linearRestrictionStdError R (heteroAsymCov μ X e) * z) :=
  chapter10_indexed_bootstrap_regression_linearRestriction_standardNormal_finSucc_olsBetaOrZero_of_gapEnvelope_tight
    (μ := μ) (X := X) (e := e) (y := y)
    β R hm.model hm.toScoreCLTConditions hΩ hTail hGapTail

set_option linter.style.longLine false in
/-- Bounded scalar one-row ordinary-bootstrap OLS restriction transfer in the
scaled standard-normal form used by the studentization wrappers. -/
theorem
    chapter10_indexed_bootstrap_regression_linearRestriction_standardNormal_finSucc_olsBetaOrZero_of_gapEnvelope_bounds
    [IsProbabilityMeasure μ]
    {k : Type*} [Fintype k] [DecidableEq k]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    {Clin Cbeta : ℝ}
    (β : k → ℝ) (R : Matrix Unit k ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (h : ScoreCLTConditions μ X e)
    (hΩ : (scoreCovMat μ X e).PosDef)
    (hLinBound : ∀ᶠ n in atTop,
      ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
        ‖regressionLinearizedScoreFinSucc μ X e n ω ωs‖ ≤ Clin)
    (hBetaBound : ∀ᶠ n in atTop,
      ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
        ‖regressionBootstrapBetaStatisticFinSucc X y n ω ωs‖ ≤ Cbeta)
    (hGapTail : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          ((ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
              Measure (Fin (n + 1) → Fin (n + 1)))).real
            {ωs |
              δ ≤ regressionBootstrapBetaLinearizedGapEnvelopeFinSucc
                μ X e β n ω ωs})
        atTop (fun _ => 0)) :
    TendstoInBootstrapWeakDistributionIndexed μ
      (fun n _ =>
        (ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))))
      (fun n ω ωs => regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs)
      (gaussianReal 0 1)
      (fun z : ℝ => linearRestrictionStdError R (heteroAsymCov μ X e) * z) :=
  regressionBootstrapLinearRestrictionStatisticFinSucc_tendsto_standardNormal_of_gaussian
    (μ := μ) (X := X) (e := e) (y := y) R h
    (chapter10_indexed_bootstrap_regression_linearRestriction_gaussian_finSucc_olsBetaOrZero_of_gapEnvelope_bounds
      (μ := μ) (X := X) (e := e) (y := y)
      β R hmodel h hΩ hLinBound hBetaBound hGapTail)

set_option linter.style.longLine false in
/-- Robust-feasible HC specialization of the bounded scalar one-row OLS
standard-normal numerator transfer. -/
theorem
    chapter10_indexed_bootstrap_regression_linearRestriction_standardNormal_finSucc_olsBetaOrZero_of_gapEnvelope_bounds_of_robustFeasibleHCMomentConditions
    [IsProbabilityMeasure μ]
    {k : Type*} [Fintype k] [DecidableEq k]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    {Clin Cbeta : ℝ}
    (β : k → ℝ) (R : Matrix Unit k ℝ)
    (hm : RobustFeasibleHCMomentConditions μ X e y β)
    (hΩ : (scoreCovMat μ X e).PosDef)
    (hLinBound : ∀ᶠ n in atTop,
      ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
        ‖regressionLinearizedScoreFinSucc μ X e n ω ωs‖ ≤ Clin)
    (hBetaBound : ∀ᶠ n in atTop,
      ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
        ‖regressionBootstrapBetaStatisticFinSucc X y n ω ωs‖ ≤ Cbeta)
    (hGapTail : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          ((ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
              Measure (Fin (n + 1) → Fin (n + 1)))).real
            {ωs |
              δ ≤ regressionBootstrapBetaLinearizedGapEnvelopeFinSucc
                μ X e β n ω ωs})
        atTop (fun _ => 0)) :
    TendstoInBootstrapWeakDistributionIndexed μ
      (fun n _ =>
        (ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))))
      (fun n ω ωs => regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs)
      (gaussianReal 0 1)
      (fun z : ℝ => linearRestrictionStdError R (heteroAsymCov μ X e) * z) :=
  chapter10_indexed_bootstrap_regression_linearRestriction_standardNormal_finSucc_olsBetaOrZero_of_gapEnvelope_bounds
    (μ := μ) (X := X) (e := e) (y := y)
    β R hm.model hm.toScoreCLTConditions hΩ hLinBound hBetaBound hGapTail

set_option linter.style.longLine false in
/-- Concrete ordinary-bootstrap OLS t-statistic transfer from the finite
gap-envelope numerator route and scalar compact-tail control.

The numerator is Hansen's one-row `sqrt(n+1)(R βhat* - R βhat)`, and the
scale is left as a model-specific feasible bootstrap standard error. -/
theorem
    chapter10_indexed_bootstrap_regression_tstat_standardNormal_finSucc_olsBetaOrZero_of_gapEnvelope_scalarTail
    [IsProbabilityMeasure μ]
    {k : Type*} [Fintype k] [DecidableEq k]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    {seThetaStar : ∀ n, Ω → (Fin (n + 1) → Fin (n + 1)) → ℝ}
    (β : k → ℝ) (R : Matrix Unit k ℝ)
    (hseθ : 0 < linearRestrictionStdError R (heteroAsymCov μ X e))
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (h : ScoreCLTConditions μ X e)
    (hΩ : (scoreCovMat μ X e).PosDef)
    (hTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set (EuclideanSpace ℝ k), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω =>
            ((ProbabilityTheory.uniformOn
              (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                Measure (Fin (n + 1) → Fin (n + 1)))).real
              {ωs | regressionLinearizedScoreFinSucc μ X e n ω ωs ∉ K})
          atTop (fun _ => 0) ∧
        TendstoInMeasure μ
          (fun n ω =>
            ((ProbabilityTheory.uniformOn
              (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                Measure (Fin (n + 1) → Fin (n + 1)))).real
              {ωs | regressionBootstrapBetaStatisticFinSucc X y n ω ωs ∉ K})
          atTop (fun _ => 0))
    (hGapTail : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          ((ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
              Measure (Fin (n + 1) → Fin (n + 1)))).real
            {ωs |
              δ ≤ regressionBootstrapBetaLinearizedGapEnvelopeFinSucc
                μ X e β n ω ωs})
        atTop (fun _ => 0))
    (hseThetaStar : ∀ n ω, Measurable (seThetaStar n ω))
    (hTtail : ∀ η : ℝ, 0 < η →
      ∃ Kt : Set ℝ, IsCompact Kt ∧
        TendstoInMeasure μ
          (fun n ω =>
            ((ProbabilityTheory.uniformOn
              (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                Measure (Fin (n + 1) → Fin (n + 1)))).real
              {ωs |
                regressionBootstrapLinearRestrictionStatisticFinSucc
                  R X y n ω ωs ∉ Kt})
          atTop (fun _ => 0))
    (hse :
      TendstoInBootstrapProbabilityIndexed μ
        (fun n _ =>
          (ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
              Measure (Fin (n + 1) → Fin (n + 1))))
        seThetaStar
        (fun _ => linearRestrictionStdError R (heteroAsymCov μ X e))) :
    TendstoInBootstrapWeakDistributionIndexed μ
      (fun n _ =>
        (ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))))
      (fun n ω ωs =>
        regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs /
          seThetaStar n ω ωs)
      (gaussianReal 0 1) (fun z : ℝ => z) :=
  chapter10_indexed_bootstrap_studentized_ratio_standardNormal_of_scalarTail
    (μ := μ)
    (Pstar := fun n _ =>
      (ProbabilityTheory.uniformOn
        (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
          Measure (Fin (n + 1) → Fin (n + 1))))
    (Xstar := fun n ω ωs =>
      regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs)
    (Ystar := seThetaStar)
    (c := linearRestrictionStdError R (heteroAsymCov μ X e))
    hseθ
    (chapter10_indexed_bootstrap_regression_linearRestriction_standardNormal_finSucc_olsBetaOrZero_of_gapEnvelope_tight
      (μ := μ) (X := X) (e := e) (y := y)
      β R hmodel h hΩ hTail hGapTail)
    (fun _ _ => inferInstance) (fun _ _ => measurable_of_finite _)
    hseThetaStar hTtail hse

set_option linter.style.longLine false in
/-- Robust-feasible HC specialization of the concrete finite OLS
t-statistic transfer from scalar compact-tail control. -/
theorem
    chapter10_indexed_bootstrap_regression_tstat_standardNormal_finSucc_olsBetaOrZero_of_gapEnvelope_scalarTail_of_robustFeasibleHCMomentConditions
    [IsProbabilityMeasure μ]
    {k : Type*} [Fintype k] [DecidableEq k]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    {seThetaStar : ∀ n, Ω → (Fin (n + 1) → Fin (n + 1)) → ℝ}
    (β : k → ℝ) (R : Matrix Unit k ℝ)
    (hseθ : 0 < linearRestrictionStdError R (heteroAsymCov μ X e))
    (hm : RobustFeasibleHCMomentConditions μ X e y β)
    (hΩ : (scoreCovMat μ X e).PosDef)
    (hTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set (EuclideanSpace ℝ k), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω =>
            ((ProbabilityTheory.uniformOn
              (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                Measure (Fin (n + 1) → Fin (n + 1)))).real
              {ωs | regressionLinearizedScoreFinSucc μ X e n ω ωs ∉ K})
          atTop (fun _ => 0) ∧
        TendstoInMeasure μ
          (fun n ω =>
            ((ProbabilityTheory.uniformOn
              (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                Measure (Fin (n + 1) → Fin (n + 1)))).real
              {ωs | regressionBootstrapBetaStatisticFinSucc X y n ω ωs ∉ K})
          atTop (fun _ => 0))
    (hGapTail : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          ((ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
              Measure (Fin (n + 1) → Fin (n + 1)))).real
            {ωs |
              δ ≤ regressionBootstrapBetaLinearizedGapEnvelopeFinSucc
                μ X e β n ω ωs})
        atTop (fun _ => 0))
    (hseThetaStar : ∀ n ω, Measurable (seThetaStar n ω))
    (hTtail : ∀ η : ℝ, 0 < η →
      ∃ Kt : Set ℝ, IsCompact Kt ∧
        TendstoInMeasure μ
          (fun n ω =>
            ((ProbabilityTheory.uniformOn
              (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                Measure (Fin (n + 1) → Fin (n + 1)))).real
              {ωs |
                regressionBootstrapLinearRestrictionStatisticFinSucc
                  R X y n ω ωs ∉ Kt})
          atTop (fun _ => 0))
    (hse :
      TendstoInBootstrapProbabilityIndexed μ
        (fun n _ =>
          (ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
              Measure (Fin (n + 1) → Fin (n + 1))))
        seThetaStar
        (fun _ => linearRestrictionStdError R (heteroAsymCov μ X e))) :
    TendstoInBootstrapWeakDistributionIndexed μ
      (fun n _ =>
        (ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))))
      (fun n ω ωs =>
        regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs /
          seThetaStar n ω ωs)
      (gaussianReal 0 1) (fun z : ℝ => z) :=
  chapter10_indexed_bootstrap_regression_tstat_standardNormal_finSucc_olsBetaOrZero_of_gapEnvelope_scalarTail
    (μ := μ) (X := X) (e := e) (y := y)
    β R hseθ hm.model hm.toScoreCLTConditions hΩ hTail hGapTail
    hseThetaStar hTtail hse

set_option linter.style.longLine false in
/-- Hansen Definition 10.2 face of the concrete finite OLS t-statistic
transfer from the gap-envelope numerator route and scalar compact-tail
control. -/
theorem
    chapter10_indexed_bootstrap_regression_tstat_distribution_standardNormal_finSucc_olsBetaOrZero_of_gapEnvelope_scalarTail
    [IsProbabilityMeasure μ]
    {k : Type*} [Fintype k] [DecidableEq k]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    {seThetaStar : ∀ n, Ω → (Fin (n + 1) → Fin (n + 1)) → ℝ}
    (β : k → ℝ) (R : Matrix Unit k ℝ)
    (hseθ : 0 < linearRestrictionStdError R (heteroAsymCov μ X e))
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (h : ScoreCLTConditions μ X e)
    (hΩ : (scoreCovMat μ X e).PosDef)
    (hTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set (EuclideanSpace ℝ k), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω =>
            ((ProbabilityTheory.uniformOn
              (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                Measure (Fin (n + 1) → Fin (n + 1)))).real
              {ωs | regressionLinearizedScoreFinSucc μ X e n ω ωs ∉ K})
          atTop (fun _ => 0) ∧
        TendstoInMeasure μ
          (fun n ω =>
            ((ProbabilityTheory.uniformOn
              (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                Measure (Fin (n + 1) → Fin (n + 1)))).real
              {ωs | regressionBootstrapBetaStatisticFinSucc X y n ω ωs ∉ K})
          atTop (fun _ => 0))
    (hGapTail : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          ((ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
              Measure (Fin (n + 1) → Fin (n + 1)))).real
            {ωs |
              δ ≤ regressionBootstrapBetaLinearizedGapEnvelopeFinSucc
                μ X e β n ω ωs})
        atTop (fun _ => 0))
    (hseThetaStar : ∀ n ω, Measurable (seThetaStar n ω))
    (hTtail : ∀ η : ℝ, 0 < η →
      ∃ Kt : Set ℝ, IsCompact Kt ∧
        TendstoInMeasure μ
          (fun n ω =>
            ((ProbabilityTheory.uniformOn
              (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                Measure (Fin (n + 1) → Fin (n + 1)))).real
              {ωs |
                regressionBootstrapLinearRestrictionStatisticFinSucc
                  R X y n ω ωs ∉ Kt})
          atTop (fun _ => 0))
    (hse :
      TendstoInBootstrapProbabilityIndexed μ
        (fun n _ =>
          (ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
              Measure (Fin (n + 1) → Fin (n + 1))))
        seThetaStar
        (fun _ => linearRestrictionStdError R (heteroAsymCov μ X e))) :
    TendstoInBootstrapDistributionIndexed μ
      (fun n _ =>
        (ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))))
      (fun n ω ωs (_ : Unit) =>
        regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs /
          seThetaStar n ω ωs)
      (gaussianReal 0 1) (fun z : ℝ => fun _ : Unit => z) :=
  chapter10_indexed_bootstrap_studentized_ratio_distribution_of_scalarTail
    (μ := μ)
    (Pstar := fun n _ =>
      (ProbabilityTheory.uniformOn
        (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
          Measure (Fin (n + 1) → Fin (n + 1))))
    (Xstar := fun n ω ωs =>
      regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs)
    (Ystar := seThetaStar)
    (c := linearRestrictionStdError R (heteroAsymCov μ X e))
    hseθ
    (chapter10_indexed_bootstrap_regression_linearRestriction_standardNormal_finSucc_olsBetaOrZero_of_gapEnvelope_tight
      (μ := μ) (X := X) (e := e) (y := y)
      β R hmodel h hΩ hTail hGapTail)
    (fun _ _ => inferInstance) (fun _ _ => measurable_of_finite _)
    hseThetaStar hTtail hse

set_option linter.style.longLine false in
/-- Robust-feasible HC specialization of the Definition 10.2 concrete finite
OLS t-statistic transfer from scalar compact-tail control. -/
theorem
    chapter10_indexed_bootstrap_regression_tstat_distribution_standardNormal_finSucc_olsBetaOrZero_of_gapEnvelope_scalarTail_of_robustFeasibleHCMomentConditions
    [IsProbabilityMeasure μ]
    {k : Type*} [Fintype k] [DecidableEq k]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    {seThetaStar : ∀ n, Ω → (Fin (n + 1) → Fin (n + 1)) → ℝ}
    (β : k → ℝ) (R : Matrix Unit k ℝ)
    (hseθ : 0 < linearRestrictionStdError R (heteroAsymCov μ X e))
    (hm : RobustFeasibleHCMomentConditions μ X e y β)
    (hΩ : (scoreCovMat μ X e).PosDef)
    (hTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set (EuclideanSpace ℝ k), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω =>
            ((ProbabilityTheory.uniformOn
              (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                Measure (Fin (n + 1) → Fin (n + 1)))).real
              {ωs | regressionLinearizedScoreFinSucc μ X e n ω ωs ∉ K})
          atTop (fun _ => 0) ∧
        TendstoInMeasure μ
          (fun n ω =>
            ((ProbabilityTheory.uniformOn
              (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                Measure (Fin (n + 1) → Fin (n + 1)))).real
              {ωs | regressionBootstrapBetaStatisticFinSucc X y n ω ωs ∉ K})
          atTop (fun _ => 0))
    (hGapTail : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          ((ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
              Measure (Fin (n + 1) → Fin (n + 1)))).real
            {ωs |
              δ ≤ regressionBootstrapBetaLinearizedGapEnvelopeFinSucc
                μ X e β n ω ωs})
        atTop (fun _ => 0))
    (hseThetaStar : ∀ n ω, Measurable (seThetaStar n ω))
    (hTtail : ∀ η : ℝ, 0 < η →
      ∃ Kt : Set ℝ, IsCompact Kt ∧
        TendstoInMeasure μ
          (fun n ω =>
            ((ProbabilityTheory.uniformOn
              (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                Measure (Fin (n + 1) → Fin (n + 1)))).real
              {ωs |
                regressionBootstrapLinearRestrictionStatisticFinSucc
                  R X y n ω ωs ∉ Kt})
          atTop (fun _ => 0))
    (hse :
      TendstoInBootstrapProbabilityIndexed μ
        (fun n _ =>
          (ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
              Measure (Fin (n + 1) → Fin (n + 1))))
        seThetaStar
        (fun _ => linearRestrictionStdError R (heteroAsymCov μ X e))) :
    TendstoInBootstrapDistributionIndexed μ
      (fun n _ =>
        (ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))))
      (fun n ω ωs (_ : Unit) =>
        regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs /
          seThetaStar n ω ωs)
      (gaussianReal 0 1) (fun z : ℝ => fun _ : Unit => z) :=
  chapter10_indexed_bootstrap_regression_tstat_distribution_standardNormal_finSucc_olsBetaOrZero_of_gapEnvelope_scalarTail
    (μ := μ) (X := X) (e := e) (y := y)
    β R hseθ hm.model hm.toScoreCLTConditions hΩ hTail hGapTail
    hseThetaStar hTtail hse

set_option linter.style.longLine false in
/-- Concrete ordinary-bootstrap OLS absolute t-statistic transfer from the
finite gap-envelope numerator route and scalar compact-tail control. -/
theorem
    chapter10_indexed_bootstrap_regression_abs_tstat_standardNormalAbs_finSucc_olsBetaOrZero_of_gapEnvelope_scalarTail
    [IsProbabilityMeasure μ]
    {k : Type*} [Fintype k] [DecidableEq k]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    {seThetaStar : ∀ n, Ω → (Fin (n + 1) → Fin (n + 1)) → ℝ}
    (β : k → ℝ) (R : Matrix Unit k ℝ)
    (hseθ : 0 < linearRestrictionStdError R (heteroAsymCov μ X e))
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (h : ScoreCLTConditions μ X e)
    (hΩ : (scoreCovMat μ X e).PosDef)
    (hTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set (EuclideanSpace ℝ k), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω =>
            ((ProbabilityTheory.uniformOn
              (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                Measure (Fin (n + 1) → Fin (n + 1)))).real
              {ωs | regressionLinearizedScoreFinSucc μ X e n ω ωs ∉ K})
          atTop (fun _ => 0) ∧
        TendstoInMeasure μ
          (fun n ω =>
            ((ProbabilityTheory.uniformOn
              (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                Measure (Fin (n + 1) → Fin (n + 1)))).real
              {ωs | regressionBootstrapBetaStatisticFinSucc X y n ω ωs ∉ K})
          atTop (fun _ => 0))
    (hGapTail : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          ((ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
              Measure (Fin (n + 1) → Fin (n + 1)))).real
            {ωs |
              δ ≤ regressionBootstrapBetaLinearizedGapEnvelopeFinSucc
                μ X e β n ω ωs})
        atTop (fun _ => 0))
    (hseThetaStar : ∀ n ω, Measurable (seThetaStar n ω))
    (hTtail : ∀ η : ℝ, 0 < η →
      ∃ Kt : Set ℝ, IsCompact Kt ∧
        TendstoInMeasure μ
          (fun n ω =>
            ((ProbabilityTheory.uniformOn
              (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                Measure (Fin (n + 1) → Fin (n + 1)))).real
              {ωs |
                regressionBootstrapLinearRestrictionStatisticFinSucc
                  R X y n ω ωs ∉ Kt})
          atTop (fun _ => 0))
    (hse :
      TendstoInBootstrapProbabilityIndexed μ
        (fun n _ =>
          (ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
              Measure (Fin (n + 1) → Fin (n + 1))))
        seThetaStar
        (fun _ => linearRestrictionStdError R (heteroAsymCov μ X e))) :
    TendstoInBootstrapWeakDistributionIndexed μ
      (fun n _ =>
        (ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))))
      (fun n ω ωs =>
        |regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs /
          seThetaStar n ω ωs|)
      ((gaussianReal 0 1).map (fun z : ℝ => |z|)) (fun z : ℝ => z) :=
  chapter10_indexed_bootstrap_studentized_ratio_abs_of_scalarTail
    (μ := μ)
    (Pstar := fun n _ =>
      (ProbabilityTheory.uniformOn
        (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
          Measure (Fin (n + 1) → Fin (n + 1))))
    (Xstar := fun n ω ωs =>
      regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs)
    (Ystar := seThetaStar)
    (c := linearRestrictionStdError R (heteroAsymCov μ X e))
    hseθ
    (chapter10_indexed_bootstrap_regression_linearRestriction_standardNormal_finSucc_olsBetaOrZero_of_gapEnvelope_tight
      (μ := μ) (X := X) (e := e) (y := y)
      β R hmodel h hΩ hTail hGapTail)
    (fun _ _ => inferInstance) (fun _ _ => measurable_of_finite _)
    hseThetaStar hTtail hse

set_option linter.style.longLine false in
/-- Robust-feasible HC specialization of the concrete finite OLS absolute
t-statistic transfer from scalar compact-tail control. -/
theorem
    chapter10_indexed_bootstrap_regression_abs_tstat_standardNormalAbs_finSucc_olsBetaOrZero_of_gapEnvelope_scalarTail_of_robustFeasibleHCMomentConditions
    [IsProbabilityMeasure μ]
    {k : Type*} [Fintype k] [DecidableEq k]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    {seThetaStar : ∀ n, Ω → (Fin (n + 1) → Fin (n + 1)) → ℝ}
    (β : k → ℝ) (R : Matrix Unit k ℝ)
    (hseθ : 0 < linearRestrictionStdError R (heteroAsymCov μ X e))
    (hm : RobustFeasibleHCMomentConditions μ X e y β)
    (hΩ : (scoreCovMat μ X e).PosDef)
    (hTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set (EuclideanSpace ℝ k), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω =>
            ((ProbabilityTheory.uniformOn
              (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                Measure (Fin (n + 1) → Fin (n + 1)))).real
              {ωs | regressionLinearizedScoreFinSucc μ X e n ω ωs ∉ K})
          atTop (fun _ => 0) ∧
        TendstoInMeasure μ
          (fun n ω =>
            ((ProbabilityTheory.uniformOn
              (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                Measure (Fin (n + 1) → Fin (n + 1)))).real
              {ωs | regressionBootstrapBetaStatisticFinSucc X y n ω ωs ∉ K})
          atTop (fun _ => 0))
    (hGapTail : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          ((ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
              Measure (Fin (n + 1) → Fin (n + 1)))).real
            {ωs |
              δ ≤ regressionBootstrapBetaLinearizedGapEnvelopeFinSucc
                μ X e β n ω ωs})
        atTop (fun _ => 0))
    (hseThetaStar : ∀ n ω, Measurable (seThetaStar n ω))
    (hTtail : ∀ η : ℝ, 0 < η →
      ∃ Kt : Set ℝ, IsCompact Kt ∧
        TendstoInMeasure μ
          (fun n ω =>
            ((ProbabilityTheory.uniformOn
              (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                Measure (Fin (n + 1) → Fin (n + 1)))).real
              {ωs |
                regressionBootstrapLinearRestrictionStatisticFinSucc
                  R X y n ω ωs ∉ Kt})
          atTop (fun _ => 0))
    (hse :
      TendstoInBootstrapProbabilityIndexed μ
        (fun n _ =>
          (ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
              Measure (Fin (n + 1) → Fin (n + 1))))
        seThetaStar
        (fun _ => linearRestrictionStdError R (heteroAsymCov μ X e))) :
    TendstoInBootstrapWeakDistributionIndexed μ
      (fun n _ =>
        (ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))))
      (fun n ω ωs =>
        |regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs /
          seThetaStar n ω ωs|)
      ((gaussianReal 0 1).map (fun z : ℝ => |z|)) (fun z : ℝ => z) :=
  chapter10_indexed_bootstrap_regression_abs_tstat_standardNormalAbs_finSucc_olsBetaOrZero_of_gapEnvelope_scalarTail
    (μ := μ) (X := X) (e := e) (y := y)
    β R hseθ hm.model hm.toScoreCLTConditions hΩ hTail hGapTail
    hseThetaStar hTtail hse

set_option linter.style.longLine false in
/-- Hansen Definition 10.2 face of the concrete finite OLS absolute
t-statistic transfer from the gap-envelope numerator route and scalar
compact-tail control. -/
theorem
    chapter10_indexed_bootstrap_regression_abs_tstat_distribution_standardNormalAbs_finSucc_olsBetaOrZero_of_gapEnvelope_scalarTail
    [IsProbabilityMeasure μ]
    {k : Type*} [Fintype k] [DecidableEq k]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    {seThetaStar : ∀ n, Ω → (Fin (n + 1) → Fin (n + 1)) → ℝ}
    (β : k → ℝ) (R : Matrix Unit k ℝ)
    (hseθ : 0 < linearRestrictionStdError R (heteroAsymCov μ X e))
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (h : ScoreCLTConditions μ X e)
    (hΩ : (scoreCovMat μ X e).PosDef)
    (hTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set (EuclideanSpace ℝ k), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω =>
            ((ProbabilityTheory.uniformOn
              (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                Measure (Fin (n + 1) → Fin (n + 1)))).real
              {ωs | regressionLinearizedScoreFinSucc μ X e n ω ωs ∉ K})
          atTop (fun _ => 0) ∧
        TendstoInMeasure μ
          (fun n ω =>
            ((ProbabilityTheory.uniformOn
              (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                Measure (Fin (n + 1) → Fin (n + 1)))).real
              {ωs | regressionBootstrapBetaStatisticFinSucc X y n ω ωs ∉ K})
          atTop (fun _ => 0))
    (hGapTail : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          ((ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
              Measure (Fin (n + 1) → Fin (n + 1)))).real
            {ωs |
              δ ≤ regressionBootstrapBetaLinearizedGapEnvelopeFinSucc
                μ X e β n ω ωs})
        atTop (fun _ => 0))
    (hseThetaStar : ∀ n ω, Measurable (seThetaStar n ω))
    (hTtail : ∀ η : ℝ, 0 < η →
      ∃ Kt : Set ℝ, IsCompact Kt ∧
        TendstoInMeasure μ
          (fun n ω =>
            ((ProbabilityTheory.uniformOn
              (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                Measure (Fin (n + 1) → Fin (n + 1)))).real
              {ωs |
                regressionBootstrapLinearRestrictionStatisticFinSucc
                  R X y n ω ωs ∉ Kt})
          atTop (fun _ => 0))
    (hse :
      TendstoInBootstrapProbabilityIndexed μ
        (fun n _ =>
          (ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
              Measure (Fin (n + 1) → Fin (n + 1))))
        seThetaStar
        (fun _ => linearRestrictionStdError R (heteroAsymCov μ X e))) :
    TendstoInBootstrapDistributionIndexed μ
      (fun n _ =>
        (ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))))
      (fun n ω ωs (_ : Unit) =>
        |regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs /
          seThetaStar n ω ωs|)
      ((gaussianReal 0 1).map (fun z : ℝ => |z|))
      (fun z : ℝ => fun _ : Unit => z) :=
  chapter10_indexed_bootstrap_studentized_abs_distribution_of_scalarTail
    (μ := μ)
    (Pstar := fun n _ =>
      (ProbabilityTheory.uniformOn
        (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
          Measure (Fin (n + 1) → Fin (n + 1))))
    (Xstar := fun n ω ωs =>
      regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs)
    (Ystar := seThetaStar)
    (c := linearRestrictionStdError R (heteroAsymCov μ X e))
    hseθ
    (chapter10_indexed_bootstrap_regression_linearRestriction_standardNormal_finSucc_olsBetaOrZero_of_gapEnvelope_tight
      (μ := μ) (X := X) (e := e) (y := y)
      β R hmodel h hΩ hTail hGapTail)
    (fun _ _ => inferInstance) (fun _ _ => measurable_of_finite _)
    hseThetaStar hTtail hse

set_option linter.style.longLine false in
/-- Robust-feasible HC specialization of the Definition 10.2 concrete finite
OLS absolute t-statistic transfer from scalar compact-tail control. -/
theorem
    chapter10_indexed_bootstrap_regression_abs_tstat_distribution_standardNormalAbs_finSucc_olsBetaOrZero_of_gapEnvelope_scalarTail_of_robustFeasibleHCMomentConditions
    [IsProbabilityMeasure μ]
    {k : Type*} [Fintype k] [DecidableEq k]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    {seThetaStar : ∀ n, Ω → (Fin (n + 1) → Fin (n + 1)) → ℝ}
    (β : k → ℝ) (R : Matrix Unit k ℝ)
    (hseθ : 0 < linearRestrictionStdError R (heteroAsymCov μ X e))
    (hm : RobustFeasibleHCMomentConditions μ X e y β)
    (hΩ : (scoreCovMat μ X e).PosDef)
    (hTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set (EuclideanSpace ℝ k), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω =>
            ((ProbabilityTheory.uniformOn
              (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                Measure (Fin (n + 1) → Fin (n + 1)))).real
              {ωs | regressionLinearizedScoreFinSucc μ X e n ω ωs ∉ K})
          atTop (fun _ => 0) ∧
        TendstoInMeasure μ
          (fun n ω =>
            ((ProbabilityTheory.uniformOn
              (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                Measure (Fin (n + 1) → Fin (n + 1)))).real
              {ωs | regressionBootstrapBetaStatisticFinSucc X y n ω ωs ∉ K})
          atTop (fun _ => 0))
    (hGapTail : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          ((ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
              Measure (Fin (n + 1) → Fin (n + 1)))).real
            {ωs |
              δ ≤ regressionBootstrapBetaLinearizedGapEnvelopeFinSucc
                μ X e β n ω ωs})
        atTop (fun _ => 0))
    (hseThetaStar : ∀ n ω, Measurable (seThetaStar n ω))
    (hTtail : ∀ η : ℝ, 0 < η →
      ∃ Kt : Set ℝ, IsCompact Kt ∧
        TendstoInMeasure μ
          (fun n ω =>
            ((ProbabilityTheory.uniformOn
              (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                Measure (Fin (n + 1) → Fin (n + 1)))).real
              {ωs |
                regressionBootstrapLinearRestrictionStatisticFinSucc
                  R X y n ω ωs ∉ Kt})
          atTop (fun _ => 0))
    (hse :
      TendstoInBootstrapProbabilityIndexed μ
        (fun n _ =>
          (ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
              Measure (Fin (n + 1) → Fin (n + 1))))
        seThetaStar
        (fun _ => linearRestrictionStdError R (heteroAsymCov μ X e))) :
    TendstoInBootstrapDistributionIndexed μ
      (fun n _ =>
        (ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))))
      (fun n ω ωs (_ : Unit) =>
        |regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs /
          seThetaStar n ω ωs|)
      ((gaussianReal 0 1).map (fun z : ℝ => |z|))
      (fun z : ℝ => fun _ : Unit => z) :=
  chapter10_indexed_bootstrap_regression_abs_tstat_distribution_standardNormalAbs_finSucc_olsBetaOrZero_of_gapEnvelope_scalarTail
    (μ := μ) (X := X) (e := e) (y := y)
    β R hseθ hm.model hm.toScoreCLTConditions hΩ hTail hGapTail
    hseThetaStar hTtail hse

set_option linter.style.longLine false in
/-- Bounded concrete ordinary-bootstrap OLS t-statistic transfer from the
finite gap-envelope numerator route. -/
theorem
    chapter10_indexed_bootstrap_regression_tstat_standardNormal_finSucc_olsBetaOrZero_of_gapEnvelope_bounds
    [IsProbabilityMeasure μ]
    {k : Type*} [Fintype k] [DecidableEq k]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    {seThetaStar : ∀ n, Ω → (Fin (n + 1) → Fin (n + 1)) → ℝ}
    {Clin Cbeta Cnum : ℝ}
    (β : k → ℝ) (R : Matrix Unit k ℝ)
    (hseθ : 0 < linearRestrictionStdError R (heteroAsymCov μ X e))
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (h : ScoreCLTConditions μ X e)
    (hΩ : (scoreCovMat μ X e).PosDef)
    (hLinBound : ∀ᶠ n in atTop,
      ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
        ‖regressionLinearizedScoreFinSucc μ X e n ω ωs‖ ≤ Clin)
    (hBetaBound : ∀ᶠ n in atTop,
      ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
        ‖regressionBootstrapBetaStatisticFinSucc X y n ω ωs‖ ≤ Cbeta)
    (hGapTail : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          ((ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
              Measure (Fin (n + 1) → Fin (n + 1)))).real
            {ωs |
              δ ≤ regressionBootstrapBetaLinearizedGapEnvelopeFinSucc
                μ X e β n ω ωs})
        atTop (fun _ => 0))
    (hseThetaStar : ∀ n ω, Measurable (seThetaStar n ω))
    (hNumBound : ∀ᶠ n in atTop,
      ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
        |regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs| ≤
          Cnum)
    (hse :
      TendstoInBootstrapProbabilityIndexed μ
        (fun n _ =>
          (ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
              Measure (Fin (n + 1) → Fin (n + 1))))
        seThetaStar
        (fun _ => linearRestrictionStdError R (heteroAsymCov μ X e))) :
    TendstoInBootstrapWeakDistributionIndexed μ
      (fun n _ =>
        (ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))))
      (fun n ω ωs =>
        regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs /
          seThetaStar n ω ωs)
      (gaussianReal 0 1) (fun z : ℝ => z) :=
  chapter10_indexed_bootstrap_studentized_ratio_standardNormal_of_eventually_bound
    (μ := μ)
    (Pstar := fun n _ =>
      (ProbabilityTheory.uniformOn
        (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
          Measure (Fin (n + 1) → Fin (n + 1))))
    (Xstar := fun n ω ωs =>
      regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs)
    (Ystar := seThetaStar)
    (c := linearRestrictionStdError R (heteroAsymCov μ X e))
    (C := Cnum)
    hseθ
    (chapter10_indexed_bootstrap_regression_linearRestriction_standardNormal_finSucc_olsBetaOrZero_of_gapEnvelope_bounds
      (μ := μ) (X := X) (e := e) (y := y)
      β R hmodel h hΩ hLinBound hBetaBound hGapTail)
    (fun _ _ => inferInstance) (fun _ _ => measurable_of_finite _)
    hseThetaStar hNumBound hse

set_option linter.style.longLine false in
/-- Robust-feasible HC specialization of the bounded concrete finite OLS
t-statistic transfer. -/
theorem
    chapter10_indexed_bootstrap_regression_tstat_standardNormal_finSucc_olsBetaOrZero_of_gapEnvelope_bounds_of_robustFeasibleHCMomentConditions
    [IsProbabilityMeasure μ]
    {k : Type*} [Fintype k] [DecidableEq k]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    {seThetaStar : ∀ n, Ω → (Fin (n + 1) → Fin (n + 1)) → ℝ}
    {Clin Cbeta Cnum : ℝ}
    (β : k → ℝ) (R : Matrix Unit k ℝ)
    (hseθ : 0 < linearRestrictionStdError R (heteroAsymCov μ X e))
    (hm : RobustFeasibleHCMomentConditions μ X e y β)
    (hΩ : (scoreCovMat μ X e).PosDef)
    (hLinBound : ∀ᶠ n in atTop,
      ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
        ‖regressionLinearizedScoreFinSucc μ X e n ω ωs‖ ≤ Clin)
    (hBetaBound : ∀ᶠ n in atTop,
      ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
        ‖regressionBootstrapBetaStatisticFinSucc X y n ω ωs‖ ≤ Cbeta)
    (hGapTail : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          ((ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
              Measure (Fin (n + 1) → Fin (n + 1)))).real
            {ωs |
              δ ≤ regressionBootstrapBetaLinearizedGapEnvelopeFinSucc
                μ X e β n ω ωs})
        atTop (fun _ => 0))
    (hseThetaStar : ∀ n ω, Measurable (seThetaStar n ω))
    (hNumBound : ∀ᶠ n in atTop,
      ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
        |regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs| ≤
          Cnum)
    (hse :
      TendstoInBootstrapProbabilityIndexed μ
        (fun n _ =>
          (ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
              Measure (Fin (n + 1) → Fin (n + 1))))
        seThetaStar
        (fun _ => linearRestrictionStdError R (heteroAsymCov μ X e))) :
    TendstoInBootstrapWeakDistributionIndexed μ
      (fun n _ =>
        (ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))))
      (fun n ω ωs =>
        regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs /
          seThetaStar n ω ωs)
      (gaussianReal 0 1) (fun z : ℝ => z) :=
  chapter10_indexed_bootstrap_regression_tstat_standardNormal_finSucc_olsBetaOrZero_of_gapEnvelope_bounds
    (μ := μ) (X := X) (e := e) (y := y)
    β R hseθ hm.model hm.toScoreCLTConditions hΩ hLinBound hBetaBound
    hGapTail hseThetaStar hNumBound hse

set_option linter.style.longLine false in
/-- Hansen Definition 10.2 face of the bounded concrete finite OLS
t-statistic transfer. -/
theorem
    chapter10_indexed_bootstrap_regression_tstat_distribution_standardNormal_finSucc_olsBetaOrZero_of_gapEnvelope_bounds
    [IsProbabilityMeasure μ]
    {k : Type*} [Fintype k] [DecidableEq k]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    {seThetaStar : ∀ n, Ω → (Fin (n + 1) → Fin (n + 1)) → ℝ}
    {Clin Cbeta Cnum : ℝ}
    (β : k → ℝ) (R : Matrix Unit k ℝ)
    (hseθ : 0 < linearRestrictionStdError R (heteroAsymCov μ X e))
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (h : ScoreCLTConditions μ X e)
    (hΩ : (scoreCovMat μ X e).PosDef)
    (hLinBound : ∀ᶠ n in atTop,
      ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
        ‖regressionLinearizedScoreFinSucc μ X e n ω ωs‖ ≤ Clin)
    (hBetaBound : ∀ᶠ n in atTop,
      ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
        ‖regressionBootstrapBetaStatisticFinSucc X y n ω ωs‖ ≤ Cbeta)
    (hGapTail : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          ((ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
              Measure (Fin (n + 1) → Fin (n + 1)))).real
            {ωs |
              δ ≤ regressionBootstrapBetaLinearizedGapEnvelopeFinSucc
                μ X e β n ω ωs})
        atTop (fun _ => 0))
    (hseThetaStar : ∀ n ω, Measurable (seThetaStar n ω))
    (hNumBound : ∀ᶠ n in atTop,
      ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
        |regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs| ≤
          Cnum)
    (hse :
      TendstoInBootstrapProbabilityIndexed μ
        (fun n _ =>
          (ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
              Measure (Fin (n + 1) → Fin (n + 1))))
        seThetaStar
        (fun _ => linearRestrictionStdError R (heteroAsymCov μ X e))) :
    TendstoInBootstrapDistributionIndexed μ
      (fun n _ =>
        (ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))))
      (fun n ω ωs (_ : Unit) =>
        regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs /
          seThetaStar n ω ωs)
      (gaussianReal 0 1) (fun z : ℝ => fun _ : Unit => z) :=
  chapter10_indexed_bootstrap_studentized_ratio_distribution_of_eventually_bound
    (μ := μ)
    (Pstar := fun n _ =>
      (ProbabilityTheory.uniformOn
        (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
          Measure (Fin (n + 1) → Fin (n + 1))))
    (Xstar := fun n ω ωs =>
      regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs)
    (Ystar := seThetaStar)
    (c := linearRestrictionStdError R (heteroAsymCov μ X e))
    (C := Cnum)
    hseθ
    (chapter10_indexed_bootstrap_regression_linearRestriction_standardNormal_finSucc_olsBetaOrZero_of_gapEnvelope_bounds
      (μ := μ) (X := X) (e := e) (y := y)
      β R hmodel h hΩ hLinBound hBetaBound hGapTail)
    (fun _ _ => inferInstance) (fun _ _ => measurable_of_finite _)
    hseThetaStar hNumBound hse

set_option linter.style.longLine false in
/-- Robust-feasible HC specialization of the Definition 10.2 bounded concrete
finite OLS t-statistic transfer. -/
theorem
    chapter10_indexed_bootstrap_regression_tstat_distribution_standardNormal_finSucc_olsBetaOrZero_of_gapEnvelope_bounds_of_robustFeasibleHCMomentConditions
    [IsProbabilityMeasure μ]
    {k : Type*} [Fintype k] [DecidableEq k]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    {seThetaStar : ∀ n, Ω → (Fin (n + 1) → Fin (n + 1)) → ℝ}
    {Clin Cbeta Cnum : ℝ}
    (β : k → ℝ) (R : Matrix Unit k ℝ)
    (hseθ : 0 < linearRestrictionStdError R (heteroAsymCov μ X e))
    (hm : RobustFeasibleHCMomentConditions μ X e y β)
    (hΩ : (scoreCovMat μ X e).PosDef)
    (hLinBound : ∀ᶠ n in atTop,
      ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
        ‖regressionLinearizedScoreFinSucc μ X e n ω ωs‖ ≤ Clin)
    (hBetaBound : ∀ᶠ n in atTop,
      ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
        ‖regressionBootstrapBetaStatisticFinSucc X y n ω ωs‖ ≤ Cbeta)
    (hGapTail : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          ((ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
              Measure (Fin (n + 1) → Fin (n + 1)))).real
            {ωs |
              δ ≤ regressionBootstrapBetaLinearizedGapEnvelopeFinSucc
                μ X e β n ω ωs})
        atTop (fun _ => 0))
    (hseThetaStar : ∀ n ω, Measurable (seThetaStar n ω))
    (hNumBound : ∀ᶠ n in atTop,
      ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
        |regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs| ≤
          Cnum)
    (hse :
      TendstoInBootstrapProbabilityIndexed μ
        (fun n _ =>
          (ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
              Measure (Fin (n + 1) → Fin (n + 1))))
        seThetaStar
        (fun _ => linearRestrictionStdError R (heteroAsymCov μ X e))) :
    TendstoInBootstrapDistributionIndexed μ
      (fun n _ =>
        (ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))))
      (fun n ω ωs (_ : Unit) =>
        regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs /
          seThetaStar n ω ωs)
      (gaussianReal 0 1) (fun z : ℝ => fun _ : Unit => z) :=
  chapter10_indexed_bootstrap_regression_tstat_distribution_standardNormal_finSucc_olsBetaOrZero_of_gapEnvelope_bounds
    (μ := μ) (X := X) (e := e) (y := y)
    β R hseθ hm.model hm.toScoreCLTConditions hΩ hLinBound hBetaBound
    hGapTail hseThetaStar hNumBound hse

set_option linter.style.longLine false in
/-- Bounded concrete ordinary-bootstrap OLS absolute t-statistic transfer from
the finite gap-envelope numerator route. -/
theorem
    chapter10_indexed_bootstrap_regression_abs_tstat_standardNormalAbs_finSucc_olsBetaOrZero_of_gapEnvelope_bounds
    [IsProbabilityMeasure μ]
    {k : Type*} [Fintype k] [DecidableEq k]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    {seThetaStar : ∀ n, Ω → (Fin (n + 1) → Fin (n + 1)) → ℝ}
    {Clin Cbeta Cnum : ℝ}
    (β : k → ℝ) (R : Matrix Unit k ℝ)
    (hseθ : 0 < linearRestrictionStdError R (heteroAsymCov μ X e))
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (h : ScoreCLTConditions μ X e)
    (hΩ : (scoreCovMat μ X e).PosDef)
    (hLinBound : ∀ᶠ n in atTop,
      ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
        ‖regressionLinearizedScoreFinSucc μ X e n ω ωs‖ ≤ Clin)
    (hBetaBound : ∀ᶠ n in atTop,
      ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
        ‖regressionBootstrapBetaStatisticFinSucc X y n ω ωs‖ ≤ Cbeta)
    (hGapTail : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          ((ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
              Measure (Fin (n + 1) → Fin (n + 1)))).real
            {ωs |
              δ ≤ regressionBootstrapBetaLinearizedGapEnvelopeFinSucc
                μ X e β n ω ωs})
        atTop (fun _ => 0))
    (hseThetaStar : ∀ n ω, Measurable (seThetaStar n ω))
    (hNumBound : ∀ᶠ n in atTop,
      ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
        |regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs| ≤
          Cnum)
    (hse :
      TendstoInBootstrapProbabilityIndexed μ
        (fun n _ =>
          (ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
              Measure (Fin (n + 1) → Fin (n + 1))))
        seThetaStar
        (fun _ => linearRestrictionStdError R (heteroAsymCov μ X e))) :
    TendstoInBootstrapWeakDistributionIndexed μ
      (fun n _ =>
        (ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))))
      (fun n ω ωs =>
        |regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs /
          seThetaStar n ω ωs|)
      ((gaussianReal 0 1).map (fun z : ℝ => |z|)) (fun z : ℝ => z) :=
  chapter10_indexed_bootstrap_studentized_ratio_abs_of_eventually_bound
    (μ := μ)
    (Pstar := fun n _ =>
      (ProbabilityTheory.uniformOn
        (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
          Measure (Fin (n + 1) → Fin (n + 1))))
    (Xstar := fun n ω ωs =>
      regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs)
    (Ystar := seThetaStar)
    (c := linearRestrictionStdError R (heteroAsymCov μ X e))
    (C := Cnum)
    hseθ
    (chapter10_indexed_bootstrap_regression_linearRestriction_standardNormal_finSucc_olsBetaOrZero_of_gapEnvelope_bounds
      (μ := μ) (X := X) (e := e) (y := y)
      β R hmodel h hΩ hLinBound hBetaBound hGapTail)
    (fun _ _ => inferInstance) (fun _ _ => measurable_of_finite _)
    hseThetaStar hNumBound hse

set_option linter.style.longLine false in
/-- Robust-feasible HC specialization of the bounded concrete finite OLS
absolute t-statistic transfer. -/
theorem
    chapter10_indexed_bootstrap_regression_abs_tstat_standardNormalAbs_finSucc_olsBetaOrZero_of_gapEnvelope_bounds_of_robustFeasibleHCMomentConditions
    [IsProbabilityMeasure μ]
    {k : Type*} [Fintype k] [DecidableEq k]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    {seThetaStar : ∀ n, Ω → (Fin (n + 1) → Fin (n + 1)) → ℝ}
    {Clin Cbeta Cnum : ℝ}
    (β : k → ℝ) (R : Matrix Unit k ℝ)
    (hseθ : 0 < linearRestrictionStdError R (heteroAsymCov μ X e))
    (hm : RobustFeasibleHCMomentConditions μ X e y β)
    (hΩ : (scoreCovMat μ X e).PosDef)
    (hLinBound : ∀ᶠ n in atTop,
      ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
        ‖regressionLinearizedScoreFinSucc μ X e n ω ωs‖ ≤ Clin)
    (hBetaBound : ∀ᶠ n in atTop,
      ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
        ‖regressionBootstrapBetaStatisticFinSucc X y n ω ωs‖ ≤ Cbeta)
    (hGapTail : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          ((ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
              Measure (Fin (n + 1) → Fin (n + 1)))).real
            {ωs |
              δ ≤ regressionBootstrapBetaLinearizedGapEnvelopeFinSucc
                μ X e β n ω ωs})
        atTop (fun _ => 0))
    (hseThetaStar : ∀ n ω, Measurable (seThetaStar n ω))
    (hNumBound : ∀ᶠ n in atTop,
      ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
        |regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs| ≤
          Cnum)
    (hse :
      TendstoInBootstrapProbabilityIndexed μ
        (fun n _ =>
          (ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
              Measure (Fin (n + 1) → Fin (n + 1))))
        seThetaStar
        (fun _ => linearRestrictionStdError R (heteroAsymCov μ X e))) :
    TendstoInBootstrapWeakDistributionIndexed μ
      (fun n _ =>
        (ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))))
      (fun n ω ωs =>
        |regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs /
          seThetaStar n ω ωs|)
      ((gaussianReal 0 1).map (fun z : ℝ => |z|)) (fun z : ℝ => z) :=
  chapter10_indexed_bootstrap_regression_abs_tstat_standardNormalAbs_finSucc_olsBetaOrZero_of_gapEnvelope_bounds
    (μ := μ) (X := X) (e := e) (y := y)
    β R hseθ hm.model hm.toScoreCLTConditions hΩ hLinBound hBetaBound
    hGapTail hseThetaStar hNumBound hse

set_option linter.style.longLine false in
/-- Hansen Definition 10.2 face of the bounded concrete finite OLS absolute
t-statistic transfer. -/
theorem
    chapter10_indexed_bootstrap_regression_abs_tstat_distribution_standardNormalAbs_finSucc_olsBetaOrZero_of_gapEnvelope_bounds
    [IsProbabilityMeasure μ]
    {k : Type*} [Fintype k] [DecidableEq k]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    {seThetaStar : ∀ n, Ω → (Fin (n + 1) → Fin (n + 1)) → ℝ}
    {Clin Cbeta Cnum : ℝ}
    (β : k → ℝ) (R : Matrix Unit k ℝ)
    (hseθ : 0 < linearRestrictionStdError R (heteroAsymCov μ X e))
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (h : ScoreCLTConditions μ X e)
    (hΩ : (scoreCovMat μ X e).PosDef)
    (hLinBound : ∀ᶠ n in atTop,
      ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
        ‖regressionLinearizedScoreFinSucc μ X e n ω ωs‖ ≤ Clin)
    (hBetaBound : ∀ᶠ n in atTop,
      ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
        ‖regressionBootstrapBetaStatisticFinSucc X y n ω ωs‖ ≤ Cbeta)
    (hGapTail : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          ((ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
              Measure (Fin (n + 1) → Fin (n + 1)))).real
            {ωs |
              δ ≤ regressionBootstrapBetaLinearizedGapEnvelopeFinSucc
                μ X e β n ω ωs})
        atTop (fun _ => 0))
    (hseThetaStar : ∀ n ω, Measurable (seThetaStar n ω))
    (hNumBound : ∀ᶠ n in atTop,
      ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
        |regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs| ≤
          Cnum)
    (hse :
      TendstoInBootstrapProbabilityIndexed μ
        (fun n _ =>
          (ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
              Measure (Fin (n + 1) → Fin (n + 1))))
        seThetaStar
        (fun _ => linearRestrictionStdError R (heteroAsymCov μ X e))) :
    TendstoInBootstrapDistributionIndexed μ
      (fun n _ =>
        (ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))))
      (fun n ω ωs (_ : Unit) =>
        |regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs /
          seThetaStar n ω ωs|)
      ((gaussianReal 0 1).map (fun z : ℝ => |z|))
      (fun z : ℝ => fun _ : Unit => z) :=
  chapter10_indexed_bootstrap_studentized_abs_distribution_of_eventually_bound
    (μ := μ)
    (Pstar := fun n _ =>
      (ProbabilityTheory.uniformOn
        (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
          Measure (Fin (n + 1) → Fin (n + 1))))
    (Xstar := fun n ω ωs =>
      regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs)
    (Ystar := seThetaStar)
    (c := linearRestrictionStdError R (heteroAsymCov μ X e))
    (C := Cnum)
    hseθ
    (chapter10_indexed_bootstrap_regression_linearRestriction_standardNormal_finSucc_olsBetaOrZero_of_gapEnvelope_bounds
      (μ := μ) (X := X) (e := e) (y := y)
      β R hmodel h hΩ hLinBound hBetaBound hGapTail)
    (fun _ _ => inferInstance) (fun _ _ => measurable_of_finite _)
    hseThetaStar hNumBound hse

set_option linter.style.longLine false in
/-- Robust-feasible HC specialization of the Definition 10.2 bounded concrete
finite OLS absolute t-statistic transfer. -/
theorem
    chapter10_indexed_bootstrap_regression_abs_tstat_distribution_standardNormalAbs_finSucc_olsBetaOrZero_of_gapEnvelope_bounds_of_robustFeasibleHCMomentConditions
    [IsProbabilityMeasure μ]
    {k : Type*} [Fintype k] [DecidableEq k]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    {seThetaStar : ∀ n, Ω → (Fin (n + 1) → Fin (n + 1)) → ℝ}
    {Clin Cbeta Cnum : ℝ}
    (β : k → ℝ) (R : Matrix Unit k ℝ)
    (hseθ : 0 < linearRestrictionStdError R (heteroAsymCov μ X e))
    (hm : RobustFeasibleHCMomentConditions μ X e y β)
    (hΩ : (scoreCovMat μ X e).PosDef)
    (hLinBound : ∀ᶠ n in atTop,
      ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
        ‖regressionLinearizedScoreFinSucc μ X e n ω ωs‖ ≤ Clin)
    (hBetaBound : ∀ᶠ n in atTop,
      ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
        ‖regressionBootstrapBetaStatisticFinSucc X y n ω ωs‖ ≤ Cbeta)
    (hGapTail : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          ((ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
              Measure (Fin (n + 1) → Fin (n + 1)))).real
            {ωs |
              δ ≤ regressionBootstrapBetaLinearizedGapEnvelopeFinSucc
                μ X e β n ω ωs})
        atTop (fun _ => 0))
    (hseThetaStar : ∀ n ω, Measurable (seThetaStar n ω))
    (hNumBound : ∀ᶠ n in atTop,
      ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
        |regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs| ≤
          Cnum)
    (hse :
      TendstoInBootstrapProbabilityIndexed μ
        (fun n _ =>
          (ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
              Measure (Fin (n + 1) → Fin (n + 1))))
        seThetaStar
        (fun _ => linearRestrictionStdError R (heteroAsymCov μ X e))) :
    TendstoInBootstrapDistributionIndexed μ
      (fun n _ =>
        (ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))))
      (fun n ω ωs (_ : Unit) =>
        |regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs /
          seThetaStar n ω ωs|)
      ((gaussianReal 0 1).map (fun z : ℝ => |z|))
      (fun z : ℝ => fun _ : Unit => z) :=
  chapter10_indexed_bootstrap_regression_abs_tstat_distribution_standardNormalAbs_finSucc_olsBetaOrZero_of_gapEnvelope_bounds
    (μ := μ) (X := X) (e := e) (y := y)
    β R hseθ hm.model hm.toScoreCLTConditions hΩ hLinBound hBetaBound
    hGapTail hseThetaStar hNumBound hse

set_option linter.style.longLine false in
/-- Bounded concrete ordinary-bootstrap OLS t-statistic transfer where the
scalar numerator bound is discharged by the coefficient-statistic norm bound. -/
theorem
    chapter10_indexed_bootstrap_regression_tstat_standardNormal_finSucc_olsBetaOrZero_of_gapEnvelope_beta_bound
    [IsProbabilityMeasure μ]
    {k : Type*} [Fintype k] [DecidableEq k]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    {seThetaStar : ∀ n, Ω → (Fin (n + 1) → Fin (n + 1)) → ℝ}
    {Clin Cbeta : ℝ}
    (β : k → ℝ) (R : Matrix Unit k ℝ)
    (hseθ : 0 < linearRestrictionStdError R (heteroAsymCov μ X e))
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (h : ScoreCLTConditions μ X e)
    (hΩ : (scoreCovMat μ X e).PosDef)
    (hLinBound : ∀ᶠ n in atTop,
      ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
        ‖regressionLinearizedScoreFinSucc μ X e n ω ωs‖ ≤ Clin)
    (hBetaBound : ∀ᶠ n in atTop,
      ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
        ‖regressionBootstrapBetaStatisticFinSucc X y n ω ωs‖ ≤ Cbeta)
    (hGapTail : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          ((ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
              Measure (Fin (n + 1) → Fin (n + 1)))).real
            {ωs |
              δ ≤ regressionBootstrapBetaLinearizedGapEnvelopeFinSucc
                μ X e β n ω ωs})
        atTop (fun _ => 0))
    (hseThetaStar : ∀ n ω, Measurable (seThetaStar n ω))
    (hse :
      TendstoInBootstrapProbabilityIndexed μ
        (fun n _ =>
          (ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
              Measure (Fin (n + 1) → Fin (n + 1))))
        seThetaStar
        (fun _ => linearRestrictionStdError R (heteroAsymCov μ X e))) :
    TendstoInBootstrapWeakDistributionIndexed μ
      (fun n _ =>
        (ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))))
      (fun n ω ωs =>
        regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs /
          seThetaStar n ω ωs)
      (gaussianReal 0 1) (fun z : ℝ => z) :=
  chapter10_indexed_bootstrap_regression_tstat_standardNormal_finSucc_olsBetaOrZero_of_gapEnvelope_bounds
    (μ := μ) (X := X) (e := e) (y := y)
    (Cnum := ‖PiLp.proj (p := (2 : ℝ≥0∞)) (𝕜 := ℝ)
        (β := fun _ : Unit => ℝ) ()‖ * (‖matrixContinuousLinearMap R‖ * Cbeta))
    β R hseθ hmodel h hΩ hLinBound hBetaBound hGapTail hseThetaStar
    (regressionBootstrapLinearRestrictionStatisticFinSucc_eventually_abs_bound_of_beta_bound
      (R := R) (X := X) (y := y) hBetaBound)
    hse

set_option linter.style.longLine false in
/-- Robust-feasible HC specialization of the beta-bound concrete finite OLS
t-statistic transfer. -/
theorem
    chapter10_indexed_bootstrap_regression_tstat_standardNormal_finSucc_olsBetaOrZero_of_gapEnvelope_beta_bound_of_robustFeasibleHCMomentConditions
    [IsProbabilityMeasure μ]
    {k : Type*} [Fintype k] [DecidableEq k]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    {seThetaStar : ∀ n, Ω → (Fin (n + 1) → Fin (n + 1)) → ℝ}
    {Clin Cbeta : ℝ}
    (β : k → ℝ) (R : Matrix Unit k ℝ)
    (hseθ : 0 < linearRestrictionStdError R (heteroAsymCov μ X e))
    (hm : RobustFeasibleHCMomentConditions μ X e y β)
    (hΩ : (scoreCovMat μ X e).PosDef)
    (hLinBound : ∀ᶠ n in atTop,
      ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
        ‖regressionLinearizedScoreFinSucc μ X e n ω ωs‖ ≤ Clin)
    (hBetaBound : ∀ᶠ n in atTop,
      ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
        ‖regressionBootstrapBetaStatisticFinSucc X y n ω ωs‖ ≤ Cbeta)
    (hGapTail : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          ((ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
              Measure (Fin (n + 1) → Fin (n + 1)))).real
            {ωs |
              δ ≤ regressionBootstrapBetaLinearizedGapEnvelopeFinSucc
                μ X e β n ω ωs})
        atTop (fun _ => 0))
    (hseThetaStar : ∀ n ω, Measurable (seThetaStar n ω))
    (hse :
      TendstoInBootstrapProbabilityIndexed μ
        (fun n _ =>
          (ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
              Measure (Fin (n + 1) → Fin (n + 1))))
        seThetaStar
        (fun _ => linearRestrictionStdError R (heteroAsymCov μ X e))) :
    TendstoInBootstrapWeakDistributionIndexed μ
      (fun n _ =>
        (ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))))
      (fun n ω ωs =>
        regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs /
          seThetaStar n ω ωs)
      (gaussianReal 0 1) (fun z : ℝ => z) :=
  chapter10_indexed_bootstrap_regression_tstat_standardNormal_finSucc_olsBetaOrZero_of_gapEnvelope_beta_bound
    (μ := μ) (X := X) (e := e) (y := y)
    β R hseθ hm.model hm.toScoreCLTConditions hΩ hLinBound hBetaBound
    hGapTail hseThetaStar hse

set_option linter.style.longLine false in
/-- Hansen Definition 10.2 face of the beta-bound concrete finite OLS
t-statistic transfer. -/
theorem
    chapter10_indexed_bootstrap_regression_tstat_distribution_standardNormal_finSucc_olsBetaOrZero_of_gapEnvelope_beta_bound
    [IsProbabilityMeasure μ]
    {k : Type*} [Fintype k] [DecidableEq k]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    {seThetaStar : ∀ n, Ω → (Fin (n + 1) → Fin (n + 1)) → ℝ}
    {Clin Cbeta : ℝ}
    (β : k → ℝ) (R : Matrix Unit k ℝ)
    (hseθ : 0 < linearRestrictionStdError R (heteroAsymCov μ X e))
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (h : ScoreCLTConditions μ X e)
    (hΩ : (scoreCovMat μ X e).PosDef)
    (hLinBound : ∀ᶠ n in atTop,
      ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
        ‖regressionLinearizedScoreFinSucc μ X e n ω ωs‖ ≤ Clin)
    (hBetaBound : ∀ᶠ n in atTop,
      ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
        ‖regressionBootstrapBetaStatisticFinSucc X y n ω ωs‖ ≤ Cbeta)
    (hGapTail : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          ((ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
              Measure (Fin (n + 1) → Fin (n + 1)))).real
            {ωs |
              δ ≤ regressionBootstrapBetaLinearizedGapEnvelopeFinSucc
                μ X e β n ω ωs})
        atTop (fun _ => 0))
    (hseThetaStar : ∀ n ω, Measurable (seThetaStar n ω))
    (hse :
      TendstoInBootstrapProbabilityIndexed μ
        (fun n _ =>
          (ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
              Measure (Fin (n + 1) → Fin (n + 1))))
        seThetaStar
        (fun _ => linearRestrictionStdError R (heteroAsymCov μ X e))) :
    TendstoInBootstrapDistributionIndexed μ
      (fun n _ =>
        (ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))))
      (fun n ω ωs (_ : Unit) =>
        regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs /
          seThetaStar n ω ωs)
      (gaussianReal 0 1) (fun z : ℝ => fun _ : Unit => z) :=
  chapter10_indexed_bootstrap_regression_tstat_distribution_standardNormal_finSucc_olsBetaOrZero_of_gapEnvelope_bounds
    (μ := μ) (X := X) (e := e) (y := y)
    (Cnum := ‖PiLp.proj (p := (2 : ℝ≥0∞)) (𝕜 := ℝ)
        (β := fun _ : Unit => ℝ) ()‖ * (‖matrixContinuousLinearMap R‖ * Cbeta))
    β R hseθ hmodel h hΩ hLinBound hBetaBound hGapTail hseThetaStar
    (regressionBootstrapLinearRestrictionStatisticFinSucc_eventually_abs_bound_of_beta_bound
      (R := R) (X := X) (y := y) hBetaBound)
    hse

set_option linter.style.longLine false in
/-- Robust-feasible HC specialization of the Definition 10.2 beta-bound
concrete finite OLS t-statistic transfer. -/
theorem
    chapter10_indexed_bootstrap_regression_tstat_distribution_standardNormal_finSucc_olsBetaOrZero_of_gapEnvelope_beta_bound_of_robustFeasibleHCMomentConditions
    [IsProbabilityMeasure μ]
    {k : Type*} [Fintype k] [DecidableEq k]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    {seThetaStar : ∀ n, Ω → (Fin (n + 1) → Fin (n + 1)) → ℝ}
    {Clin Cbeta : ℝ}
    (β : k → ℝ) (R : Matrix Unit k ℝ)
    (hseθ : 0 < linearRestrictionStdError R (heteroAsymCov μ X e))
    (hm : RobustFeasibleHCMomentConditions μ X e y β)
    (hΩ : (scoreCovMat μ X e).PosDef)
    (hLinBound : ∀ᶠ n in atTop,
      ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
        ‖regressionLinearizedScoreFinSucc μ X e n ω ωs‖ ≤ Clin)
    (hBetaBound : ∀ᶠ n in atTop,
      ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
        ‖regressionBootstrapBetaStatisticFinSucc X y n ω ωs‖ ≤ Cbeta)
    (hGapTail : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          ((ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
              Measure (Fin (n + 1) → Fin (n + 1)))).real
            {ωs |
              δ ≤ regressionBootstrapBetaLinearizedGapEnvelopeFinSucc
                μ X e β n ω ωs})
        atTop (fun _ => 0))
    (hseThetaStar : ∀ n ω, Measurable (seThetaStar n ω))
    (hse :
      TendstoInBootstrapProbabilityIndexed μ
        (fun n _ =>
          (ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
              Measure (Fin (n + 1) → Fin (n + 1))))
        seThetaStar
        (fun _ => linearRestrictionStdError R (heteroAsymCov μ X e))) :
    TendstoInBootstrapDistributionIndexed μ
      (fun n _ =>
        (ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))))
      (fun n ω ωs (_ : Unit) =>
        regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs /
          seThetaStar n ω ωs)
      (gaussianReal 0 1) (fun z : ℝ => fun _ : Unit => z) :=
  chapter10_indexed_bootstrap_regression_tstat_distribution_standardNormal_finSucc_olsBetaOrZero_of_gapEnvelope_beta_bound
    (μ := μ) (X := X) (e := e) (y := y)
    β R hseθ hm.model hm.toScoreCLTConditions hΩ hLinBound hBetaBound
    hGapTail hseThetaStar hse

set_option linter.style.longLine false in
/-- Bounded concrete ordinary-bootstrap OLS absolute t-statistic transfer
where the scalar numerator bound is discharged by the coefficient-statistic
norm bound. -/
theorem
    chapter10_indexed_bootstrap_regression_abs_tstat_standardNormalAbs_finSucc_olsBetaOrZero_of_gapEnvelope_beta_bound
    [IsProbabilityMeasure μ]
    {k : Type*} [Fintype k] [DecidableEq k]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    {seThetaStar : ∀ n, Ω → (Fin (n + 1) → Fin (n + 1)) → ℝ}
    {Clin Cbeta : ℝ}
    (β : k → ℝ) (R : Matrix Unit k ℝ)
    (hseθ : 0 < linearRestrictionStdError R (heteroAsymCov μ X e))
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (h : ScoreCLTConditions μ X e)
    (hΩ : (scoreCovMat μ X e).PosDef)
    (hLinBound : ∀ᶠ n in atTop,
      ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
        ‖regressionLinearizedScoreFinSucc μ X e n ω ωs‖ ≤ Clin)
    (hBetaBound : ∀ᶠ n in atTop,
      ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
        ‖regressionBootstrapBetaStatisticFinSucc X y n ω ωs‖ ≤ Cbeta)
    (hGapTail : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          ((ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
              Measure (Fin (n + 1) → Fin (n + 1)))).real
            {ωs |
              δ ≤ regressionBootstrapBetaLinearizedGapEnvelopeFinSucc
                μ X e β n ω ωs})
        atTop (fun _ => 0))
    (hseThetaStar : ∀ n ω, Measurable (seThetaStar n ω))
    (hse :
      TendstoInBootstrapProbabilityIndexed μ
        (fun n _ =>
          (ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
              Measure (Fin (n + 1) → Fin (n + 1))))
        seThetaStar
        (fun _ => linearRestrictionStdError R (heteroAsymCov μ X e))) :
    TendstoInBootstrapWeakDistributionIndexed μ
      (fun n _ =>
        (ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))))
      (fun n ω ωs =>
        |regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs /
          seThetaStar n ω ωs|)
      ((gaussianReal 0 1).map (fun z : ℝ => |z|)) (fun z : ℝ => z) :=
  chapter10_indexed_bootstrap_regression_abs_tstat_standardNormalAbs_finSucc_olsBetaOrZero_of_gapEnvelope_bounds
    (μ := μ) (X := X) (e := e) (y := y)
    (Cnum := ‖PiLp.proj (p := (2 : ℝ≥0∞)) (𝕜 := ℝ)
        (β := fun _ : Unit => ℝ) ()‖ * (‖matrixContinuousLinearMap R‖ * Cbeta))
    β R hseθ hmodel h hΩ hLinBound hBetaBound hGapTail hseThetaStar
    (regressionBootstrapLinearRestrictionStatisticFinSucc_eventually_abs_bound_of_beta_bound
      (R := R) (X := X) (y := y) hBetaBound)
    hse

set_option linter.style.longLine false in
/-- Robust-feasible HC specialization of the beta-bound concrete finite OLS
absolute t-statistic transfer. -/
theorem
    chapter10_indexed_bootstrap_regression_abs_tstat_standardNormalAbs_finSucc_olsBetaOrZero_of_gapEnvelope_beta_bound_of_robustFeasibleHCMomentConditions
    [IsProbabilityMeasure μ]
    {k : Type*} [Fintype k] [DecidableEq k]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    {seThetaStar : ∀ n, Ω → (Fin (n + 1) → Fin (n + 1)) → ℝ}
    {Clin Cbeta : ℝ}
    (β : k → ℝ) (R : Matrix Unit k ℝ)
    (hseθ : 0 < linearRestrictionStdError R (heteroAsymCov μ X e))
    (hm : RobustFeasibleHCMomentConditions μ X e y β)
    (hΩ : (scoreCovMat μ X e).PosDef)
    (hLinBound : ∀ᶠ n in atTop,
      ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
        ‖regressionLinearizedScoreFinSucc μ X e n ω ωs‖ ≤ Clin)
    (hBetaBound : ∀ᶠ n in atTop,
      ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
        ‖regressionBootstrapBetaStatisticFinSucc X y n ω ωs‖ ≤ Cbeta)
    (hGapTail : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          ((ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
              Measure (Fin (n + 1) → Fin (n + 1)))).real
            {ωs |
              δ ≤ regressionBootstrapBetaLinearizedGapEnvelopeFinSucc
                μ X e β n ω ωs})
        atTop (fun _ => 0))
    (hseThetaStar : ∀ n ω, Measurable (seThetaStar n ω))
    (hse :
      TendstoInBootstrapProbabilityIndexed μ
        (fun n _ =>
          (ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
              Measure (Fin (n + 1) → Fin (n + 1))))
        seThetaStar
        (fun _ => linearRestrictionStdError R (heteroAsymCov μ X e))) :
    TendstoInBootstrapWeakDistributionIndexed μ
      (fun n _ =>
        (ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))))
      (fun n ω ωs =>
        |regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs /
          seThetaStar n ω ωs|)
      ((gaussianReal 0 1).map (fun z : ℝ => |z|)) (fun z : ℝ => z) :=
  chapter10_indexed_bootstrap_regression_abs_tstat_standardNormalAbs_finSucc_olsBetaOrZero_of_gapEnvelope_beta_bound
    (μ := μ) (X := X) (e := e) (y := y)
    β R hseθ hm.model hm.toScoreCLTConditions hΩ hLinBound hBetaBound
    hGapTail hseThetaStar hse

set_option linter.style.longLine false in
/-- Hansen Definition 10.2 face of the beta-bound concrete finite OLS
absolute t-statistic transfer. -/
theorem
    chapter10_indexed_bootstrap_regression_abs_tstat_distribution_standardNormalAbs_finSucc_olsBetaOrZero_of_gapEnvelope_beta_bound
    [IsProbabilityMeasure μ]
    {k : Type*} [Fintype k] [DecidableEq k]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    {seThetaStar : ∀ n, Ω → (Fin (n + 1) → Fin (n + 1)) → ℝ}
    {Clin Cbeta : ℝ}
    (β : k → ℝ) (R : Matrix Unit k ℝ)
    (hseθ : 0 < linearRestrictionStdError R (heteroAsymCov μ X e))
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (h : ScoreCLTConditions μ X e)
    (hΩ : (scoreCovMat μ X e).PosDef)
    (hLinBound : ∀ᶠ n in atTop,
      ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
        ‖regressionLinearizedScoreFinSucc μ X e n ω ωs‖ ≤ Clin)
    (hBetaBound : ∀ᶠ n in atTop,
      ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
        ‖regressionBootstrapBetaStatisticFinSucc X y n ω ωs‖ ≤ Cbeta)
    (hGapTail : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          ((ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
              Measure (Fin (n + 1) → Fin (n + 1)))).real
            {ωs |
              δ ≤ regressionBootstrapBetaLinearizedGapEnvelopeFinSucc
                μ X e β n ω ωs})
        atTop (fun _ => 0))
    (hseThetaStar : ∀ n ω, Measurable (seThetaStar n ω))
    (hse :
      TendstoInBootstrapProbabilityIndexed μ
        (fun n _ =>
          (ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
              Measure (Fin (n + 1) → Fin (n + 1))))
        seThetaStar
        (fun _ => linearRestrictionStdError R (heteroAsymCov μ X e))) :
    TendstoInBootstrapDistributionIndexed μ
      (fun n _ =>
        (ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))))
      (fun n ω ωs (_ : Unit) =>
        |regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs /
          seThetaStar n ω ωs|)
      ((gaussianReal 0 1).map (fun z : ℝ => |z|))
      (fun z : ℝ => fun _ : Unit => z) :=
  chapter10_indexed_bootstrap_regression_abs_tstat_distribution_standardNormalAbs_finSucc_olsBetaOrZero_of_gapEnvelope_bounds
    (μ := μ) (X := X) (e := e) (y := y)
    (Cnum := ‖PiLp.proj (p := (2 : ℝ≥0∞)) (𝕜 := ℝ)
        (β := fun _ : Unit => ℝ) ()‖ * (‖matrixContinuousLinearMap R‖ * Cbeta))
    β R hseθ hmodel h hΩ hLinBound hBetaBound hGapTail hseThetaStar
    (regressionBootstrapLinearRestrictionStatisticFinSucc_eventually_abs_bound_of_beta_bound
      (R := R) (X := X) (y := y) hBetaBound)
    hse

set_option linter.style.longLine false in
/-- Robust-feasible HC specialization of the Definition 10.2 beta-bound
concrete finite OLS absolute t-statistic transfer. -/
theorem
    chapter10_indexed_bootstrap_regression_abs_tstat_distribution_standardNormalAbs_finSucc_olsBetaOrZero_of_gapEnvelope_beta_bound_of_robustFeasibleHCMomentConditions
    [IsProbabilityMeasure μ]
    {k : Type*} [Fintype k] [DecidableEq k]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    {seThetaStar : ∀ n, Ω → (Fin (n + 1) → Fin (n + 1)) → ℝ}
    {Clin Cbeta : ℝ}
    (β : k → ℝ) (R : Matrix Unit k ℝ)
    (hseθ : 0 < linearRestrictionStdError R (heteroAsymCov μ X e))
    (hm : RobustFeasibleHCMomentConditions μ X e y β)
    (hΩ : (scoreCovMat μ X e).PosDef)
    (hLinBound : ∀ᶠ n in atTop,
      ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
        ‖regressionLinearizedScoreFinSucc μ X e n ω ωs‖ ≤ Clin)
    (hBetaBound : ∀ᶠ n in atTop,
      ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
        ‖regressionBootstrapBetaStatisticFinSucc X y n ω ωs‖ ≤ Cbeta)
    (hGapTail : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          ((ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
              Measure (Fin (n + 1) → Fin (n + 1)))).real
            {ωs |
              δ ≤ regressionBootstrapBetaLinearizedGapEnvelopeFinSucc
                μ X e β n ω ωs})
        atTop (fun _ => 0))
    (hseThetaStar : ∀ n ω, Measurable (seThetaStar n ω))
    (hse :
      TendstoInBootstrapProbabilityIndexed μ
        (fun n _ =>
          (ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
              Measure (Fin (n + 1) → Fin (n + 1))))
        seThetaStar
        (fun _ => linearRestrictionStdError R (heteroAsymCov μ X e))) :
    TendstoInBootstrapDistributionIndexed μ
      (fun n _ =>
        (ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))))
      (fun n ω ωs (_ : Unit) =>
        |regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs /
          seThetaStar n ω ωs|)
      ((gaussianReal 0 1).map (fun z : ℝ => |z|))
      (fun z : ℝ => fun _ : Unit => z) :=
  chapter10_indexed_bootstrap_regression_abs_tstat_distribution_standardNormalAbs_finSucc_olsBetaOrZero_of_gapEnvelope_beta_bound
    (μ := μ) (X := X) (e := e) (y := y)
    β R hseθ hm.model hm.toScoreCLTConditions hΩ hLinBound hBetaBound
    hGapTail hseThetaStar hse

set_option linter.style.longLine false in
/-- Concrete transformed ordinary-bootstrap OLS statistic transfer with
compact-tail control discharged by deterministic eventual norm bounds.

This bounded-statistic face works directly in the transformed `Rᵀ` space:
model-specific work is a norm bound for the transformed linearized statistic,
a norm bound for the concrete transformed OLS statistic, and conditional
closeness between those two transformed statistics. -/
theorem
    chapter10_indexed_bootstrap_regression_theta_gaussian_finSucc_olsBetaOrZero_of_linearizedScore_bounds
    [IsProbabilityMeasure μ]
    {k q : Type*} [Fintype k] [Fintype q] [DecidableEq k] [DecidableEq q]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    {Clin Ctheta : ℝ}
    (R : Matrix k q ℝ)
    (h : ScoreCLTConditions μ X e)
    (hΩ : (scoreCovMat μ X e).PosDef)
    (hLinBound : ∀ᶠ n in atTop,
      ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
        ‖matrixContinuousLinearMap Rᵀ
          (regressionLinearizedScoreFinSucc μ X e n ω ωs)‖ ≤ Clin)
    (hThetaBound : ∀ᶠ n in atTop,
      ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
        ‖regressionBootstrapThetaStatisticFinSucc R X y n ω ωs‖ ≤ Ctheta)
    (hclose : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          ((ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
              Measure (Fin (n + 1) → Fin (n + 1)))).real
            {ωs |
              δ ≤ dist (regressionBootstrapThetaStatisticFinSucc R X y n ω ωs)
                (matrixContinuousLinearMap Rᵀ
                  (regressionLinearizedScoreFinSucc μ X e n ω ωs))})
        atTop (fun _ => 0)) :
    TendstoInBootstrapWeakDistributionIndexed μ
      (fun n _ =>
        (ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))))
      (fun n ω ωs => regressionBootstrapThetaStatisticFinSucc R X y n ω ωs)
      (multivariateGaussian (0 : EuclideanSpace ℝ q)
        (Rᵀ * heteroAsymCov μ X e * R))
      (fun z : EuclideanSpace ℝ q => z) := by
  simpa [Matrix.transpose_transpose] using
    chapter10_indexed_bootstrap_delta_method_gaussian_of_compact_tail_closeness
      (μ := μ)
      (Pstar := fun n _ =>
        (ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))))
      (Tstar := fun n ω ωs =>
        regressionLinearizedScoreFinSucc μ X e n ω ωs)
      (thetaStar := fun n ω ωs =>
        regressionBootstrapThetaStatisticFinSucc R X y n ω ωs)
      (V := heteroAsymCov μ X e) Rᵀ
      (heteroAsymCov_posSemidef_of_scoreCLTConditions
        (μ := μ) (X := X) (e := e) h)
      (chapter10_indexed_bootstrap_regression_linearizedScore_gaussian_finSucc_resampleMean
        (μ := μ) (X := X) (e := e) h hΩ)
      (fun _ _ => inferInstance) (fun _ _ => measurable_of_finite _)
      (fun _ _ => measurable_of_finite _)
      (chapter10_indexed_bootstrap_euclidean_pair_compactTail_of_eventually_norm_bound
        (μ := μ)
        (Pstar := fun n _ =>
          (ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
              Measure (Fin (n + 1) → Fin (n + 1))))
        (Zstar := fun n ω ωs =>
          matrixContinuousLinearMap Rᵀ
            (regressionLinearizedScoreFinSucc μ X e n ω ωs))
        (Zstar' := fun n ω ωs =>
          regressionBootstrapThetaStatisticFinSucc R X y n ω ωs)
        hLinBound hThetaBound)
      hclose

set_option linter.style.longLine false in
/-- Robust-feasible HC specialization of the bounded concrete transformed
ordinary-bootstrap OLS statistic transfer. -/
theorem
    chapter10_indexed_bootstrap_regression_theta_gaussian_finSucc_olsBetaOrZero_of_linearizedScore_bounds_of_robustFeasibleHCMomentConditions
    [IsProbabilityMeasure μ]
    {k q : Type*} [Fintype k] [Fintype q] [DecidableEq k] [DecidableEq q]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    {Clin Ctheta : ℝ}
    (β : k → ℝ) (R : Matrix k q ℝ)
    (hm : RobustFeasibleHCMomentConditions μ X e y β)
    (hΩ : (scoreCovMat μ X e).PosDef)
    (hLinBound : ∀ᶠ n in atTop,
      ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
        ‖matrixContinuousLinearMap Rᵀ
          (regressionLinearizedScoreFinSucc μ X e n ω ωs)‖ ≤ Clin)
    (hThetaBound : ∀ᶠ n in atTop,
      ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
        ‖regressionBootstrapThetaStatisticFinSucc R X y n ω ωs‖ ≤ Ctheta)
    (hclose : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          ((ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
              Measure (Fin (n + 1) → Fin (n + 1)))).real
            {ωs |
              δ ≤ dist (regressionBootstrapThetaStatisticFinSucc R X y n ω ωs)
                (matrixContinuousLinearMap Rᵀ
                  (regressionLinearizedScoreFinSucc μ X e n ω ωs))})
        atTop (fun _ => 0)) :
    TendstoInBootstrapWeakDistributionIndexed μ
      (fun n _ =>
        (ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))))
      (fun n ω ωs => regressionBootstrapThetaStatisticFinSucc R X y n ω ωs)
      (multivariateGaussian (0 : EuclideanSpace ℝ q)
        (Rᵀ * heteroAsymCov μ X e * R))
      (fun z : EuclideanSpace ℝ q => z) :=
  chapter10_indexed_bootstrap_regression_theta_gaussian_finSucc_olsBetaOrZero_of_linearizedScore_bounds
    (μ := μ) (X := X) (e := e) (y := y)
    R hm.toScoreCLTConditions hΩ hLinBound hThetaBound hclose

set_option linter.style.longLine false in
/-- Hansen Definition 10.2 face of the bounded concrete transformed
ordinary-bootstrap OLS statistic transfer. -/
theorem
    chapter10_indexed_bootstrap_regression_theta_gaussian_distribution_finSucc_olsBetaOrZero_of_linearizedScore_bounds
    [IsProbabilityMeasure μ]
    {k q : Type*} [Fintype k] [Fintype q] [DecidableEq k] [DecidableEq q]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    {Clin Ctheta : ℝ}
    (R : Matrix k q ℝ)
    (h : ScoreCLTConditions μ X e)
    (hΩ : (scoreCovMat μ X e).PosDef)
    (hLinBound : ∀ᶠ n in atTop,
      ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
        ‖matrixContinuousLinearMap Rᵀ
          (regressionLinearizedScoreFinSucc μ X e n ω ωs)‖ ≤ Clin)
    (hThetaBound : ∀ᶠ n in atTop,
      ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
        ‖regressionBootstrapThetaStatisticFinSucc R X y n ω ωs‖ ≤ Ctheta)
    (hclose : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          ((ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
              Measure (Fin (n + 1) → Fin (n + 1)))).real
            {ωs |
              δ ≤ dist (regressionBootstrapThetaStatisticFinSucc R X y n ω ωs)
                (matrixContinuousLinearMap Rᵀ
                  (regressionLinearizedScoreFinSucc μ X e n ω ωs))})
        atTop (fun _ => 0))
    (hfrontier : ∀ x : q → ℝ,
      ContinuousAt
          (fun y =>
            vectorCDF
              (multivariateGaussian (0 : EuclideanSpace ℝ q)
                (Rᵀ * heteroAsymCov μ X e * R))
              (fun z : EuclideanSpace ℝ q => (z : q → ℝ)) y) x →
        ((multivariateGaussian (0 : EuclideanSpace ℝ q)
            (Rᵀ * heteroAsymCov μ X e * R)).map
            (fun z : EuclideanSpace ℝ q => (z : q → ℝ)))
          (frontier {z : q → ℝ | coordinateLE z x}) = 0) :
    TendstoInBootstrapDistributionIndexed μ
      (fun n _ =>
        (ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))))
      (fun n ω ωs =>
        ((regressionBootstrapThetaStatisticFinSucc R X y n ω ωs :
          EuclideanSpace ℝ q) : q → ℝ))
      (multivariateGaussian (0 : EuclideanSpace ℝ q)
        (Rᵀ * heteroAsymCov μ X e * R))
      (fun z : EuclideanSpace ℝ q => (z : q → ℝ)) := by
  simpa [Matrix.transpose_transpose] using
    chapter10_indexed_bootstrap_delta_method_gaussian_distribution_of_compact_tail_closeness
      (μ := μ)
      (Pstar := fun n _ =>
        (ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))))
      (Tstar := fun n ω ωs =>
        regressionLinearizedScoreFinSucc μ X e n ω ωs)
      (thetaStar := fun n ω ωs =>
        regressionBootstrapThetaStatisticFinSucc R X y n ω ωs)
      (V := heteroAsymCov μ X e) Rᵀ
      (heteroAsymCov_posSemidef_of_scoreCLTConditions
        (μ := μ) (X := X) (e := e) h)
      (chapter10_indexed_bootstrap_regression_linearizedScore_gaussian_finSucc_resampleMean
        (μ := μ) (X := X) (e := e) h hΩ)
      (fun _ _ => inferInstance) (fun _ _ => measurable_of_finite _)
      (fun _ _ => measurable_of_finite _)
      (chapter10_indexed_bootstrap_euclidean_pair_compactTail_of_eventually_norm_bound
        (μ := μ)
        (Pstar := fun n _ =>
          (ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
              Measure (Fin (n + 1) → Fin (n + 1))))
        (Zstar := fun n ω ωs =>
          matrixContinuousLinearMap Rᵀ
            (regressionLinearizedScoreFinSucc μ X e n ω ωs))
        (Zstar' := fun n ω ωs =>
          regressionBootstrapThetaStatisticFinSucc R X y n ω ωs)
        hLinBound hThetaBound)
      hclose
      (by simpa [Matrix.transpose_transpose] using hfrontier)

set_option linter.style.longLine false in
/-- Positive-definite transformed-covariance CDF face of the bounded concrete
transformed ordinary-bootstrap OLS statistic transfer. -/
theorem
    chapter10_indexed_bootstrap_regression_theta_gaussian_distribution_posDef_finSucc_olsBetaOrZero_of_linearizedScore_bounds
    [IsProbabilityMeasure μ]
    {k q : Type*} [Fintype k] [Fintype q] [DecidableEq k] [DecidableEq q]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    {Clin Ctheta : ℝ}
    (R : Matrix k q ℝ)
    (h : ScoreCLTConditions μ X e)
    (hΩ : (scoreCovMat μ X e).PosDef)
    (hRVR : (Rᵀ * heteroAsymCov μ X e * R).PosDef)
    (hLinBound : ∀ᶠ n in atTop,
      ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
        ‖matrixContinuousLinearMap Rᵀ
          (regressionLinearizedScoreFinSucc μ X e n ω ωs)‖ ≤ Clin)
    (hThetaBound : ∀ᶠ n in atTop,
      ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
        ‖regressionBootstrapThetaStatisticFinSucc R X y n ω ωs‖ ≤ Ctheta)
    (hclose : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          ((ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
              Measure (Fin (n + 1) → Fin (n + 1)))).real
            {ωs |
              δ ≤ dist (regressionBootstrapThetaStatisticFinSucc R X y n ω ωs)
                (matrixContinuousLinearMap Rᵀ
                  (regressionLinearizedScoreFinSucc μ X e n ω ωs))})
        atTop (fun _ => 0)) :
    TendstoInBootstrapDistributionIndexed μ
      (fun n _ =>
        (ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))))
      (fun n ω ωs =>
        ((regressionBootstrapThetaStatisticFinSucc R X y n ω ωs :
          EuclideanSpace ℝ q) : q → ℝ))
      (multivariateGaussian (0 : EuclideanSpace ℝ q)
        (Rᵀ * heteroAsymCov μ X e * R))
      (fun z : EuclideanSpace ℝ q => (z : q → ℝ)) :=
  chapter10_indexed_bootstrap_regression_theta_gaussian_distribution_finSucc_olsBetaOrZero_of_linearizedScore_bounds
    (μ := μ) (X := X) (e := e) (y := y) R h hΩ hLinBound hThetaBound
    hclose
    (fun x _hx => multivariateGaussian_coordinateLE_frontier_null_of_posDef hRVR x)

set_option linter.style.longLine false in
/-- Robust-feasible HC Hansen Definition 10.2 face of the bounded concrete
transformed ordinary-bootstrap OLS statistic transfer. -/
theorem
    chapter10_indexed_bootstrap_regression_theta_gaussian_distribution_finSucc_olsBetaOrZero_of_linearizedScore_bounds_of_robustFeasibleHCMomentConditions
    [IsProbabilityMeasure μ]
    {k q : Type*} [Fintype k] [Fintype q] [DecidableEq k] [DecidableEq q]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    {Clin Ctheta : ℝ}
    (β : k → ℝ) (R : Matrix k q ℝ)
    (hm : RobustFeasibleHCMomentConditions μ X e y β)
    (hΩ : (scoreCovMat μ X e).PosDef)
    (hLinBound : ∀ᶠ n in atTop,
      ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
        ‖matrixContinuousLinearMap Rᵀ
          (regressionLinearizedScoreFinSucc μ X e n ω ωs)‖ ≤ Clin)
    (hThetaBound : ∀ᶠ n in atTop,
      ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
        ‖regressionBootstrapThetaStatisticFinSucc R X y n ω ωs‖ ≤ Ctheta)
    (hclose : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          ((ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
              Measure (Fin (n + 1) → Fin (n + 1)))).real
            {ωs |
              δ ≤ dist (regressionBootstrapThetaStatisticFinSucc R X y n ω ωs)
                (matrixContinuousLinearMap Rᵀ
                  (regressionLinearizedScoreFinSucc μ X e n ω ωs))})
        atTop (fun _ => 0))
    (hfrontier : ∀ x : q → ℝ,
      ContinuousAt
          (fun y =>
            vectorCDF
              (multivariateGaussian (0 : EuclideanSpace ℝ q)
                (Rᵀ * heteroAsymCov μ X e * R))
              (fun z : EuclideanSpace ℝ q => (z : q → ℝ)) y) x →
        ((multivariateGaussian (0 : EuclideanSpace ℝ q)
            (Rᵀ * heteroAsymCov μ X e * R)).map
            (fun z : EuclideanSpace ℝ q => (z : q → ℝ)))
          (frontier {z : q → ℝ | coordinateLE z x}) = 0) :
    TendstoInBootstrapDistributionIndexed μ
      (fun n _ =>
        (ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))))
      (fun n ω ωs =>
        ((regressionBootstrapThetaStatisticFinSucc R X y n ω ωs :
          EuclideanSpace ℝ q) : q → ℝ))
      (multivariateGaussian (0 : EuclideanSpace ℝ q)
        (Rᵀ * heteroAsymCov μ X e * R))
      (fun z : EuclideanSpace ℝ q => (z : q → ℝ)) :=
  chapter10_indexed_bootstrap_regression_theta_gaussian_distribution_finSucc_olsBetaOrZero_of_linearizedScore_bounds
    (μ := μ) (X := X) (e := e) (y := y)
    R hm.toScoreCLTConditions hΩ hLinBound hThetaBound hclose hfrontier

set_option linter.style.longLine false in
/-- Positive-definite transformed-covariance robust-feasible HC CDF face of
the bounded concrete transformed ordinary-bootstrap OLS statistic transfer. -/
theorem
    chapter10_indexed_bootstrap_regression_theta_gaussian_distribution_posDef_finSucc_olsBetaOrZero_of_linearizedScore_bounds_of_robustFeasibleHCMomentConditions
    [IsProbabilityMeasure μ]
    {k q : Type*} [Fintype k] [Fintype q] [DecidableEq k] [DecidableEq q]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    {Clin Ctheta : ℝ}
    (β : k → ℝ) (R : Matrix k q ℝ)
    (hm : RobustFeasibleHCMomentConditions μ X e y β)
    (hΩ : (scoreCovMat μ X e).PosDef)
    (hRVR : (Rᵀ * heteroAsymCov μ X e * R).PosDef)
    (hLinBound : ∀ᶠ n in atTop,
      ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
        ‖matrixContinuousLinearMap Rᵀ
          (regressionLinearizedScoreFinSucc μ X e n ω ωs)‖ ≤ Clin)
    (hThetaBound : ∀ᶠ n in atTop,
      ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
        ‖regressionBootstrapThetaStatisticFinSucc R X y n ω ωs‖ ≤ Ctheta)
    (hclose : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          ((ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
              Measure (Fin (n + 1) → Fin (n + 1)))).real
            {ωs |
              δ ≤ dist (regressionBootstrapThetaStatisticFinSucc R X y n ω ωs)
                (matrixContinuousLinearMap Rᵀ
                  (regressionLinearizedScoreFinSucc μ X e n ω ωs))})
        atTop (fun _ => 0)) :
    TendstoInBootstrapDistributionIndexed μ
      (fun n _ =>
        (ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))))
      (fun n ω ωs =>
        ((regressionBootstrapThetaStatisticFinSucc R X y n ω ωs :
          EuclideanSpace ℝ q) : q → ℝ))
      (multivariateGaussian (0 : EuclideanSpace ℝ q)
        (Rᵀ * heteroAsymCov μ X e * R))
      (fun z : EuclideanSpace ℝ q => (z : q → ℝ)) :=
  chapter10_indexed_bootstrap_regression_theta_gaussian_distribution_posDef_finSucc_olsBetaOrZero_of_linearizedScore_bounds
    (μ := μ) (X := X) (e := e) (y := y) R hm.toScoreCLTConditions
    hΩ hRVR hLinBound hThetaBound hclose

set_option linter.style.longLine false in
/-- Coefficient-bound face of the concrete transformed ordinary-bootstrap OLS
statistic transfer.

This variant asks for deterministic bounds on the linearized and concrete
coefficient statistics; the operator-norm bridge supplies the transformed
compact-tail bounds required by
`chapter10_indexed_bootstrap_regression_theta_gaussian_finSucc_olsBetaOrZero_of_linearizedScore_bounds`. -/
theorem
    chapter10_indexed_bootstrap_regression_theta_gaussian_finSucc_olsBetaOrZero_of_linearizedScore_coefficient_bounds
    [IsProbabilityMeasure μ]
    {k q : Type*} [Fintype k] [Fintype q] [DecidableEq k] [DecidableEq q]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    {Clin Cbeta : ℝ}
    (R : Matrix k q ℝ)
    (h : ScoreCLTConditions μ X e)
    (hΩ : (scoreCovMat μ X e).PosDef)
    (hLinBound : ∀ᶠ n in atTop,
      ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
        ‖regressionLinearizedScoreFinSucc μ X e n ω ωs‖ ≤ Clin)
    (hBetaBound : ∀ᶠ n in atTop,
      ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
        ‖regressionBootstrapBetaStatisticFinSucc X y n ω ωs‖ ≤ Cbeta)
    (hclose : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          ((ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
              Measure (Fin (n + 1) → Fin (n + 1)))).real
            {ωs |
              δ ≤ dist (regressionBootstrapThetaStatisticFinSucc R X y n ω ωs)
                (matrixContinuousLinearMap Rᵀ
                  (regressionLinearizedScoreFinSucc μ X e n ω ωs))})
        atTop (fun _ => 0)) :
    TendstoInBootstrapWeakDistributionIndexed μ
      (fun n _ =>
        (ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))))
      (fun n ω ωs => regressionBootstrapThetaStatisticFinSucc R X y n ω ωs)
      (multivariateGaussian (0 : EuclideanSpace ℝ q)
        (Rᵀ * heteroAsymCov μ X e * R))
      (fun z : EuclideanSpace ℝ q => z) :=
  chapter10_indexed_bootstrap_regression_theta_gaussian_finSucc_olsBetaOrZero_of_linearizedScore_bounds
    (μ := μ) (X := X) (e := e) (y := y)
    (Clin := ‖matrixContinuousLinearMap Rᵀ‖ * Clin)
    (Ctheta := ‖matrixContinuousLinearMap Rᵀ‖ * Cbeta)
    R h hΩ
    (regressionLinearizedScoreFinSucc_transformed_eventually_norm_bound_of_bound
      (μ := μ) (X := X) (e := e) R hLinBound)
    (regressionBootstrapThetaStatisticFinSucc_eventually_norm_bound_of_beta_bound
      (X := X) (y := y) R hBetaBound)
    hclose

set_option linter.style.longLine false in
/-- Robust-feasible HC specialization of the coefficient-bound concrete
transformed ordinary-bootstrap OLS statistic transfer. -/
theorem
    chapter10_indexed_bootstrap_regression_theta_gaussian_finSucc_olsBetaOrZero_of_linearizedScore_coefficient_bounds_of_robustFeasibleHCMomentConditions
    [IsProbabilityMeasure μ]
    {k q : Type*} [Fintype k] [Fintype q] [DecidableEq k] [DecidableEq q]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    {Clin Cbeta : ℝ}
    (β : k → ℝ) (R : Matrix k q ℝ)
    (hm : RobustFeasibleHCMomentConditions μ X e y β)
    (hΩ : (scoreCovMat μ X e).PosDef)
    (hLinBound : ∀ᶠ n in atTop,
      ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
        ‖regressionLinearizedScoreFinSucc μ X e n ω ωs‖ ≤ Clin)
    (hBetaBound : ∀ᶠ n in atTop,
      ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
        ‖regressionBootstrapBetaStatisticFinSucc X y n ω ωs‖ ≤ Cbeta)
    (hclose : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          ((ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
              Measure (Fin (n + 1) → Fin (n + 1)))).real
            {ωs |
              δ ≤ dist (regressionBootstrapThetaStatisticFinSucc R X y n ω ωs)
                (matrixContinuousLinearMap Rᵀ
                  (regressionLinearizedScoreFinSucc μ X e n ω ωs))})
        atTop (fun _ => 0)) :
    TendstoInBootstrapWeakDistributionIndexed μ
      (fun n _ =>
        (ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))))
      (fun n ω ωs => regressionBootstrapThetaStatisticFinSucc R X y n ω ωs)
      (multivariateGaussian (0 : EuclideanSpace ℝ q)
        (Rᵀ * heteroAsymCov μ X e * R))
      (fun z : EuclideanSpace ℝ q => z) :=
  chapter10_indexed_bootstrap_regression_theta_gaussian_finSucc_olsBetaOrZero_of_linearizedScore_coefficient_bounds
    (μ := μ) (X := X) (e := e) (y := y)
    R hm.toScoreCLTConditions hΩ hLinBound hBetaBound hclose

set_option linter.style.longLine false in
/-- Hansen Definition 10.2 face of the coefficient-bound transformed
ordinary-bootstrap OLS statistic transfer. -/
theorem
    chapter10_indexed_bootstrap_regression_theta_gaussian_distribution_finSucc_olsBetaOrZero_of_linearizedScore_coefficient_bounds
    [IsProbabilityMeasure μ]
    {k q : Type*} [Fintype k] [Fintype q] [DecidableEq k] [DecidableEq q]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    {Clin Cbeta : ℝ}
    (R : Matrix k q ℝ)
    (h : ScoreCLTConditions μ X e)
    (hΩ : (scoreCovMat μ X e).PosDef)
    (hLinBound : ∀ᶠ n in atTop,
      ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
        ‖regressionLinearizedScoreFinSucc μ X e n ω ωs‖ ≤ Clin)
    (hBetaBound : ∀ᶠ n in atTop,
      ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
        ‖regressionBootstrapBetaStatisticFinSucc X y n ω ωs‖ ≤ Cbeta)
    (hclose : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          ((ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
              Measure (Fin (n + 1) → Fin (n + 1)))).real
            {ωs |
              δ ≤ dist (regressionBootstrapThetaStatisticFinSucc R X y n ω ωs)
                (matrixContinuousLinearMap Rᵀ
                  (regressionLinearizedScoreFinSucc μ X e n ω ωs))})
        atTop (fun _ => 0))
    (hfrontier : ∀ x : q → ℝ,
      ContinuousAt
          (fun y =>
            vectorCDF
              (multivariateGaussian (0 : EuclideanSpace ℝ q)
                (Rᵀ * heteroAsymCov μ X e * R))
              (fun z : EuclideanSpace ℝ q => (z : q → ℝ)) y) x →
        ((multivariateGaussian (0 : EuclideanSpace ℝ q)
            (Rᵀ * heteroAsymCov μ X e * R)).map
            (fun z : EuclideanSpace ℝ q => (z : q → ℝ)))
          (frontier {z : q → ℝ | coordinateLE z x}) = 0) :
    TendstoInBootstrapDistributionIndexed μ
      (fun n _ =>
        (ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))))
      (fun n ω ωs =>
        ((regressionBootstrapThetaStatisticFinSucc R X y n ω ωs :
          EuclideanSpace ℝ q) : q → ℝ))
      (multivariateGaussian (0 : EuclideanSpace ℝ q)
        (Rᵀ * heteroAsymCov μ X e * R))
      (fun z : EuclideanSpace ℝ q => (z : q → ℝ)) :=
  chapter10_indexed_bootstrap_regression_theta_gaussian_distribution_finSucc_olsBetaOrZero_of_linearizedScore_bounds
    (μ := μ) (X := X) (e := e) (y := y)
    (Clin := ‖matrixContinuousLinearMap Rᵀ‖ * Clin)
    (Ctheta := ‖matrixContinuousLinearMap Rᵀ‖ * Cbeta)
    R h hΩ
    (regressionLinearizedScoreFinSucc_transformed_eventually_norm_bound_of_bound
      (μ := μ) (X := X) (e := e) R hLinBound)
    (regressionBootstrapThetaStatisticFinSucc_eventually_norm_bound_of_beta_bound
      (X := X) (y := y) R hBetaBound)
    hclose hfrontier

set_option linter.style.longLine false in
/-- Positive-definite transformed-covariance CDF face of the coefficient-bound
transformed ordinary-bootstrap OLS statistic transfer. -/
theorem
    chapter10_indexed_bootstrap_regression_theta_gaussian_distribution_posDef_finSucc_olsBetaOrZero_of_linearizedScore_coefficient_bounds
    [IsProbabilityMeasure μ]
    {k q : Type*} [Fintype k] [Fintype q] [DecidableEq k] [DecidableEq q]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    {Clin Cbeta : ℝ}
    (R : Matrix k q ℝ)
    (h : ScoreCLTConditions μ X e)
    (hΩ : (scoreCovMat μ X e).PosDef)
    (hRVR : (Rᵀ * heteroAsymCov μ X e * R).PosDef)
    (hLinBound : ∀ᶠ n in atTop,
      ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
        ‖regressionLinearizedScoreFinSucc μ X e n ω ωs‖ ≤ Clin)
    (hBetaBound : ∀ᶠ n in atTop,
      ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
        ‖regressionBootstrapBetaStatisticFinSucc X y n ω ωs‖ ≤ Cbeta)
    (hclose : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          ((ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
              Measure (Fin (n + 1) → Fin (n + 1)))).real
            {ωs |
              δ ≤ dist (regressionBootstrapThetaStatisticFinSucc R X y n ω ωs)
                (matrixContinuousLinearMap Rᵀ
                  (regressionLinearizedScoreFinSucc μ X e n ω ωs))})
        atTop (fun _ => 0)) :
    TendstoInBootstrapDistributionIndexed μ
      (fun n _ =>
        (ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))))
      (fun n ω ωs =>
        ((regressionBootstrapThetaStatisticFinSucc R X y n ω ωs :
          EuclideanSpace ℝ q) : q → ℝ))
      (multivariateGaussian (0 : EuclideanSpace ℝ q)
        (Rᵀ * heteroAsymCov μ X e * R))
      (fun z : EuclideanSpace ℝ q => (z : q → ℝ)) :=
  chapter10_indexed_bootstrap_regression_theta_gaussian_distribution_finSucc_olsBetaOrZero_of_linearizedScore_coefficient_bounds
    (μ := μ) (X := X) (e := e) (y := y)
    R h hΩ hLinBound hBetaBound hclose
    (fun x _hx => multivariateGaussian_coordinateLE_frontier_null_of_posDef hRVR x)

set_option linter.style.longLine false in
/-- Robust-feasible HC Hansen Definition 10.2 face of the coefficient-bound
transformed ordinary-bootstrap OLS statistic transfer. -/
theorem
    chapter10_indexed_bootstrap_regression_theta_gaussian_distribution_finSucc_olsBetaOrZero_of_linearizedScore_coefficient_bounds_of_robustFeasibleHCMomentConditions
    [IsProbabilityMeasure μ]
    {k q : Type*} [Fintype k] [Fintype q] [DecidableEq k] [DecidableEq q]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    {Clin Cbeta : ℝ}
    (β : k → ℝ) (R : Matrix k q ℝ)
    (hm : RobustFeasibleHCMomentConditions μ X e y β)
    (hΩ : (scoreCovMat μ X e).PosDef)
    (hLinBound : ∀ᶠ n in atTop,
      ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
        ‖regressionLinearizedScoreFinSucc μ X e n ω ωs‖ ≤ Clin)
    (hBetaBound : ∀ᶠ n in atTop,
      ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
        ‖regressionBootstrapBetaStatisticFinSucc X y n ω ωs‖ ≤ Cbeta)
    (hclose : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          ((ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
              Measure (Fin (n + 1) → Fin (n + 1)))).real
            {ωs |
              δ ≤ dist (regressionBootstrapThetaStatisticFinSucc R X y n ω ωs)
                (matrixContinuousLinearMap Rᵀ
                  (regressionLinearizedScoreFinSucc μ X e n ω ωs))})
        atTop (fun _ => 0))
    (hfrontier : ∀ x : q → ℝ,
      ContinuousAt
          (fun y =>
            vectorCDF
              (multivariateGaussian (0 : EuclideanSpace ℝ q)
                (Rᵀ * heteroAsymCov μ X e * R))
              (fun z : EuclideanSpace ℝ q => (z : q → ℝ)) y) x →
        ((multivariateGaussian (0 : EuclideanSpace ℝ q)
            (Rᵀ * heteroAsymCov μ X e * R)).map
            (fun z : EuclideanSpace ℝ q => (z : q → ℝ)))
          (frontier {z : q → ℝ | coordinateLE z x}) = 0) :
    TendstoInBootstrapDistributionIndexed μ
      (fun n _ =>
        (ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))))
      (fun n ω ωs =>
        ((regressionBootstrapThetaStatisticFinSucc R X y n ω ωs :
          EuclideanSpace ℝ q) : q → ℝ))
      (multivariateGaussian (0 : EuclideanSpace ℝ q)
        (Rᵀ * heteroAsymCov μ X e * R))
      (fun z : EuclideanSpace ℝ q => (z : q → ℝ)) :=
  chapter10_indexed_bootstrap_regression_theta_gaussian_distribution_finSucc_olsBetaOrZero_of_linearizedScore_coefficient_bounds
    (μ := μ) (X := X) (e := e) (y := y)
    R hm.toScoreCLTConditions hΩ hLinBound hBetaBound hclose hfrontier

set_option linter.style.longLine false in
/-- Positive-definite transformed-covariance robust-feasible HC CDF face of
the coefficient-bound transformed ordinary-bootstrap OLS statistic transfer. -/
theorem
    chapter10_indexed_bootstrap_regression_theta_gaussian_distribution_posDef_finSucc_olsBetaOrZero_of_linearizedScore_coefficient_bounds_of_robustFeasibleHCMomentConditions
    [IsProbabilityMeasure μ]
    {k q : Type*} [Fintype k] [Fintype q] [DecidableEq k] [DecidableEq q]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    {Clin Cbeta : ℝ}
    (β : k → ℝ) (R : Matrix k q ℝ)
    (hm : RobustFeasibleHCMomentConditions μ X e y β)
    (hΩ : (scoreCovMat μ X e).PosDef)
    (hRVR : (Rᵀ * heteroAsymCov μ X e * R).PosDef)
    (hLinBound : ∀ᶠ n in atTop,
      ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
        ‖regressionLinearizedScoreFinSucc μ X e n ω ωs‖ ≤ Clin)
    (hBetaBound : ∀ᶠ n in atTop,
      ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
        ‖regressionBootstrapBetaStatisticFinSucc X y n ω ωs‖ ≤ Cbeta)
    (hclose : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          ((ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
              Measure (Fin (n + 1) → Fin (n + 1)))).real
            {ωs |
              δ ≤ dist (regressionBootstrapThetaStatisticFinSucc R X y n ω ωs)
                (matrixContinuousLinearMap Rᵀ
                  (regressionLinearizedScoreFinSucc μ X e n ω ωs))})
        atTop (fun _ => 0)) :
    TendstoInBootstrapDistributionIndexed μ
      (fun n _ =>
        (ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))))
      (fun n ω ωs =>
        ((regressionBootstrapThetaStatisticFinSucc R X y n ω ωs :
          EuclideanSpace ℝ q) : q → ℝ))
      (multivariateGaussian (0 : EuclideanSpace ℝ q)
        (Rᵀ * heteroAsymCov μ X e * R))
      (fun z : EuclideanSpace ℝ q => (z : q → ℝ)) :=
  chapter10_indexed_bootstrap_regression_theta_gaussian_distribution_posDef_finSucc_olsBetaOrZero_of_linearizedScore_coefficient_bounds
    (μ := μ) (X := X) (e := e) (y := y)
    R hm.toScoreCLTConditions hΩ hRVR hLinBound hBetaBound hclose

/-- Hansen Definition 10.2 face of the ordinary-bootstrap nonlinear
regression coefficient-transfer route.

This is the CDF counterpart of
`chapter10_indexed_bootstrap_regression_theta_gaussian_finSucc_of_linearizedScore_tight`:
conditional closeness and compact-tail control transfer the ordinary-bootstrap
linearized score CLT to the concrete transformed statistic, and the usual
Gaussian lower-orthant null-frontier premise converts weak convergence to
Definition 10.2 distribution convergence. -/
theorem
    chapter10_indexed_bootstrap_regression_theta_gaussian_distribution_finSucc_of_linearizedScore_tight
    [IsProbabilityMeasure μ]
    {k q : Type*} [Fintype k] [Fintype q] [DecidableEq k] [DecidableEq q]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ}
    {TbetaStar :
      ∀ n, Ω → (Fin (n + 1) → Fin (n + 1)) → EuclideanSpace ℝ k}
    (R : Matrix k q ℝ)
    (h : ScoreCLTConditions μ X e)
    (hΩ : (scoreCovMat μ X e).PosDef)
    (hTbetaStar : ∀ n ω, Measurable (TbetaStar n ω))
    (hTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set (EuclideanSpace ℝ k), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω =>
            ((ProbabilityTheory.uniformOn
              (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                Measure (Fin (n + 1) → Fin (n + 1)))).real
              {ωs | regressionLinearizedScoreFinSucc μ X e n ω ωs ∉ K})
          atTop (fun _ => 0) ∧
        TendstoInMeasure μ
          (fun n ω =>
            ((ProbabilityTheory.uniformOn
              (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                Measure (Fin (n + 1) → Fin (n + 1)))).real
              {ωs | TbetaStar n ω ωs ∉ K})
          atTop (fun _ => 0))
    (hclose : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          ((ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
              Measure (Fin (n + 1) → Fin (n + 1)))).real
            {ωs |
              δ ≤ dist (TbetaStar n ω ωs)
                (regressionLinearizedScoreFinSucc μ X e n ω ωs)})
        atTop (fun _ => 0))
    (hfrontier : ∀ x : q → ℝ,
      ContinuousAt
          (fun y =>
            vectorCDF
              (multivariateGaussian (0 : EuclideanSpace ℝ q)
                (Rᵀ * heteroAsymCov μ X e * R))
              (fun z : EuclideanSpace ℝ q => (z : q → ℝ)) y) x →
        ((multivariateGaussian (0 : EuclideanSpace ℝ q)
            (Rᵀ * heteroAsymCov μ X e * R)).map
            (fun z : EuclideanSpace ℝ q => (z : q → ℝ)))
          (frontier {z : q → ℝ | coordinateLE z x}) = 0) :
    TendstoInBootstrapDistributionIndexed μ
      (fun n _ =>
        (ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))))
      (fun n ω ωs =>
        ((matrixContinuousLinearMap Rᵀ (TbetaStar n ω ωs) :
          EuclideanSpace ℝ q) : q → ℝ))
      (multivariateGaussian (0 : EuclideanSpace ℝ q)
        (Rᵀ * heteroAsymCov μ X e * R))
      (fun z : EuclideanSpace ℝ q => (z : q → ℝ)) := by
  simpa [Matrix.transpose_transpose] using
    chapter10_indexed_bootstrap_delta_method_gaussian_distribution
      (μ := μ)
      (Pstar := fun n _ =>
        (ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))))
      (Tstar := TbetaStar)
      (V := heteroAsymCov μ X e) (G := Rᵀ)
      (heteroAsymCov_posSemidef_of_scoreCLTConditions
        (μ := μ) (X := X) (e := e) h)
      (chapter10_indexed_bootstrap_regression_beta_gaussian_finSucc_of_linearizedScore_tight
        (μ := μ) (X := X) (e := e) h hΩ hTbetaStar hTail hclose)
      (fun n ω => inferInstance) hTbetaStar
      (by simpa [Matrix.transpose_transpose] using hfrontier)

/-- Positive-definite transformed-covariance CDF face of the
ordinary-bootstrap nonlinear regression coefficient-transfer route.

When `R' heteroAsymCov R` is positive definite, the transformed Gaussian
lower-orthant frontier premise in
`chapter10_indexed_bootstrap_regression_theta_gaussian_distribution_finSucc_of_linearizedScore_tight`
is automatic. -/
theorem
    chapter10_indexed_bootstrap_regression_theta_gaussian_distribution_posDef_finSucc_of_linearizedScore_tight
    [IsProbabilityMeasure μ]
    {k q : Type*} [Fintype k] [Fintype q] [DecidableEq k] [DecidableEq q]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ}
    {TbetaStar :
      ∀ n, Ω → (Fin (n + 1) → Fin (n + 1)) → EuclideanSpace ℝ k}
    (R : Matrix k q ℝ)
    (h : ScoreCLTConditions μ X e)
    (hΩ : (scoreCovMat μ X e).PosDef)
    (hRVR : (Rᵀ * heteroAsymCov μ X e * R).PosDef)
    (hTbetaStar : ∀ n ω, Measurable (TbetaStar n ω))
    (hTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set (EuclideanSpace ℝ k), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω =>
            ((ProbabilityTheory.uniformOn
              (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                Measure (Fin (n + 1) → Fin (n + 1)))).real
              {ωs | regressionLinearizedScoreFinSucc μ X e n ω ωs ∉ K})
          atTop (fun _ => 0) ∧
        TendstoInMeasure μ
          (fun n ω =>
            ((ProbabilityTheory.uniformOn
              (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                Measure (Fin (n + 1) → Fin (n + 1)))).real
              {ωs | TbetaStar n ω ωs ∉ K})
          atTop (fun _ => 0))
    (hclose : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          ((ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
              Measure (Fin (n + 1) → Fin (n + 1)))).real
            {ωs |
              δ ≤ dist (TbetaStar n ω ωs)
                (regressionLinearizedScoreFinSucc μ X e n ω ωs)})
        atTop (fun _ => 0)) :
    TendstoInBootstrapDistributionIndexed μ
      (fun n _ =>
        (ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))))
      (fun n ω ωs =>
        ((matrixContinuousLinearMap Rᵀ (TbetaStar n ω ωs) :
          EuclideanSpace ℝ q) : q → ℝ))
      (multivariateGaussian (0 : EuclideanSpace ℝ q)
        (Rᵀ * heteroAsymCov μ X e * R))
      (fun z : EuclideanSpace ℝ q => (z : q → ℝ)) :=
  chapter10_indexed_bootstrap_regression_theta_gaussian_distribution_finSucc_of_linearizedScore_tight
    (μ := μ) R h hΩ hTbetaStar hTail hclose
    (fun x _hx => multivariateGaussian_coordinateLE_frontier_null_of_posDef hRVR x)

set_option linter.style.longLine false in
/-- Hansen Definition 10.2 face of the concrete ordinary-bootstrap OLS
coefficient-transfer route. -/
theorem
    chapter10_indexed_bootstrap_regression_theta_gaussian_distribution_finSucc_olsBetaOrZero_of_linearizedScore_tight
    [IsProbabilityMeasure μ]
    {k q : Type*} [Fintype k] [Fintype q] [DecidableEq k] [DecidableEq q]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    (R : Matrix k q ℝ)
    (h : ScoreCLTConditions μ X e)
    (hΩ : (scoreCovMat μ X e).PosDef)
    (hTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set (EuclideanSpace ℝ k), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω =>
            ((ProbabilityTheory.uniformOn
              (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                Measure (Fin (n + 1) → Fin (n + 1)))).real
              {ωs | regressionLinearizedScoreFinSucc μ X e n ω ωs ∉ K})
          atTop (fun _ => 0) ∧
        TendstoInMeasure μ
          (fun n ω =>
            ((ProbabilityTheory.uniformOn
              (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                Measure (Fin (n + 1) → Fin (n + 1)))).real
              {ωs | regressionBootstrapBetaStatisticFinSucc X y n ω ωs ∉ K})
          atTop (fun _ => 0))
    (hclose : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          ((ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
              Measure (Fin (n + 1) → Fin (n + 1)))).real
            {ωs |
              δ ≤ dist (regressionBootstrapBetaStatisticFinSucc X y n ω ωs)
                (regressionLinearizedScoreFinSucc μ X e n ω ωs)})
        atTop (fun _ => 0))
    (hfrontier : ∀ x : q → ℝ,
      ContinuousAt
          (fun y =>
            vectorCDF
              (multivariateGaussian (0 : EuclideanSpace ℝ q)
                (Rᵀ * heteroAsymCov μ X e * R))
              (fun z : EuclideanSpace ℝ q => (z : q → ℝ)) y) x →
        ((multivariateGaussian (0 : EuclideanSpace ℝ q)
            (Rᵀ * heteroAsymCov μ X e * R)).map
            (fun z : EuclideanSpace ℝ q => (z : q → ℝ)))
          (frontier {z : q → ℝ | coordinateLE z x}) = 0) :
    TendstoInBootstrapDistributionIndexed μ
      (fun n _ =>
        (ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))))
      (fun n ω ωs =>
        ((regressionBootstrapThetaStatisticFinSucc R X y n ω ωs :
          EuclideanSpace ℝ q) : q → ℝ))
      (multivariateGaussian (0 : EuclideanSpace ℝ q)
        (Rᵀ * heteroAsymCov μ X e * R))
      (fun z : EuclideanSpace ℝ q => (z : q → ℝ)) := by
  simpa [regressionBootstrapThetaStatisticFinSucc] using
    chapter10_indexed_bootstrap_regression_theta_gaussian_distribution_finSucc_of_linearizedScore_tight
      (μ := μ) (X := X) (e := e)
      (TbetaStar := fun n ω ωs =>
        regressionBootstrapBetaStatisticFinSucc X y n ω ωs)
      R h hΩ (fun _ _ => measurable_of_finite _) hTail hclose hfrontier

set_option linter.style.longLine false in
/-- Positive-definite transformed-covariance CDF face of the concrete
ordinary-bootstrap OLS coefficient-transfer route. -/
theorem
    chapter10_indexed_bootstrap_regression_theta_gaussian_distribution_posDef_finSucc_olsBetaOrZero_of_linearizedScore_tight
    [IsProbabilityMeasure μ]
    {k q : Type*} [Fintype k] [Fintype q] [DecidableEq k] [DecidableEq q]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    (R : Matrix k q ℝ)
    (h : ScoreCLTConditions μ X e)
    (hΩ : (scoreCovMat μ X e).PosDef)
    (hRVR : (Rᵀ * heteroAsymCov μ X e * R).PosDef)
    (hTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set (EuclideanSpace ℝ k), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω =>
            ((ProbabilityTheory.uniformOn
              (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                Measure (Fin (n + 1) → Fin (n + 1)))).real
              {ωs | regressionLinearizedScoreFinSucc μ X e n ω ωs ∉ K})
          atTop (fun _ => 0) ∧
        TendstoInMeasure μ
          (fun n ω =>
            ((ProbabilityTheory.uniformOn
              (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                Measure (Fin (n + 1) → Fin (n + 1)))).real
              {ωs | regressionBootstrapBetaStatisticFinSucc X y n ω ωs ∉ K})
          atTop (fun _ => 0))
    (hclose : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          ((ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
              Measure (Fin (n + 1) → Fin (n + 1)))).real
            {ωs |
              δ ≤ dist (regressionBootstrapBetaStatisticFinSucc X y n ω ωs)
                (regressionLinearizedScoreFinSucc μ X e n ω ωs)})
        atTop (fun _ => 0)) :
    TendstoInBootstrapDistributionIndexed μ
      (fun n _ =>
        (ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))))
      (fun n ω ωs =>
        ((regressionBootstrapThetaStatisticFinSucc R X y n ω ωs :
          EuclideanSpace ℝ q) : q → ℝ))
      (multivariateGaussian (0 : EuclideanSpace ℝ q)
        (Rᵀ * heteroAsymCov μ X e * R))
      (fun z : EuclideanSpace ℝ q => (z : q → ℝ)) :=
  chapter10_indexed_bootstrap_regression_theta_gaussian_distribution_finSucc_olsBetaOrZero_of_linearizedScore_tight
    (μ := μ) (X := X) (e := e) (y := y) R h hΩ hTail hclose
    (fun x _hx => multivariateGaussian_coordinateLE_frontier_null_of_posDef hRVR x)

set_option linter.style.longLine false in
/-- Hansen Definition 10.2 face of the concrete ordinary-bootstrap OLS
gap-envelope transfer. -/
theorem
    chapter10_indexed_bootstrap_regression_theta_gaussian_distribution_finSucc_olsBetaOrZero_of_gapEnvelope_tight
    [IsProbabilityMeasure μ]
    {k q : Type*} [Fintype k] [Fintype q] [DecidableEq k] [DecidableEq q]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    (β : k → ℝ) (R : Matrix k q ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (h : ScoreCLTConditions μ X e)
    (hΩ : (scoreCovMat μ X e).PosDef)
    (hTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set (EuclideanSpace ℝ k), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω =>
            ((ProbabilityTheory.uniformOn
              (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                Measure (Fin (n + 1) → Fin (n + 1)))).real
              {ωs | regressionLinearizedScoreFinSucc μ X e n ω ωs ∉ K})
          atTop (fun _ => 0) ∧
        TendstoInMeasure μ
          (fun n ω =>
            ((ProbabilityTheory.uniformOn
              (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                Measure (Fin (n + 1) → Fin (n + 1)))).real
              {ωs | regressionBootstrapBetaStatisticFinSucc X y n ω ωs ∉ K})
          atTop (fun _ => 0))
    (hGapTail : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          ((ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
              Measure (Fin (n + 1) → Fin (n + 1)))).real
            {ωs |
              δ ≤ regressionBootstrapBetaLinearizedGapEnvelopeFinSucc
                μ X e β n ω ωs})
        atTop (fun _ => 0))
    (hfrontier : ∀ x : q → ℝ,
      ContinuousAt
          (fun y =>
            vectorCDF
              (multivariateGaussian (0 : EuclideanSpace ℝ q)
                (Rᵀ * heteroAsymCov μ X e * R))
              (fun z : EuclideanSpace ℝ q => (z : q → ℝ)) y) x →
        ((multivariateGaussian (0 : EuclideanSpace ℝ q)
            (Rᵀ * heteroAsymCov μ X e * R)).map
            (fun z : EuclideanSpace ℝ q => (z : q → ℝ)))
          (frontier {z : q → ℝ | coordinateLE z x}) = 0) :
    TendstoInBootstrapDistributionIndexed μ
      (fun n _ =>
        (ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))))
      (fun n ω ωs =>
        ((regressionBootstrapThetaStatisticFinSucc R X y n ω ωs :
          EuclideanSpace ℝ q) : q → ℝ))
      (multivariateGaussian (0 : EuclideanSpace ℝ q)
        (Rᵀ * heteroAsymCov μ X e * R))
      (fun z : EuclideanSpace ℝ q => (z : q → ℝ)) := by
  simpa [regressionBootstrapThetaStatisticFinSucc, Matrix.transpose_transpose] using
    chapter10_indexed_bootstrap_delta_method_gaussian_distribution
      (μ := μ)
      (Pstar := fun n _ =>
        (ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))))
      (Tstar := fun n ω ωs =>
        regressionBootstrapBetaStatisticFinSucc X y n ω ωs)
      (V := heteroAsymCov μ X e) (G := Rᵀ)
      (heteroAsymCov_posSemidef_of_scoreCLTConditions
        (μ := μ) (X := X) (e := e) h)
      (chapter10_indexed_bootstrap_regression_beta_gaussian_finSucc_olsBetaOrZero_of_gapEnvelope_tight
        (μ := μ) (X := X) (e := e) (y := y)
        β hmodel h hΩ hTail hGapTail)
      (fun n ω => inferInstance) (fun n ω => measurable_of_finite _)
      (by simpa [Matrix.transpose_transpose] using hfrontier)

set_option linter.style.longLine false in
/-- Positive-definite transformed-covariance CDF face of the concrete
ordinary-bootstrap OLS gap-envelope transfer. -/
theorem
    chapter10_indexed_bootstrap_regression_theta_gaussian_distribution_posDef_finSucc_olsBetaOrZero_of_gapEnvelope_tight
    [IsProbabilityMeasure μ]
    {k q : Type*} [Fintype k] [Fintype q] [DecidableEq k] [DecidableEq q]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    (β : k → ℝ) (R : Matrix k q ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (h : ScoreCLTConditions μ X e)
    (hΩ : (scoreCovMat μ X e).PosDef)
    (hRVR : (Rᵀ * heteroAsymCov μ X e * R).PosDef)
    (hTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set (EuclideanSpace ℝ k), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω =>
            ((ProbabilityTheory.uniformOn
              (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                Measure (Fin (n + 1) → Fin (n + 1)))).real
              {ωs | regressionLinearizedScoreFinSucc μ X e n ω ωs ∉ K})
          atTop (fun _ => 0) ∧
        TendstoInMeasure μ
          (fun n ω =>
            ((ProbabilityTheory.uniformOn
              (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                Measure (Fin (n + 1) → Fin (n + 1)))).real
              {ωs | regressionBootstrapBetaStatisticFinSucc X y n ω ωs ∉ K})
          atTop (fun _ => 0))
    (hGapTail : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          ((ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
              Measure (Fin (n + 1) → Fin (n + 1)))).real
            {ωs |
              δ ≤ regressionBootstrapBetaLinearizedGapEnvelopeFinSucc
                μ X e β n ω ωs})
        atTop (fun _ => 0)) :
    TendstoInBootstrapDistributionIndexed μ
      (fun n _ =>
        (ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))))
      (fun n ω ωs =>
        ((regressionBootstrapThetaStatisticFinSucc R X y n ω ωs :
          EuclideanSpace ℝ q) : q → ℝ))
      (multivariateGaussian (0 : EuclideanSpace ℝ q)
        (Rᵀ * heteroAsymCov μ X e * R))
      (fun z : EuclideanSpace ℝ q => (z : q → ℝ)) :=
  chapter10_indexed_bootstrap_regression_theta_gaussian_distribution_finSucc_olsBetaOrZero_of_gapEnvelope_tight
    (μ := μ) (X := X) (e := e) (y := y) β R hmodel h hΩ hTail hGapTail
    (fun x _hx => multivariateGaussian_coordinateLE_frontier_null_of_posDef hRVR x)

set_option linter.style.longLine false in
/-- Robust-feasible HC Hansen Definition 10.2 face of the concrete
ordinary-bootstrap OLS gap-envelope transfer. -/
theorem
    chapter10_indexed_bootstrap_regression_theta_gaussian_distribution_finSucc_olsBetaOrZero_of_gapEnvelope_tight_of_robustFeasibleHCMomentConditions
    [IsProbabilityMeasure μ]
    {k q : Type*} [Fintype k] [Fintype q] [DecidableEq k] [DecidableEq q]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    (β : k → ℝ) (R : Matrix k q ℝ)
    (hm : RobustFeasibleHCMomentConditions μ X e y β)
    (hΩ : (scoreCovMat μ X e).PosDef)
    (hTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set (EuclideanSpace ℝ k), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω =>
            ((ProbabilityTheory.uniformOn
              (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                Measure (Fin (n + 1) → Fin (n + 1)))).real
              {ωs | regressionLinearizedScoreFinSucc μ X e n ω ωs ∉ K})
          atTop (fun _ => 0) ∧
        TendstoInMeasure μ
          (fun n ω =>
            ((ProbabilityTheory.uniformOn
              (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                Measure (Fin (n + 1) → Fin (n + 1)))).real
              {ωs | regressionBootstrapBetaStatisticFinSucc X y n ω ωs ∉ K})
          atTop (fun _ => 0))
    (hGapTail : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          ((ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
              Measure (Fin (n + 1) → Fin (n + 1)))).real
            {ωs |
              δ ≤ regressionBootstrapBetaLinearizedGapEnvelopeFinSucc
                μ X e β n ω ωs})
        atTop (fun _ => 0))
    (hfrontier : ∀ x : q → ℝ,
      ContinuousAt
          (fun y =>
            vectorCDF
              (multivariateGaussian (0 : EuclideanSpace ℝ q)
                (Rᵀ * heteroAsymCov μ X e * R))
              (fun z : EuclideanSpace ℝ q => (z : q → ℝ)) y) x →
        ((multivariateGaussian (0 : EuclideanSpace ℝ q)
            (Rᵀ * heteroAsymCov μ X e * R)).map
            (fun z : EuclideanSpace ℝ q => (z : q → ℝ)))
          (frontier {z : q → ℝ | coordinateLE z x}) = 0) :
    TendstoInBootstrapDistributionIndexed μ
      (fun n _ =>
        (ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))))
      (fun n ω ωs =>
        ((regressionBootstrapThetaStatisticFinSucc R X y n ω ωs :
          EuclideanSpace ℝ q) : q → ℝ))
      (multivariateGaussian (0 : EuclideanSpace ℝ q)
        (Rᵀ * heteroAsymCov μ X e * R))
      (fun z : EuclideanSpace ℝ q => (z : q → ℝ)) :=
  chapter10_indexed_bootstrap_regression_theta_gaussian_distribution_finSucc_olsBetaOrZero_of_gapEnvelope_tight
    (μ := μ) (X := X) (e := e) (y := y)
    β R hm.model hm.toScoreCLTConditions hΩ hTail hGapTail hfrontier

set_option linter.style.longLine false in
/-- Positive-definite transformed-covariance robust-feasible HC CDF face of
the concrete ordinary-bootstrap OLS gap-envelope transfer. -/
theorem
    chapter10_indexed_bootstrap_regression_theta_gaussian_distribution_posDef_finSucc_olsBetaOrZero_of_gapEnvelope_tight_of_robustFeasibleHCMomentConditions
    [IsProbabilityMeasure μ]
    {k q : Type*} [Fintype k] [Fintype q] [DecidableEq k] [DecidableEq q]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    (β : k → ℝ) (R : Matrix k q ℝ)
    (hm : RobustFeasibleHCMomentConditions μ X e y β)
    (hΩ : (scoreCovMat μ X e).PosDef)
    (hRVR : (Rᵀ * heteroAsymCov μ X e * R).PosDef)
    (hTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set (EuclideanSpace ℝ k), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω =>
            ((ProbabilityTheory.uniformOn
              (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                Measure (Fin (n + 1) → Fin (n + 1)))).real
              {ωs | regressionLinearizedScoreFinSucc μ X e n ω ωs ∉ K})
          atTop (fun _ => 0) ∧
        TendstoInMeasure μ
          (fun n ω =>
            ((ProbabilityTheory.uniformOn
              (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                Measure (Fin (n + 1) → Fin (n + 1)))).real
              {ωs | regressionBootstrapBetaStatisticFinSucc X y n ω ωs ∉ K})
          atTop (fun _ => 0))
    (hGapTail : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          ((ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
              Measure (Fin (n + 1) → Fin (n + 1)))).real
            {ωs |
              δ ≤ regressionBootstrapBetaLinearizedGapEnvelopeFinSucc
                μ X e β n ω ωs})
        atTop (fun _ => 0)) :
    TendstoInBootstrapDistributionIndexed μ
      (fun n _ =>
        (ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))))
      (fun n ω ωs =>
        ((regressionBootstrapThetaStatisticFinSucc R X y n ω ωs :
          EuclideanSpace ℝ q) : q → ℝ))
      (multivariateGaussian (0 : EuclideanSpace ℝ q)
        (Rᵀ * heteroAsymCov μ X e * R))
      (fun z : EuclideanSpace ℝ q => (z : q → ℝ)) :=
  chapter10_indexed_bootstrap_regression_theta_gaussian_distribution_posDef_finSucc_olsBetaOrZero_of_gapEnvelope_tight
    (μ := μ) (X := X) (e := e) (y := y) β R hm.model
    hm.toScoreCLTConditions hΩ hRVR hTail hGapTail

set_option linter.style.longLine false in
/-- Hansen Definition 10.2 face of the bounded concrete ordinary-bootstrap
OLS gap-envelope transfer. -/
theorem
    chapter10_indexed_bootstrap_regression_theta_gaussian_distribution_finSucc_olsBetaOrZero_of_gapEnvelope_bounds
    [IsProbabilityMeasure μ]
    {k q : Type*} [Fintype k] [Fintype q] [DecidableEq k] [DecidableEq q]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    {Clin Cbeta : ℝ}
    (β : k → ℝ) (R : Matrix k q ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (h : ScoreCLTConditions μ X e)
    (hΩ : (scoreCovMat μ X e).PosDef)
    (hLinBound : ∀ᶠ n in atTop,
      ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
        ‖regressionLinearizedScoreFinSucc μ X e n ω ωs‖ ≤ Clin)
    (hBetaBound : ∀ᶠ n in atTop,
      ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
        ‖regressionBootstrapBetaStatisticFinSucc X y n ω ωs‖ ≤ Cbeta)
    (hGapTail : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          ((ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
              Measure (Fin (n + 1) → Fin (n + 1)))).real
            {ωs |
              δ ≤ regressionBootstrapBetaLinearizedGapEnvelopeFinSucc
                μ X e β n ω ωs})
        atTop (fun _ => 0))
    (hfrontier : ∀ x : q → ℝ,
      ContinuousAt
          (fun y =>
            vectorCDF
              (multivariateGaussian (0 : EuclideanSpace ℝ q)
                (Rᵀ * heteroAsymCov μ X e * R))
              (fun z : EuclideanSpace ℝ q => (z : q → ℝ)) y) x →
        ((multivariateGaussian (0 : EuclideanSpace ℝ q)
            (Rᵀ * heteroAsymCov μ X e * R)).map
            (fun z : EuclideanSpace ℝ q => (z : q → ℝ)))
          (frontier {z : q → ℝ | coordinateLE z x}) = 0) :
    TendstoInBootstrapDistributionIndexed μ
      (fun n _ =>
        (ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))))
      (fun n ω ωs =>
        ((regressionBootstrapThetaStatisticFinSucc R X y n ω ωs :
          EuclideanSpace ℝ q) : q → ℝ))
      (multivariateGaussian (0 : EuclideanSpace ℝ q)
        (Rᵀ * heteroAsymCov μ X e * R))
      (fun z : EuclideanSpace ℝ q => (z : q → ℝ)) :=
  chapter10_indexed_bootstrap_regression_theta_gaussian_distribution_finSucc_olsBetaOrZero_of_gapEnvelope_tight
    (μ := μ) (X := X) (e := e) (y := y) β R hmodel h hΩ
    (chapter10_indexed_bootstrap_euclidean_pair_compactTail_of_eventually_norm_bound
      (μ := μ)
      (Pstar := fun n _ =>
        (ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))))
      (Zstar := fun n ω ωs => regressionLinearizedScoreFinSucc μ X e n ω ωs)
      (Zstar' := fun n ω ωs => regressionBootstrapBetaStatisticFinSucc X y n ω ωs)
      hLinBound hBetaBound)
    hGapTail hfrontier

set_option linter.style.longLine false in
/-- Positive-definite transformed-covariance CDF face of the bounded concrete
ordinary-bootstrap OLS gap-envelope transfer. -/
theorem
    chapter10_indexed_bootstrap_regression_theta_gaussian_distribution_posDef_finSucc_olsBetaOrZero_of_gapEnvelope_bounds
    [IsProbabilityMeasure μ]
    {k q : Type*} [Fintype k] [Fintype q] [DecidableEq k] [DecidableEq q]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    {Clin Cbeta : ℝ}
    (β : k → ℝ) (R : Matrix k q ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (h : ScoreCLTConditions μ X e)
    (hΩ : (scoreCovMat μ X e).PosDef)
    (hRVR : (Rᵀ * heteroAsymCov μ X e * R).PosDef)
    (hLinBound : ∀ᶠ n in atTop,
      ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
        ‖regressionLinearizedScoreFinSucc μ X e n ω ωs‖ ≤ Clin)
    (hBetaBound : ∀ᶠ n in atTop,
      ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
        ‖regressionBootstrapBetaStatisticFinSucc X y n ω ωs‖ ≤ Cbeta)
    (hGapTail : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          ((ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
              Measure (Fin (n + 1) → Fin (n + 1)))).real
            {ωs |
              δ ≤ regressionBootstrapBetaLinearizedGapEnvelopeFinSucc
                μ X e β n ω ωs})
        atTop (fun _ => 0)) :
    TendstoInBootstrapDistributionIndexed μ
      (fun n _ =>
        (ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))))
      (fun n ω ωs =>
        ((regressionBootstrapThetaStatisticFinSucc R X y n ω ωs :
          EuclideanSpace ℝ q) : q → ℝ))
      (multivariateGaussian (0 : EuclideanSpace ℝ q)
        (Rᵀ * heteroAsymCov μ X e * R))
      (fun z : EuclideanSpace ℝ q => (z : q → ℝ)) :=
  chapter10_indexed_bootstrap_regression_theta_gaussian_distribution_finSucc_olsBetaOrZero_of_gapEnvelope_bounds
    (μ := μ) (X := X) (e := e) (y := y) β R hmodel h hΩ
    hLinBound hBetaBound hGapTail
    (fun x _hx => multivariateGaussian_coordinateLE_frontier_null_of_posDef hRVR x)

set_option linter.style.longLine false in
/-- Robust-feasible HC Hansen Definition 10.2 face of the bounded concrete
ordinary-bootstrap OLS gap-envelope transfer. -/
theorem
    chapter10_indexed_bootstrap_regression_theta_gaussian_distribution_finSucc_olsBetaOrZero_of_gapEnvelope_bounds_of_robustFeasibleHCMomentConditions
    [IsProbabilityMeasure μ]
    {k q : Type*} [Fintype k] [Fintype q] [DecidableEq k] [DecidableEq q]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    {Clin Cbeta : ℝ}
    (β : k → ℝ) (R : Matrix k q ℝ)
    (hm : RobustFeasibleHCMomentConditions μ X e y β)
    (hΩ : (scoreCovMat μ X e).PosDef)
    (hLinBound : ∀ᶠ n in atTop,
      ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
        ‖regressionLinearizedScoreFinSucc μ X e n ω ωs‖ ≤ Clin)
    (hBetaBound : ∀ᶠ n in atTop,
      ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
        ‖regressionBootstrapBetaStatisticFinSucc X y n ω ωs‖ ≤ Cbeta)
    (hGapTail : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          ((ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
              Measure (Fin (n + 1) → Fin (n + 1)))).real
            {ωs |
              δ ≤ regressionBootstrapBetaLinearizedGapEnvelopeFinSucc
                μ X e β n ω ωs})
        atTop (fun _ => 0))
    (hfrontier : ∀ x : q → ℝ,
      ContinuousAt
          (fun y =>
            vectorCDF
              (multivariateGaussian (0 : EuclideanSpace ℝ q)
                (Rᵀ * heteroAsymCov μ X e * R))
              (fun z : EuclideanSpace ℝ q => (z : q → ℝ)) y) x →
        ((multivariateGaussian (0 : EuclideanSpace ℝ q)
            (Rᵀ * heteroAsymCov μ X e * R)).map
            (fun z : EuclideanSpace ℝ q => (z : q → ℝ)))
          (frontier {z : q → ℝ | coordinateLE z x}) = 0) :
    TendstoInBootstrapDistributionIndexed μ
      (fun n _ =>
        (ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))))
      (fun n ω ωs =>
        ((regressionBootstrapThetaStatisticFinSucc R X y n ω ωs :
          EuclideanSpace ℝ q) : q → ℝ))
      (multivariateGaussian (0 : EuclideanSpace ℝ q)
        (Rᵀ * heteroAsymCov μ X e * R))
      (fun z : EuclideanSpace ℝ q => (z : q → ℝ)) :=
  chapter10_indexed_bootstrap_regression_theta_gaussian_distribution_finSucc_olsBetaOrZero_of_gapEnvelope_bounds
    (μ := μ) (X := X) (e := e) (y := y)
    β R hm.model hm.toScoreCLTConditions hΩ hLinBound hBetaBound hGapTail
    hfrontier

set_option linter.style.longLine false in
/-- Positive-definite transformed-covariance robust-feasible HC CDF face of
the bounded concrete ordinary-bootstrap OLS gap-envelope transfer. -/
theorem
    chapter10_indexed_bootstrap_regression_theta_gaussian_distribution_posDef_finSucc_olsBetaOrZero_of_gapEnvelope_bounds_of_robustFeasibleHCMomentConditions
    [IsProbabilityMeasure μ]
    {k q : Type*} [Fintype k] [Fintype q] [DecidableEq k] [DecidableEq q]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    {Clin Cbeta : ℝ}
    (β : k → ℝ) (R : Matrix k q ℝ)
    (hm : RobustFeasibleHCMomentConditions μ X e y β)
    (hΩ : (scoreCovMat μ X e).PosDef)
    (hRVR : (Rᵀ * heteroAsymCov μ X e * R).PosDef)
    (hLinBound : ∀ᶠ n in atTop,
      ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
        ‖regressionLinearizedScoreFinSucc μ X e n ω ωs‖ ≤ Clin)
    (hBetaBound : ∀ᶠ n in atTop,
      ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
        ‖regressionBootstrapBetaStatisticFinSucc X y n ω ωs‖ ≤ Cbeta)
    (hGapTail : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          ((ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
              Measure (Fin (n + 1) → Fin (n + 1)))).real
            {ωs |
              δ ≤ regressionBootstrapBetaLinearizedGapEnvelopeFinSucc
                μ X e β n ω ωs})
        atTop (fun _ => 0)) :
    TendstoInBootstrapDistributionIndexed μ
      (fun n _ =>
        (ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))))
      (fun n ω ωs =>
        ((regressionBootstrapThetaStatisticFinSucc R X y n ω ωs :
          EuclideanSpace ℝ q) : q → ℝ))
      (multivariateGaussian (0 : EuclideanSpace ℝ q)
        (Rᵀ * heteroAsymCov μ X e * R))
      (fun z : EuclideanSpace ℝ q => (z : q → ℝ)) :=
  chapter10_indexed_bootstrap_regression_theta_gaussian_distribution_posDef_finSucc_olsBetaOrZero_of_gapEnvelope_bounds
    (μ := μ) (X := X) (e := e) (y := y) β R hm.model
    hm.toScoreCLTConditions hΩ hRVR hLinBound hBetaBound hGapTail

private theorem
    regressionBootstrapLinearRestrictionStatisticFinSucc_distribution_of_theta
    {k : Type*} [Fintype k] [DecidableEq k]
    {X : ℕ → Ω → (k → ℝ)} {y : ℕ → Ω → ℝ}
    (R : Matrix Unit k ℝ)
    {Pstar : ∀ n, Ω → Measure (Fin (n + 1) → Fin (n + 1))}
    {ν : Measure (EuclideanSpace ℝ Unit)}
    (hθ :
      TendstoInBootstrapDistributionIndexed μ Pstar
        (fun n ω ωs =>
          ((regressionBootstrapThetaStatisticFinSucc Rᵀ X y n ω ωs :
            EuclideanSpace ℝ Unit) : Unit → ℝ))
        ν (fun z : EuclideanSpace ℝ Unit => (z : Unit → ℝ))) :
    TendstoInBootstrapDistributionIndexed μ Pstar
      (fun n ω ωs (_ : Unit) =>
        regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs)
      ν (fun z : EuclideanSpace ℝ Unit => (z : Unit → ℝ)) := by
  refine hθ.congr ?_ ?_
  · intro n ω ωs
    funext u
    cases u
    exact (regressionBootstrapLinearRestrictionStatisticFinSucc_eq_theta_apply
      R X y n ω ωs).symm
  intro z
  rfl

set_option linter.style.longLine false in
/-- Hansen Definition 10.2 CDF face of the scalar one-row ordinary-bootstrap
OLS restriction transfer from the explicit finite OLS-linearization gap
envelope. -/
theorem
    chapter10_indexed_bootstrap_regression_linearRestriction_gaussian_distribution_finSucc_olsBetaOrZero_of_gapEnvelope_tight
    [IsProbabilityMeasure μ]
    {k : Type*} [Fintype k] [DecidableEq k]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    (β : k → ℝ) (R : Matrix Unit k ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (h : ScoreCLTConditions μ X e)
    (hΩ : (scoreCovMat μ X e).PosDef)
    (hTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set (EuclideanSpace ℝ k), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω =>
            ((ProbabilityTheory.uniformOn
              (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                Measure (Fin (n + 1) → Fin (n + 1)))).real
              {ωs | regressionLinearizedScoreFinSucc μ X e n ω ωs ∉ K})
          atTop (fun _ => 0) ∧
        TendstoInMeasure μ
          (fun n ω =>
            ((ProbabilityTheory.uniformOn
              (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                Measure (Fin (n + 1) → Fin (n + 1)))).real
              {ωs | regressionBootstrapBetaStatisticFinSucc X y n ω ωs ∉ K})
          atTop (fun _ => 0))
    (hGapTail : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          ((ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
              Measure (Fin (n + 1) → Fin (n + 1)))).real
            {ωs |
              δ ≤ regressionBootstrapBetaLinearizedGapEnvelopeFinSucc
                μ X e β n ω ωs})
        atTop (fun _ => 0))
    (hfrontier : ∀ x : Unit → ℝ,
      ContinuousAt
          (fun y =>
            vectorCDF
              (multivariateGaussian (0 : EuclideanSpace ℝ Unit)
                (R * heteroAsymCov μ X e * Rᵀ))
              (fun z : EuclideanSpace ℝ Unit => (z : Unit → ℝ)) y) x →
        ((multivariateGaussian (0 : EuclideanSpace ℝ Unit)
            (R * heteroAsymCov μ X e * Rᵀ)).map
            (fun z : EuclideanSpace ℝ Unit => (z : Unit → ℝ)))
          (frontier {z : Unit → ℝ | coordinateLE z x}) = 0) :
    TendstoInBootstrapDistributionIndexed μ
      (fun n _ =>
        (ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))))
      (fun n ω ωs (_ : Unit) =>
        regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs)
      (multivariateGaussian (0 : EuclideanSpace ℝ Unit)
        (R * heteroAsymCov μ X e * Rᵀ))
      (fun z : EuclideanSpace ℝ Unit => (z : Unit → ℝ)) := by
  have hθ :
      TendstoInBootstrapDistributionIndexed μ
        (fun n _ =>
          (ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
              Measure (Fin (n + 1) → Fin (n + 1))))
        (fun n ω ωs =>
          ((regressionBootstrapThetaStatisticFinSucc Rᵀ X y n ω ωs :
            EuclideanSpace ℝ Unit) : Unit → ℝ))
        (multivariateGaussian (0 : EuclideanSpace ℝ Unit)
          ((Rᵀ)ᵀ * heteroAsymCov μ X e * Rᵀ))
        (fun z : EuclideanSpace ℝ Unit => (z : Unit → ℝ)) :=
    chapter10_indexed_bootstrap_regression_theta_gaussian_distribution_finSucc_olsBetaOrZero_of_gapEnvelope_tight
      (μ := μ) (X := X) (e := e) (y := y)
      β Rᵀ hmodel h hΩ hTail hGapTail
      (by simpa [Matrix.transpose_transpose] using hfrontier)
  have hscalar :=
    regressionBootstrapLinearRestrictionStatisticFinSucc_distribution_of_theta
      (μ := μ) (X := X) (y := y) R hθ
  simpa [Matrix.transpose_transpose] using hscalar

set_option linter.style.longLine false in
/-- Positive-definite Hansen Definition 10.2 CDF face of the scalar one-row
ordinary-bootstrap OLS gap-envelope transfer. -/
theorem
    chapter10_indexed_bootstrap_regression_linearRestriction_gaussian_distribution_posDef_finSucc_olsBetaOrZero_of_gapEnvelope_tight
    [IsProbabilityMeasure μ]
    {k : Type*} [Fintype k] [DecidableEq k]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    (β : k → ℝ) (R : Matrix Unit k ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (h : ScoreCLTConditions μ X e)
    (hΩ : (scoreCovMat μ X e).PosDef)
    (hRVR : (R * heteroAsymCov μ X e * Rᵀ).PosDef)
    (hTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set (EuclideanSpace ℝ k), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω =>
            ((ProbabilityTheory.uniformOn
              (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                Measure (Fin (n + 1) → Fin (n + 1)))).real
              {ωs | regressionLinearizedScoreFinSucc μ X e n ω ωs ∉ K})
          atTop (fun _ => 0) ∧
        TendstoInMeasure μ
          (fun n ω =>
            ((ProbabilityTheory.uniformOn
              (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                Measure (Fin (n + 1) → Fin (n + 1)))).real
              {ωs | regressionBootstrapBetaStatisticFinSucc X y n ω ωs ∉ K})
          atTop (fun _ => 0))
    (hGapTail : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          ((ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
              Measure (Fin (n + 1) → Fin (n + 1)))).real
            {ωs |
              δ ≤ regressionBootstrapBetaLinearizedGapEnvelopeFinSucc
                μ X e β n ω ωs})
        atTop (fun _ => 0)) :
    TendstoInBootstrapDistributionIndexed μ
      (fun n _ =>
        (ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))))
      (fun n ω ωs (_ : Unit) =>
        regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs)
      (multivariateGaussian (0 : EuclideanSpace ℝ Unit)
        (R * heteroAsymCov μ X e * Rᵀ))
      (fun z : EuclideanSpace ℝ Unit => (z : Unit → ℝ)) :=
  chapter10_indexed_bootstrap_regression_linearRestriction_gaussian_distribution_finSucc_olsBetaOrZero_of_gapEnvelope_tight
    (μ := μ) (X := X) (e := e) (y := y)
    β R hmodel h hΩ hTail hGapTail
    (fun x _hx => multivariateGaussian_coordinateLE_frontier_null_of_posDef hRVR x)

set_option linter.style.longLine false in
/-- Robust-feasible HC Hansen Definition 10.2 CDF face of the scalar one-row
ordinary-bootstrap OLS gap-envelope transfer. -/
theorem
    chapter10_indexed_bootstrap_regression_linearRestriction_gaussian_distribution_finSucc_olsBetaOrZero_of_gapEnvelope_tight_of_robustFeasibleHCMomentConditions
    [IsProbabilityMeasure μ]
    {k : Type*} [Fintype k] [DecidableEq k]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    (β : k → ℝ) (R : Matrix Unit k ℝ)
    (hm : RobustFeasibleHCMomentConditions μ X e y β)
    (hΩ : (scoreCovMat μ X e).PosDef)
    (hTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set (EuclideanSpace ℝ k), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω =>
            ((ProbabilityTheory.uniformOn
              (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                Measure (Fin (n + 1) → Fin (n + 1)))).real
              {ωs | regressionLinearizedScoreFinSucc μ X e n ω ωs ∉ K})
          atTop (fun _ => 0) ∧
        TendstoInMeasure μ
          (fun n ω =>
            ((ProbabilityTheory.uniformOn
              (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                Measure (Fin (n + 1) → Fin (n + 1)))).real
              {ωs | regressionBootstrapBetaStatisticFinSucc X y n ω ωs ∉ K})
          atTop (fun _ => 0))
    (hGapTail : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          ((ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
              Measure (Fin (n + 1) → Fin (n + 1)))).real
            {ωs |
              δ ≤ regressionBootstrapBetaLinearizedGapEnvelopeFinSucc
                μ X e β n ω ωs})
        atTop (fun _ => 0))
    (hfrontier : ∀ x : Unit → ℝ,
      ContinuousAt
          (fun y =>
            vectorCDF
              (multivariateGaussian (0 : EuclideanSpace ℝ Unit)
                (R * heteroAsymCov μ X e * Rᵀ))
              (fun z : EuclideanSpace ℝ Unit => (z : Unit → ℝ)) y) x →
        ((multivariateGaussian (0 : EuclideanSpace ℝ Unit)
            (R * heteroAsymCov μ X e * Rᵀ)).map
            (fun z : EuclideanSpace ℝ Unit => (z : Unit → ℝ)))
          (frontier {z : Unit → ℝ | coordinateLE z x}) = 0) :
    TendstoInBootstrapDistributionIndexed μ
      (fun n _ =>
        (ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))))
      (fun n ω ωs (_ : Unit) =>
        regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs)
      (multivariateGaussian (0 : EuclideanSpace ℝ Unit)
        (R * heteroAsymCov μ X e * Rᵀ))
      (fun z : EuclideanSpace ℝ Unit => (z : Unit → ℝ)) :=
  chapter10_indexed_bootstrap_regression_linearRestriction_gaussian_distribution_finSucc_olsBetaOrZero_of_gapEnvelope_tight
    (μ := μ) (X := X) (e := e) (y := y)
    β R hm.model hm.toScoreCLTConditions hΩ hTail hGapTail hfrontier

set_option linter.style.longLine false in
/-- Positive-definite robust-feasible HC Hansen Definition 10.2 CDF face of
the scalar one-row ordinary-bootstrap OLS gap-envelope transfer. -/
theorem
    chapter10_indexed_bootstrap_regression_linearRestriction_gaussian_distribution_posDef_finSucc_olsBetaOrZero_of_gapEnvelope_tight_of_robustFeasibleHCMomentConditions
    [IsProbabilityMeasure μ]
    {k : Type*} [Fintype k] [DecidableEq k]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    (β : k → ℝ) (R : Matrix Unit k ℝ)
    (hm : RobustFeasibleHCMomentConditions μ X e y β)
    (hΩ : (scoreCovMat μ X e).PosDef)
    (hRVR : (R * heteroAsymCov μ X e * Rᵀ).PosDef)
    (hTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set (EuclideanSpace ℝ k), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω =>
            ((ProbabilityTheory.uniformOn
              (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                Measure (Fin (n + 1) → Fin (n + 1)))).real
              {ωs | regressionLinearizedScoreFinSucc μ X e n ω ωs ∉ K})
          atTop (fun _ => 0) ∧
        TendstoInMeasure μ
          (fun n ω =>
            ((ProbabilityTheory.uniformOn
              (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                Measure (Fin (n + 1) → Fin (n + 1)))).real
              {ωs | regressionBootstrapBetaStatisticFinSucc X y n ω ωs ∉ K})
          atTop (fun _ => 0))
    (hGapTail : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          ((ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
              Measure (Fin (n + 1) → Fin (n + 1)))).real
            {ωs |
              δ ≤ regressionBootstrapBetaLinearizedGapEnvelopeFinSucc
                μ X e β n ω ωs})
        atTop (fun _ => 0)) :
    TendstoInBootstrapDistributionIndexed μ
      (fun n _ =>
        (ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))))
      (fun n ω ωs (_ : Unit) =>
        regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs)
      (multivariateGaussian (0 : EuclideanSpace ℝ Unit)
        (R * heteroAsymCov μ X e * Rᵀ))
      (fun z : EuclideanSpace ℝ Unit => (z : Unit → ℝ)) :=
  chapter10_indexed_bootstrap_regression_linearRestriction_gaussian_distribution_posDef_finSucc_olsBetaOrZero_of_gapEnvelope_tight
    (μ := μ) (X := X) (e := e) (y := y)
    β R hm.model hm.toScoreCLTConditions hΩ hRVR hTail hGapTail

set_option linter.style.longLine false in
/-- Hansen Definition 10.2 CDF face of the bounded scalar one-row
ordinary-bootstrap OLS gap-envelope transfer. -/
theorem
    chapter10_indexed_bootstrap_regression_linearRestriction_gaussian_distribution_finSucc_olsBetaOrZero_of_gapEnvelope_bounds
    [IsProbabilityMeasure μ]
    {k : Type*} [Fintype k] [DecidableEq k]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    {Clin Cbeta : ℝ}
    (β : k → ℝ) (R : Matrix Unit k ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (h : ScoreCLTConditions μ X e)
    (hΩ : (scoreCovMat μ X e).PosDef)
    (hLinBound : ∀ᶠ n in atTop,
      ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
        ‖regressionLinearizedScoreFinSucc μ X e n ω ωs‖ ≤ Clin)
    (hBetaBound : ∀ᶠ n in atTop,
      ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
        ‖regressionBootstrapBetaStatisticFinSucc X y n ω ωs‖ ≤ Cbeta)
    (hGapTail : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          ((ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
              Measure (Fin (n + 1) → Fin (n + 1)))).real
            {ωs |
              δ ≤ regressionBootstrapBetaLinearizedGapEnvelopeFinSucc
                μ X e β n ω ωs})
        atTop (fun _ => 0))
    (hfrontier : ∀ x : Unit → ℝ,
      ContinuousAt
          (fun y =>
            vectorCDF
              (multivariateGaussian (0 : EuclideanSpace ℝ Unit)
                (R * heteroAsymCov μ X e * Rᵀ))
              (fun z : EuclideanSpace ℝ Unit => (z : Unit → ℝ)) y) x →
        ((multivariateGaussian (0 : EuclideanSpace ℝ Unit)
            (R * heteroAsymCov μ X e * Rᵀ)).map
            (fun z : EuclideanSpace ℝ Unit => (z : Unit → ℝ)))
          (frontier {z : Unit → ℝ | coordinateLE z x}) = 0) :
    TendstoInBootstrapDistributionIndexed μ
      (fun n _ =>
        (ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))))
      (fun n ω ωs (_ : Unit) =>
        regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs)
      (multivariateGaussian (0 : EuclideanSpace ℝ Unit)
        (R * heteroAsymCov μ X e * Rᵀ))
      (fun z : EuclideanSpace ℝ Unit => (z : Unit → ℝ)) := by
  have hθ :
      TendstoInBootstrapDistributionIndexed μ
        (fun n _ =>
          (ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
              Measure (Fin (n + 1) → Fin (n + 1))))
        (fun n ω ωs =>
          ((regressionBootstrapThetaStatisticFinSucc Rᵀ X y n ω ωs :
            EuclideanSpace ℝ Unit) : Unit → ℝ))
        (multivariateGaussian (0 : EuclideanSpace ℝ Unit)
          ((Rᵀ)ᵀ * heteroAsymCov μ X e * Rᵀ))
        (fun z : EuclideanSpace ℝ Unit => (z : Unit → ℝ)) :=
    chapter10_indexed_bootstrap_regression_theta_gaussian_distribution_finSucc_olsBetaOrZero_of_gapEnvelope_bounds
      (μ := μ) (X := X) (e := e) (y := y)
      β Rᵀ hmodel h hΩ hLinBound hBetaBound hGapTail
      (by simpa [Matrix.transpose_transpose] using hfrontier)
  have hscalar :=
    regressionBootstrapLinearRestrictionStatisticFinSucc_distribution_of_theta
      (μ := μ) (X := X) (y := y) R hθ
  simpa [Matrix.transpose_transpose] using hscalar

set_option linter.style.longLine false in
/-- Positive-definite Hansen Definition 10.2 CDF face of the bounded scalar
one-row ordinary-bootstrap OLS gap-envelope transfer. -/
theorem
    chapter10_indexed_bootstrap_regression_linearRestriction_gaussian_distribution_posDef_finSucc_olsBetaOrZero_of_gapEnvelope_bounds
    [IsProbabilityMeasure μ]
    {k : Type*} [Fintype k] [DecidableEq k]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    {Clin Cbeta : ℝ}
    (β : k → ℝ) (R : Matrix Unit k ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (h : ScoreCLTConditions μ X e)
    (hΩ : (scoreCovMat μ X e).PosDef)
    (hRVR : (R * heteroAsymCov μ X e * Rᵀ).PosDef)
    (hLinBound : ∀ᶠ n in atTop,
      ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
        ‖regressionLinearizedScoreFinSucc μ X e n ω ωs‖ ≤ Clin)
    (hBetaBound : ∀ᶠ n in atTop,
      ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
        ‖regressionBootstrapBetaStatisticFinSucc X y n ω ωs‖ ≤ Cbeta)
    (hGapTail : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          ((ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
              Measure (Fin (n + 1) → Fin (n + 1)))).real
            {ωs |
              δ ≤ regressionBootstrapBetaLinearizedGapEnvelopeFinSucc
                μ X e β n ω ωs})
        atTop (fun _ => 0)) :
    TendstoInBootstrapDistributionIndexed μ
      (fun n _ =>
        (ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))))
      (fun n ω ωs (_ : Unit) =>
        regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs)
      (multivariateGaussian (0 : EuclideanSpace ℝ Unit)
        (R * heteroAsymCov μ X e * Rᵀ))
      (fun z : EuclideanSpace ℝ Unit => (z : Unit → ℝ)) :=
  chapter10_indexed_bootstrap_regression_linearRestriction_gaussian_distribution_finSucc_olsBetaOrZero_of_gapEnvelope_bounds
    (μ := μ) (X := X) (e := e) (y := y)
    β R hmodel h hΩ hLinBound hBetaBound hGapTail
    (fun x _hx => multivariateGaussian_coordinateLE_frontier_null_of_posDef hRVR x)

set_option linter.style.longLine false in
/-- Robust-feasible HC Hansen Definition 10.2 CDF face of the bounded scalar
one-row ordinary-bootstrap OLS gap-envelope transfer. -/
theorem
    chapter10_indexed_bootstrap_regression_linearRestriction_gaussian_distribution_finSucc_olsBetaOrZero_of_gapEnvelope_bounds_of_robustFeasibleHCMomentConditions
    [IsProbabilityMeasure μ]
    {k : Type*} [Fintype k] [DecidableEq k]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    {Clin Cbeta : ℝ}
    (β : k → ℝ) (R : Matrix Unit k ℝ)
    (hm : RobustFeasibleHCMomentConditions μ X e y β)
    (hΩ : (scoreCovMat μ X e).PosDef)
    (hLinBound : ∀ᶠ n in atTop,
      ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
        ‖regressionLinearizedScoreFinSucc μ X e n ω ωs‖ ≤ Clin)
    (hBetaBound : ∀ᶠ n in atTop,
      ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
        ‖regressionBootstrapBetaStatisticFinSucc X y n ω ωs‖ ≤ Cbeta)
    (hGapTail : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          ((ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
              Measure (Fin (n + 1) → Fin (n + 1)))).real
            {ωs |
              δ ≤ regressionBootstrapBetaLinearizedGapEnvelopeFinSucc
                μ X e β n ω ωs})
        atTop (fun _ => 0))
    (hfrontier : ∀ x : Unit → ℝ,
      ContinuousAt
          (fun y =>
            vectorCDF
              (multivariateGaussian (0 : EuclideanSpace ℝ Unit)
                (R * heteroAsymCov μ X e * Rᵀ))
              (fun z : EuclideanSpace ℝ Unit => (z : Unit → ℝ)) y) x →
        ((multivariateGaussian (0 : EuclideanSpace ℝ Unit)
            (R * heteroAsymCov μ X e * Rᵀ)).map
            (fun z : EuclideanSpace ℝ Unit => (z : Unit → ℝ)))
          (frontier {z : Unit → ℝ | coordinateLE z x}) = 0) :
    TendstoInBootstrapDistributionIndexed μ
      (fun n _ =>
        (ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))))
      (fun n ω ωs (_ : Unit) =>
        regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs)
      (multivariateGaussian (0 : EuclideanSpace ℝ Unit)
        (R * heteroAsymCov μ X e * Rᵀ))
      (fun z : EuclideanSpace ℝ Unit => (z : Unit → ℝ)) :=
  chapter10_indexed_bootstrap_regression_linearRestriction_gaussian_distribution_finSucc_olsBetaOrZero_of_gapEnvelope_bounds
    (μ := μ) (X := X) (e := e) (y := y)
    β R hm.model hm.toScoreCLTConditions hΩ hLinBound hBetaBound hGapTail
    hfrontier

set_option linter.style.longLine false in
/-- Positive-definite robust-feasible HC Hansen Definition 10.2 CDF face of
the bounded scalar one-row ordinary-bootstrap OLS gap-envelope transfer. -/
theorem
    chapter10_indexed_bootstrap_regression_linearRestriction_gaussian_distribution_posDef_finSucc_olsBetaOrZero_of_gapEnvelope_bounds_of_robustFeasibleHCMomentConditions
    [IsProbabilityMeasure μ]
    {k : Type*} [Fintype k] [DecidableEq k]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    {Clin Cbeta : ℝ}
    (β : k → ℝ) (R : Matrix Unit k ℝ)
    (hm : RobustFeasibleHCMomentConditions μ X e y β)
    (hΩ : (scoreCovMat μ X e).PosDef)
    (hRVR : (R * heteroAsymCov μ X e * Rᵀ).PosDef)
    (hLinBound : ∀ᶠ n in atTop,
      ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
        ‖regressionLinearizedScoreFinSucc μ X e n ω ωs‖ ≤ Clin)
    (hBetaBound : ∀ᶠ n in atTop,
      ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
        ‖regressionBootstrapBetaStatisticFinSucc X y n ω ωs‖ ≤ Cbeta)
    (hGapTail : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          ((ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
              Measure (Fin (n + 1) → Fin (n + 1)))).real
            {ωs |
              δ ≤ regressionBootstrapBetaLinearizedGapEnvelopeFinSucc
                μ X e β n ω ωs})
        atTop (fun _ => 0)) :
    TendstoInBootstrapDistributionIndexed μ
      (fun n _ =>
        (ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))))
      (fun n ω ωs (_ : Unit) =>
        regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs)
      (multivariateGaussian (0 : EuclideanSpace ℝ Unit)
        (R * heteroAsymCov μ X e * Rᵀ))
      (fun z : EuclideanSpace ℝ Unit => (z : Unit → ℝ)) :=
  chapter10_indexed_bootstrap_regression_linearRestriction_gaussian_distribution_posDef_finSucc_olsBetaOrZero_of_gapEnvelope_bounds
    (μ := μ) (X := X) (e := e) (y := y)
    β R hm.model hm.toScoreCLTConditions hΩ hRVR hLinBound hBetaBound hGapTail

set_option linter.style.longLine false in
/-- Robust-feasible HC Hansen Definition 10.2 face of the concrete
ordinary-bootstrap OLS coefficient-transfer route. -/
theorem
    chapter10_indexed_bootstrap_regression_theta_gaussian_distribution_finSucc_olsBetaOrZero_of_linearizedScore_tight_of_robustFeasibleHCMomentConditions
    [IsProbabilityMeasure μ]
    {k q : Type*} [Fintype k] [Fintype q] [DecidableEq k] [DecidableEq q]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    (β : k → ℝ) (R : Matrix k q ℝ)
    (hm : RobustFeasibleHCMomentConditions μ X e y β)
    (hΩ : (scoreCovMat μ X e).PosDef)
    (hTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set (EuclideanSpace ℝ k), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω =>
            ((ProbabilityTheory.uniformOn
              (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                Measure (Fin (n + 1) → Fin (n + 1)))).real
              {ωs | regressionLinearizedScoreFinSucc μ X e n ω ωs ∉ K})
          atTop (fun _ => 0) ∧
        TendstoInMeasure μ
          (fun n ω =>
            ((ProbabilityTheory.uniformOn
              (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                Measure (Fin (n + 1) → Fin (n + 1)))).real
              {ωs | regressionBootstrapBetaStatisticFinSucc X y n ω ωs ∉ K})
          atTop (fun _ => 0))
    (hclose : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          ((ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
              Measure (Fin (n + 1) → Fin (n + 1)))).real
            {ωs |
              δ ≤ dist (regressionBootstrapBetaStatisticFinSucc X y n ω ωs)
                (regressionLinearizedScoreFinSucc μ X e n ω ωs)})
        atTop (fun _ => 0))
    (hfrontier : ∀ x : q → ℝ,
      ContinuousAt
          (fun y =>
            vectorCDF
              (multivariateGaussian (0 : EuclideanSpace ℝ q)
                (Rᵀ * heteroAsymCov μ X e * R))
              (fun z : EuclideanSpace ℝ q => (z : q → ℝ)) y) x →
        ((multivariateGaussian (0 : EuclideanSpace ℝ q)
            (Rᵀ * heteroAsymCov μ X e * R)).map
            (fun z : EuclideanSpace ℝ q => (z : q → ℝ)))
          (frontier {z : q → ℝ | coordinateLE z x}) = 0) :
    TendstoInBootstrapDistributionIndexed μ
      (fun n _ =>
        (ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))))
      (fun n ω ωs =>
        ((regressionBootstrapThetaStatisticFinSucc R X y n ω ωs :
          EuclideanSpace ℝ q) : q → ℝ))
      (multivariateGaussian (0 : EuclideanSpace ℝ q)
        (Rᵀ * heteroAsymCov μ X e * R))
      (fun z : EuclideanSpace ℝ q => (z : q → ℝ)) :=
  chapter10_indexed_bootstrap_regression_theta_gaussian_distribution_finSucc_olsBetaOrZero_of_linearizedScore_tight
    (μ := μ) (X := X) (e := e) (y := y)
    R hm.toScoreCLTConditions hΩ hTail hclose hfrontier

set_option linter.style.longLine false in
/-- Positive-definite transformed-covariance robust-feasible HC CDF face of
the concrete ordinary-bootstrap OLS coefficient-transfer route. -/
theorem
    chapter10_indexed_bootstrap_regression_theta_gaussian_distribution_posDef_finSucc_olsBetaOrZero_of_linearizedScore_tight_of_robustFeasibleHCMomentConditions
    [IsProbabilityMeasure μ]
    {k q : Type*} [Fintype k] [Fintype q] [DecidableEq k] [DecidableEq q]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    (β : k → ℝ) (R : Matrix k q ℝ)
    (hm : RobustFeasibleHCMomentConditions μ X e y β)
    (hΩ : (scoreCovMat μ X e).PosDef)
    (hRVR : (Rᵀ * heteroAsymCov μ X e * R).PosDef)
    (hTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set (EuclideanSpace ℝ k), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω =>
            ((ProbabilityTheory.uniformOn
              (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                Measure (Fin (n + 1) → Fin (n + 1)))).real
              {ωs | regressionLinearizedScoreFinSucc μ X e n ω ωs ∉ K})
          atTop (fun _ => 0) ∧
        TendstoInMeasure μ
          (fun n ω =>
            ((ProbabilityTheory.uniformOn
              (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                Measure (Fin (n + 1) → Fin (n + 1)))).real
              {ωs | regressionBootstrapBetaStatisticFinSucc X y n ω ωs ∉ K})
          atTop (fun _ => 0))
    (hclose : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          ((ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
              Measure (Fin (n + 1) → Fin (n + 1)))).real
            {ωs |
              δ ≤ dist (regressionBootstrapBetaStatisticFinSucc X y n ω ωs)
                (regressionLinearizedScoreFinSucc μ X e n ω ωs)})
        atTop (fun _ => 0)) :
    TendstoInBootstrapDistributionIndexed μ
      (fun n _ =>
        (ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))))
      (fun n ω ωs =>
        ((regressionBootstrapThetaStatisticFinSucc R X y n ω ωs :
          EuclideanSpace ℝ q) : q → ℝ))
      (multivariateGaussian (0 : EuclideanSpace ℝ q)
        (Rᵀ * heteroAsymCov μ X e * R))
      (fun z : EuclideanSpace ℝ q => (z : q → ℝ)) :=
  chapter10_indexed_bootstrap_regression_theta_gaussian_distribution_posDef_finSucc_olsBetaOrZero_of_linearizedScore_tight
    (μ := μ) (X := X) (e := e) (y := y) R hm.toScoreCLTConditions
    hΩ hRVR hTail hclose

/-- Robust-feasible HC face of the finite ordinary-bootstrap linearized score
route.

The Chapter 7 robust-feasible condition package supplies the score CLT
conditions; positive definiteness of the score covariance remains explicit. -/
theorem
    chapter10_indexed_bootstrap_regression_theta_gaussian_finSucc_linearizedScore_of_robustFeasibleHCMomentConditions
    [IsProbabilityMeasure μ]
    {k q : Type*} [Fintype k] [Fintype q] [DecidableEq k] [DecidableEq q]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    (β : k → ℝ) (R : Matrix k q ℝ)
    (hm : RobustFeasibleHCMomentConditions μ X e y β)
    (hΩ : (scoreCovMat μ X e).PosDef) :
    TendstoInBootstrapWeakDistributionIndexed μ
      (fun n _ =>
        (ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))))
      (fun n ω ωs =>
        matrixContinuousLinearMap Rᵀ
          (regressionLinearizedScoreFinSucc μ X e n ω ωs))
      (multivariateGaussian (0 : EuclideanSpace ℝ q)
        (Rᵀ * heteroAsymCov μ X e * R))
      (fun z : EuclideanSpace ℝ q => z) :=
  chapter10_indexed_bootstrap_regression_theta_gaussian_finSucc_linearizedScore
    (μ := μ) R hm.toScoreCLTConditions hΩ

/-- Hansen Definition 10.2 robust-feasible HC face of the finite
ordinary-bootstrap linearized score route. -/
theorem
    chapter10_indexed_bootstrap_regression_theta_gaussian_distribution_finSucc_linearizedScore_of_robustFeasibleHCMomentConditions
    [IsProbabilityMeasure μ]
    {k q : Type*} [Fintype k] [Fintype q] [DecidableEq k] [DecidableEq q]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    (β : k → ℝ) (R : Matrix k q ℝ)
    (hm : RobustFeasibleHCMomentConditions μ X e y β)
    (hΩ : (scoreCovMat μ X e).PosDef)
    (hfrontier : ∀ x : q → ℝ,
      ContinuousAt
          (fun y =>
            vectorCDF
              (multivariateGaussian (0 : EuclideanSpace ℝ q)
                (Rᵀ * heteroAsymCov μ X e * R))
              (fun z : EuclideanSpace ℝ q => (z : q → ℝ)) y) x →
        ((multivariateGaussian (0 : EuclideanSpace ℝ q)
            (Rᵀ * heteroAsymCov μ X e * R)).map
            (fun z : EuclideanSpace ℝ q => (z : q → ℝ)))
          (frontier {z : q → ℝ | coordinateLE z x}) = 0) :
    TendstoInBootstrapDistributionIndexed μ
      (fun n _ =>
        (ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))))
      (fun n ω ωs =>
        ((matrixContinuousLinearMap Rᵀ
          (regressionLinearizedScoreFinSucc μ X e n ω ωs) :
            EuclideanSpace ℝ q) : q → ℝ))
      (multivariateGaussian (0 : EuclideanSpace ℝ q)
        (Rᵀ * heteroAsymCov μ X e * R))
      (fun z : EuclideanSpace ℝ q => (z : q → ℝ)) :=
  chapter10_indexed_bootstrap_regression_theta_gaussian_distribution_finSucc_linearizedScore
    (μ := μ) R hm.toScoreCLTConditions hΩ hfrontier

/-- Positive-definite transformed-covariance robust-feasible HC CDF face of
the finite ordinary-bootstrap linearized score route. -/
theorem
    chapter10_indexed_bootstrap_regression_theta_gaussian_distribution_posDef_finSucc_linearizedScore_of_robustFeasibleHCMomentConditions
    [IsProbabilityMeasure μ]
    {k q : Type*} [Fintype k] [Fintype q] [DecidableEq k] [DecidableEq q]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    (β : k → ℝ) (R : Matrix k q ℝ)
    (hm : RobustFeasibleHCMomentConditions μ X e y β)
    (hΩ : (scoreCovMat μ X e).PosDef)
    (hRVR : (Rᵀ * heteroAsymCov μ X e * R).PosDef) :
    TendstoInBootstrapDistributionIndexed μ
      (fun n _ =>
        (ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))))
      (fun n ω ωs =>
        ((matrixContinuousLinearMap Rᵀ
          (regressionLinearizedScoreFinSucc μ X e n ω ωs) :
            EuclideanSpace ℝ q) : q → ℝ))
      (multivariateGaussian (0 : EuclideanSpace ℝ q)
        (Rᵀ * heteroAsymCov μ X e * R))
      (fun z : EuclideanSpace ℝ q => (z : q → ℝ)) :=
  chapter10_indexed_bootstrap_regression_theta_gaussian_distribution_posDef_finSucc_linearizedScore
    (μ := μ) R hm.toScoreCLTConditions hΩ hRVR

/-- Robust-feasible HC face of the finite ordinary-bootstrap nonlinear
coefficient-transfer route.

The robust-feasible condition package supplies the score CLT conditions; the
model-specific nonlinear OLS work remains the conditional closeness and
compact-tail premise for `TbetaStar`. -/
theorem
    chapter10_indexed_bootstrap_regression_beta_gaussian_finSucc_of_linearizedScore_tight_of_robustFeasibleHCMomentConditions
    [IsProbabilityMeasure μ]
    {k : Type*} [Fintype k] [DecidableEq k]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    {TbetaStar :
      ∀ n, Ω → (Fin (n + 1) → Fin (n + 1)) → EuclideanSpace ℝ k}
    (β : k → ℝ)
    (hm : RobustFeasibleHCMomentConditions μ X e y β)
    (hΩ : (scoreCovMat μ X e).PosDef)
    (hTbetaStar : ∀ n ω, Measurable (TbetaStar n ω))
    (hTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set (EuclideanSpace ℝ k), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω =>
            ((ProbabilityTheory.uniformOn
              (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                Measure (Fin (n + 1) → Fin (n + 1)))).real
              {ωs | regressionLinearizedScoreFinSucc μ X e n ω ωs ∉ K})
          atTop (fun _ => 0) ∧
        TendstoInMeasure μ
          (fun n ω =>
            ((ProbabilityTheory.uniformOn
              (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                Measure (Fin (n + 1) → Fin (n + 1)))).real
              {ωs | TbetaStar n ω ωs ∉ K})
          atTop (fun _ => 0))
    (hclose : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          ((ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
              Measure (Fin (n + 1) → Fin (n + 1)))).real
            {ωs |
              δ ≤ dist (TbetaStar n ω ωs)
                (regressionLinearizedScoreFinSucc μ X e n ω ωs)})
        atTop (fun _ => 0)) :
    TendstoInBootstrapWeakDistributionIndexed μ
      (fun n _ =>
        (ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))))
      TbetaStar
      (multivariateGaussian (0 : EuclideanSpace ℝ k) (heteroAsymCov μ X e))
      (fun z : EuclideanSpace ℝ k => z) :=
  chapter10_indexed_bootstrap_regression_beta_gaussian_finSucc_of_linearizedScore_tight
    (μ := μ) (X := X) (e := e) hm.toScoreCLTConditions hΩ
    hTbetaStar hTail hclose

/-- Robust-feasible HC face of the finite ordinary-bootstrap transformed
nonlinear coefficient-transfer route. -/
theorem
    chapter10_indexed_bootstrap_regression_theta_gaussian_finSucc_of_linearizedScore_tight_of_robustFeasibleHCMomentConditions
    [IsProbabilityMeasure μ]
    {k q : Type*} [Fintype k] [Fintype q] [DecidableEq k] [DecidableEq q]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    {TbetaStar :
      ∀ n, Ω → (Fin (n + 1) → Fin (n + 1)) → EuclideanSpace ℝ k}
    (β : k → ℝ) (R : Matrix k q ℝ)
    (hm : RobustFeasibleHCMomentConditions μ X e y β)
    (hΩ : (scoreCovMat μ X e).PosDef)
    (hTbetaStar : ∀ n ω, Measurable (TbetaStar n ω))
    (hTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set (EuclideanSpace ℝ k), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω =>
            ((ProbabilityTheory.uniformOn
              (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                Measure (Fin (n + 1) → Fin (n + 1)))).real
              {ωs | regressionLinearizedScoreFinSucc μ X e n ω ωs ∉ K})
          atTop (fun _ => 0) ∧
        TendstoInMeasure μ
          (fun n ω =>
            ((ProbabilityTheory.uniformOn
              (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                Measure (Fin (n + 1) → Fin (n + 1)))).real
              {ωs | TbetaStar n ω ωs ∉ K})
          atTop (fun _ => 0))
    (hclose : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          ((ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
              Measure (Fin (n + 1) → Fin (n + 1)))).real
            {ωs |
              δ ≤ dist (TbetaStar n ω ωs)
                (regressionLinearizedScoreFinSucc μ X e n ω ωs)})
        atTop (fun _ => 0)) :
    TendstoInBootstrapWeakDistributionIndexed μ
      (fun n _ =>
        (ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))))
      (fun n ω ωs => matrixContinuousLinearMap Rᵀ (TbetaStar n ω ωs))
      (multivariateGaussian (0 : EuclideanSpace ℝ q)
        (Rᵀ * heteroAsymCov μ X e * R))
      (fun z : EuclideanSpace ℝ q => z) :=
  chapter10_indexed_bootstrap_regression_theta_gaussian_finSucc_of_linearizedScore_tight
    (μ := μ) R hm.toScoreCLTConditions hΩ hTbetaStar hTail hclose

/-- Hansen Definition 10.2 robust-feasible HC face of the finite
ordinary-bootstrap nonlinear coefficient-transfer route. -/
theorem
    chapter10_indexed_bootstrap_regression_theta_gaussian_distribution_finSucc_of_linearizedScore_tight_of_robustFeasibleHCMomentConditions
    [IsProbabilityMeasure μ]
    {k q : Type*} [Fintype k] [Fintype q] [DecidableEq k] [DecidableEq q]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    {TbetaStar :
      ∀ n, Ω → (Fin (n + 1) → Fin (n + 1)) → EuclideanSpace ℝ k}
    (β : k → ℝ) (R : Matrix k q ℝ)
    (hm : RobustFeasibleHCMomentConditions μ X e y β)
    (hΩ : (scoreCovMat μ X e).PosDef)
    (hTbetaStar : ∀ n ω, Measurable (TbetaStar n ω))
    (hTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set (EuclideanSpace ℝ k), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω =>
            ((ProbabilityTheory.uniformOn
              (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                Measure (Fin (n + 1) → Fin (n + 1)))).real
              {ωs | regressionLinearizedScoreFinSucc μ X e n ω ωs ∉ K})
          atTop (fun _ => 0) ∧
        TendstoInMeasure μ
          (fun n ω =>
            ((ProbabilityTheory.uniformOn
              (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                Measure (Fin (n + 1) → Fin (n + 1)))).real
              {ωs | TbetaStar n ω ωs ∉ K})
          atTop (fun _ => 0))
    (hclose : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          ((ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
              Measure (Fin (n + 1) → Fin (n + 1)))).real
            {ωs |
              δ ≤ dist (TbetaStar n ω ωs)
                (regressionLinearizedScoreFinSucc μ X e n ω ωs)})
        atTop (fun _ => 0))
    (hfrontier : ∀ x : q → ℝ,
      ContinuousAt
          (fun y =>
            vectorCDF
              (multivariateGaussian (0 : EuclideanSpace ℝ q)
                (Rᵀ * heteroAsymCov μ X e * R))
              (fun z : EuclideanSpace ℝ q => (z : q → ℝ)) y) x →
        ((multivariateGaussian (0 : EuclideanSpace ℝ q)
            (Rᵀ * heteroAsymCov μ X e * R)).map
            (fun z : EuclideanSpace ℝ q => (z : q → ℝ)))
          (frontier {z : q → ℝ | coordinateLE z x}) = 0) :
    TendstoInBootstrapDistributionIndexed μ
      (fun n _ =>
        (ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))))
      (fun n ω ωs =>
        ((matrixContinuousLinearMap Rᵀ (TbetaStar n ω ωs) :
          EuclideanSpace ℝ q) : q → ℝ))
      (multivariateGaussian (0 : EuclideanSpace ℝ q)
        (Rᵀ * heteroAsymCov μ X e * R))
      (fun z : EuclideanSpace ℝ q => (z : q → ℝ)) :=
  chapter10_indexed_bootstrap_regression_theta_gaussian_distribution_finSucc_of_linearizedScore_tight
    (μ := μ) R hm.toScoreCLTConditions hΩ hTbetaStar hTail hclose hfrontier

/-- Positive-definite transformed-covariance robust-feasible HC CDF face of
the finite ordinary-bootstrap nonlinear coefficient-transfer route. -/
theorem
    chapter10_indexed_bootstrap_regression_theta_gaussian_distribution_posDef_finSucc_of_linearizedScore_tight_of_robustFeasibleHCMomentConditions
    [IsProbabilityMeasure μ]
    {k q : Type*} [Fintype k] [Fintype q] [DecidableEq k] [DecidableEq q]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    {TbetaStar :
      ∀ n, Ω → (Fin (n + 1) → Fin (n + 1)) → EuclideanSpace ℝ k}
    (β : k → ℝ) (R : Matrix k q ℝ)
    (hm : RobustFeasibleHCMomentConditions μ X e y β)
    (hΩ : (scoreCovMat μ X e).PosDef)
    (hRVR : (Rᵀ * heteroAsymCov μ X e * R).PosDef)
    (hTbetaStar : ∀ n ω, Measurable (TbetaStar n ω))
    (hTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set (EuclideanSpace ℝ k), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω =>
            ((ProbabilityTheory.uniformOn
              (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                Measure (Fin (n + 1) → Fin (n + 1)))).real
              {ωs | regressionLinearizedScoreFinSucc μ X e n ω ωs ∉ K})
          atTop (fun _ => 0) ∧
        TendstoInMeasure μ
          (fun n ω =>
            ((ProbabilityTheory.uniformOn
              (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                Measure (Fin (n + 1) → Fin (n + 1)))).real
              {ωs | TbetaStar n ω ωs ∉ K})
          atTop (fun _ => 0))
    (hclose : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          ((ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
              Measure (Fin (n + 1) → Fin (n + 1)))).real
            {ωs |
              δ ≤ dist (TbetaStar n ω ωs)
                (regressionLinearizedScoreFinSucc μ X e n ω ωs)})
        atTop (fun _ => 0)) :
    TendstoInBootstrapDistributionIndexed μ
      (fun n _ =>
        (ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))))
      (fun n ω ωs =>
        ((matrixContinuousLinearMap Rᵀ (TbetaStar n ω ωs) :
          EuclideanSpace ℝ q) : q → ℝ))
      (multivariateGaussian (0 : EuclideanSpace ℝ q)
        (Rᵀ * heteroAsymCov μ X e * R))
      (fun z : EuclideanSpace ℝ q => (z : q → ℝ)) :=
  chapter10_indexed_bootstrap_regression_theta_gaussian_distribution_posDef_finSucc_of_linearizedScore_tight
    (μ := μ) R hm.toScoreCLTConditions hΩ hRVR hTbetaStar hTail hclose

/-- Indexed Hansen Theorem 10.18, regression Gaussian CDF wrapper. -/
theorem chapter10_indexed_bootstrap_regression_theta_gaussian_distribution
    {k q : Type*} [Fintype k] [Fintype q] [DecidableEq k] [DecidableEq q]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {TbetaStar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ k}
    {Vβ : Matrix k k ℝ} (R : Matrix k q ℝ)
    (hVβ : Vβ.PosSemidef)
    (hβ :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar TbetaStar
        (multivariateGaussian (0 : EuclideanSpace ℝ k) Vβ)
        (fun z : EuclideanSpace ℝ k => z))
    (hPstar : ∀ n ω, IsFiniteMeasure (Pstar n ω))
    (hTbetaStar : ∀ n ω, Measurable (TbetaStar n ω))
    (hfrontier : ∀ x : q → ℝ,
      ContinuousAt
          (fun y =>
            vectorCDF
              (multivariateGaussian (0 : EuclideanSpace ℝ q) (Rᵀ * Vβ * R))
              (fun z : EuclideanSpace ℝ q => (z : q → ℝ)) y) x →
        ((multivariateGaussian (0 : EuclideanSpace ℝ q) (Rᵀ * Vβ * R)).map
            (fun z : EuclideanSpace ℝ q => (z : q → ℝ)))
          (frontier {z : q → ℝ | coordinateLE z x}) = 0) :
    TendstoInBootstrapDistributionIndexed μ Pstar
      (fun n ω ωs =>
        ((matrixContinuousLinearMap Rᵀ (TbetaStar n ω ωs) :
          EuclideanSpace ℝ q) : q → ℝ))
      (multivariateGaussian (0 : EuclideanSpace ℝ q) (Rᵀ * Vβ * R))
      (fun z : EuclideanSpace ℝ q => (z : q → ℝ)) := by
  simpa [Matrix.transpose_transpose] using
    chapter10_indexed_bootstrap_delta_method_gaussian_distribution
      (μ := μ) (Pstar := Pstar) (Tstar := TbetaStar) (V := Vβ)
      (G := Rᵀ) hVβ hβ hPstar hTbetaStar
      (by simpa [Matrix.transpose_transpose] using hfrontier)

/-- Indexed Hansen Theorem 10.18, regression Gaussian CDF wrapper with
positive definite transformed covariance. -/
theorem chapter10_indexed_bootstrap_regression_theta_gaussian_distribution_posDef
    {k q : Type*} [Fintype k] [Fintype q] [DecidableEq k] [DecidableEq q]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {TbetaStar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ k}
    {Vβ : Matrix k k ℝ} (R : Matrix k q ℝ)
    (hVβ : Vβ.PosSemidef)
    (hRVR : (Rᵀ * Vβ * R).PosDef)
    (hβ :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar TbetaStar
        (multivariateGaussian (0 : EuclideanSpace ℝ k) Vβ)
        (fun z : EuclideanSpace ℝ k => z))
    (hPstar : ∀ n ω, IsFiniteMeasure (Pstar n ω))
    (hTbetaStar : ∀ n ω, Measurable (TbetaStar n ω)) :
    TendstoInBootstrapDistributionIndexed μ Pstar
      (fun n ω ωs =>
        ((matrixContinuousLinearMap Rᵀ (TbetaStar n ω ωs) :
          EuclideanSpace ℝ q) : q → ℝ))
      (multivariateGaussian (0 : EuclideanSpace ℝ q) (Rᵀ * Vβ * R))
      (fun z : EuclideanSpace ℝ q => (z : q → ℝ)) :=
  chapter10_indexed_bootstrap_regression_theta_gaussian_distribution
    (μ := μ) (Pstar := Pstar) (TbetaStar := TbetaStar) (Vβ := Vβ)
    R hVβ hβ hPstar hTbetaStar
    (fun x _hx => multivariateGaussian_coordinateLE_frontier_null_of_posDef hRVR x)

/-- Indexed Hansen Theorem 10.18 regression Gaussian wrapper under the Chapter
7 robust feasible HC condition package.

This discharges positive semidefiniteness of `heteroAsymCov μ X e`; the
indexed coefficient-level bootstrap CLT remains explicit. -/
theorem
chapter10_indexed_bootstrap_regression_theta_gaussian_of_robustFeasibleHCMomentConditions
    [IsProbabilityMeasure μ]
    {k q : Type*} [Fintype k] [Fintype q] [DecidableEq k] [DecidableEq q]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {TbetaStar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ k}
    (β : k → ℝ) (R : Matrix k q ℝ)
    (hm : RobustFeasibleHCMomentConditions μ X e y β)
    (hβ :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar TbetaStar
        (multivariateGaussian (0 : EuclideanSpace ℝ k)
          (heteroAsymCov μ X e))
        (fun z : EuclideanSpace ℝ k => z)) :
    TendstoInBootstrapWeakDistributionIndexed μ Pstar
      (fun n ω ωs => matrixContinuousLinearMap Rᵀ (TbetaStar n ω ωs))
      (multivariateGaussian (0 : EuclideanSpace ℝ q)
        (Rᵀ * heteroAsymCov μ X e * R))
      (fun z : EuclideanSpace ℝ q => z) :=
  chapter10_indexed_bootstrap_regression_theta_gaussian
    (μ := μ) (Pstar := Pstar) (TbetaStar := TbetaStar)
    (Vβ := heteroAsymCov μ X e) R
    (heteroAsymCov_posSemidef_of_scoreCLTConditions
      (μ := μ) (X := X) (e := e) hm.toScoreCLTConditions)
    hβ

/-- Indexed Hansen Definition 10.2 face of
`chapter10_indexed_bootstrap_regression_theta_gaussian_of_robustFeasibleHCMomentConditions`. -/
theorem
chapter10_indexed_bootstrap_regression_theta_gaussian_distribution_of_robustFeasibleHCMomentConditions
    [IsProbabilityMeasure μ]
    {k q : Type*} [Fintype k] [Fintype q] [DecidableEq k] [DecidableEq q]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {TbetaStar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ k}
    (β : k → ℝ) (R : Matrix k q ℝ)
    (hm : RobustFeasibleHCMomentConditions μ X e y β)
    (hβ :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar TbetaStar
        (multivariateGaussian (0 : EuclideanSpace ℝ k)
          (heteroAsymCov μ X e))
        (fun z : EuclideanSpace ℝ k => z))
    (hPstar : ∀ n ω, IsFiniteMeasure (Pstar n ω))
    (hTbetaStar : ∀ n ω, Measurable (TbetaStar n ω))
    (hfrontier : ∀ x : q → ℝ,
      ContinuousAt
          (fun y =>
            vectorCDF
              (multivariateGaussian (0 : EuclideanSpace ℝ q)
                (Rᵀ * heteroAsymCov μ X e * R))
              (fun z : EuclideanSpace ℝ q => (z : q → ℝ)) y) x →
        ((multivariateGaussian (0 : EuclideanSpace ℝ q)
            (Rᵀ * heteroAsymCov μ X e * R)).map
            (fun z : EuclideanSpace ℝ q => (z : q → ℝ)))
          (frontier {z : q → ℝ | coordinateLE z x}) = 0) :
    TendstoInBootstrapDistributionIndexed μ Pstar
      (fun n ω ωs =>
        ((matrixContinuousLinearMap Rᵀ (TbetaStar n ω ωs) :
          EuclideanSpace ℝ q) : q → ℝ))
      (multivariateGaussian (0 : EuclideanSpace ℝ q)
        (Rᵀ * heteroAsymCov μ X e * R))
      (fun z : EuclideanSpace ℝ q => (z : q → ℝ)) :=
  chapter10_indexed_bootstrap_regression_theta_gaussian_distribution
    (μ := μ) (Pstar := Pstar) (TbetaStar := TbetaStar)
    (Vβ := heteroAsymCov μ X e) R
    (heteroAsymCov_posSemidef_of_scoreCLTConditions
      (μ := μ) (X := X) (e := e) hm.toScoreCLTConditions)
    hβ hPstar hTbetaStar hfrontier

/-- Positive-definite transformed-covariance version of
`chapter10_indexed_bootstrap_regression_theta_gaussian_distribution_of_robustFeasibleHCMomentConditions`. -/
theorem
chapter10_indexed_bootstrap_regression_theta_gaussian_distribution_posDef_of_robustFeasibleHCMomentConditions
    [IsProbabilityMeasure μ]
    {k q : Type*} [Fintype k] [Fintype q] [DecidableEq k] [DecidableEq q]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {TbetaStar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ k}
    (β : k → ℝ) (R : Matrix k q ℝ)
    (hm : RobustFeasibleHCMomentConditions μ X e y β)
    (hRVR : (Rᵀ * heteroAsymCov μ X e * R).PosDef)
    (hβ :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar TbetaStar
        (multivariateGaussian (0 : EuclideanSpace ℝ k)
          (heteroAsymCov μ X e))
        (fun z : EuclideanSpace ℝ k => z))
    (hPstar : ∀ n ω, IsFiniteMeasure (Pstar n ω))
    (hTbetaStar : ∀ n ω, Measurable (TbetaStar n ω)) :
    TendstoInBootstrapDistributionIndexed μ Pstar
      (fun n ω ωs =>
        ((matrixContinuousLinearMap Rᵀ (TbetaStar n ω ωs) :
          EuclideanSpace ℝ q) : q → ℝ))
      (multivariateGaussian (0 : EuclideanSpace ℝ q)
        (Rᵀ * heteroAsymCov μ X e * R))
      (fun z : EuclideanSpace ℝ q => (z : q → ℝ)) :=
  chapter10_indexed_bootstrap_regression_theta_gaussian_distribution_posDef
    (μ := μ) (Pstar := Pstar) (TbetaStar := TbetaStar)
    (Vβ := heteroAsymCov μ X e) R
    (heteroAsymCov_posSemidef_of_scoreCLTConditions
      (μ := μ) (X := X) (e := e) hm.toScoreCLTConditions)
    hRVR hβ hPstar hTbetaStar

set_option linter.style.longLine true

/-- Hansen Theorem 10.18, regression bootstrap t-statistic standard-normal
wrapper.

If the transformed regression numerator and feasible standard-error scale have
joint bootstrap weak limit `(s Z, s)` with `Z ~ N(0,1)`, and the scale itself
converges to the positive constant `s` in bootstrap probability, then the
studentized transformed statistic has standard-normal bootstrap weak limit.
Concrete regression applications supply the joint numerator/scale limit and
scale consistency from the model-specific covariance estimator. -/
theorem chapter10_bootstrap_regression_tstat_standardNormal
    {Pstar : ℕ → Ω → Measure Ωs}
    {TthetaStar seThetaStar : ℕ → Ω → Ωs → ℝ} {seθ : ℝ}
    (hseθ : 0 < seθ)
    (hjoint :
      TendstoInBootstrapWeakDistribution μ Pstar
        (fun n ω ωs => (TthetaStar n ω ωs, seThetaStar n ω ωs))
        (gaussianReal 0 1) (fun z : ℝ => (seθ * z, seθ)))
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hTthetaStar : ∀ n ω, Measurable (TthetaStar n ω))
    (hseThetaStar : ∀ n ω, Measurable (seThetaStar n ω))
    (hse :
      TendstoInBootstrapProbability μ Pstar seThetaStar (fun _ => seθ)) :
    TendstoInBootstrapWeakDistribution μ Pstar
      (fun n ω ωs => TthetaStar n ω ωs / seThetaStar n ω ωs)
      (gaussianReal 0 1) (fun z : ℝ => z) :=
  chapter10_bootstrap_studentized_ratio_standardNormal
    (μ := μ) (Pstar := Pstar) (Xstar := TthetaStar)
    (Ystar := seThetaStar) (c := seθ)
    hseθ hjoint hPstar hTthetaStar hseThetaStar hse

/-- Indexed Hansen Theorem 10.18, regression bootstrap t-statistic
standard-normal wrapper for sample-size-dependent bootstrap spaces. -/
theorem chapter10_indexed_bootstrap_regression_tstat_standardNormal
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {TthetaStar seThetaStar : ∀ n, Ω → Ωboot n → ℝ} {seθ : ℝ}
    (hseθ : 0 < seθ)
    (hjoint :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar
        (fun n ω ωs => (TthetaStar n ω ωs, seThetaStar n ω ωs))
        (gaussianReal 0 1) (fun z : ℝ => (seθ * z, seθ)))
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hTthetaStar : ∀ n ω, Measurable (TthetaStar n ω))
    (hseThetaStar : ∀ n ω, Measurable (seThetaStar n ω))
    (hse :
      TendstoInBootstrapProbabilityIndexed μ Pstar seThetaStar (fun _ => seθ)) :
    TendstoInBootstrapWeakDistributionIndexed μ Pstar
      (fun n ω ωs => TthetaStar n ω ωs / seThetaStar n ω ωs)
      (gaussianReal 0 1) (fun z : ℝ => z) :=
  chapter10_indexed_bootstrap_studentized_ratio_standardNormal
    (μ := μ) (Pstar := Pstar) (Xstar := TthetaStar)
    (Ystar := seThetaStar) (c := seθ)
    hseθ hjoint hPstar hTthetaStar hseThetaStar hse

/-- Hansen Definition 10.2 face of the regression bootstrap t-statistic
standard-normal wrapper. -/
theorem chapter10_bootstrap_regression_tstat_distribution_standardNormal
    {Pstar : ℕ → Ω → Measure Ωs}
    {TthetaStar seThetaStar : ℕ → Ω → Ωs → ℝ} {seθ : ℝ}
    (hseθ : 0 < seθ)
    (hjoint :
      TendstoInBootstrapWeakDistribution μ Pstar
        (fun n ω ωs => (TthetaStar n ω ωs, seThetaStar n ω ωs))
        (gaussianReal 0 1) (fun z : ℝ => (seθ * z, seθ)))
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hTthetaStar : ∀ n ω, Measurable (TthetaStar n ω))
    (hseThetaStar : ∀ n ω, Measurable (seThetaStar n ω))
    (hse :
      TendstoInBootstrapProbability μ Pstar seThetaStar (fun _ => seθ)) :
    TendstoInBootstrapDistribution μ Pstar
      (fun n ω ωs (_ : Unit) =>
        TthetaStar n ω ωs / seThetaStar n ω ωs)
      (gaussianReal 0 1) (fun z : ℝ => fun _ : Unit => z) :=
  chapter10_bootstrap_studentized_ratio_distribution_standardNormal
    (μ := μ) (Pstar := Pstar) (Xstar := TthetaStar)
    (Ystar := seThetaStar) (c := seθ)
    hseθ hjoint hPstar hTthetaStar hseThetaStar hse

/-- Indexed Hansen Definition 10.2 face of the regression bootstrap
t-statistic standard-normal wrapper. -/
theorem chapter10_indexed_bootstrap_regression_tstat_distribution_standardNormal
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {TthetaStar seThetaStar : ∀ n, Ω → Ωboot n → ℝ} {seθ : ℝ}
    (hseθ : 0 < seθ)
    (hjoint :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar
        (fun n ω ωs => (TthetaStar n ω ωs, seThetaStar n ω ωs))
        (gaussianReal 0 1) (fun z : ℝ => (seθ * z, seθ)))
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hTthetaStar : ∀ n ω, Measurable (TthetaStar n ω))
    (hseThetaStar : ∀ n ω, Measurable (seThetaStar n ω))
    (hse :
      TendstoInBootstrapProbabilityIndexed μ Pstar seThetaStar (fun _ => seθ)) :
    TendstoInBootstrapDistributionIndexed μ Pstar
      (fun n ω ωs (_ : Unit) =>
        TthetaStar n ω ωs / seThetaStar n ω ωs)
      (gaussianReal 0 1) (fun z : ℝ => fun _ : Unit => z) :=
  chapter10_indexed_bootstrap_studentized_ratio_distribution_standardNormal
    (μ := μ) (Pstar := Pstar) (Xstar := TthetaStar)
    (Ystar := seThetaStar) (c := seθ)
    hseθ hjoint hPstar hTthetaStar hseThetaStar hse

/-- Hansen Theorem 10.18, absolute regression bootstrap t-statistic
absolute-standard-normal wrapper.

This is the weak bootstrap law for the absolute statistic used by the
two-sided bootstrap-test critical-value route in Theorem 10.16. -/
theorem chapter10_bootstrap_regression_abs_tstat_standardNormalAbs
    {Pstar : ℕ → Ω → Measure Ωs}
    {TthetaStar seThetaStar : ℕ → Ω → Ωs → ℝ} {seθ : ℝ}
    (hseθ : 0 < seθ)
    (hjoint :
      TendstoInBootstrapWeakDistribution μ Pstar
        (fun n ω ωs => (TthetaStar n ω ωs, seThetaStar n ω ωs))
        (gaussianReal 0 1) (fun z : ℝ => (seθ * z, seθ)))
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hTthetaStar : ∀ n ω, Measurable (TthetaStar n ω))
    (hseThetaStar : ∀ n ω, Measurable (seThetaStar n ω))
    (hse :
      TendstoInBootstrapProbability μ Pstar seThetaStar (fun _ => seθ)) :
    TendstoInBootstrapWeakDistribution μ Pstar
      (fun n ω ωs => |TthetaStar n ω ωs / seThetaStar n ω ωs|)
      ((gaussianReal 0 1).map (fun z : ℝ => |z|)) (fun z : ℝ => z) :=
  chapter10_bootstrap_studentized_ratio_abs_standardNormalAbs
    (μ := μ) (Pstar := Pstar) (Xstar := TthetaStar)
    (Ystar := seThetaStar) (c := seθ)
    hseθ hjoint hPstar hTthetaStar hseThetaStar hse

/-- Indexed Hansen Theorem 10.18, absolute regression bootstrap t-statistic
absolute-standard-normal wrapper. -/
theorem chapter10_indexed_bootstrap_regression_abs_tstat_standardNormalAbs
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {TthetaStar seThetaStar : ∀ n, Ω → Ωboot n → ℝ} {seθ : ℝ}
    (hseθ : 0 < seθ)
    (hjoint :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar
        (fun n ω ωs => (TthetaStar n ω ωs, seThetaStar n ω ωs))
        (gaussianReal 0 1) (fun z : ℝ => (seθ * z, seθ)))
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hTthetaStar : ∀ n ω, Measurable (TthetaStar n ω))
    (hseThetaStar : ∀ n ω, Measurable (seThetaStar n ω))
    (hse :
      TendstoInBootstrapProbabilityIndexed μ Pstar seThetaStar (fun _ => seθ)) :
    TendstoInBootstrapWeakDistributionIndexed μ Pstar
      (fun n ω ωs => |TthetaStar n ω ωs / seThetaStar n ω ωs|)
      ((gaussianReal 0 1).map (fun z : ℝ => |z|)) (fun z : ℝ => z) :=
  chapter10_indexed_bootstrap_studentized_ratio_abs_standardNormalAbs
    (μ := μ) (Pstar := Pstar) (Xstar := TthetaStar)
    (Ystar := seThetaStar) (c := seθ)
    hseθ hjoint hPstar hTthetaStar hseThetaStar hse

/-- Hansen Definition 10.2 face of the absolute regression bootstrap
t-statistic law. -/
theorem chapter10_bootstrap_regression_abs_tstat_distribution_standardNormalAbs
    {Pstar : ℕ → Ω → Measure Ωs}
    {TthetaStar seThetaStar : ℕ → Ω → Ωs → ℝ} {seθ : ℝ}
    (hseθ : 0 < seθ)
    (hjoint :
      TendstoInBootstrapWeakDistribution μ Pstar
        (fun n ω ωs => (TthetaStar n ω ωs, seThetaStar n ω ωs))
        (gaussianReal 0 1) (fun z : ℝ => (seθ * z, seθ)))
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hTthetaStar : ∀ n ω, Measurable (TthetaStar n ω))
    (hseThetaStar : ∀ n ω, Measurable (seThetaStar n ω))
    (hse :
      TendstoInBootstrapProbability μ Pstar seThetaStar (fun _ => seθ)) :
    TendstoInBootstrapDistribution μ Pstar
      (fun n ω ωs (_ : Unit) =>
        |TthetaStar n ω ωs / seThetaStar n ω ωs|)
      ((gaussianReal 0 1).map (fun z : ℝ => |z|))
      (fun z : ℝ => fun _ : Unit => z) :=
  chapter10_bootstrap_studentized_ratio_abs_distribution_standardNormalAbs
    (μ := μ) (Pstar := Pstar) (Xstar := TthetaStar)
    (Ystar := seThetaStar) (c := seθ)
    hseθ hjoint hPstar hTthetaStar hseThetaStar hse

/-- Indexed Hansen Definition 10.2 face of the absolute regression bootstrap
t-statistic law. -/
theorem chapter10_indexed_bootstrap_regression_abs_tstat_distribution_standardNormalAbs
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {TthetaStar seThetaStar : ∀ n, Ω → Ωboot n → ℝ} {seθ : ℝ}
    (hseθ : 0 < seθ)
    (hjoint :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar
        (fun n ω ωs => (TthetaStar n ω ωs, seThetaStar n ω ωs))
        (gaussianReal 0 1) (fun z : ℝ => (seθ * z, seθ)))
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hTthetaStar : ∀ n ω, Measurable (TthetaStar n ω))
    (hseThetaStar : ∀ n ω, Measurable (seThetaStar n ω))
    (hse :
      TendstoInBootstrapProbabilityIndexed μ Pstar seThetaStar (fun _ => seθ)) :
    TendstoInBootstrapDistributionIndexed μ Pstar
      (fun n ω ωs (_ : Unit) =>
        |TthetaStar n ω ωs / seThetaStar n ω ωs|)
      ((gaussianReal 0 1).map (fun z : ℝ => |z|))
      (fun z : ℝ => fun _ : Unit => z) :=
  chapter10_indexed_bootstrap_studentized_ratio_abs_distribution_standardNormalAbs
    (μ := μ) (Pstar := Pstar) (Xstar := TthetaStar)
    (Ystar := seThetaStar) (c := seθ)
    hseθ hjoint hPstar hTthetaStar hseThetaStar hse

/-- Hansen Theorem 10.18, regression bootstrap t-statistic standard-normal
wrapper from a marginal numerator CLT plus feasible-scale consistency.

Compared with `chapter10_bootstrap_regression_tstat_standardNormal`, this
version assembles the joint numerator/standard-error weak limit internally from
the numerator bootstrap CLT, bootstrap-probability scale consistency, and the
explicit compact-tail premise needed for the noncompact Slutsky step. -/
theorem chapter10_bootstrap_regression_tstat_standardNormal_of_numerator_tight
    {Pstar : ℕ → Ω → Measure Ωs}
    {TthetaStar seThetaStar : ℕ → Ω → Ωs → ℝ} {seθ : ℝ}
    (hseθ : 0 < seθ)
    (hT :
      TendstoInBootstrapWeakDistribution μ Pstar TthetaStar
        (gaussianReal 0 1) (fun z : ℝ => seθ * z))
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hTthetaStar : ∀ n ω, Measurable (TthetaStar n ω))
    (hseThetaStar : ∀ n ω, Measurable (seThetaStar n ω))
    (hTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set (ℝ × ℝ), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω => (Pstar n ω).real {ωs | (TthetaStar n ω ωs, seθ) ∉ K})
          atTop (fun _ => 0) ∧
        TendstoInMeasure μ
          (fun n ω =>
            (Pstar n ω).real
              {ωs | (TthetaStar n ω ωs, seThetaStar n ω ωs) ∉ K})
          atTop (fun _ => 0))
    (hse :
      TendstoInBootstrapProbability μ Pstar seThetaStar (fun _ => seθ)) :
    TendstoInBootstrapWeakDistribution μ Pstar
      (fun n ω ωs => TthetaStar n ω ωs / seThetaStar n ω ωs)
      (gaussianReal 0 1) (fun z : ℝ => z) :=
  chapter10_bootstrap_studentized_ratio_standardNormal_of_numerator_tight
    (μ := μ) (Pstar := Pstar) (Xstar := TthetaStar)
    (Ystar := seThetaStar) (c := seθ)
    hseθ hT hPstar hTthetaStar hseThetaStar hTail hse

/-- Indexed Hansen Theorem 10.18 regression bootstrap t-statistic
standard-normal wrapper from a marginal numerator CLT plus feasible-scale
consistency. -/
theorem
chapter10_indexed_bootstrap_regression_tstat_standardNormal_of_numerator_tight
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {TthetaStar seThetaStar : ∀ n, Ω → Ωboot n → ℝ} {seθ : ℝ}
    (hseθ : 0 < seθ)
    (hT :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar TthetaStar
        (gaussianReal 0 1) (fun z : ℝ => seθ * z))
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hTthetaStar : ∀ n ω, Measurable (TthetaStar n ω))
    (hseThetaStar : ∀ n ω, Measurable (seThetaStar n ω))
    (hTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set (ℝ × ℝ), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω => (Pstar n ω).real {ωs | (TthetaStar n ω ωs, seθ) ∉ K})
          atTop (fun _ => 0) ∧
        TendstoInMeasure μ
          (fun n ω =>
            (Pstar n ω).real
              {ωs | (TthetaStar n ω ωs, seThetaStar n ω ωs) ∉ K})
          atTop (fun _ => 0))
    (hse :
      TendstoInBootstrapProbabilityIndexed μ Pstar seThetaStar (fun _ => seθ)) :
    TendstoInBootstrapWeakDistributionIndexed μ Pstar
      (fun n ω ωs => TthetaStar n ω ωs / seThetaStar n ω ωs)
      (gaussianReal 0 1) (fun z : ℝ => z) :=
  chapter10_indexed_bootstrap_studentized_ratio_standardNormal_of_numerator_tight
    (μ := μ) (Pstar := Pstar) (Xstar := TthetaStar)
    (Ystar := seThetaStar) (c := seθ)
    hseθ hT hPstar hTthetaStar hseThetaStar hTail hse

/-- Hansen Definition 10.2 face of the regression t-statistic route from a
marginal numerator CLT plus feasible-scale consistency. -/
theorem
chapter10_bootstrap_regression_tstat_distribution_standardNormal_of_numerator_tight
    {Pstar : ℕ → Ω → Measure Ωs}
    {TthetaStar seThetaStar : ℕ → Ω → Ωs → ℝ} {seθ : ℝ}
    (hseθ : 0 < seθ)
    (hT :
      TendstoInBootstrapWeakDistribution μ Pstar TthetaStar
        (gaussianReal 0 1) (fun z : ℝ => seθ * z))
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hTthetaStar : ∀ n ω, Measurable (TthetaStar n ω))
    (hseThetaStar : ∀ n ω, Measurable (seThetaStar n ω))
    (hTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set (ℝ × ℝ), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω => (Pstar n ω).real {ωs | (TthetaStar n ω ωs, seθ) ∉ K})
          atTop (fun _ => 0) ∧
        TendstoInMeasure μ
          (fun n ω =>
            (Pstar n ω).real
              {ωs | (TthetaStar n ω ωs, seThetaStar n ω ωs) ∉ K})
          atTop (fun _ => 0))
    (hse :
      TendstoInBootstrapProbability μ Pstar seThetaStar (fun _ => seθ)) :
    TendstoInBootstrapDistribution μ Pstar
      (fun n ω ωs (_ : Unit) =>
        TthetaStar n ω ωs / seThetaStar n ω ωs)
      (gaussianReal 0 1) (fun z : ℝ => fun _ : Unit => z) :=
  chapter10_bootstrap_studentized_ratio_distribution_standardNormal_of_numerator_tight
    (μ := μ) (Pstar := Pstar) (Xstar := TthetaStar)
    (Ystar := seThetaStar) (c := seθ)
    hseθ hT hPstar hTthetaStar hseThetaStar hTail hse

/-- Indexed Hansen Definition 10.2 face of the regression t-statistic route
from a marginal numerator CLT plus feasible-scale consistency. -/
theorem
chapter10_indexed_bootstrap_regression_tstat_distribution_standardNormal_of_numerator_tight
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {TthetaStar seThetaStar : ∀ n, Ω → Ωboot n → ℝ} {seθ : ℝ}
    (hseθ : 0 < seθ)
    (hT :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar TthetaStar
        (gaussianReal 0 1) (fun z : ℝ => seθ * z))
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hTthetaStar : ∀ n ω, Measurable (TthetaStar n ω))
    (hseThetaStar : ∀ n ω, Measurable (seThetaStar n ω))
    (hTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set (ℝ × ℝ), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω => (Pstar n ω).real {ωs | (TthetaStar n ω ωs, seθ) ∉ K})
          atTop (fun _ => 0) ∧
        TendstoInMeasure μ
          (fun n ω =>
            (Pstar n ω).real
              {ωs | (TthetaStar n ω ωs, seThetaStar n ω ωs) ∉ K})
          atTop (fun _ => 0))
    (hse :
      TendstoInBootstrapProbabilityIndexed μ Pstar seThetaStar (fun _ => seθ)) :
    TendstoInBootstrapDistributionIndexed μ Pstar
      (fun n ω ωs (_ : Unit) =>
        TthetaStar n ω ωs / seThetaStar n ω ωs)
      (gaussianReal 0 1) (fun z : ℝ => fun _ : Unit => z) :=
  chapter10_indexed_bootstrap_studentized_ratio_distribution_standardNormal_of_numerator_tight
    (μ := μ) (Pstar := Pstar) (Xstar := TthetaStar)
    (Ystar := seThetaStar) (c := seθ)
    hseθ hT hPstar hTthetaStar hseThetaStar hTail hse

/-- Hansen Theorem 10.18, absolute regression bootstrap t-statistic route from
a marginal numerator CLT plus feasible-scale consistency. -/
theorem
chapter10_bootstrap_regression_abs_tstat_standardNormalAbs_of_numerator_tight
    {Pstar : ℕ → Ω → Measure Ωs}
    {TthetaStar seThetaStar : ℕ → Ω → Ωs → ℝ} {seθ : ℝ}
    (hseθ : 0 < seθ)
    (hT :
      TendstoInBootstrapWeakDistribution μ Pstar TthetaStar
        (gaussianReal 0 1) (fun z : ℝ => seθ * z))
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hTthetaStar : ∀ n ω, Measurable (TthetaStar n ω))
    (hseThetaStar : ∀ n ω, Measurable (seThetaStar n ω))
    (hTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set (ℝ × ℝ), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω => (Pstar n ω).real {ωs | (TthetaStar n ω ωs, seθ) ∉ K})
          atTop (fun _ => 0) ∧
        TendstoInMeasure μ
          (fun n ω =>
            (Pstar n ω).real
              {ωs | (TthetaStar n ω ωs, seThetaStar n ω ωs) ∉ K})
          atTop (fun _ => 0))
    (hse :
      TendstoInBootstrapProbability μ Pstar seThetaStar (fun _ => seθ)) :
    TendstoInBootstrapWeakDistribution μ Pstar
      (fun n ω ωs => |TthetaStar n ω ωs / seThetaStar n ω ωs|)
      ((gaussianReal 0 1).map (fun z : ℝ => |z|)) (fun z : ℝ => z) :=
  chapter10_bootstrap_studentized_ratio_abs_standardNormalAbs_of_numerator_tight
    (μ := μ) (Pstar := Pstar) (Xstar := TthetaStar)
    (Ystar := seThetaStar) (c := seθ)
    hseθ hT hPstar hTthetaStar hseThetaStar hTail hse

/-- Indexed Hansen Theorem 10.18, absolute regression bootstrap t-statistic
route from a marginal numerator CLT plus feasible-scale consistency. -/
theorem
chapter10_indexed_bootstrap_regression_abs_tstat_standardNormalAbs_of_numerator_tight
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {TthetaStar seThetaStar : ∀ n, Ω → Ωboot n → ℝ} {seθ : ℝ}
    (hseθ : 0 < seθ)
    (hT :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar TthetaStar
        (gaussianReal 0 1) (fun z : ℝ => seθ * z))
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hTthetaStar : ∀ n ω, Measurable (TthetaStar n ω))
    (hseThetaStar : ∀ n ω, Measurable (seThetaStar n ω))
    (hTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set (ℝ × ℝ), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω => (Pstar n ω).real {ωs | (TthetaStar n ω ωs, seθ) ∉ K})
          atTop (fun _ => 0) ∧
        TendstoInMeasure μ
          (fun n ω =>
            (Pstar n ω).real
              {ωs | (TthetaStar n ω ωs, seThetaStar n ω ωs) ∉ K})
          atTop (fun _ => 0))
    (hse :
      TendstoInBootstrapProbabilityIndexed μ Pstar seThetaStar (fun _ => seθ)) :
    TendstoInBootstrapWeakDistributionIndexed μ Pstar
      (fun n ω ωs => |TthetaStar n ω ωs / seThetaStar n ω ωs|)
      ((gaussianReal 0 1).map (fun z : ℝ => |z|)) (fun z : ℝ => z) :=
  chapter10_indexed_bootstrap_studentized_ratio_abs_standardNormalAbs_of_numerator_tight
    (μ := μ) (Pstar := Pstar) (Xstar := TthetaStar)
    (Ystar := seThetaStar) (c := seθ)
    hseθ hT hPstar hTthetaStar hseThetaStar hTail hse

/-- Hansen Definition 10.2 face of the absolute regression bootstrap
t-statistic route from a marginal numerator CLT plus feasible-scale
consistency. -/
theorem
chapter10_bootstrap_regression_abs_tstat_distribution_standardNormalAbs_of_numerator_tight
    {Pstar : ℕ → Ω → Measure Ωs}
    {TthetaStar seThetaStar : ℕ → Ω → Ωs → ℝ} {seθ : ℝ}
    (hseθ : 0 < seθ)
    (hT :
      TendstoInBootstrapWeakDistribution μ Pstar TthetaStar
        (gaussianReal 0 1) (fun z : ℝ => seθ * z))
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hTthetaStar : ∀ n ω, Measurable (TthetaStar n ω))
    (hseThetaStar : ∀ n ω, Measurable (seThetaStar n ω))
    (hTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set (ℝ × ℝ), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω => (Pstar n ω).real {ωs | (TthetaStar n ω ωs, seθ) ∉ K})
          atTop (fun _ => 0) ∧
        TendstoInMeasure μ
          (fun n ω =>
            (Pstar n ω).real
              {ωs | (TthetaStar n ω ωs, seThetaStar n ω ωs) ∉ K})
          atTop (fun _ => 0))
    (hse :
      TendstoInBootstrapProbability μ Pstar seThetaStar (fun _ => seθ)) :
    TendstoInBootstrapDistribution μ Pstar
      (fun n ω ωs (_ : Unit) =>
        |TthetaStar n ω ωs / seThetaStar n ω ωs|)
      ((gaussianReal 0 1).map (fun z : ℝ => |z|))
      (fun z : ℝ => fun _ : Unit => z) :=
  chapter10_bootstrap_studentized_abs_distribution_of_numerator_tight
    (μ := μ) (Pstar := Pstar) (Xstar := TthetaStar)
    (Ystar := seThetaStar) (c := seθ)
    hseθ hT hPstar hTthetaStar hseThetaStar hTail hse

/-- Indexed Hansen Definition 10.2 face of the absolute regression bootstrap
t-statistic route from a marginal numerator CLT plus feasible-scale
consistency. -/
theorem
chapter10_indexed_bootstrap_regression_abs_tstat_distribution_standardNormalAbs_of_numerator_tight
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {TthetaStar seThetaStar : ∀ n, Ω → Ωboot n → ℝ} {seθ : ℝ}
    (hseθ : 0 < seθ)
    (hT :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar TthetaStar
        (gaussianReal 0 1) (fun z : ℝ => seθ * z))
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hTthetaStar : ∀ n ω, Measurable (TthetaStar n ω))
    (hseThetaStar : ∀ n ω, Measurable (seThetaStar n ω))
    (hTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set (ℝ × ℝ), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω => (Pstar n ω).real {ωs | (TthetaStar n ω ωs, seθ) ∉ K})
          atTop (fun _ => 0) ∧
        TendstoInMeasure μ
          (fun n ω =>
            (Pstar n ω).real
              {ωs | (TthetaStar n ω ωs, seThetaStar n ω ωs) ∉ K})
          atTop (fun _ => 0))
    (hse :
      TendstoInBootstrapProbabilityIndexed μ Pstar seThetaStar (fun _ => seθ)) :
    TendstoInBootstrapDistributionIndexed μ Pstar
      (fun n ω ωs (_ : Unit) =>
        |TthetaStar n ω ωs / seThetaStar n ω ωs|)
      ((gaussianReal 0 1).map (fun z : ℝ => |z|))
      (fun z : ℝ => fun _ : Unit => z) :=
  chapter10_indexed_bootstrap_studentized_abs_distribution_of_numerator_tight
    (μ := μ) (Pstar := Pstar) (Xstar := TthetaStar)
    (Ystar := seThetaStar) (c := seθ)
    hseθ hT hPstar hTthetaStar hseThetaStar hTail hse

/-- Hansen Theorem 10.18 regression t-statistic route from a marginal
numerator CLT, scalar numerator compact-tail control, and feasible-scale
consistency. -/
theorem chapter10_bootstrap_regression_tstat_standardNormal_of_scalarTail
    {Pstar : ℕ → Ω → Measure Ωs}
    {TthetaStar seThetaStar : ℕ → Ω → Ωs → ℝ} {seθ : ℝ}
    (hseθ : 0 < seθ)
    (hT :
      TendstoInBootstrapWeakDistribution μ Pstar TthetaStar
        (gaussianReal 0 1) (fun z : ℝ => seθ * z))
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hTthetaStar : ∀ n ω, Measurable (TthetaStar n ω))
    (hseThetaStar : ∀ n ω, Measurable (seThetaStar n ω))
    (hTtail : ∀ η : ℝ, 0 < η →
      ∃ Kt : Set ℝ, IsCompact Kt ∧
        TendstoInMeasure μ
          (fun n ω => (Pstar n ω).real {ωs | TthetaStar n ω ωs ∉ Kt})
          atTop (fun _ => 0))
    (hse :
      TendstoInBootstrapProbability μ Pstar seThetaStar (fun _ => seθ)) :
    TendstoInBootstrapWeakDistribution μ Pstar
      (fun n ω ωs => TthetaStar n ω ωs / seThetaStar n ω ωs)
      (gaussianReal 0 1) (fun z : ℝ => z) :=
  chapter10_bootstrap_studentized_ratio_standardNormal_of_scalarTail
    (μ := μ) (Pstar := Pstar) (Xstar := TthetaStar)
    (Ystar := seThetaStar) (c := seθ)
    hseθ hT hPstar hTthetaStar hseThetaStar hTtail hse

/-- Indexed Hansen Theorem 10.18 regression t-statistic route from scalar
numerator compact-tail control. -/
theorem chapter10_indexed_bootstrap_regression_tstat_standardNormal_of_scalarTail
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {TthetaStar seThetaStar : ∀ n, Ω → Ωboot n → ℝ} {seθ : ℝ}
    (hseθ : 0 < seθ)
    (hT :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar TthetaStar
        (gaussianReal 0 1) (fun z : ℝ => seθ * z))
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hTthetaStar : ∀ n ω, Measurable (TthetaStar n ω))
    (hseThetaStar : ∀ n ω, Measurable (seThetaStar n ω))
    (hTtail : ∀ η : ℝ, 0 < η →
      ∃ Kt : Set ℝ, IsCompact Kt ∧
        TendstoInMeasure μ
          (fun n ω => (Pstar n ω).real {ωs | TthetaStar n ω ωs ∉ Kt})
          atTop (fun _ => 0))
    (hse :
      TendstoInBootstrapProbabilityIndexed μ Pstar seThetaStar (fun _ => seθ)) :
    TendstoInBootstrapWeakDistributionIndexed μ Pstar
      (fun n ω ωs => TthetaStar n ω ωs / seThetaStar n ω ωs)
      (gaussianReal 0 1) (fun z : ℝ => z) :=
  chapter10_indexed_bootstrap_studentized_ratio_standardNormal_of_scalarTail
    (μ := μ) (Pstar := Pstar) (Xstar := TthetaStar)
    (Ystar := seThetaStar) (c := seθ)
    hseθ hT hPstar hTthetaStar hseThetaStar hTtail hse

/-- Hansen Definition 10.2 face of the regression t-statistic route from
scalar numerator compact-tail control. -/
theorem chapter10_bootstrap_regression_tstat_distribution_of_scalarTail
    {Pstar : ℕ → Ω → Measure Ωs}
    {TthetaStar seThetaStar : ℕ → Ω → Ωs → ℝ} {seθ : ℝ}
    (hseθ : 0 < seθ)
    (hT :
      TendstoInBootstrapWeakDistribution μ Pstar TthetaStar
        (gaussianReal 0 1) (fun z : ℝ => seθ * z))
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hTthetaStar : ∀ n ω, Measurable (TthetaStar n ω))
    (hseThetaStar : ∀ n ω, Measurable (seThetaStar n ω))
    (hTtail : ∀ η : ℝ, 0 < η →
      ∃ Kt : Set ℝ, IsCompact Kt ∧
        TendstoInMeasure μ
          (fun n ω => (Pstar n ω).real {ωs | TthetaStar n ω ωs ∉ Kt})
          atTop (fun _ => 0))
    (hse :
      TendstoInBootstrapProbability μ Pstar seThetaStar (fun _ => seθ)) :
    TendstoInBootstrapDistribution μ Pstar
      (fun n ω ωs (_ : Unit) =>
        TthetaStar n ω ωs / seThetaStar n ω ωs)
      (gaussianReal 0 1) (fun z : ℝ => fun _ : Unit => z) :=
  chapter10_bootstrap_studentized_ratio_distribution_of_scalarTail
    (μ := μ) (Pstar := Pstar) (Xstar := TthetaStar)
    (Ystar := seThetaStar) (c := seθ)
    hseθ hT hPstar hTthetaStar hseThetaStar hTtail hse

/-- Indexed Hansen Definition 10.2 face of the regression t-statistic route
from scalar numerator compact-tail control. -/
theorem chapter10_indexed_bootstrap_regression_tstat_distribution_of_scalarTail
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {TthetaStar seThetaStar : ∀ n, Ω → Ωboot n → ℝ} {seθ : ℝ}
    (hseθ : 0 < seθ)
    (hT :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar TthetaStar
        (gaussianReal 0 1) (fun z : ℝ => seθ * z))
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hTthetaStar : ∀ n ω, Measurable (TthetaStar n ω))
    (hseThetaStar : ∀ n ω, Measurable (seThetaStar n ω))
    (hTtail : ∀ η : ℝ, 0 < η →
      ∃ Kt : Set ℝ, IsCompact Kt ∧
        TendstoInMeasure μ
          (fun n ω => (Pstar n ω).real {ωs | TthetaStar n ω ωs ∉ Kt})
          atTop (fun _ => 0))
    (hse :
      TendstoInBootstrapProbabilityIndexed μ Pstar seThetaStar (fun _ => seθ)) :
    TendstoInBootstrapDistributionIndexed μ Pstar
      (fun n ω ωs (_ : Unit) =>
        TthetaStar n ω ωs / seThetaStar n ω ωs)
      (gaussianReal 0 1) (fun z : ℝ => fun _ : Unit => z) :=
  chapter10_indexed_bootstrap_studentized_ratio_distribution_of_scalarTail
    (μ := μ) (Pstar := Pstar) (Xstar := TthetaStar)
    (Ystar := seThetaStar) (c := seθ)
    hseθ hT hPstar hTthetaStar hseThetaStar hTtail hse

/-- Hansen Theorem 10.18 absolute regression t-statistic route from scalar
numerator compact-tail control. -/
theorem chapter10_bootstrap_regression_abs_tstat_of_scalarTail
    {Pstar : ℕ → Ω → Measure Ωs}
    {TthetaStar seThetaStar : ℕ → Ω → Ωs → ℝ} {seθ : ℝ}
    (hseθ : 0 < seθ)
    (hT :
      TendstoInBootstrapWeakDistribution μ Pstar TthetaStar
        (gaussianReal 0 1) (fun z : ℝ => seθ * z))
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hTthetaStar : ∀ n ω, Measurable (TthetaStar n ω))
    (hseThetaStar : ∀ n ω, Measurable (seThetaStar n ω))
    (hTtail : ∀ η : ℝ, 0 < η →
      ∃ Kt : Set ℝ, IsCompact Kt ∧
        TendstoInMeasure μ
          (fun n ω => (Pstar n ω).real {ωs | TthetaStar n ω ωs ∉ Kt})
          atTop (fun _ => 0))
    (hse :
      TendstoInBootstrapProbability μ Pstar seThetaStar (fun _ => seθ)) :
    TendstoInBootstrapWeakDistribution μ Pstar
      (fun n ω ωs => |TthetaStar n ω ωs / seThetaStar n ω ωs|)
      ((gaussianReal 0 1).map (fun z : ℝ => |z|)) (fun z : ℝ => z) :=
  chapter10_bootstrap_studentized_ratio_abs_of_scalarTail
    (μ := μ) (Pstar := Pstar) (Xstar := TthetaStar)
    (Ystar := seThetaStar) (c := seθ)
    hseθ hT hPstar hTthetaStar hseThetaStar hTtail hse

/-- Indexed Hansen Theorem 10.18 absolute regression t-statistic route from
scalar numerator compact-tail control. -/
theorem chapter10_indexed_bootstrap_regression_abs_tstat_of_scalarTail
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {TthetaStar seThetaStar : ∀ n, Ω → Ωboot n → ℝ} {seθ : ℝ}
    (hseθ : 0 < seθ)
    (hT :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar TthetaStar
        (gaussianReal 0 1) (fun z : ℝ => seθ * z))
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hTthetaStar : ∀ n ω, Measurable (TthetaStar n ω))
    (hseThetaStar : ∀ n ω, Measurable (seThetaStar n ω))
    (hTtail : ∀ η : ℝ, 0 < η →
      ∃ Kt : Set ℝ, IsCompact Kt ∧
        TendstoInMeasure μ
          (fun n ω => (Pstar n ω).real {ωs | TthetaStar n ω ωs ∉ Kt})
          atTop (fun _ => 0))
    (hse :
      TendstoInBootstrapProbabilityIndexed μ Pstar seThetaStar (fun _ => seθ)) :
    TendstoInBootstrapWeakDistributionIndexed μ Pstar
      (fun n ω ωs => |TthetaStar n ω ωs / seThetaStar n ω ωs|)
      ((gaussianReal 0 1).map (fun z : ℝ => |z|)) (fun z : ℝ => z) :=
  chapter10_indexed_bootstrap_studentized_ratio_abs_of_scalarTail
    (μ := μ) (Pstar := Pstar) (Xstar := TthetaStar)
    (Ystar := seThetaStar) (c := seθ)
    hseθ hT hPstar hTthetaStar hseThetaStar hTtail hse

/-- Hansen Definition 10.2 face of the absolute regression t-statistic route
from scalar numerator compact-tail control. -/
theorem chapter10_bootstrap_regression_abs_tstat_distribution_of_scalarTail
    {Pstar : ℕ → Ω → Measure Ωs}
    {TthetaStar seThetaStar : ℕ → Ω → Ωs → ℝ} {seθ : ℝ}
    (hseθ : 0 < seθ)
    (hT :
      TendstoInBootstrapWeakDistribution μ Pstar TthetaStar
        (gaussianReal 0 1) (fun z : ℝ => seθ * z))
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hTthetaStar : ∀ n ω, Measurable (TthetaStar n ω))
    (hseThetaStar : ∀ n ω, Measurable (seThetaStar n ω))
    (hTtail : ∀ η : ℝ, 0 < η →
      ∃ Kt : Set ℝ, IsCompact Kt ∧
        TendstoInMeasure μ
          (fun n ω => (Pstar n ω).real {ωs | TthetaStar n ω ωs ∉ Kt})
          atTop (fun _ => 0))
    (hse :
      TendstoInBootstrapProbability μ Pstar seThetaStar (fun _ => seθ)) :
    TendstoInBootstrapDistribution μ Pstar
      (fun n ω ωs (_ : Unit) =>
        |TthetaStar n ω ωs / seThetaStar n ω ωs|)
      ((gaussianReal 0 1).map (fun z : ℝ => |z|))
      (fun z : ℝ => fun _ : Unit => z) :=
  chapter10_bootstrap_studentized_abs_distribution_of_scalarTail
    (μ := μ) (Pstar := Pstar) (Xstar := TthetaStar)
    (Ystar := seThetaStar) (c := seθ)
    hseθ hT hPstar hTthetaStar hseThetaStar hTtail hse

/-- Indexed Hansen Definition 10.2 face of the absolute regression t-statistic
route from scalar numerator compact-tail control. -/
theorem chapter10_indexed_bootstrap_regression_abs_tstat_distribution_of_scalarTail
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {TthetaStar seThetaStar : ∀ n, Ω → Ωboot n → ℝ} {seθ : ℝ}
    (hseθ : 0 < seθ)
    (hT :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar TthetaStar
        (gaussianReal 0 1) (fun z : ℝ => seθ * z))
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hTthetaStar : ∀ n ω, Measurable (TthetaStar n ω))
    (hseThetaStar : ∀ n ω, Measurable (seThetaStar n ω))
    (hTtail : ∀ η : ℝ, 0 < η →
      ∃ Kt : Set ℝ, IsCompact Kt ∧
        TendstoInMeasure μ
          (fun n ω => (Pstar n ω).real {ωs | TthetaStar n ω ωs ∉ Kt})
          atTop (fun _ => 0))
    (hse :
      TendstoInBootstrapProbabilityIndexed μ Pstar seThetaStar (fun _ => seθ)) :
    TendstoInBootstrapDistributionIndexed μ Pstar
      (fun n ω ωs (_ : Unit) =>
        |TthetaStar n ω ωs / seThetaStar n ω ωs|)
      ((gaussianReal 0 1).map (fun z : ℝ => |z|))
      (fun z : ℝ => fun _ : Unit => z) :=
  chapter10_indexed_bootstrap_studentized_abs_distribution_of_scalarTail
    (μ := μ) (Pstar := Pstar) (Xstar := TthetaStar)
    (Ystar := seThetaStar) (c := seθ)
    hseθ hT hPstar hTthetaStar hseThetaStar hTtail hse

/-- Hansen Theorem 10.18 regression t-statistic route from an eventually bounded
transformed numerator and feasible-scale consistency. -/
theorem chapter10_bootstrap_regression_tstat_standardNormal_of_eventually_bound
    {Pstar : ℕ → Ω → Measure Ωs}
    {TthetaStar seThetaStar : ℕ → Ω → Ωs → ℝ} {seθ C : ℝ}
    (hseθ : 0 < seθ)
    (hT :
      TendstoInBootstrapWeakDistribution μ Pstar TthetaStar
        (gaussianReal 0 1) (fun z : ℝ => seθ * z))
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hTthetaStar : ∀ n ω, Measurable (TthetaStar n ω))
    (hseThetaStar : ∀ n ω, Measurable (seThetaStar n ω))
    (hbound : ∀ᶠ n in atTop, ∀ ω ωs, |TthetaStar n ω ωs| ≤ C)
    (hse :
      TendstoInBootstrapProbability μ Pstar seThetaStar (fun _ => seθ)) :
    TendstoInBootstrapWeakDistribution μ Pstar
      (fun n ω ωs => TthetaStar n ω ωs / seThetaStar n ω ωs)
      (gaussianReal 0 1) (fun z : ℝ => z) :=
  chapter10_bootstrap_studentized_ratio_standardNormal_of_eventually_bound
    (μ := μ) (Pstar := Pstar) (Xstar := TthetaStar)
    (Ystar := seThetaStar) (c := seθ) (C := C)
    hseθ hT hPstar hTthetaStar hseThetaStar hbound hse

/-- Indexed Hansen Theorem 10.18 regression t-statistic route from an
eventually bounded transformed numerator. -/
theorem
chapter10_indexed_bootstrap_regression_tstat_standardNormal_of_eventually_bound
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {TthetaStar seThetaStar : ∀ n, Ω → Ωboot n → ℝ} {seθ C : ℝ}
    (hseθ : 0 < seθ)
    (hT :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar TthetaStar
        (gaussianReal 0 1) (fun z : ℝ => seθ * z))
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hTthetaStar : ∀ n ω, Measurable (TthetaStar n ω))
    (hseThetaStar : ∀ n ω, Measurable (seThetaStar n ω))
    (hbound : ∀ᶠ n in atTop, ∀ ω ωs, |TthetaStar n ω ωs| ≤ C)
    (hse :
      TendstoInBootstrapProbabilityIndexed μ Pstar seThetaStar (fun _ => seθ)) :
    TendstoInBootstrapWeakDistributionIndexed μ Pstar
      (fun n ω ωs => TthetaStar n ω ωs / seThetaStar n ω ωs)
      (gaussianReal 0 1) (fun z : ℝ => z) :=
  chapter10_indexed_bootstrap_studentized_ratio_standardNormal_of_eventually_bound
    (μ := μ) (Pstar := Pstar) (Xstar := TthetaStar)
    (Ystar := seThetaStar) (c := seθ) (C := C)
    hseθ hT hPstar hTthetaStar hseThetaStar hbound hse

/-- Hansen Definition 10.2 face of the regression t-statistic route from an
eventually bounded transformed numerator. -/
theorem chapter10_bootstrap_regression_tstat_distribution_of_eventually_bound
    {Pstar : ℕ → Ω → Measure Ωs}
    {TthetaStar seThetaStar : ℕ → Ω → Ωs → ℝ} {seθ C : ℝ}
    (hseθ : 0 < seθ)
    (hT :
      TendstoInBootstrapWeakDistribution μ Pstar TthetaStar
        (gaussianReal 0 1) (fun z : ℝ => seθ * z))
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hTthetaStar : ∀ n ω, Measurable (TthetaStar n ω))
    (hseThetaStar : ∀ n ω, Measurable (seThetaStar n ω))
    (hbound : ∀ᶠ n in atTop, ∀ ω ωs, |TthetaStar n ω ωs| ≤ C)
    (hse :
      TendstoInBootstrapProbability μ Pstar seThetaStar (fun _ => seθ)) :
    TendstoInBootstrapDistribution μ Pstar
      (fun n ω ωs (_ : Unit) =>
        TthetaStar n ω ωs / seThetaStar n ω ωs)
      (gaussianReal 0 1) (fun z : ℝ => fun _ : Unit => z) :=
  chapter10_bootstrap_studentized_ratio_distribution_of_eventually_bound
    (μ := μ) (Pstar := Pstar) (Xstar := TthetaStar)
    (Ystar := seThetaStar) (c := seθ) (C := C)
    hseθ hT hPstar hTthetaStar hseThetaStar hbound hse

/-- Indexed Hansen Definition 10.2 face of the regression t-statistic route
from an eventually bounded transformed numerator. -/
theorem
chapter10_indexed_bootstrap_regression_tstat_distribution_of_eventually_bound
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {TthetaStar seThetaStar : ∀ n, Ω → Ωboot n → ℝ} {seθ C : ℝ}
    (hseθ : 0 < seθ)
    (hT :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar TthetaStar
        (gaussianReal 0 1) (fun z : ℝ => seθ * z))
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hTthetaStar : ∀ n ω, Measurable (TthetaStar n ω))
    (hseThetaStar : ∀ n ω, Measurable (seThetaStar n ω))
    (hbound : ∀ᶠ n in atTop, ∀ ω ωs, |TthetaStar n ω ωs| ≤ C)
    (hse :
      TendstoInBootstrapProbabilityIndexed μ Pstar seThetaStar (fun _ => seθ)) :
    TendstoInBootstrapDistributionIndexed μ Pstar
      (fun n ω ωs (_ : Unit) =>
        TthetaStar n ω ωs / seThetaStar n ω ωs)
      (gaussianReal 0 1) (fun z : ℝ => fun _ : Unit => z) :=
  chapter10_indexed_bootstrap_studentized_ratio_distribution_of_eventually_bound
    (μ := μ) (Pstar := Pstar) (Xstar := TthetaStar)
    (Ystar := seThetaStar) (c := seθ) (C := C)
    hseθ hT hPstar hTthetaStar hseThetaStar hbound hse

/-- Hansen Theorem 10.18 absolute regression t-statistic route from an
eventually bounded transformed numerator. -/
theorem chapter10_bootstrap_regression_abs_tstat_of_eventually_bound
    {Pstar : ℕ → Ω → Measure Ωs}
    {TthetaStar seThetaStar : ℕ → Ω → Ωs → ℝ} {seθ C : ℝ}
    (hseθ : 0 < seθ)
    (hT :
      TendstoInBootstrapWeakDistribution μ Pstar TthetaStar
        (gaussianReal 0 1) (fun z : ℝ => seθ * z))
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hTthetaStar : ∀ n ω, Measurable (TthetaStar n ω))
    (hseThetaStar : ∀ n ω, Measurable (seThetaStar n ω))
    (hbound : ∀ᶠ n in atTop, ∀ ω ωs, |TthetaStar n ω ωs| ≤ C)
    (hse :
      TendstoInBootstrapProbability μ Pstar seThetaStar (fun _ => seθ)) :
    TendstoInBootstrapWeakDistribution μ Pstar
      (fun n ω ωs => |TthetaStar n ω ωs / seThetaStar n ω ωs|)
      ((gaussianReal 0 1).map (fun z : ℝ => |z|)) (fun z : ℝ => z) :=
  chapter10_bootstrap_studentized_ratio_abs_of_eventually_bound
    (μ := μ) (Pstar := Pstar) (Xstar := TthetaStar)
    (Ystar := seThetaStar) (c := seθ) (C := C)
    hseθ hT hPstar hTthetaStar hseThetaStar hbound hse

/-- Indexed Hansen Theorem 10.18 absolute regression t-statistic route from an
eventually bounded transformed numerator. -/
theorem chapter10_indexed_bootstrap_regression_abs_tstat_of_eventually_bound
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {TthetaStar seThetaStar : ∀ n, Ω → Ωboot n → ℝ} {seθ C : ℝ}
    (hseθ : 0 < seθ)
    (hT :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar TthetaStar
        (gaussianReal 0 1) (fun z : ℝ => seθ * z))
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hTthetaStar : ∀ n ω, Measurable (TthetaStar n ω))
    (hseThetaStar : ∀ n ω, Measurable (seThetaStar n ω))
    (hbound : ∀ᶠ n in atTop, ∀ ω ωs, |TthetaStar n ω ωs| ≤ C)
    (hse :
      TendstoInBootstrapProbabilityIndexed μ Pstar seThetaStar (fun _ => seθ)) :
    TendstoInBootstrapWeakDistributionIndexed μ Pstar
      (fun n ω ωs => |TthetaStar n ω ωs / seThetaStar n ω ωs|)
      ((gaussianReal 0 1).map (fun z : ℝ => |z|)) (fun z : ℝ => z) :=
  chapter10_indexed_bootstrap_studentized_ratio_abs_of_eventually_bound
    (μ := μ) (Pstar := Pstar) (Xstar := TthetaStar)
    (Ystar := seThetaStar) (c := seθ) (C := C)
    hseθ hT hPstar hTthetaStar hseThetaStar hbound hse

/-- Hansen Definition 10.2 face of the absolute regression t-statistic route
from an eventually bounded transformed numerator. -/
theorem chapter10_bootstrap_regression_abs_tstat_distribution_of_eventually_bound
    {Pstar : ℕ → Ω → Measure Ωs}
    {TthetaStar seThetaStar : ℕ → Ω → Ωs → ℝ} {seθ C : ℝ}
    (hseθ : 0 < seθ)
    (hT :
      TendstoInBootstrapWeakDistribution μ Pstar TthetaStar
        (gaussianReal 0 1) (fun z : ℝ => seθ * z))
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hTthetaStar : ∀ n ω, Measurable (TthetaStar n ω))
    (hseThetaStar : ∀ n ω, Measurable (seThetaStar n ω))
    (hbound : ∀ᶠ n in atTop, ∀ ω ωs, |TthetaStar n ω ωs| ≤ C)
    (hse :
      TendstoInBootstrapProbability μ Pstar seThetaStar (fun _ => seθ)) :
    TendstoInBootstrapDistribution μ Pstar
      (fun n ω ωs (_ : Unit) =>
        |TthetaStar n ω ωs / seThetaStar n ω ωs|)
      ((gaussianReal 0 1).map (fun z : ℝ => |z|))
      (fun z : ℝ => fun _ : Unit => z) :=
  chapter10_bootstrap_studentized_abs_distribution_of_eventually_bound
    (μ := μ) (Pstar := Pstar) (Xstar := TthetaStar)
    (Ystar := seThetaStar) (c := seθ) (C := C)
    hseθ hT hPstar hTthetaStar hseThetaStar hbound hse

/-- Indexed Hansen Definition 10.2 face of the absolute regression t-statistic
route from an eventually bounded transformed numerator. -/
theorem
chapter10_indexed_bootstrap_regression_abs_tstat_distribution_of_eventually_bound
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {TthetaStar seThetaStar : ∀ n, Ω → Ωboot n → ℝ} {seθ C : ℝ}
    (hseθ : 0 < seθ)
    (hT :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar TthetaStar
        (gaussianReal 0 1) (fun z : ℝ => seθ * z))
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hTthetaStar : ∀ n ω, Measurable (TthetaStar n ω))
    (hseThetaStar : ∀ n ω, Measurable (seThetaStar n ω))
    (hbound : ∀ᶠ n in atTop, ∀ ω ωs, |TthetaStar n ω ωs| ≤ C)
    (hse :
      TendstoInBootstrapProbabilityIndexed μ Pstar seThetaStar (fun _ => seθ)) :
    TendstoInBootstrapDistributionIndexed μ Pstar
      (fun n ω ωs (_ : Unit) =>
        |TthetaStar n ω ωs / seThetaStar n ω ωs|)
      ((gaussianReal 0 1).map (fun z : ℝ => |z|))
      (fun z : ℝ => fun _ : Unit => z) :=
  chapter10_indexed_bootstrap_studentized_abs_distribution_of_eventually_bound
    (μ := μ) (Pstar := Pstar) (Xstar := TthetaStar)
    (Ystar := seThetaStar) (c := seθ) (C := C)
    hseθ hT hPstar hTthetaStar hseThetaStar hbound hse

/-- Hansen Theorem 10.19, regression-facing trimmed bootstrap variance bridge.

For the transformed regression statistic, if the trimmed conditional mean
converges to zero and the trimmed conditional cross moment converges to the
delta-method covariance `R' Vβ R`, then the trimmed bootstrap covariance
estimator converges to `R' Vβ R`.  The concrete regression proof supplies these
moment premises from Theorems 10.11 and 10.12. -/
theorem chapter10_bootstrap_regression_trimmedVariance_tendsto
    {k q : Type*} [Fintype k] [Fintype q]
    {Pstar : ℕ → Ω → Measure Ωs}
    {ZthetaStar : ℕ → Ω → Ωs → q → ℝ}
    {τ : ℕ → ℝ} {Vβ : Matrix k k ℝ} (R : Matrix k q ℝ)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZ :
      ∀ n ω a,
        MemLp (fun ωs => trimmedBootstrapStatistic ZthetaStar τ n ω ωs a) 2
          (Pstar n ω))
    (hmean :
      TendstoInMeasure μ
        (bootstrapMeanVec Pstar (trimmedBootstrapStatistic ZthetaStar τ))
        atTop (fun _ => 0))
    (hcross :
      TendstoInMeasure μ
        (bootstrapCrossMomentMat Pstar (trimmedBootstrapStatistic ZthetaStar τ))
        atTop (fun _ => smoothFunctionVarianceFunctional R Vβ)) :
    TendstoInMeasure μ (trimmedBootstrapCovarianceMat Pstar ZthetaStar τ) atTop
      (fun _ => smoothFunctionVarianceFunctional R Vβ) :=
  chapter10_trimmedBootstrapVariance_tendsto
    (μ := μ) (Pstar := Pstar) (Zstar := ZthetaStar) (τ := τ)
    hPstar hZ hmean hcross

/-- Indexed Hansen Theorem 10.19, regression-facing trimmed bootstrap variance
bridge for sample-size-dependent bootstrap spaces. -/
theorem chapter10_indexed_bootstrap_regression_trimmedVariance_tendsto
    {k q : Type*} [Fintype k] [Fintype q]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {ZthetaStar : ∀ n, Ω → Ωboot n → q → ℝ}
    {τ : ℕ → ℝ} {Vβ : Matrix k k ℝ} (R : Matrix k q ℝ)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZ :
      ∀ n ω a,
        MemLp
          (fun ωs =>
            trimmedBootstrapStatisticIndexed ZthetaStar τ n ω ωs a) 2
          (Pstar n ω))
    (hmean :
      TendstoInMeasure μ
        (bootstrapMeanVecIndexed Pstar
          (trimmedBootstrapStatisticIndexed ZthetaStar τ))
        atTop (fun _ => 0))
    (hcross :
      TendstoInMeasure μ
        (bootstrapCrossMomentMatIndexed Pstar
          (trimmedBootstrapStatisticIndexed ZthetaStar τ))
        atTop (fun _ => smoothFunctionVarianceFunctional R Vβ)) :
    TendstoInMeasure μ
      (trimmedBootstrapCovarianceMatIndexed Pstar ZthetaStar τ)
      atTop (fun _ => smoothFunctionVarianceFunctional R Vβ) :=
  chapter10_indexed_trimmedBootstrapVariance_tendsto
    (μ := μ) (Pstar := Pstar) (Zstar := ZthetaStar) (τ := τ)
    hPstar hZ hmean hcross

/-- Hansen Theorem 10.19, regression-facing trimmed covariance consistency
from coefficient-level Gaussian bootstrap convergence and norm-fourth control.

This specializes the smooth exact-linearization trimmed covariance route to the
regression transform `Rᵀ Tβ*`, so callers do not have to separately provide the
trimmed conditional mean and cross-moment convergence premises. -/
theorem
    chapter10_bootstrap_regression_trimmedVariance_tendsto_of_linearization_normFourth
    {k q : Type*} [Fintype k] [Fintype q] [DecidableEq k] [DecidableEq q]
    {Pstar : ℕ → Ω → Measure Ωs}
    {TbetaStar : ℕ → Ω → Ωs → EuclideanSpace ℝ k}
    {τ : ℕ → ℝ} {Vβ : Matrix k k ℝ} (R : Matrix k q ℝ)
    [IsFiniteMeasure
      (multivariateGaussian (0 : EuclideanSpace ℝ q)
        (Rᵀ * Vβ * (Rᵀ)ᵀ))]
    {B : ℝ}
    (hVβ : Vβ.PosSemidef)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hτ : ∀ n, 0 ≤ τ n)
    (hT :
      TendstoInBootstrapWeakDistribution μ Pstar TbetaStar
        (multivariateGaussian (0 : EuclideanSpace ℝ k) Vβ)
        (fun z : EuclideanSpace ℝ k => z))
    (hTbetaMeas : ∀ n ω, Measurable (TbetaStar n ω))
    (hcoordMem :
      ∀ n ω a,
        MemLp
          (fun ωs =>
            (((matrixContinuousLinearMap Rᵀ (TbetaStar n ω ωs) :
                EuclideanSpace ℝ q) : q → ℝ) a))
          2 (Pstar n ω))
    (hlimMem :
      ∀ a,
        MemLp (fun z : EuclideanSpace ℝ q => (z : q → ℝ) a) 2
          (multivariateGaussian (0 : EuclideanSpace ℝ q)
            (Rᵀ * Vβ * (Rᵀ)ᵀ)))
    (hTailProb :
      TendstoInMeasure μ
        (fun n ω =>
          ((Pstar n ω)
            {ωs |
              τ n <
                ‖((matrixContinuousLinearMap Rᵀ (TbetaStar n ω ωs) :
                    EuclideanSpace ℝ q) : q → ℝ)‖}).toReal)
        atTop (fun _ => 0))
    (hB : 0 ≤ B)
    (hNormFourth :
      TendstoInMeasure μ
        (fun n ω => ∫ ωs, ‖TbetaStar n ω ωs‖ ^ 4 ∂Pstar n ω)
        atTop (fun _ => B))
    (hNormFourthInt :
      ∀ n ω, Integrable (fun ωs => ‖TbetaStar n ω ωs‖ ^ 4)
        (Pstar n ω)) :
    TendstoInMeasure μ
      (trimmedBootstrapCovarianceMat Pstar
        (fun n ω ωs =>
          ((matrixContinuousLinearMap Rᵀ (TbetaStar n ω ωs) :
            EuclideanSpace ℝ q) : q → ℝ)) τ)
      atTop (fun _ => smoothFunctionVarianceFunctional R Vβ) := by
  have htrim :
      TendstoInMeasure μ
        (trimmedBootstrapCovarianceMat Pstar
          (fun n ω ωs =>
            ((matrixContinuousLinearMap Rᵀ (TbetaStar n ω ωs) :
              EuclideanSpace ℝ q) : q → ℝ)) τ)
        atTop (fun _ => Rᵀ * Vβ * (Rᵀ)ᵀ) :=
    chapter10_smooth_trimmedBootstrapVariance_tendsto_of_linearization_normFourth
      (μ := μ) (Pstar := Pstar) (Tstar := TbetaStar)
      (thetaStar := fun n ω ωs => matrixContinuousLinearMap Rᵀ
        (TbetaStar n ω ωs))
      (V := Vβ) (G := Rᵀ) hVβ hPstar hτ hT
      (fun n ω =>
        (PiLp.continuous_ofLp 2 (fun _ : q => ℝ)).measurable.comp
          ((matrixContinuousLinearMap Rᵀ).continuous.measurable.comp
            (hTbetaMeas n ω)))
      hcoordMem hlimMem (fun _ _ _ => rfl) hTailProb hB hNormFourth
      hNormFourthInt
  refine TendstoInMeasure.congr (fun _ => EventuallyEq.rfl) ?_ htrim
  exact ae_of_all μ fun _ => by
    simp [smoothFunctionVarianceFunctional, Matrix.transpose_transpose]

/-- Indexed Hansen Theorem 10.19 regression-facing trimmed covariance route
from coefficient-level Gaussian bootstrap convergence and norm-fourth control. -/
theorem
    chapter10_indexed_bootstrap_regression_trimmedVariance_tendsto_of_linearization_normFourth
    {k q : Type*} [Fintype k] [Fintype q] [DecidableEq k] [DecidableEq q]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {TbetaStar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ k}
    {τ : ℕ → ℝ} {Vβ : Matrix k k ℝ} (R : Matrix k q ℝ)
    [IsFiniteMeasure
      (multivariateGaussian (0 : EuclideanSpace ℝ q)
        (Rᵀ * Vβ * (Rᵀ)ᵀ))]
    {B : ℝ}
    (hVβ : Vβ.PosSemidef)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hτ : ∀ n, 0 ≤ τ n)
    (hT :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar TbetaStar
        (multivariateGaussian (0 : EuclideanSpace ℝ k) Vβ)
        (fun z : EuclideanSpace ℝ k => z))
    (hTbetaMeas : ∀ n ω, Measurable (TbetaStar n ω))
    (hcoordMem :
      ∀ n ω a,
        MemLp
          (fun ωs =>
            (((matrixContinuousLinearMap Rᵀ (TbetaStar n ω ωs) :
                EuclideanSpace ℝ q) : q → ℝ) a))
          2 (Pstar n ω))
    (hlimMem :
      ∀ a,
        MemLp (fun z : EuclideanSpace ℝ q => (z : q → ℝ) a) 2
          (multivariateGaussian (0 : EuclideanSpace ℝ q)
            (Rᵀ * Vβ * (Rᵀ)ᵀ)))
    (hTailProb :
      TendstoInMeasure μ
        (fun n ω =>
          ((Pstar n ω)
            {ωs |
              τ n <
                ‖((matrixContinuousLinearMap Rᵀ (TbetaStar n ω ωs) :
                    EuclideanSpace ℝ q) : q → ℝ)‖}).toReal)
        atTop (fun _ => 0))
    (hB : 0 ≤ B)
    (hNormFourth :
      TendstoInMeasure μ
        (fun n ω => ∫ ωs, ‖TbetaStar n ω ωs‖ ^ 4 ∂Pstar n ω)
        atTop (fun _ => B))
    (hNormFourthInt :
      ∀ n ω, Integrable (fun ωs => ‖TbetaStar n ω ωs‖ ^ 4)
        (Pstar n ω)) :
    TendstoInMeasure μ
      (trimmedBootstrapCovarianceMatIndexed Pstar
        (fun n ω ωs =>
          ((matrixContinuousLinearMap Rᵀ (TbetaStar n ω ωs) :
            EuclideanSpace ℝ q) : q → ℝ)) τ)
      atTop (fun _ => smoothFunctionVarianceFunctional R Vβ) := by
  have htrim :
      TendstoInMeasure μ
        (trimmedBootstrapCovarianceMatIndexed Pstar
          (fun n ω ωs =>
            ((matrixContinuousLinearMap Rᵀ (TbetaStar n ω ωs) :
              EuclideanSpace ℝ q) : q → ℝ)) τ)
        atTop (fun _ => Rᵀ * Vβ * (Rᵀ)ᵀ) :=
    chapter10_indexed_smooth_trimmedBootstrapVariance_tendsto_of_linearization_normFourth
      (μ := μ) (Pstar := Pstar) (Tstar := TbetaStar)
      (thetaStar := fun n ω ωs => matrixContinuousLinearMap Rᵀ
        (TbetaStar n ω ωs))
      (V := Vβ) (G := Rᵀ) hVβ hPstar hτ hT
      (fun n ω =>
        (PiLp.continuous_ofLp 2 (fun _ : q => ℝ)).measurable.comp
          ((matrixContinuousLinearMap Rᵀ).continuous.measurable.comp
            (hTbetaMeas n ω)))
      hcoordMem hlimMem (fun _ _ _ => rfl) hTailProb hB hNormFourth
      hNormFourthInt
  refine TendstoInMeasure.congr (fun _ => EventuallyEq.rfl) ?_ htrim
  exact ae_of_all μ fun _ => by
    simp [smoothFunctionVarianceFunctional, Matrix.transpose_transpose]

/-- Hansen Theorem 10.19 regression-facing trimmed covariance route with the
trimming-tail probability discharged by conditional second moments and a
diverging threshold. -/
theorem
    chapter10_bootstrap_regression_trimmedVariance_tendsto_of_linearization_secondMoment
    {k q : Type*} [Fintype k] [Fintype q] [DecidableEq k] [DecidableEq q]
    {Pstar : ℕ → Ω → Measure Ωs}
    {TbetaStar : ℕ → Ω → Ωs → EuclideanSpace ℝ k}
    {τ : ℕ → ℝ} {Vβ : Matrix k k ℝ} (R : Matrix k q ℝ)
    [IsFiniteMeasure
      (multivariateGaussian (0 : EuclideanSpace ℝ q)
        (Rᵀ * Vβ * (Rᵀ)ᵀ))]
    {Bsecond Bfourth : ℝ}
    (hVβ : Vβ.PosSemidef)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hτpos : ∀ n, 0 < τ n)
    (hτinv : Tendsto (fun n => ((τ n) ^ 2)⁻¹) atTop (𝓝 0))
    (hT :
      TendstoInBootstrapWeakDistribution μ Pstar TbetaStar
        (multivariateGaussian (0 : EuclideanSpace ℝ k) Vβ)
        (fun z : EuclideanSpace ℝ k => z))
    (hTbetaMeas : ∀ n ω, Measurable (TbetaStar n ω))
    (hThetaMem :
      ∀ n ω,
        MemLp
          (fun ωs =>
            ((matrixContinuousLinearMap Rᵀ (TbetaStar n ω ωs) :
              EuclideanSpace ℝ q) : q → ℝ))
          2 (Pstar n ω))
    (hcoordMem :
      ∀ n ω a,
        MemLp
          (fun ωs =>
            (((matrixContinuousLinearMap Rᵀ (TbetaStar n ω ωs) :
                EuclideanSpace ℝ q) : q → ℝ) a))
          2 (Pstar n ω))
    (hlimMem :
      ∀ a,
        MemLp (fun z : EuclideanSpace ℝ q => (z : q → ℝ) a) 2
          (multivariateGaussian (0 : EuclideanSpace ℝ q)
            (Rᵀ * Vβ * (Rᵀ)ᵀ)))
    (hSecond :
      TendstoInMeasure μ
        (fun n ω =>
          ∫ ωs,
            ‖((matrixContinuousLinearMap Rᵀ (TbetaStar n ω ωs) :
              EuclideanSpace ℝ q) : q → ℝ)‖ ^ 2 ∂Pstar n ω)
        atTop (fun _ => Bsecond))
    (hBfourth : 0 ≤ Bfourth)
    (hNormFourth :
      TendstoInMeasure μ
        (fun n ω => ∫ ωs, ‖TbetaStar n ω ωs‖ ^ 4 ∂Pstar n ω)
        atTop (fun _ => Bfourth))
    (hNormFourthInt :
      ∀ n ω, Integrable (fun ωs => ‖TbetaStar n ω ωs‖ ^ 4)
        (Pstar n ω)) :
    TendstoInMeasure μ
      (trimmedBootstrapCovarianceMat Pstar
        (fun n ω ωs =>
          ((matrixContinuousLinearMap Rᵀ (TbetaStar n ω ωs) :
            EuclideanSpace ℝ q) : q → ℝ)) τ)
      atTop (fun _ => smoothFunctionVarianceFunctional R Vβ) :=
  chapter10_bootstrap_regression_trimmedVariance_tendsto_of_linearization_normFourth
    (μ := μ) (Pstar := Pstar) (TbetaStar := TbetaStar)
    (τ := τ) (Vβ := Vβ) R hVβ hPstar (fun n => (hτpos n).le)
    hT hTbetaMeas hcoordMem hlimMem
    (trimmedTailProb_tendsto_zero_of_integral_norm_sq
      (μ := μ) (Pstar := Pstar)
      (Zstar := fun n ω ωs =>
        ((matrixContinuousLinearMap Rᵀ (TbetaStar n ω ωs) :
          EuclideanSpace ℝ q) : q → ℝ))
      (τ := τ) hPstar hThetaMem hτpos hτinv hSecond)
    hBfourth hNormFourth hNormFourthInt

/-- Indexed version of
`chapter10_bootstrap_regression_trimmedVariance_tendsto_of_linearization_secondMoment`. -/
theorem
    chapter10_indexed_bootstrap_regression_trimmedVariance_tendsto_of_linearization_secondMoment
    {k q : Type*} [Fintype k] [Fintype q] [DecidableEq k] [DecidableEq q]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {TbetaStar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ k}
    {τ : ℕ → ℝ} {Vβ : Matrix k k ℝ} (R : Matrix k q ℝ)
    [IsFiniteMeasure
      (multivariateGaussian (0 : EuclideanSpace ℝ q)
        (Rᵀ * Vβ * (Rᵀ)ᵀ))]
    {Bsecond Bfourth : ℝ}
    (hVβ : Vβ.PosSemidef)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hτpos : ∀ n, 0 < τ n)
    (hτinv : Tendsto (fun n => ((τ n) ^ 2)⁻¹) atTop (𝓝 0))
    (hT :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar TbetaStar
        (multivariateGaussian (0 : EuclideanSpace ℝ k) Vβ)
        (fun z : EuclideanSpace ℝ k => z))
    (hTbetaMeas : ∀ n ω, Measurable (TbetaStar n ω))
    (hThetaMem :
      ∀ n ω,
        MemLp
          (fun ωs =>
            ((matrixContinuousLinearMap Rᵀ (TbetaStar n ω ωs) :
              EuclideanSpace ℝ q) : q → ℝ))
          2 (Pstar n ω))
    (hcoordMem :
      ∀ n ω a,
        MemLp
          (fun ωs =>
            (((matrixContinuousLinearMap Rᵀ (TbetaStar n ω ωs) :
                EuclideanSpace ℝ q) : q → ℝ) a))
          2 (Pstar n ω))
    (hlimMem :
      ∀ a,
        MemLp (fun z : EuclideanSpace ℝ q => (z : q → ℝ) a) 2
          (multivariateGaussian (0 : EuclideanSpace ℝ q)
            (Rᵀ * Vβ * (Rᵀ)ᵀ)))
    (hSecond :
      TendstoInMeasure μ
        (fun n ω =>
          ∫ ωs,
            ‖((matrixContinuousLinearMap Rᵀ (TbetaStar n ω ωs) :
              EuclideanSpace ℝ q) : q → ℝ)‖ ^ 2 ∂Pstar n ω)
        atTop (fun _ => Bsecond))
    (hBfourth : 0 ≤ Bfourth)
    (hNormFourth :
      TendstoInMeasure μ
        (fun n ω => ∫ ωs, ‖TbetaStar n ω ωs‖ ^ 4 ∂Pstar n ω)
        atTop (fun _ => Bfourth))
    (hNormFourthInt :
      ∀ n ω, Integrable (fun ωs => ‖TbetaStar n ω ωs‖ ^ 4)
        (Pstar n ω)) :
    TendstoInMeasure μ
      (trimmedBootstrapCovarianceMatIndexed Pstar
        (fun n ω ωs =>
          ((matrixContinuousLinearMap Rᵀ (TbetaStar n ω ωs) :
            EuclideanSpace ℝ q) : q → ℝ)) τ)
      atTop (fun _ => smoothFunctionVarianceFunctional R Vβ) :=
  chapter10_indexed_bootstrap_regression_trimmedVariance_tendsto_of_linearization_normFourth
    (μ := μ) (Pstar := Pstar) (TbetaStar := TbetaStar)
    (τ := τ) (Vβ := Vβ) R hVβ hPstar (fun n => (hτpos n).le)
    hT hTbetaMeas hcoordMem hlimMem
    (trimmedTailProbIndexed_tendsto_zero_of_integral_norm_sq
      (μ := μ) (Pstar := Pstar)
      (Zstar := fun n ω ωs =>
        ((matrixContinuousLinearMap Rᵀ (TbetaStar n ω ωs) :
          EuclideanSpace ℝ q) : q → ℝ))
      (τ := τ) hPstar hThetaMem hτpos hτinv hSecond)
    hBfourth hNormFourth hNormFourthInt

/-- Regression-facing Theorem 10.19 norm-fourth route with the Gaussian-limit
coordinate `MemLp 2` premises discharged automatically. -/
theorem
    chapter10_bootstrap_regression_trimmedVariance_normFourth_gaussianLimit
    {k q : Type*} [Fintype k] [DecidableEq k] [Fintype q]
    {Pstar : ℕ → Ω → Measure Ωs}
    {TbetaStar : ℕ → Ω → Ωs → EuclideanSpace ℝ k}
    {τ : ℕ → ℝ} {Vβ : Matrix k k ℝ} (R : Matrix k q ℝ)
    {B : ℝ}
    (hVβ : Vβ.PosSemidef)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hτ : ∀ n, 0 ≤ τ n)
    (hT :
      TendstoInBootstrapWeakDistribution μ Pstar TbetaStar
        (multivariateGaussian (0 : EuclideanSpace ℝ k) Vβ)
        (fun z : EuclideanSpace ℝ k => z))
    (hTbetaMeas : ∀ n ω, Measurable (TbetaStar n ω))
    (hcoordMem :
      ∀ n ω a,
        MemLp
          (fun ωs =>
            (((matrixContinuousLinearMap Rᵀ (TbetaStar n ω ωs) :
                EuclideanSpace ℝ q) : q → ℝ) a))
          2 (Pstar n ω))
    (hTailProb :
      TendstoInMeasure μ
        (fun n ω =>
          ((Pstar n ω)
            {ωs |
              τ n <
                ‖((matrixContinuousLinearMap Rᵀ (TbetaStar n ω ωs) :
                    EuclideanSpace ℝ q) : q → ℝ)‖}).toReal)
        atTop (fun _ => 0))
    (hB : 0 ≤ B)
    (hNormFourth :
      TendstoInMeasure μ
        (fun n ω => ∫ ωs, ‖TbetaStar n ω ωs‖ ^ 4 ∂Pstar n ω)
        atTop (fun _ => B))
    (hNormFourthInt :
      ∀ n ω, Integrable (fun ωs => ‖TbetaStar n ω ωs‖ ^ 4)
        (Pstar n ω)) :
    TendstoInMeasure μ
      (trimmedBootstrapCovarianceMat Pstar
        (fun n ω ωs =>
          ((matrixContinuousLinearMap Rᵀ (TbetaStar n ω ωs) :
            EuclideanSpace ℝ q) : q → ℝ)) τ)
      atTop (fun _ => smoothFunctionVarianceFunctional R Vβ) := by
  classical
  exact
    chapter10_bootstrap_regression_trimmedVariance_tendsto_of_linearization_normFourth
    (μ := μ) (Pstar := Pstar) (TbetaStar := TbetaStar)
    (τ := τ) (Vβ := Vβ) R hVβ hPstar hτ hT hTbetaMeas
    hcoordMem (fun a => memLp_multivariateGaussian_coord_two a) hTailProb
    hB hNormFourth hNormFourthInt

/-- Indexed regression-facing Theorem 10.19 norm-fourth route with automatic
Gaussian-limit coordinate `MemLp 2` premises. -/
theorem
    chapter10_indexed_bootstrap_regression_trimmedVariance_normFourth_gaussianLimit
    {k q : Type*} [Fintype k] [DecidableEq k] [Fintype q]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {TbetaStar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ k}
    {τ : ℕ → ℝ} {Vβ : Matrix k k ℝ} (R : Matrix k q ℝ)
    {B : ℝ}
    (hVβ : Vβ.PosSemidef)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hτ : ∀ n, 0 ≤ τ n)
    (hT :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar TbetaStar
        (multivariateGaussian (0 : EuclideanSpace ℝ k) Vβ)
        (fun z : EuclideanSpace ℝ k => z))
    (hTbetaMeas : ∀ n ω, Measurable (TbetaStar n ω))
    (hcoordMem :
      ∀ n ω a,
        MemLp
          (fun ωs =>
            (((matrixContinuousLinearMap Rᵀ (TbetaStar n ω ωs) :
                EuclideanSpace ℝ q) : q → ℝ) a))
          2 (Pstar n ω))
    (hTailProb :
      TendstoInMeasure μ
        (fun n ω =>
          ((Pstar n ω)
            {ωs |
              τ n <
                ‖((matrixContinuousLinearMap Rᵀ (TbetaStar n ω ωs) :
                    EuclideanSpace ℝ q) : q → ℝ)‖}).toReal)
        atTop (fun _ => 0))
    (hB : 0 ≤ B)
    (hNormFourth :
      TendstoInMeasure μ
        (fun n ω => ∫ ωs, ‖TbetaStar n ω ωs‖ ^ 4 ∂Pstar n ω)
        atTop (fun _ => B))
    (hNormFourthInt :
      ∀ n ω, Integrable (fun ωs => ‖TbetaStar n ω ωs‖ ^ 4)
        (Pstar n ω)) :
    TendstoInMeasure μ
      (trimmedBootstrapCovarianceMatIndexed Pstar
        (fun n ω ωs =>
          ((matrixContinuousLinearMap Rᵀ (TbetaStar n ω ωs) :
            EuclideanSpace ℝ q) : q → ℝ)) τ)
      atTop (fun _ => smoothFunctionVarianceFunctional R Vβ) := by
  classical
  exact
    chapter10_indexed_bootstrap_regression_trimmedVariance_tendsto_of_linearization_normFourth
    (μ := μ) (Pstar := Pstar) (TbetaStar := TbetaStar)
    (τ := τ) (Vβ := Vβ) R hVβ hPstar hτ hT hTbetaMeas
    hcoordMem (fun a => memLp_multivariateGaussian_coord_two a) hTailProb
    hB hNormFourth hNormFourthInt

/-- Regression-facing Theorem 10.19 second-moment/diverging-threshold route
with the Gaussian-limit coordinate `MemLp 2` premises discharged
automatically. -/
theorem
    chapter10_bootstrap_regression_trimmedVariance_secondMoment_gaussianLimit
    {k q : Type*} [Fintype k] [DecidableEq k] [Fintype q]
    {Pstar : ℕ → Ω → Measure Ωs}
    {TbetaStar : ℕ → Ω → Ωs → EuclideanSpace ℝ k}
    {τ : ℕ → ℝ} {Vβ : Matrix k k ℝ} (R : Matrix k q ℝ)
    {Bsecond Bfourth : ℝ}
    (hVβ : Vβ.PosSemidef)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hτpos : ∀ n, 0 < τ n)
    (hτinv : Tendsto (fun n => ((τ n) ^ 2)⁻¹) atTop (𝓝 0))
    (hT :
      TendstoInBootstrapWeakDistribution μ Pstar TbetaStar
        (multivariateGaussian (0 : EuclideanSpace ℝ k) Vβ)
        (fun z : EuclideanSpace ℝ k => z))
    (hTbetaMeas : ∀ n ω, Measurable (TbetaStar n ω))
    (hThetaMem :
      ∀ n ω,
        MemLp
          (fun ωs =>
            ((matrixContinuousLinearMap Rᵀ (TbetaStar n ω ωs) :
              EuclideanSpace ℝ q) : q → ℝ))
          2 (Pstar n ω))
    (hcoordMem :
      ∀ n ω a,
        MemLp
          (fun ωs =>
            (((matrixContinuousLinearMap Rᵀ (TbetaStar n ω ωs) :
                EuclideanSpace ℝ q) : q → ℝ) a))
          2 (Pstar n ω))
    (hSecond :
      TendstoInMeasure μ
        (fun n ω =>
          ∫ ωs,
            ‖((matrixContinuousLinearMap Rᵀ (TbetaStar n ω ωs) :
              EuclideanSpace ℝ q) : q → ℝ)‖ ^ 2 ∂Pstar n ω)
        atTop (fun _ => Bsecond))
    (hBfourth : 0 ≤ Bfourth)
    (hNormFourth :
      TendstoInMeasure μ
        (fun n ω => ∫ ωs, ‖TbetaStar n ω ωs‖ ^ 4 ∂Pstar n ω)
        atTop (fun _ => Bfourth))
    (hNormFourthInt :
      ∀ n ω, Integrable (fun ωs => ‖TbetaStar n ω ωs‖ ^ 4)
        (Pstar n ω)) :
    TendstoInMeasure μ
      (trimmedBootstrapCovarianceMat Pstar
        (fun n ω ωs =>
          ((matrixContinuousLinearMap Rᵀ (TbetaStar n ω ωs) :
            EuclideanSpace ℝ q) : q → ℝ)) τ)
      atTop (fun _ => smoothFunctionVarianceFunctional R Vβ) := by
  classical
  exact
    chapter10_bootstrap_regression_trimmedVariance_tendsto_of_linearization_secondMoment
    (μ := μ) (Pstar := Pstar) (TbetaStar := TbetaStar)
    (τ := τ) (Vβ := Vβ) R hVβ hPstar hτpos hτinv hT hTbetaMeas
    hThetaMem hcoordMem (fun a => memLp_multivariateGaussian_coord_two a)
    hSecond hBfourth hNormFourth hNormFourthInt

/-- Indexed regression-facing Theorem 10.19 second-moment/diverging-threshold
route with automatic Gaussian-limit coordinate `MemLp 2` premises. -/
theorem
    chapter10_indexed_bootstrap_regression_trimmedVariance_secondMoment_gaussianLimit
    {k q : Type*} [Fintype k] [DecidableEq k] [Fintype q]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {TbetaStar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ k}
    {τ : ℕ → ℝ} {Vβ : Matrix k k ℝ} (R : Matrix k q ℝ)
    {Bsecond Bfourth : ℝ}
    (hVβ : Vβ.PosSemidef)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hτpos : ∀ n, 0 < τ n)
    (hτinv : Tendsto (fun n => ((τ n) ^ 2)⁻¹) atTop (𝓝 0))
    (hT :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar TbetaStar
        (multivariateGaussian (0 : EuclideanSpace ℝ k) Vβ)
        (fun z : EuclideanSpace ℝ k => z))
    (hTbetaMeas : ∀ n ω, Measurable (TbetaStar n ω))
    (hThetaMem :
      ∀ n ω,
        MemLp
          (fun ωs =>
            ((matrixContinuousLinearMap Rᵀ (TbetaStar n ω ωs) :
              EuclideanSpace ℝ q) : q → ℝ))
          2 (Pstar n ω))
    (hcoordMem :
      ∀ n ω a,
        MemLp
          (fun ωs =>
            (((matrixContinuousLinearMap Rᵀ (TbetaStar n ω ωs) :
                EuclideanSpace ℝ q) : q → ℝ) a))
          2 (Pstar n ω))
    (hSecond :
      TendstoInMeasure μ
        (fun n ω =>
          ∫ ωs,
            ‖((matrixContinuousLinearMap Rᵀ (TbetaStar n ω ωs) :
              EuclideanSpace ℝ q) : q → ℝ)‖ ^ 2 ∂Pstar n ω)
        atTop (fun _ => Bsecond))
    (hBfourth : 0 ≤ Bfourth)
    (hNormFourth :
      TendstoInMeasure μ
        (fun n ω => ∫ ωs, ‖TbetaStar n ω ωs‖ ^ 4 ∂Pstar n ω)
        atTop (fun _ => Bfourth))
    (hNormFourthInt :
      ∀ n ω, Integrable (fun ωs => ‖TbetaStar n ω ωs‖ ^ 4)
        (Pstar n ω)) :
    TendstoInMeasure μ
      (trimmedBootstrapCovarianceMatIndexed Pstar
        (fun n ω ωs =>
          ((matrixContinuousLinearMap Rᵀ (TbetaStar n ω ωs) :
            EuclideanSpace ℝ q) : q → ℝ)) τ)
      atTop (fun _ => smoothFunctionVarianceFunctional R Vβ) := by
  classical
  exact
    chapter10_indexed_bootstrap_regression_trimmedVariance_tendsto_of_linearization_secondMoment
    (μ := μ) (Pstar := Pstar) (TbetaStar := TbetaStar)
    (τ := τ) (Vβ := Vβ) R hVβ hPstar hτpos hτinv hT hTbetaMeas
    hThetaMem hcoordMem (fun a => memLp_multivariateGaussian_coord_two a)
    hSecond hBfourth hNormFourth hNormFourthInt

set_option linter.style.longLine false

/-- Robust-feasible HC specialization of the Theorem 10.19 norm-fourth
trimmed covariance route.

This fixes `Vβ = heteroAsymCov μ X e` and discharges positive
semidefiniteness from the Chapter 7 robust feasible HC condition package.  The
coefficient-level bootstrap weak convergence and norm-fourth/trimming premises
remain explicit. -/
theorem
chapter10_bootstrap_regression_trimmedVariance_normFourth_gaussianLimit_of_robustFeasibleHCMomentConditions
    [IsProbabilityMeasure μ]
    {k q : Type*} [Fintype k] [DecidableEq k] [Fintype q]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    {Pstar : ℕ → Ω → Measure Ωs}
    {TbetaStar : ℕ → Ω → Ωs → EuclideanSpace ℝ k}
    {τ : ℕ → ℝ} (β : k → ℝ) (R : Matrix k q ℝ) {B : ℝ}
    (hm : RobustFeasibleHCMomentConditions μ X e y β)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hτ : ∀ n, 0 ≤ τ n)
    (hT :
      TendstoInBootstrapWeakDistribution μ Pstar TbetaStar
        (multivariateGaussian (0 : EuclideanSpace ℝ k)
          (heteroAsymCov μ X e))
        (fun z : EuclideanSpace ℝ k => z))
    (hTbetaMeas : ∀ n ω, Measurable (TbetaStar n ω))
    (hcoordMem :
      ∀ n ω a,
        MemLp
          (fun ωs =>
            (((matrixContinuousLinearMap Rᵀ (TbetaStar n ω ωs) :
                EuclideanSpace ℝ q) : q → ℝ) a))
          2 (Pstar n ω))
    (hTailProb :
      TendstoInMeasure μ
        (fun n ω =>
          ((Pstar n ω)
            {ωs |
              τ n <
                ‖((matrixContinuousLinearMap Rᵀ (TbetaStar n ω ωs) :
                    EuclideanSpace ℝ q) : q → ℝ)‖}).toReal)
        atTop (fun _ => 0))
    (hB : 0 ≤ B)
    (hNormFourth :
      TendstoInMeasure μ
        (fun n ω => ∫ ωs, ‖TbetaStar n ω ωs‖ ^ 4 ∂Pstar n ω)
        atTop (fun _ => B))
    (hNormFourthInt :
      ∀ n ω, Integrable (fun ωs => ‖TbetaStar n ω ωs‖ ^ 4)
        (Pstar n ω)) :
    TendstoInMeasure μ
      (trimmedBootstrapCovarianceMat Pstar
        (fun n ω ωs =>
          ((matrixContinuousLinearMap Rᵀ (TbetaStar n ω ωs) :
            EuclideanSpace ℝ q) : q → ℝ)) τ)
      atTop (fun _ =>
        smoothFunctionVarianceFunctional R (heteroAsymCov μ X e)) :=
  chapter10_bootstrap_regression_trimmedVariance_normFourth_gaussianLimit
    (μ := μ) (Pstar := Pstar) (TbetaStar := TbetaStar)
    (τ := τ) (Vβ := heteroAsymCov μ X e) R
    (heteroAsymCov_posSemidef_of_scoreCLTConditions
      (μ := μ) (X := X) (e := e) hm.toScoreCLTConditions)
    hPstar hτ hT hTbetaMeas hcoordMem hTailProb hB hNormFourth
    hNormFourthInt

/-- Indexed robust-feasible HC specialization of the Theorem 10.19
norm-fourth trimmed covariance route. -/
theorem
chapter10_indexed_bootstrap_regression_trimmedVariance_normFourth_gaussianLimit_of_robustFeasibleHCMomentConditions
    [IsProbabilityMeasure μ]
    {k q : Type*} [Fintype k] [DecidableEq k] [Fintype q]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {TbetaStar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ k}
    {τ : ℕ → ℝ} (β : k → ℝ) (R : Matrix k q ℝ) {B : ℝ}
    (hm : RobustFeasibleHCMomentConditions μ X e y β)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hτ : ∀ n, 0 ≤ τ n)
    (hT :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar TbetaStar
        (multivariateGaussian (0 : EuclideanSpace ℝ k)
          (heteroAsymCov μ X e))
        (fun z : EuclideanSpace ℝ k => z))
    (hTbetaMeas : ∀ n ω, Measurable (TbetaStar n ω))
    (hcoordMem :
      ∀ n ω a,
        MemLp
          (fun ωs =>
            (((matrixContinuousLinearMap Rᵀ (TbetaStar n ω ωs) :
                EuclideanSpace ℝ q) : q → ℝ) a))
          2 (Pstar n ω))
    (hTailProb :
      TendstoInMeasure μ
        (fun n ω =>
          ((Pstar n ω)
            {ωs |
              τ n <
                ‖((matrixContinuousLinearMap Rᵀ (TbetaStar n ω ωs) :
                    EuclideanSpace ℝ q) : q → ℝ)‖}).toReal)
        atTop (fun _ => 0))
    (hB : 0 ≤ B)
    (hNormFourth :
      TendstoInMeasure μ
        (fun n ω => ∫ ωs, ‖TbetaStar n ω ωs‖ ^ 4 ∂Pstar n ω)
        atTop (fun _ => B))
    (hNormFourthInt :
      ∀ n ω, Integrable (fun ωs => ‖TbetaStar n ω ωs‖ ^ 4)
        (Pstar n ω)) :
    TendstoInMeasure μ
      (trimmedBootstrapCovarianceMatIndexed Pstar
        (fun n ω ωs =>
          ((matrixContinuousLinearMap Rᵀ (TbetaStar n ω ωs) :
            EuclideanSpace ℝ q) : q → ℝ)) τ)
      atTop (fun _ =>
        smoothFunctionVarianceFunctional R (heteroAsymCov μ X e)) :=
  chapter10_indexed_bootstrap_regression_trimmedVariance_normFourth_gaussianLimit
    (μ := μ) (Pstar := Pstar) (TbetaStar := TbetaStar)
    (τ := τ) (Vβ := heteroAsymCov μ X e) R
    (heteroAsymCov_posSemidef_of_scoreCLTConditions
      (μ := μ) (X := X) (e := e) hm.toScoreCLTConditions)
    hPstar hτ hT hTbetaMeas hcoordMem hTailProb hB hNormFourth
    hNormFourthInt

/-- Robust-feasible HC specialization of the Theorem 10.19
second-moment/diverging-threshold trimmed covariance route.

The conditional second-moment and norm-fourth premises remain explicit; this
wrapper only supplies the heteroskedastic covariance positive-semidefinite
premise from `RobustFeasibleHCMomentConditions`. -/
theorem
chapter10_bootstrap_regression_trimmedVariance_secondMoment_gaussianLimit_of_robustFeasibleHCMomentConditions
    [IsProbabilityMeasure μ]
    {k q : Type*} [Fintype k] [DecidableEq k] [Fintype q]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    {Pstar : ℕ → Ω → Measure Ωs}
    {TbetaStar : ℕ → Ω → Ωs → EuclideanSpace ℝ k}
    {τ : ℕ → ℝ} (β : k → ℝ) (R : Matrix k q ℝ)
    {Bsecond Bfourth : ℝ}
    (hm : RobustFeasibleHCMomentConditions μ X e y β)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hτpos : ∀ n, 0 < τ n)
    (hτinv : Tendsto (fun n => ((τ n) ^ 2)⁻¹) atTop (𝓝 0))
    (hT :
      TendstoInBootstrapWeakDistribution μ Pstar TbetaStar
        (multivariateGaussian (0 : EuclideanSpace ℝ k)
          (heteroAsymCov μ X e))
        (fun z : EuclideanSpace ℝ k => z))
    (hTbetaMeas : ∀ n ω, Measurable (TbetaStar n ω))
    (hThetaMem :
      ∀ n ω,
        MemLp
          (fun ωs =>
            ((matrixContinuousLinearMap Rᵀ (TbetaStar n ω ωs) :
              EuclideanSpace ℝ q) : q → ℝ))
          2 (Pstar n ω))
    (hcoordMem :
      ∀ n ω a,
        MemLp
          (fun ωs =>
            (((matrixContinuousLinearMap Rᵀ (TbetaStar n ω ωs) :
                EuclideanSpace ℝ q) : q → ℝ) a))
          2 (Pstar n ω))
    (hSecond :
      TendstoInMeasure μ
        (fun n ω =>
          ∫ ωs,
            ‖((matrixContinuousLinearMap Rᵀ (TbetaStar n ω ωs) :
              EuclideanSpace ℝ q) : q → ℝ)‖ ^ 2 ∂Pstar n ω)
        atTop (fun _ => Bsecond))
    (hBfourth : 0 ≤ Bfourth)
    (hNormFourth :
      TendstoInMeasure μ
        (fun n ω => ∫ ωs, ‖TbetaStar n ω ωs‖ ^ 4 ∂Pstar n ω)
        atTop (fun _ => Bfourth))
    (hNormFourthInt :
      ∀ n ω, Integrable (fun ωs => ‖TbetaStar n ω ωs‖ ^ 4)
        (Pstar n ω)) :
    TendstoInMeasure μ
      (trimmedBootstrapCovarianceMat Pstar
        (fun n ω ωs =>
          ((matrixContinuousLinearMap Rᵀ (TbetaStar n ω ωs) :
            EuclideanSpace ℝ q) : q → ℝ)) τ)
      atTop (fun _ =>
        smoothFunctionVarianceFunctional R (heteroAsymCov μ X e)) :=
  chapter10_bootstrap_regression_trimmedVariance_secondMoment_gaussianLimit
    (μ := μ) (Pstar := Pstar) (TbetaStar := TbetaStar)
    (τ := τ) (Vβ := heteroAsymCov μ X e) R
    (heteroAsymCov_posSemidef_of_scoreCLTConditions
      (μ := μ) (X := X) (e := e) hm.toScoreCLTConditions)
    hPstar hτpos hτinv hT hTbetaMeas hThetaMem hcoordMem hSecond
    hBfourth hNormFourth hNormFourthInt

/-- Indexed robust-feasible HC specialization of the Theorem 10.19
second-moment/diverging-threshold trimmed covariance route. -/
theorem
chapter10_indexed_bootstrap_regression_trimmedVariance_secondMoment_gaussianLimit_of_robustFeasibleHCMomentConditions
    [IsProbabilityMeasure μ]
    {k q : Type*} [Fintype k] [DecidableEq k] [Fintype q]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {TbetaStar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ k}
    {τ : ℕ → ℝ} (β : k → ℝ) (R : Matrix k q ℝ)
    {Bsecond Bfourth : ℝ}
    (hm : RobustFeasibleHCMomentConditions μ X e y β)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hτpos : ∀ n, 0 < τ n)
    (hτinv : Tendsto (fun n => ((τ n) ^ 2)⁻¹) atTop (𝓝 0))
    (hT :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar TbetaStar
        (multivariateGaussian (0 : EuclideanSpace ℝ k)
          (heteroAsymCov μ X e))
        (fun z : EuclideanSpace ℝ k => z))
    (hTbetaMeas : ∀ n ω, Measurable (TbetaStar n ω))
    (hThetaMem :
      ∀ n ω,
        MemLp
          (fun ωs =>
            ((matrixContinuousLinearMap Rᵀ (TbetaStar n ω ωs) :
              EuclideanSpace ℝ q) : q → ℝ))
          2 (Pstar n ω))
    (hcoordMem :
      ∀ n ω a,
        MemLp
          (fun ωs =>
            (((matrixContinuousLinearMap Rᵀ (TbetaStar n ω ωs) :
                EuclideanSpace ℝ q) : q → ℝ) a))
          2 (Pstar n ω))
    (hSecond :
      TendstoInMeasure μ
        (fun n ω =>
          ∫ ωs,
            ‖((matrixContinuousLinearMap Rᵀ (TbetaStar n ω ωs) :
              EuclideanSpace ℝ q) : q → ℝ)‖ ^ 2 ∂Pstar n ω)
        atTop (fun _ => Bsecond))
    (hBfourth : 0 ≤ Bfourth)
    (hNormFourth :
      TendstoInMeasure μ
        (fun n ω => ∫ ωs, ‖TbetaStar n ω ωs‖ ^ 4 ∂Pstar n ω)
        atTop (fun _ => Bfourth))
    (hNormFourthInt :
      ∀ n ω, Integrable (fun ωs => ‖TbetaStar n ω ωs‖ ^ 4)
        (Pstar n ω)) :
    TendstoInMeasure μ
      (trimmedBootstrapCovarianceMatIndexed Pstar
        (fun n ω ωs =>
          ((matrixContinuousLinearMap Rᵀ (TbetaStar n ω ωs) :
            EuclideanSpace ℝ q) : q → ℝ)) τ)
      atTop (fun _ =>
        smoothFunctionVarianceFunctional R (heteroAsymCov μ X e)) :=
  chapter10_indexed_bootstrap_regression_trimmedVariance_secondMoment_gaussianLimit
    (μ := μ) (Pstar := Pstar) (TbetaStar := TbetaStar)
    (τ := τ) (Vβ := heteroAsymCov μ X e) R
    (heteroAsymCov_posSemidef_of_scoreCLTConditions
      (μ := μ) (X := X) (e := e) hm.toScoreCLTConditions)
    hPstar hτpos hτinv hT hTbetaMeas hThetaMem hcoordMem hSecond
    hBfourth hNormFourth hNormFourthInt

set_option linter.style.longLine true

end BootstrapRegression

end HansenEconometrics
