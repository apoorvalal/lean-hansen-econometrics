import HansenEconometrics.Chapter10Bootstrap.PercentileT
import HansenEconometrics.Chapter12InstrumentalVariables.Asymptotics
import HansenEconometrics.Chapter12InstrumentalVariables.Basic
import HansenEconometrics.Chapter12InstrumentalVariables.Functions

/-!
# Chapter 12 — bootstrap instrumental variables

This file contains the deterministic bootstrap 2SLS surface for Hansen
Theorem 12.8. The definitions mirror the finite-resample Chapter 10 regression
API, but keep Hansen's IV-specific recentering explicit:
`n^{-1/2}(Z^{*'} e^* - Z' ehat)`.

The public asymptotic surface also includes the observed-Assumption-12.2
bootstrap linearization-matrix limit and an honest coefficient-closeness
constructor that leaves only the nonlinear coefficient remainder to callers.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology MeasureTheory ProbabilityTheory Matrix
open scoped Matrix.Norms.Elementwise Function
open scoped symmDiff

namespace HansenEconometrics

open Matrix

variable {Ω : Type*} {k l : Type*}
variable [Fintype k] [Fintype l] [DecidableEq k] [DecidableEq l]

section DeterministicBootstrap

/-- Ordinary finite-resample bootstrap IV instrument matrix. -/
def twoSLSBootstrapInstrumentsFinSucc
    (Z : ℕ → Ω → l → ℝ)
    (n : ℕ) (ω : Ω) (ωs : Fin (n + 1) → Fin (n + 1)) :
    Matrix (Fin (n + 1)) l ℝ :=
  Matrix.of fun i a => Z (ωs i).val ω a

/-- Ordinary finite-resample bootstrap IV regressor matrix. -/
def twoSLSBootstrapRegressorsFinSucc
    (X : ℕ → Ω → k → ℝ)
    (n : ℕ) (ω : Ω) (ωs : Fin (n + 1) → Fin (n + 1)) :
    Matrix (Fin (n + 1)) k ℝ :=
  Matrix.of fun i a => X (ωs i).val ω a

/-- Ordinary finite-resample bootstrap IV outcome vector. -/
def twoSLSBootstrapOutcomesFinSucc
    (Y : ℕ → Ω → ℝ)
    (n : ℕ) (ω : Ω) (ωs : Fin (n + 1) → Fin (n + 1)) :
    Fin (n + 1) → ℝ :=
  fun i => Y (ωs i).val ω

/-- Hansen's bootstrap-universe true value for 2SLS. Replacing population
moments by empirical moments gives the original-sample 2SLS estimator. -/
noncomputable def twoSLSBootstrapTrueValueFinSucc
    (Z : ℕ → Ω → l → ℝ) (X : ℕ → Ω → k → ℝ) (Y : ℕ → Ω → ℝ)
    (n : ℕ) (ω : Ω) : k → ℝ :=
  twoSLSBetaStar (stackRegressors Z (n + 1) ω) (stackRegressors X (n + 1) ω)
    (stackOutcomes Y (n + 1) ω)

/-- The bootstrap-universe true value is the original-sample totalized 2SLS
estimate. This is the Lean form of Hansen's displayed empirical-moment
calculation before equation (12.43). -/
theorem twoSLSBootstrapTrueValueFinSucc_eq_twoSLSBetaStar
    (Z : ℕ → Ω → l → ℝ) (X : ℕ → Ω → k → ℝ) (Y : ℕ → Ω → ℝ)
    (n : ℕ) (ω : Ω) :
    twoSLSBootstrapTrueValueFinSucc Z X Y n ω =
      twoSLSBetaStar (stackRegressors Z (n + 1) ω) (stackRegressors X (n + 1) ω)
        (stackOutcomes Y (n + 1) ω) :=
  rfl

/-- Bootstrap structural residuals `e_i^* = Y_i^* - X_i^{*'} βhat_2sls`,
centered at the bootstrap-universe true value `βhat_2sls`. -/
noncomputable def twoSLSBootstrapResidualsFinSucc
    (Z : ℕ → Ω → l → ℝ) (X : ℕ → Ω → k → ℝ) (Y : ℕ → Ω → ℝ)
    (n : ℕ) (ω : Ω) (ωs : Fin (n + 1) → Fin (n + 1)) :
    Fin (n + 1) → ℝ :=
  twoSLSBootstrapOutcomesFinSucc Y n ω ωs -
    twoSLSBootstrapRegressorsFinSucc X n ω ωs *ᵥ
      twoSLSBootstrapTrueValueFinSucc Z X Y n ω

/-- Hansen equation (12.43), pathwise: bootstrap residuals are resampled
original structural 2SLS residuals. -/
theorem twoSLSBootstrapResidualsFinSucc_eq_resampled_residuals
    (Z : ℕ → Ω → l → ℝ) (X : ℕ → Ω → k → ℝ) (Y : ℕ → Ω → ℝ)
    (n : ℕ) (ω : Ω) (ωs : Fin (n + 1) → Fin (n + 1)) :
    twoSLSBootstrapResidualsFinSucc Z X Y n ω ωs =
      fun i =>
        twoSLSResidualStar
          (stackRegressors Z (n + 1) ω) (stackRegressors X (n + 1) ω)
          (stackOutcomes Y (n + 1) ω) (ωs i) := by
  funext i
  simp [twoSLSBootstrapResidualsFinSucc, twoSLSBootstrapOutcomesFinSucc,
    twoSLSBootstrapRegressorsFinSucc, twoSLSBootstrapTrueValueFinSucc,
    twoSLSResidualStar, stackRegressors, stackOutcomes, Matrix.mulVec,
    dotProduct]

/-- Bootstrap 2SLS estimator computed from resampled triples. -/
noncomputable def twoSLSBootstrapBetaFinSucc
    (Z : ℕ → Ω → l → ℝ) (X : ℕ → Ω → k → ℝ) (Y : ℕ → Ω → ℝ)
    (n : ℕ) (ω : Ω) (ωs : Fin (n + 1) → Fin (n + 1)) :
    k → ℝ :=
  twoSLSBetaStar (twoSLSBootstrapInstrumentsFinSucc Z n ω ωs)
    (twoSLSBootstrapRegressorsFinSucc X n ω ωs)
    (twoSLSBootstrapOutcomesFinSucc Y n ω ωs)

/-- Hansen Theorem 12.8 coefficient statistic
`sqrt(n)(βhat_2sls^* - βhat_2sls)`, with the `Fin (n+1)` indexing convention
used by the Chapter 10 bootstrap API. -/
noncomputable def twoSLSBootstrapBetaGapFinSucc
    (Z : ℕ → Ω → l → ℝ) (X : ℕ → Ω → k → ℝ) (Y : ℕ → Ω → ℝ)
    (n : ℕ) (ω : Ω) (ωs : Fin (n + 1) → Fin (n + 1)) :
    k → ℝ :=
  Real.sqrt (n + 1 : ℝ) •
    (twoSLSBootstrapBetaFinSucc Z X Y n ω ωs -
      twoSLSBootstrapTrueValueFinSucc Z X Y n ω)

/-- Euclidean-space version of `twoSLSBootstrapBetaGapFinSucc`, convenient for
Chapter 10 weak-bootstrap distribution theorems. -/
noncomputable def twoSLSBootstrapBetaStatisticFinSucc
    (Z : ℕ → Ω → l → ℝ) (X : ℕ → Ω → k → ℝ) (Y : ℕ → Ω → ℝ)
    (n : ℕ) (ω : Ω) (ωs : Fin (n + 1) → Fin (n + 1)) :
    EuclideanSpace ℝ k :=
  WithLp.toLp 2 (twoSLSBootstrapBetaGapFinSucc Z X Y n ω ωs)

/-- Bootstrap IV score `n^{-1} Z^{*'} e^*`. -/
noncomputable def twoSLSBootstrapScoreFinSucc
    (Z : ℕ → Ω → l → ℝ) (X : ℕ → Ω → k → ℝ) (Y : ℕ → Ω → ℝ)
    (n : ℕ) (ω : Ω) (ωs : Fin (n + 1) → Fin (n + 1)) :
    l → ℝ :=
  sampleCrossMoment (twoSLSBootstrapInstrumentsFinSucc Z n ω ωs)
    (twoSLSBootstrapResidualsFinSucc Z X Y n ω ωs)

/-- Original empirical IV score `n^{-1} Z' ehat`, the recentering term in
Hansen equation (12.44). -/
noncomputable def twoSLSBootstrapScoreCenterFinSucc
    (Z : ℕ → Ω → l → ℝ) (X : ℕ → Ω → k → ℝ) (Y : ℕ → Ω → ℝ)
    (n : ℕ) (ω : Ω) : l → ℝ :=
  sampleCrossMoment (stackRegressors Z (n + 1) ω)
    (twoSLSResidualStar
      (stackRegressors Z (n + 1) ω) (stackRegressors X (n + 1) ω)
      (stackOutcomes Y (n + 1) ω))

/-- The triangular residual-instrument score rows resampled by the ordinary
2SLS bootstrap.

For fixed original sample size `n+1`, the row value depends on the full
original-sample 2SLS residual vector, not only on the observation index. This
is the concrete triangular-array object to which Chapter 10 ordinary-bootstrap
mean CLT machinery must be applied for Hansen Theorem 12.8. -/
noncomputable def twoSLSBootstrapScoreRowsFinSucc
    (Z : ℕ → Ω → l → ℝ) (X : ℕ → Ω → k → ℝ) (Y : ℕ → Ω → ℝ)
    (n : ℕ) (ω : Ω) (i : Fin (n + 1)) : l → ℝ :=
  twoSLSResidualStar
    (stackRegressors Z (n + 1) ω) (stackRegressors X (n + 1) ω)
    (stackOutcomes Y (n + 1) ω) i • Z i.val ω

/-- True structural-error score rows inside the bootstrap residual-score
decomposition. -/
noncomputable def twoSLSBootstrapTrueScoreRowsFinSucc
    (Z : ℕ → Ω → l → ℝ) (e : ℕ → Ω → ℝ)
    (n : ℕ) (ω : Ω) (i : Fin (n + 1)) : l → ℝ :=
  e i.val ω • Z i.val ω

/-- Residual-substitution score rows created by replacing the true error with
the original-sample 2SLS residual.  Under the structural equation, the
bootstrap residual score equals true score minus this term. -/
noncomputable def twoSLSBootstrapResidualSubstitutionRowsFinSucc
    (Z : ℕ → Ω → l → ℝ) (X : ℕ → Ω → k → ℝ)
    (Y : ℕ → Ω → ℝ) (β : k → ℝ)
    (n : ℕ) (ω : Ω) (i : Fin (n + 1)) : l → ℝ :=
  ((X i.val ω) ⬝ᵥ
      (twoSLSBetaStar
        (stackRegressors Z (n + 1) ω) (stackRegressors X (n + 1) ω)
        (stackOutcomes Y (n + 1) ω) - β)) • Z i.val ω

/-- Hansen Theorem 12.8 residual-score row decomposition.

When `Y = Xβ + e`, each triangular bootstrap score row is the true
instrument-error score row minus the residual-substitution row caused by using
the original-sample 2SLS residual. -/
theorem twoSLSBootstrapScoreRowsFinSucc_eq_trueScoreRows_sub_residualSubstitution
    (Z : ℕ → Ω → l → ℝ) (X : ℕ → Ω → k → ℝ)
    (Y e : ℕ → Ω → ℝ) (β : k → ℝ)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (n : ℕ) (ω : Ω) :
    twoSLSBootstrapScoreRowsFinSucc Z X Y n ω =
      twoSLSBootstrapTrueScoreRowsFinSucc Z e n ω -
        twoSLSBootstrapResidualSubstitutionRowsFinSucc Z X Y β n ω := by
  have hstack := stack_linear_model X e Y β hmodel (n + 1) ω
  ext i a
  have hrowOf : ∀ v : k → ℝ,
      ((Matrix.of fun i : Fin (n + 1) => fun j : k => X i.val ω j) i) ⬝ᵥ v =
        X i.val ω ⬝ᵥ v := by
    intro v
    simp [dotProduct]
  simp [twoSLSBootstrapScoreRowsFinSucc,
    twoSLSBootstrapTrueScoreRowsFinSucc,
    twoSLSBootstrapResidualSubstitutionRowsFinSucc,
    hstack, twoSLSResidualStar_linear_model_apply,
    stackRegressors, stackErrors, smul_eq_mul]
  rw [hrowOf, hrowOf]
  ring_nf

/-- Empirical-mean version of the residual-score row decomposition. -/
theorem empiricalMean_twoSLSBootstrapScoreRowsFinSucc_eq_trueScore_sub_residualSubstitution
    (Z : ℕ → Ω → l → ℝ) (X : ℕ → Ω → k → ℝ)
    (Y e : ℕ → Ω → ℝ) (β : k → ℝ)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (n : ℕ) (ω : Ω) :
    empiricalMean (twoSLSBootstrapScoreRowsFinSucc Z X Y n ω) =
      empiricalMean (twoSLSBootstrapTrueScoreRowsFinSucc Z e n ω) -
        empiricalMean
          (twoSLSBootstrapResidualSubstitutionRowsFinSucc Z X Y β n ω) := by
  have hrows :=
    twoSLSBootstrapScoreRowsFinSucc_eq_trueScoreRows_sub_residualSubstitution
      Z X Y e β hmodel n ω
  ext a
  simp [hrows, empiricalMean, Pi.sub_apply, Finset.sum_sub_distrib]
  ring

/-- Resample-mean version of the residual-score row decomposition. -/
theorem resampleMean_twoSLSBootstrapScoreRowsFinSucc_eq_trueScore_sub_remainder
    (Z : ℕ → Ω → l → ℝ) (X : ℕ → Ω → k → ℝ)
    (Y e : ℕ → Ω → ℝ) (β : k → ℝ)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (n : ℕ) (ω : Ω) (ωs : Fin (n + 1) → Fin (n + 1)) :
    empiricalBootstrapResampleMean
        (twoSLSBootstrapScoreRowsFinSucc Z X Y n ω)
        (fun ωs t => ωs t) ωs =
      empiricalBootstrapResampleMean
          (twoSLSBootstrapTrueScoreRowsFinSucc Z e n ω)
          (fun ωs t => ωs t) ωs -
        empiricalBootstrapResampleMean
          (twoSLSBootstrapResidualSubstitutionRowsFinSucc Z X Y β n ω)
          (fun ωs t => ωs t) ωs := by
  have hrows :=
    twoSLSBootstrapScoreRowsFinSucc_eq_trueScoreRows_sub_residualSubstitution
      Z X Y e β hmodel n ω
  ext a
  simp [hrows, empiricalBootstrapResampleMean, Pi.sub_apply, Finset.sum_sub_distrib]
  ring

/-- The bootstrap score is the empirical resample mean of the original
structural residual instrument score. -/
theorem twoSLSBootstrapScoreFinSucc_eq_resampleMean
    (Z : ℕ → Ω → l → ℝ) (X : ℕ → Ω → k → ℝ) (Y : ℕ → Ω → ℝ)
    (n : ℕ) (ω : Ω) (ωs : Fin (n + 1) → Fin (n + 1)) :
    twoSLSBootstrapScoreFinSucc Z X Y n ω ωs =
      empiricalBootstrapResampleMean
        (fun i : Fin (n + 1) =>
          twoSLSResidualStar
            (stackRegressors Z (n + 1) ω) (stackRegressors X (n + 1) ω)
            (stackOutcomes Y (n + 1) ω) i • Z i.val ω)
        (fun ωs t => ωs t) ωs := by
  rw [twoSLSBootstrapScoreFinSucc, twoSLSBootstrapResidualsFinSucc_eq_resampled_residuals]
  funext a
  simp [sampleCrossMoment, empiricalBootstrapResampleMean,
    twoSLSBootstrapInstrumentsFinSucc, Matrix.mulVec, dotProduct, smul_eq_mul,
    mul_comm]

/-- Hansen equation (12.44): the bootstrap-universe IV score center is the
original empirical score `n^{-1} Z'ehat`. -/
theorem twoSLSBootstrapScoreCenterFinSucc_eq_empiricalMean
    (Z : ℕ → Ω → l → ℝ) (X : ℕ → Ω → k → ℝ) (Y : ℕ → Ω → ℝ)
    (n : ℕ) (ω : Ω) :
    twoSLSBootstrapScoreCenterFinSucc Z X Y n ω =
      empiricalMean
        (fun i : Fin (n + 1) =>
          twoSLSResidualStar
            (stackRegressors Z (n + 1) ω) (stackRegressors X (n + 1) ω)
            (stackOutcomes Y (n + 1) ω) i • Z i.val ω) := by
  have htoReal : ((n : ℝ≥0∞) + 1).toReal = (n : ℝ) + 1 := by
    rw [ENNReal.toReal_add (by simp) (by simp)]
    simp [ENNReal.toReal_natCast]
  funext a
  simp [twoSLSBootstrapScoreCenterFinSucc, sampleCrossMoment, empiricalMean,
    ENNReal.toReal_inv, htoReal, Nat.cast_add, Nat.cast_one,
    stackRegressors, Matrix.mulVec, dotProduct, smul_eq_mul, mul_comm,
    Fintype.card_fin]

/-- Recentered bootstrap IV score
`sqrt(n)(n^{-1}Z^{*'}e^* - n^{-1}Z'ehat)`, matching Hansen equation (12.45). -/
noncomputable def twoSLSBootstrapRecenteredScoreFinSucc
    (Z : ℕ → Ω → l → ℝ) (X : ℕ → Ω → k → ℝ) (Y : ℕ → Ω → ℝ)
    (n : ℕ) (ω : Ω) (ωs : Fin (n + 1) → Fin (n + 1)) :
    l → ℝ :=
  Real.sqrt (n + 1 : ℝ) •
    (twoSLSBootstrapScoreFinSucc Z X Y n ω ωs -
      twoSLSBootstrapScoreCenterFinSucc Z X Y n ω)

/-- The recentered bootstrap score is exactly the centered empirical resample
mean of residual instrument scores, scaled by `sqrt(n+1)`. -/
theorem twoSLSBootstrapRecenteredScoreFinSucc_eq_centered_resampleMean
    (Z : ℕ → Ω → l → ℝ) (X : ℕ → Ω → k → ℝ) (Y : ℕ → Ω → ℝ)
    (n : ℕ) (ω : Ω) (ωs : Fin (n + 1) → Fin (n + 1)) :
    twoSLSBootstrapRecenteredScoreFinSucc Z X Y n ω ωs =
      Real.sqrt (n + 1 : ℝ) •
        (empiricalBootstrapResampleMean
          (fun i : Fin (n + 1) =>
            twoSLSResidualStar
              (stackRegressors Z (n + 1) ω) (stackRegressors X (n + 1) ω)
              (stackOutcomes Y (n + 1) ω) i • Z i.val ω)
          (fun ωs t => ωs t) ωs -
            empiricalMean
              (fun i : Fin (n + 1) =>
                twoSLSResidualStar
                  (stackRegressors Z (n + 1) ω) (stackRegressors X (n + 1) ω)
                  (stackOutcomes Y (n + 1) ω) i • Z i.val ω)) := by
  rw [twoSLSBootstrapRecenteredScoreFinSucc,
    twoSLSBootstrapScoreFinSucc_eq_resampleMean,
    twoSLSBootstrapScoreCenterFinSucc_eq_empiricalMean]

/-- Named-row version of
`twoSLSBootstrapRecenteredScoreFinSucc_eq_centered_resampleMean`.

This is the bridge from Hansen's recentered IV score to the Chapter 10 ordinary
bootstrap sample-mean statistic, with the triangular residual-score rows made
explicit. -/
theorem twoSLSBootstrapRecenteredScoreFinSucc_eq_scoreRows_resampleMean
    (Z : ℕ → Ω → l → ℝ) (X : ℕ → Ω → k → ℝ) (Y : ℕ → Ω → ℝ)
    (n : ℕ) (ω : Ω) (ωs : Fin (n + 1) → Fin (n + 1)) :
    twoSLSBootstrapRecenteredScoreFinSucc Z X Y n ω ωs =
      Real.sqrt (n + 1 : ℝ) •
        (empiricalBootstrapResampleMean
          (twoSLSBootstrapScoreRowsFinSucc Z X Y n ω)
          (fun ωs t => ωs t) ωs -
            empiricalMean (twoSLSBootstrapScoreRowsFinSucc Z X Y n ω)) := by
  simpa [twoSLSBootstrapScoreRowsFinSucc] using
    twoSLSBootstrapRecenteredScoreFinSucc_eq_centered_resampleMean
      (Z := Z) (X := X) (Y := Y) n ω ωs

/-- Recentered bootstrap score decomposition under the structural equation.

The Hansen recentered residual score is the centered resample mean of the true
instrument-error scores minus the centered resample mean of the residual
substitution rows.  This isolates the exact perturbation that must be shown
negligible in the proof of Theorem 12.8. -/
theorem twoSLSBootstrapRecenteredScoreFinSucc_eq_trueScore_centered_sub_remainder
    (Z : ℕ → Ω → l → ℝ) (X : ℕ → Ω → k → ℝ)
    (Y e : ℕ → Ω → ℝ) (β : k → ℝ)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (n : ℕ) (ω : Ω) (ωs : Fin (n + 1) → Fin (n + 1)) :
    twoSLSBootstrapRecenteredScoreFinSucc Z X Y n ω ωs =
      Real.sqrt (n + 1 : ℝ) •
        ((empiricalBootstrapResampleMean
            (twoSLSBootstrapTrueScoreRowsFinSucc Z e n ω)
            (fun ωs t => ωs t) ωs -
          empiricalMean (twoSLSBootstrapTrueScoreRowsFinSucc Z e n ω)) -
        (empiricalBootstrapResampleMean
            (twoSLSBootstrapResidualSubstitutionRowsFinSucc Z X Y β n ω)
            (fun ωs t => ωs t) ωs -
          empiricalMean
            (twoSLSBootstrapResidualSubstitutionRowsFinSucc Z X Y β n ω))) := by
  rw [twoSLSBootstrapRecenteredScoreFinSucc_eq_scoreRows_resampleMean]
  rw [resampleMean_twoSLSBootstrapScoreRowsFinSucc_eq_trueScore_sub_remainder
    Z X Y e β hmodel]
  rw [empiricalMean_twoSLSBootstrapScoreRowsFinSucc_eq_trueScore_sub_residualSubstitution
    Z X Y e β hmodel]
  ext a
  simp [Pi.sub_apply]
  ring_nf
  simp

/-- Recentered bootstrap score built from the true structural score rows
`Z_i e_i`, before residual substitution. -/
noncomputable def twoSLSBootstrapTrueRecenteredScoreFinSucc
    (Z : ℕ → Ω → l → ℝ) (e : ℕ → Ω → ℝ)
    (n : ℕ) (ω : Ω) (ωs : Fin (n + 1) → Fin (n + 1)) :
    l → ℝ :=
  Real.sqrt (n + 1 : ℝ) •
    (empiricalBootstrapResampleMean
      (twoSLSBootstrapTrueScoreRowsFinSucc Z e n ω)
      (fun ωs t => ωs t) ωs -
        empiricalMean (twoSLSBootstrapTrueScoreRowsFinSucc Z e n ω))

/-- Recentered residual-substitution score term in Hansen Theorem 12.8. -/
noncomputable def twoSLSBootstrapResidualSubstitutionRecenteredScoreFinSucc
    (Z : ℕ → Ω → l → ℝ) (X : ℕ → Ω → k → ℝ)
    (Y : ℕ → Ω → ℝ) (β : k → ℝ)
    (n : ℕ) (ω : Ω) (ωs : Fin (n + 1) → Fin (n + 1)) :
    l → ℝ :=
  Real.sqrt (n + 1 : ℝ) •
    (empiricalBootstrapResampleMean
      (twoSLSBootstrapResidualSubstitutionRowsFinSucc Z X Y β n ω)
      (fun ωs t => ωs t) ωs -
        empiricalMean (twoSLSBootstrapResidualSubstitutionRowsFinSucc Z X Y β n ω))

/-- Named residual-substitution decomposition of Hansen's recentered bootstrap
score. -/
theorem twoSLSBootstrapRecenteredScoreFinSucc_eq_true_sub_residualSubstitution
    (Z : ℕ → Ω → l → ℝ) (X : ℕ → Ω → k → ℝ)
    (Y e : ℕ → Ω → ℝ) (β : k → ℝ)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (n : ℕ) (ω : Ω) (ωs : Fin (n + 1) → Fin (n + 1)) :
    twoSLSBootstrapRecenteredScoreFinSucc Z X Y n ω ωs =
      twoSLSBootstrapTrueRecenteredScoreFinSucc Z e n ω ωs -
        twoSLSBootstrapResidualSubstitutionRecenteredScoreFinSucc
          Z X Y β n ω ωs := by
  rw [twoSLSBootstrapRecenteredScoreFinSucc_eq_trueScore_centered_sub_remainder
    Z X Y e β hmodel]
  ext a
  simp [twoSLSBootstrapTrueRecenteredScoreFinSucc,
    twoSLSBootstrapResidualSubstitutionRecenteredScoreFinSucc,
    Pi.sub_apply, smul_eq_mul]
  ring

/-- Euclidean-space version of Hansen's recentered bootstrap IV score. -/
noncomputable def twoSLSBootstrapRecenteredScoreStatisticFinSucc
    (Z : ℕ → Ω → l → ℝ) (X : ℕ → Ω → k → ℝ) (Y : ℕ → Ω → ℝ)
    (n : ℕ) (ω : Ω) (ωs : Fin (n + 1) → Fin (n + 1)) :
    EuclideanSpace ℝ l :=
  WithLp.toLp 2 (twoSLSBootstrapRecenteredScoreFinSucc Z X Y n ω ωs)

/-- Euclidean-space version of the true-score centered resample mean. -/
noncomputable def twoSLSBootstrapTrueRecenteredScoreStatisticFinSucc
    (Z : ℕ → Ω → l → ℝ) (e : ℕ → Ω → ℝ)
    (n : ℕ) (ω : Ω) (ωs : Fin (n + 1) → Fin (n + 1)) :
    EuclideanSpace ℝ l :=
  WithLp.toLp 2 (twoSLSBootstrapTrueRecenteredScoreFinSucc Z e n ω ωs)

/-- Euclidean-space version of the residual-substitution centered resample
mean. -/
noncomputable def twoSLSBootstrapResidualSubstitutionRecenteredScoreStatisticFinSucc
    (Z : ℕ → Ω → l → ℝ) (X : ℕ → Ω → k → ℝ)
    (Y : ℕ → Ω → ℝ) (β : k → ℝ)
    (n : ℕ) (ω : Ω) (ωs : Fin (n + 1) → Fin (n + 1)) :
    EuclideanSpace ℝ l :=
  WithLp.toLp 2
    (twoSLSBootstrapResidualSubstitutionRecenteredScoreFinSucc Z X Y β n ω ωs)

/-- Euclidean residual-substitution decomposition of Hansen's recentered
bootstrap IV score. -/
theorem twoSLSBootstrapRecenteredScoreStatisticFinSucc_eq_true_sub_residualSubstitution
    (Z : ℕ → Ω → l → ℝ) (X : ℕ → Ω → k → ℝ)
    (Y e : ℕ → Ω → ℝ) (β : k → ℝ)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (n : ℕ) (ω : Ω) (ωs : Fin (n + 1) → Fin (n + 1)) :
    twoSLSBootstrapRecenteredScoreStatisticFinSucc Z X Y n ω ωs =
      twoSLSBootstrapTrueRecenteredScoreStatisticFinSucc Z e n ω ωs -
        twoSLSBootstrapResidualSubstitutionRecenteredScoreStatisticFinSucc
          Z X Y β n ω ωs := by
  apply WithLp.ofLp_injective (p := (2 : ℝ≥0∞))
  simpa [twoSLSBootstrapRecenteredScoreStatisticFinSucc,
    twoSLSBootstrapTrueRecenteredScoreStatisticFinSucc,
    twoSLSBootstrapResidualSubstitutionRecenteredScoreStatisticFinSucc] using
    twoSLSBootstrapRecenteredScoreFinSucc_eq_true_sub_residualSubstitution
      Z X Y e β hmodel n ω ωs

/-- Bootstrap-sample 2SLS linearization matrix. -/
noncomputable def twoSLSBootstrapLinearizationMatrixFinSucc
    (Z : ℕ → Ω → l → ℝ) (X : ℕ → Ω → k → ℝ)
    (n : ℕ) (ω : Ω) (ωs : Fin (n + 1) → Fin (n + 1)) :
    Matrix k l ℝ :=
  twoSLSLinearizationMatrix (twoSLSBootstrapInstrumentsFinSucc Z n ω ωs)
    (twoSLSBootstrapRegressorsFinSucc X n ω ωs)

/-- Linearized bootstrap 2SLS statistic, the first term in Hansen equations
(12.46)--(12.47) after recentering the bootstrap score. -/
noncomputable def twoSLSBootstrapLinearizedStatisticFinSucc
    (Z : ℕ → Ω → l → ℝ) (X : ℕ → Ω → k → ℝ) (Y : ℕ → Ω → ℝ)
    (n : ℕ) (ω : Ω) (ωs : Fin (n + 1) → Fin (n + 1)) :
    EuclideanSpace ℝ k :=
  WithLp.toLp 2
    (twoSLSBootstrapLinearizationMatrixFinSucc Z X n ω ωs *ᵥ
      twoSLSBootstrapRecenteredScoreFinSucc Z X Y n ω ωs)

/-- Coordinate-vector face of the linearized bootstrap 2SLS statistic. -/
noncomputable def twoSLSBootstrapLinearizedGapFinSucc
    (Z : ℕ → Ω → l → ℝ) (X : ℕ → Ω → k → ℝ) (Y : ℕ → Ω → ℝ)
    (n : ℕ) (ω : Ω) (ωs : Fin (n + 1) → Fin (n + 1)) :
    k → ℝ :=
  (twoSLSBootstrapLinearizedStatisticFinSucc Z X Y n ω ωs : k → ℝ)

/-- Population-linearized bootstrap 2SLS statistic.  This is the exact
Chapter 10 Delta-method target before replacing the population linearization
matrix by the bootstrap sample one. -/
noncomputable def twoSLSBootstrapPopulationLinearizedStatisticFinSucc
    (QXZ : Matrix k l ℝ) (QZZ : Matrix l l ℝ) (QZX : Matrix l k ℝ)
    (Z : ℕ → Ω → l → ℝ) (X : ℕ → Ω → k → ℝ) (Y : ℕ → Ω → ℝ)
    (n : ℕ) (ω : Ω) (ωs : Fin (n + 1) → Fin (n + 1)) :
    EuclideanSpace ℝ k :=
  matrixContinuousLinearMap
    (twoSLSPopulationLinearizationMatrix QXZ QZZ QZX)
    (twoSLSBootstrapRecenteredScoreStatisticFinSucc Z X Y n ω ωs)

/-- Coordinate-vector face of the population-linearized bootstrap 2SLS
statistic. -/
noncomputable def twoSLSBootstrapPopulationLinearizedGapFinSucc
    (QXZ : Matrix k l ℝ) (QZZ : Matrix l l ℝ) (QZX : Matrix l k ℝ)
    (Z : ℕ → Ω → l → ℝ) (X : ℕ → Ω → k → ℝ) (Y : ℕ → Ω → ℝ)
    (n : ℕ) (ω : Ω) (ωs : Fin (n + 1) → Fin (n + 1)) :
    k → ℝ :=
  (twoSLSBootstrapPopulationLinearizedStatisticFinSucc
    QXZ QZZ QZX Z X Y n ω ωs : k → ℝ)

/-- Ordinary finite-resample nonparametric-bootstrap law on resampling maps,
`uniformOn Set.univ`, used by Hansen Theorem 12.8. -/
noncomputable def twoSLSBootstrapUniformPstarFinSucc
    (n : ℕ) (_ω : Ω) : Measure (Fin (n + 1) → Fin (n + 1)) :=
  ProbabilityTheory.uniformOn
    (Set.univ : Set (Fin (n + 1) → Fin (n + 1)))

/-- The ordinary finite-resample bootstrap law is a probability measure. -/
theorem twoSLSBootstrapUniformPstarFinSucc_isProbabilityMeasure
    (n : ℕ) (ω : Ω) :
    IsProbabilityMeasure (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω) n ω) := by
  change IsProbabilityMeasure
    (ProbabilityTheory.uniformOn
      (Set.univ : Set (Fin (n + 1) → Fin (n + 1))))
  infer_instance

section BootstrapLinearizationConvergence

variable [MeasurableSpace Ω] {μ : Measure Ω}

private noncomputable def twoSLSBootstrapCombinedMomentRows
    (Z : ℕ → Ω → l → ℝ) (X : ℕ → Ω → k → ℝ) :
    ℕ → Ω → EuclideanSpace ℝ ((l ⊕ k) × (l ⊕ k)) :=
  fun i ω => WithLp.toLp 2 (fun p =>
    twoSLSCombinedRegressors Z X i ω p.1 *
      twoSLSCombinedRegressors Z X i ω p.2)

private noncomputable def twoSLSBootstrapCombinedMomentMatrix
    (v : EuclideanSpace ℝ ((l ⊕ k) × (l ⊕ k))) :
    Matrix (l ⊕ k) (l ⊕ k) ℝ :=
  fun i j => v (i, j)

omit [DecidableEq k] [DecidableEq l] in
private theorem
    twoSLSBootstrapCombinedSampleGramFinSucc_tendstoInBootstrapProbability_uniform
    [IsProbabilityMeasure μ]
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {e Y : ℕ → Ω → ℝ} {β : k → ℝ}
    (h : TwoSLSAssumption12_2ObservedIidTextbookFourthConditions
      μ Z X e Y β) :
    TendstoInBootstrapProbabilityIndexed μ
      (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
      (fun n ω ωs =>
        sampleGram
          (Matrix.fromCols
            (fun i : Fin (n + 1) => Z (ωs i).val ω)
            (fun i : Fin (n + 1) => X (ωs i).val ω)))
      (fun _ => popGram μ (twoSLSCombinedRegressors Z X)) := by
  classical
  let hiid := h.toTextbookSecondConditions.toJointIidConditions.toIidConditions
  let hGram := hiid.toGramConditions
  have hrow_mem : MemLp (twoSLSBootstrapCombinedMomentRows Z X 0) 1 μ := by
    rw [memLp_piLp_iff]
    intro p
    exact memLp_one_iff_integrable.mpr
      (by
        simpa [twoSLSBootstrapCombinedMomentRows, Matrix.vecMulVec_apply] using
          Integrable.eval (Integrable.eval hGram.combined_gram.int_outer p.1) p.2)
  have houter_meas : Measurable
      (fun x : l ⊕ k → ℝ =>
        WithLp.toLp 2 (fun p : (l ⊕ k) × (l ⊕ k) => x p.1 * x p.2)) := by
    fun_prop
  have hrow_indep : iIndepFun (twoSLSBootstrapCombinedMomentRows Z X) μ := by
    simpa [twoSLSBootstrapCombinedMomentRows, Function.comp_def] using
      hiid.combined_iIndep.comp
        (fun _ (x : l ⊕ k → ℝ) =>
          WithLp.toLp 2 (fun p : (l ⊕ k) × (l ⊕ k) => x p.1 * x p.2))
        (fun _ => houter_meas)
  have hrow_ident : ∀ i,
      IdentDistrib (twoSLSBootstrapCombinedMomentRows Z X i)
        (twoSLSBootstrapCombinedMomentRows Z X 0) μ μ := by
    intro i
    have hi := hiid.combined_identDistrib i
    simpa [twoSLSBootstrapCombinedMomentRows, Function.comp_def] using
      hi.comp houter_meas
  have hrows :
      TendstoInBootstrapProbabilityIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs =>
          empiricalBootstrapResampleMean
            (fun i : Fin (n + 1) =>
              twoSLSBootstrapCombinedMomentRows Z X i.val ω)
            (fun ωs t => ωs t) ωs)
        (fun _ => ∫ ω, twoSLSBootstrapCombinedMomentRows Z X 0 ω ∂μ) := by
    simpa [twoSLSBootstrapUniformPstarFinSucc] using
      (chapter10_indexed_bootstrap_wlln_level_finSucc_resampleMean_of_iid_integrable
        (μ := μ) (Y := twoSLSBootstrapCombinedMomentRows Z X)
        hrow_mem hrow_indep hrow_ident)
  have hmatrix :
      TendstoInBootstrapProbabilityIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs =>
          twoSLSBootstrapCombinedMomentMatrix
            (empiricalBootstrapResampleMean
              (fun i : Fin (n + 1) =>
                twoSLSBootstrapCombinedMomentRows Z X i.val ω)
              (fun ωs t => ωs t) ωs))
        (fun _ => popGram μ (twoSLSCombinedRegressors Z X)) := by
    have hmatrix_cont : Continuous
        (twoSLSBootstrapCombinedMomentMatrix (k := k) (l := l)) := by
      exact continuous_matrix fun i j => by
        simpa [twoSLSBootstrapCombinedMomentMatrix] using
          (PiLp.continuous_apply
            (p := 2) (β := fun _ : (l ⊕ k) × (l ⊕ k) => ℝ) (i, j))
    have hmapped := hrows.continuousAt_const_comp
      (fun n ω =>
        twoSLSBootstrapUniformPstarFinSucc_isProbabilityMeasure (Ω := Ω) n ω)
      hmatrix_cont.continuousAt
    have hmatrix_integral :
        twoSLSBootstrapCombinedMomentMatrix
            (∫ ω, twoSLSBootstrapCombinedMomentRows Z X 0 ω ∂μ) =
          popGram μ (twoSLSCombinedRegressors Z X) := by
      ext i j
      rw [show twoSLSBootstrapCombinedMomentMatrix
          (∫ ω, twoSLSBootstrapCombinedMomentRows Z X 0 ω ∂μ) i j =
          (∫ ω, twoSLSBootstrapCombinedMomentRows Z X 0 ω ∂μ) (i, j) by rfl]
      rw [eval_integral_piLp
        (fun p => memLp_one_iff_integrable.mp hrow_mem |>.eval_piLp p)]
      rw [popGram]
      exact (integral_apply_apply hGram.combined_gram.int_outer i j).symm
    exact hmapped.congr (fun _ _ _ => rfl) (fun _ => hmatrix_integral)
  refine hmatrix.congr ?_ (fun _ => rfl)
  intro n ω ωs
  ext i j
  simp [twoSLSBootstrapCombinedMomentMatrix, twoSLSBootstrapCombinedMomentRows,
    empiricalBootstrapResampleMean, sampleGram, Matrix.fromCols,
    twoSLSCombinedRegressors, Matrix.mul_apply, Matrix.transpose_apply]

set_option linter.style.longLine false in
set_option maxHeartbeats 1200000 in
-- The nested rectangular matrix inverses make continuous-map elaboration expensive.
/-- Under observed textbook Assumption 12.2, the ordinary-bootstrap 2SLS
linearization matrix converges in bootstrap probability to its population
counterpart. The moment step is the indexed Chapter 10 bootstrap WLLN; the two
matrix inverses are then handled by the 2SLS continuous-mapping pattern at the
nonsingular population moments. -/
theorem
    twoSLSBootstrapLinearizationMatrixFinSucc_tendstoInBootstrapProbability_uniform_of_observed_textbook_fourth
    [IsProbabilityMeasure μ]
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {e Y : ℕ → Ω → ℝ} {β : k → ℝ}
    (h : TwoSLSAssumption12_2ObservedIidTextbookFourthConditions
      μ Z X e Y β) :
    TendstoInBootstrapProbabilityIndexed μ
      (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
      (fun n ω ωs => twoSLSBootstrapLinearizationMatrixFinSucc Z X n ω ωs)
      (fun _ =>
        twoSLSPopulationLinearizationMatrix
          (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
          (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
          (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))) := by
  let hiid := h.toTextbookSecondConditions.toJointIidConditions.toIidConditions
  let hGram := hiid.toGramConditions
  have hmatrix' :=
    twoSLSBootstrapCombinedSampleGramFinSucc_tendstoInBootstrapProbability_uniform
      (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y) (β := β) h
  let Q : Matrix (l ⊕ k) (l ⊕ k) ℝ :=
    popGram μ (twoSLSCombinedRegressors Z X)
  let QXZ : Matrix k l ℝ := twoSLSCombinedQXZ Q
  let QZZ : Matrix l l ℝ := twoSLSCombinedQZZ Q
  let QZX : Matrix l k ℝ := twoSLSCombinedQZX Q
  have hPstar : ∀ n ω,
      IsProbabilityMeasure (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω) n ω) :=
    fun n ω =>
      twoSLSBootstrapUniformPstarFinSucc_isProbabilityMeasure (Ω := Ω) n ω
  have hQZZ_unit : IsUnit QZZ.det := by
    dsimp [QZZ, Q]
    exact (Matrix.isUnit_iff_isUnit_det _).mp h.qzz_posDef.isUnit
  have hbread_unit : IsUnit (twoSLSBread QXZ QZZ QZX).det := by
    dsimp [QXZ, QZZ, QZX, Q]
    exact isUnit_twoSLSBread_det_of_qzz_posDef_rank
      (twoSLSCombinedQXZ_eq_transpose_QZX_of_popGram_wlln
        (μ := μ) (Z := Z) (X := X) hGram.combined_gram)
      h.qzz_posDef h.qzx_rank
  let linFun : Matrix (l ⊕ k) (l ⊕ k) ℝ → Matrix k l ℝ := fun M =>
    (twoSLSBread (M.submatrix Sum.inr Sum.inl)
      (M.submatrix Sum.inl Sum.inl) (M.submatrix Sum.inl Sum.inr))⁻¹ *
        M.submatrix Sum.inr Sum.inl * (M.submatrix Sum.inl Sum.inl)⁻¹
  have hA : ContinuousAt
      (fun M : Matrix (l ⊕ k) (l ⊕ k) ℝ => M.submatrix Sum.inr Sum.inl) Q :=
    (continuous_id.matrix_submatrix Sum.inr Sum.inl).continuousAt
  have hB : ContinuousAt
      (fun M : Matrix (l ⊕ k) (l ⊕ k) ℝ => M.submatrix Sum.inl Sum.inl) Q :=
    (continuous_id.matrix_submatrix Sum.inl Sum.inl).continuousAt
  have hC : ContinuousAt
      (fun M : Matrix (l ⊕ k) (l ⊕ k) ℝ => M.submatrix Sum.inl Sum.inr) Q :=
    (continuous_id.matrix_submatrix Sum.inl Sum.inr).continuousAt
  have hBInv : ContinuousAt
      (fun M : Matrix (l ⊕ k) (l ⊕ k) ℝ =>
        (M.submatrix Sum.inl Sum.inl)⁻¹) Q := by
    have hinv : ContinuousAt Inv.inv QZZ := by
      refine continuousAt_matrix_inv _ ?_
      rw [Ring.inverse_eq_inv']
      exact continuousAt_inv₀ hQZZ_unit.ne_zero
    simpa [QZZ] using hinv.comp hB
  have hABInv : ContinuousAt
      (fun M : Matrix (l ⊕ k) (l ⊕ k) ℝ =>
        M.submatrix Sum.inr Sum.inl * (M.submatrix Sum.inl Sum.inl)⁻¹) Q :=
    (Continuous.matrix_mul continuous_fst continuous_snd).continuousAt.comp
      (hA.prodMk hBInv)
  have hBread : ContinuousAt
      (fun M : Matrix (l ⊕ k) (l ⊕ k) ℝ =>
        twoSLSBread (M.submatrix Sum.inr Sum.inl)
          (M.submatrix Sum.inl Sum.inl) (M.submatrix Sum.inl Sum.inr)) Q := by
    simpa [twoSLSBread] using
      (Continuous.matrix_mul continuous_fst continuous_snd).continuousAt.comp
        (hABInv.prodMk hC)
  have hBreadInv : ContinuousAt
      (fun M : Matrix (l ⊕ k) (l ⊕ k) ℝ =>
        (twoSLSBread (M.submatrix Sum.inr Sum.inl)
          (M.submatrix Sum.inl Sum.inl) (M.submatrix Sum.inl Sum.inr))⁻¹) Q := by
    have hbread_unit' : IsUnit
        (twoSLSBread (Q.submatrix Sum.inr Sum.inl)
          (Q.submatrix Sum.inl Sum.inl) (Q.submatrix Sum.inl Sum.inr)).det := by
      simpa [QXZ, QZZ, QZX, Q, twoSLSCombinedQXZ, twoSLSCombinedQZZ,
        twoSLSCombinedQZX] using hbread_unit
    have hinv : ContinuousAt (fun M : Matrix k k ℝ => M⁻¹)
        (twoSLSBread (Q.submatrix Sum.inr Sum.inl)
          (Q.submatrix Sum.inl Sum.inl) (Q.submatrix Sum.inl Sum.inr)) := by
      refine continuousAt_matrix_inv _ ?_
      rw [Ring.inverse_eq_inv']
      exact continuousAt_inv₀ hbread_unit'.ne_zero
    exact ContinuousAt.comp
      (f := fun M : Matrix (l ⊕ k) (l ⊕ k) ℝ =>
        twoSLSBread (M.submatrix Sum.inr Sum.inl)
          (M.submatrix Sum.inl Sum.inl) (M.submatrix Sum.inl Sum.inr))
      hinv hBread
  have hLeft : ContinuousAt
      (fun M : Matrix (l ⊕ k) (l ⊕ k) ℝ =>
        (twoSLSBread (M.submatrix Sum.inr Sum.inl)
          (M.submatrix Sum.inl Sum.inl) (M.submatrix Sum.inl Sum.inr))⁻¹ *
            M.submatrix Sum.inr Sum.inl) Q :=
    (Continuous.matrix_mul continuous_fst continuous_snd).continuousAt.comp
      (hBreadInv.prodMk hA)
  have hlin_cont : ContinuousAt linFun Q := by
    exact (Continuous.matrix_mul continuous_fst continuous_snd).continuousAt.comp
      (hLeft.prodMk hBInv)
  have hlin := hmatrix'.continuousAt_const_comp hPstar hlin_cont
  refine hlin.congr ?_ ?_
  · intro n ω ωs
    have hZ : (fun i : Fin (n + 1) => Z (ωs i).val ω) =
        twoSLSBootstrapInstrumentsFinSucc Z n ω ωs := by
      ext i a
      rfl
    have hX : (fun i : Fin (n + 1) => X (ωs i).val ω) =
        twoSLSBootstrapRegressorsFinSucc X n ω ωs := by
      ext i a
      rfl
    simp only [linFun, sampleGram_fromCols_right_left,
      sampleGram_fromCols_left_left, sampleGram_fromCols_left_right,
      twoSLSBootstrapLinearizationMatrixFinSucc, twoSLSLinearizationMatrix]
    rw [hZ, hX]
  · intro ω
    simp [linFun, twoSLSCombinedQXZ,
      twoSLSCombinedQZZ, twoSLSCombinedQZX,
      twoSLSPopulationLinearizationMatrix]

end BootstrapLinearizationConvergence

/-- Scalar one-row restriction numerator
`sqrt(n)(R βhat_2sls^* - R βhat_2sls)` for Hansen's bootstrap t-ratio in
Theorem 12.8. -/
noncomputable def twoSLSBootstrapLinearRestrictionStatisticFinSucc
    (R : Matrix Unit k ℝ)
    (Z : ℕ → Ω → l → ℝ) (X : ℕ → Ω → k → ℝ) (Y : ℕ → Ω → ℝ)
    (n : ℕ) (ω : Ω) (ωs : Fin (n + 1) → Fin (n + 1)) : ℝ :=
  linearRestrictionEstimate R (twoSLSBootstrapBetaGapFinSucc Z X Y n ω ωs)

/-- Bootstrap standard error for a one-row 2SLS restriction, supplied through a
bootstrap covariance estimator and evaluated with the Chapter 7 restriction
standard-error functional. -/
noncomputable def twoSLSBootstrapLinearRestrictionStdErrorFinSucc
    (R : Matrix Unit k ℝ)
    (Vstar : ∀ n, Ω → (Fin (n + 1) → Fin (n + 1)) → Matrix k k ℝ)
    (n : ℕ) (ω : Ω) (ωs : Fin (n + 1) → Fin (n + 1)) : ℝ :=
  linearRestrictionStdError R (Vstar n ω ωs)

/-- Robust bootstrap 2SLS covariance estimator computed on the ordinary
resampled triples. This is the bootstrap analogue of Hansen's robust 2SLS
plug-in covariance estimator from Theorem 12.3. -/
noncomputable def twoSLSBootstrapVHatStarFinSucc
    (Z : ℕ → Ω → l → ℝ) (X : ℕ → Ω → k → ℝ) (Y : ℕ → Ω → ℝ)
    (n : ℕ) (ω : Ω) (ωs : Fin (n + 1) → Fin (n + 1)) : Matrix k k ℝ :=
  twoSLSVHatStar (twoSLSBootstrapInstrumentsFinSucc Z n ω ωs)
    (twoSLSBootstrapRegressorsFinSucc X n ω ωs)
    (twoSLSBootstrapOutcomesFinSucc Y n ω ωs)

/-- Robust bootstrap standard error for a one-row 2SLS restriction, using the
resampled robust 2SLS covariance estimator. -/
noncomputable def twoSLSBootstrapRobustLinearRestrictionStdErrorFinSucc
    (R : Matrix Unit k ℝ)
    (Z : ℕ → Ω → l → ℝ) (X : ℕ → Ω → k → ℝ) (Y : ℕ → Ω → ℝ)
    (n : ℕ) (ω : Ω) (ωs : Fin (n + 1) → Fin (n + 1)) : ℝ :=
  linearRestrictionStdError R (twoSLSBootstrapVHatStarFinSucc Z X Y n ω ωs)

/-- The concrete robust bootstrap standard error is the generic standard-error
functional applied to the concrete robust bootstrap covariance estimator. -/
theorem twoSLSBootstrapRobustLinearRestrictionStdErrorFinSucc_eq_generic
    (R : Matrix Unit k ℝ)
    (Z : ℕ → Ω → l → ℝ) (X : ℕ → Ω → k → ℝ) (Y : ℕ → Ω → ℝ)
    (n : ℕ) (ω : Ω) (ωs : Fin (n + 1) → Fin (n + 1)) :
    twoSLSBootstrapRobustLinearRestrictionStdErrorFinSucc R Z X Y n ω ωs =
      twoSLSBootstrapLinearRestrictionStdErrorFinSucc R
        (fun n ω ωs => twoSLSBootstrapVHatStarFinSucc Z X Y n ω ωs)
        n ω ωs :=
  rfl

/-- Hansen Theorem 12.8 bootstrap t-ratio
`T^* = sqrt(n)(R βhat_2sls^* - R βhat_2sls) / se^*`. -/
noncomputable def twoSLSBootstrapLinearTStatFinSucc
    (R : Matrix Unit k ℝ)
    (Z : ℕ → Ω → l → ℝ) (X : ℕ → Ω → k → ℝ) (Y : ℕ → Ω → ℝ)
    (Vstar : ∀ n, Ω → (Fin (n + 1) → Fin (n + 1)) → Matrix k k ℝ)
    (n : ℕ) (ω : Ω) (ωs : Fin (n + 1) → Fin (n + 1)) : ℝ :=
  twoSLSBootstrapLinearRestrictionStatisticFinSucc R Z X Y n ω ωs /
    twoSLSBootstrapLinearRestrictionStdErrorFinSucc R Vstar n ω ωs

/-- Hansen Theorem 12.8 robust bootstrap t-ratio with the standard error
computed from the resampled robust 2SLS covariance estimator. -/
noncomputable def twoSLSBootstrapRobustLinearTStatFinSucc
    (R : Matrix Unit k ℝ)
    (Z : ℕ → Ω → l → ℝ) (X : ℕ → Ω → k → ℝ) (Y : ℕ → Ω → ℝ)
    (n : ℕ) (ω : Ω) (ωs : Fin (n + 1) → Fin (n + 1)) : ℝ :=
  twoSLSBootstrapLinearTStatFinSucc R Z X Y
    (fun n ω ωs => twoSLSBootstrapVHatStarFinSucc Z X Y n ω ωs)
    n ω ωs

/-- Finite-resample measurability of Hansen's bootstrap one-row restriction
numerator. -/
theorem twoSLSBootstrapLinearRestrictionStatisticFinSucc_measurable
    (R : Matrix Unit k ℝ)
    (Z : ℕ → Ω → l → ℝ) (X : ℕ → Ω → k → ℝ) (Y : ℕ → Ω → ℝ)
    (n : ℕ) (ω : Ω) :
    Measurable
      (fun ωs =>
        twoSLSBootstrapLinearRestrictionStatisticFinSucc R Z X Y n ω ωs) := by
  fun_prop

/-- Finite-resample measurability of Hansen's robust bootstrap one-row
standard error. -/
theorem twoSLSBootstrapRobustLinearRestrictionStdErrorFinSucc_measurable
    (R : Matrix Unit k ℝ)
    (Z : ℕ → Ω → l → ℝ) (X : ℕ → Ω → k → ℝ) (Y : ℕ → Ω → ℝ)
    (n : ℕ) (ω : Ω) :
    Measurable
      (fun ωs =>
        twoSLSBootstrapRobustLinearRestrictionStdErrorFinSucc
          R Z X Y n ω ωs) := by
  fun_prop

/-- Original-sample one-row 2SLS restriction estimate in the `Fin (n+1)`
indexing convention used by the bootstrap API. -/
noncomputable def twoSLSLinearRestrictionEstimateFinSucc
    (R : Matrix Unit k ℝ)
    (Z : ℕ → Ω → l → ℝ) (X : ℕ → Ω → k → ℝ) (Y : ℕ → Ω → ℝ)
    (n : ℕ) (ω : Ω) : ℝ :=
  linearRestrictionEstimate R
    (twoSLSBetaStar
      (stackRegressors Z (n + 1) ω) (stackRegressors X (n + 1) ω)
      (stackOutcomes Y (n + 1) ω))

/-- Original-sample robust 2SLS standard-error scale for
`sqrt(n+1)(R βhat - R β)`. -/
noncomputable def twoSLSRobustLinearRestrictionStdErrorFinSucc
    (R : Matrix Unit k ℝ)
    (Z : ℕ → Ω → l → ℝ) (X : ℕ → Ω → k → ℝ) (Y : ℕ → Ω → ℝ)
    (n : ℕ) (ω : Ω) : ℝ :=
  linearRestrictionStdError R
    (twoSLSVHatStar
      (stackRegressors Z (n + 1) ω) (stackRegressors X (n + 1) ω)
      (stackOutcomes Y (n + 1) ω))

/-- Original-sample robust 2SLS standard error for the unscaled scalar
restriction estimate. -/
noncomputable def twoSLSRobustLinearRestrictionEstimatorStdErrorFinSucc
    (R : Matrix Unit k ℝ)
    (Z : ℕ → Ω → l → ℝ) (X : ℕ → Ω → k → ℝ) (Y : ℕ → Ω → ℝ)
    (n : ℕ) (ω : Ω) : ℝ :=
  twoSLSRobustLinearRestrictionStdErrorFinSucc R Z X Y n ω /
    Real.sqrt (n + 1 : ℝ)

/-- Original-sample robust 2SLS t-ratio for a one-row linear restriction. -/
noncomputable def twoSLSRobustLinearTStatFinSucc
    (R : Matrix Unit k ℝ)
    (Z : ℕ → Ω → l → ℝ) (X : ℕ → Ω → k → ℝ) (Y : ℕ → Ω → ℝ)
    (β : k → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  scalarFunctionTStat
    (twoSLSLinearRestrictionEstimateFinSucc R Z X Y n ω)
    (linearRestrictionEstimate R β)
    (twoSLSRobustLinearRestrictionStdErrorFinSucc R Z X Y n ω)
    (Real.sqrt (n + 1 : ℝ))

end DeterministicBootstrap

/-- Finite-resample a.e. measurability of Hansen's robust bootstrap t-ratio
under the ordinary finite bootstrap law. -/
theorem twoSLSBootstrapRobustLinearTStatFinSucc_aemeasurable
    (R : Matrix Unit k ℝ)
    (Z : ℕ → Ω → l → ℝ) (X : ℕ → Ω → k → ℝ) (Y : ℕ → Ω → ℝ)
    (n : ℕ) (ω : Ω) :
    AEMeasurable
      (fun ωs => twoSLSBootstrapRobustLinearTStatFinSucc R Z X Y n ω ωs)
      (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω) n ω) := by
  simpa [twoSLSBootstrapRobustLinearTStatFinSucc,
    twoSLSBootstrapLinearTStatFinSucc] using
    ((twoSLSBootstrapLinearRestrictionStatisticFinSucc_measurable
      (R := R) (Z := Z) (X := X) (Y := Y) n ω).div
      (twoSLSBootstrapRobustLinearRestrictionStdErrorFinSucc_measurable
        (R := R) (Z := Z) (X := X) (Y := Y) n ω)).aemeasurable

/-- Percentile-`t` confidence-interval event generated from the robust ordinary
2SLS bootstrap t-ratio in Hansen Theorem 12.8. -/
noncomputable def twoSLSBootstrapRobustPercentileTCIEventFinSucc
    (R : Matrix Unit k ℝ)
    (Z : ℕ → Ω → l → ℝ) (X : ℕ → Ω → k → ℝ) (Y : ℕ → Ω → ℝ)
    (β : k → ℝ) (α : ℝ) (n : ℕ) (ω : Ω) : Prop :=
  percentileTCIEvent
    (linearRestrictionEstimate R β)
    (twoSLSLinearRestrictionEstimateFinSucc R Z X Y n ω)
    (twoSLSRobustLinearRestrictionEstimatorStdErrorFinSucc R Z X Y n ω)
    (bootstrapScalarLowerQuantileIndexed
      (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
      (fun n ω ωs => twoSLSBootstrapRobustLinearTStatFinSucc R Z X Y n ω ωs)
      (α / 2) n ω)
    (bootstrapScalarLowerQuantileIndexed
      (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
      (fun n ω ωs => twoSLSBootstrapRobustLinearTStatFinSucc R Z X Y n ω ωs)
      (1 - α / 2) n ω)

/-- Non-studentized percentile confidence-interval event generated from the
ordinary 2SLS bootstrap one-row numerator in Hansen Theorem 12.8.

The bootstrap lower quantiles are quantiles of
`sqrt(n+1)(R βhat_2sls^* - R βhat_2sls)`, so the interval endpoints add the
quantiles to the original-sample restriction estimate after dividing by
`sqrt(n+1)`. -/
noncomputable def twoSLSBootstrapLinearRestrictionPercentileCIEventFinSucc
    (R : Matrix Unit k ℝ)
    (Z : ℕ → Ω → l → ℝ) (X : ℕ → Ω → k → ℝ) (Y : ℕ → Ω → ℝ)
    (β : k → ℝ) (α : ℝ) (n : ℕ) (ω : Ω) : Prop :=
  percentileCIEvent
    (linearRestrictionEstimate R β)
    (twoSLSLinearRestrictionEstimateFinSucc R Z X Y n ω +
      bootstrapScalarLowerQuantileIndexed
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs =>
          twoSLSBootstrapLinearRestrictionStatisticFinSucc R Z X Y n ω ωs)
        (α / 2) n ω / Real.sqrt ((n + 1 : ℕ) : ℝ))
    (twoSLSLinearRestrictionEstimateFinSucc R Z X Y n ω +
      bootstrapScalarLowerQuantileIndexed
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs =>
          twoSLSBootstrapLinearRestrictionStatisticFinSucc R Z X Y n ω ωs)
        (1 - α / 2) n ω / Real.sqrt ((n + 1 : ℕ) : ℝ))

section DistributionInterfaces

variable {Ωs Ωlim Ωstar : Type*}
variable [MeasurableSpace Ω] [MeasurableSpace Ωlim] [MeasurableSpace Ωstar]
variable {μ : Measure Ω} {ν : Measure Ωlim}
variable {Pstar : ∀ n, Ω → Measure (Fin (n + 1) → Fin (n + 1))}

private theorem scalarLaw_unit_coordinateLE_frontier_null_of_hasLaw
    {νstar : Measure Ωstar} {η : Measure ℝ} [NoAtoms η]
    {Zlim : Ωstar → ℝ} (hZlaw : HasLaw Zlim η νstar)
    (x : Unit → ℝ) :
    (νstar.map (fun ωstar => fun _ : Unit => Zlim ωstar))
      (frontier {z : Unit → ℝ | coordinateLE z x}) = 0 := by
  have hZ :
      AEMeasurable (fun ωstar => fun _ : Unit => Zlim ωstar) νstar := by
    refine aemeasurable_pi_lambda _ ?_
    intro _
    exact hZlaw.aemeasurable
  refine map_measure_frontier_coordinateLE_eq_zero_of_coord_singletons
    (ν := νstar) (Z := fun ωstar => fun _ : Unit => Zlim ωstar)
    hZ x ?_
  intro i
  change νstar {ωstar | Zlim ωstar = x i} = 0
  have hpre :
      {ωstar : Ωstar | Zlim ωstar = x i} =
        Zlim ⁻¹' ({x i} : Set ℝ) := by
    ext ωstar
    simp
  rw [hpre, ← Measure.map_apply_of_aemeasurable hZlaw.aemeasurable
    (measurableSet_singleton (x i)), hZlaw.map_eq]
  exact measure_singleton (x i)

set_option linter.style.longLine false in
private theorem scalarBootstrapWeakDistribution_to_unitDistribution_of_hasLaw
    {νstar : Measure Ωstar} [IsProbabilityMeasure νstar]
    {η : Measure ℝ} [NoAtoms η]
    {Tstar : ∀ n, Ω → (Fin (n + 1) → Fin (n + 1)) → ℝ}
    {Zlim : Ωstar → ℝ}
    (hweak : TendstoInBootstrapWeakDistributionIndexed μ Pstar Tstar νstar Zlim)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hTstar : ∀ n ω, Measurable (Tstar n ω))
    (hZlaw : HasLaw Zlim η νstar) :
    TendstoInBootstrapDistributionIndexed μ Pstar
      (fun n ω ωs (_ : Unit) => Tstar n ω ωs)
      νstar (fun ωstar (_ : Unit) => Zlim ωstar) := by
  have hmap_cont : Continuous (fun z : ℝ => fun _ : Unit => z) := by
    refine continuous_pi ?_
    intro _
    exact continuous_id
  have hweakUnit :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar
        (fun n ω ωs => fun _ : Unit => Tstar n ω ωs)
        νstar (fun ωstar => fun _ : Unit => Zlim ωstar) :=
    chapter10_indexed_bootstrap_continuous_mapping_distribution
      (μ := μ) (Pstar := Pstar) (Zstar := Tstar)
      (ν := νstar) (Z := Zlim) (g := fun z : ℝ => fun _ : Unit => z)
      hweak hmap_cont
  have hPfinite : ∀ n ω, IsFiniteMeasure (Pstar n ω) := by
    intro n ω
    letI : IsProbabilityMeasure (Pstar n ω) := hPstar n ω
    infer_instance
  have hZstar :
      ∀ n ω,
        Measurable (fun ωs => fun _ : Unit => Tstar n ω ωs) := by
    intro n ω
    refine measurable_pi_lambda _ ?_
    intro _
    exact hTstar n ω
  have hZlim :
      AEMeasurable (fun ωstar => fun _ : Unit => Zlim ωstar) νstar := by
    refine aemeasurable_pi_lambda _ ?_
    intro _
    exact hZlaw.aemeasurable
  exact
    TendstoInBootstrapDistributionIndexed.of_weakDistribution_null_frontiers
      (μ := μ) (Pstar := Pstar)
      (Zstar := fun n ω ωs (_ : Unit) => Tstar n ω ωs)
      (ν := νstar) (Z := fun ωstar (_ : Unit) => Zlim ωstar)
      hweakUnit hPfinite hZstar hZlim
      (fun x _hx =>
        scalarLaw_unit_coordinateLE_frontier_null_of_hasLaw
          (νstar := νstar) (η := η) hZlaw x)

/-- Theorem-facing bridge for the remaining numerator CLT in Hansen Theorem
12.8.

It rewrites the recentered IV bootstrap score into the Chapter-10 ordinary
bootstrap centered-resample-mean form for the concrete triangular residual-score
rows `twoSLSBootstrapScoreRowsFinSucc`. The unresolved probabilistic input is
therefore exactly the weak bootstrap CLT for those rows, not a final 2SLS or
t-statistic conclusion. -/
theorem
    twoSLSBootstrapRecenteredScoreFinSucc_tendstoInBootstrapWeakDistribution_of_scoreRows_resampleMean
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {Zlim : Ωlim → l → ℝ}
    (hscoreRows :
      TendstoInBootstrapWeakDistributionIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs =>
          Real.sqrt (n + 1 : ℝ) •
            (empiricalBootstrapResampleMean
              (twoSLSBootstrapScoreRowsFinSucc Z X Y n ω)
              (fun (ωs : Fin (n + 1) → Fin (n + 1)) (t : Fin (n + 1)) => ωs t) ωs -
                empiricalMean (twoSLSBootstrapScoreRowsFinSucc Z X Y n ω)))
        ν Zlim) :
    TendstoInBootstrapWeakDistributionIndexed μ
      (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
      (fun n ω ωs => twoSLSBootstrapRecenteredScoreFinSucc Z X Y n ω ωs)
      ν Zlim := by
  intro f
  simpa [bootstrapBoundedContinuousIntegralIndexed,
    twoSLSBootstrapRecenteredScoreFinSucc_eq_scoreRows_resampleMean] using
    hscoreRows f

omit [DecidableEq k] in
/-- True-score ordinary-bootstrap CLT for Hansen Theorem 12.8 from primitive
Assumption 12.2.

This is the exact point where the Chapter 10 ordinary-bootstrap mean CLT is
reused. It applies that machinery to the fixed iid score rows `Z_i e_i`,
before the triangular residual-substitution perturbation is introduced. -/
theorem
    twoSLSBootstrapTrueRecenteredScoreStatisticFinSucc_tendstoInBootstrapWeakDistribution_uniform_of_assumption12_2
    [IsProbabilityMeasure μ]
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e : ℕ → Ω → ℝ}
    (h : TwoSLSAssumption12_2IidFourthConditions μ Z X e) :
    TendstoInBootstrapWeakDistributionIndexed μ
      (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
      (fun n ω ωs =>
        twoSLSBootstrapTrueRecenteredScoreStatisticFinSucc Z e n ω ωs)
      (multivariateGaussian (0 : EuclideanSpace ℝ l) (scoreCovMat μ Z e))
      (fun z : EuclideanSpace ℝ l => z) := by
  let hs : ScoreCLTConditions μ Z e := h.toGramConditions.score_clt
  have hvec :
      TendstoInBootstrapWeakDistributionIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs a =>
          Real.sqrt (n + 1 : ℝ) *
            (empiricalBootstrapResampleMean
                (fun i : Fin (n + 1) => e i.val ω • Z i.val ω)
                (fun ωs t => ωs t) ωs a -
              empiricalMean
                (fun i : Fin (n + 1) => e i.val ω • Z i.val ω) a))
        (multivariateGaussian (0 : EuclideanSpace ℝ l) (scoreCovMat μ Z e))
        (fun z : EuclideanSpace ℝ l => (z : l → ℝ)) := by
    simpa [twoSLSBootstrapUniformPstarFinSucc] using
      (chapter10_indexed_bootstrap_weak_clt_gaussian_finSucc_resampleMean_of_iIndep_covMat_tail_posDef
        (μ := μ) (Y := fun i ω => e i ω • Z i ω)
        (fun a => scoreCoordinate_memLp_two (μ := μ) (X := Z) (e := e) hs a)
        hs.iIndep_cross hs.ident_cross h.omega_posDef)
  have htoLp :
      TendstoInBootstrapWeakDistributionIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs =>
          WithLp.toLp 2
            (fun a =>
              Real.sqrt (n + 1 : ℝ) *
                (empiricalBootstrapResampleMean
                    (fun i : Fin (n + 1) => e i.val ω • Z i.val ω)
                    (fun ωs t => ωs t) ωs a -
                  empiricalMean
                    (fun i : Fin (n + 1) => e i.val ω • Z i.val ω) a)))
        (multivariateGaussian (0 : EuclideanSpace ℝ l) (scoreCovMat μ Z e))
        (fun z : EuclideanSpace ℝ l =>
          WithLp.toLp 2 ((z : EuclideanSpace ℝ l) : l → ℝ)) :=
    chapter10_indexed_bootstrap_continuous_mapping_distribution
      (μ := μ) (Pstar := twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
      (Zstar := fun n ω ωs a =>
        Real.sqrt (n + 1 : ℝ) *
          (empiricalBootstrapResampleMean
              (fun i : Fin (n + 1) => e i.val ω • Z i.val ω)
              (fun ωs t => ωs t) ωs a -
            empiricalMean
              (fun i : Fin (n + 1) => e i.val ω • Z i.val ω) a))
      (ν := multivariateGaussian (0 : EuclideanSpace ℝ l) (scoreCovMat μ Z e))
      (Z := fun z : EuclideanSpace ℝ l => (z : l → ℝ))
      (g := (WithLp.toLp 2 : (l → ℝ) → EuclideanSpace ℝ l))
      hvec (PiLp.continuous_toLp 2 (fun _ : l => ℝ))
  simpa [twoSLSBootstrapTrueRecenteredScoreStatisticFinSucc,
    twoSLSBootstrapTrueRecenteredScoreFinSucc,
    twoSLSBootstrapTrueScoreRowsFinSucc, smul_eq_mul] using htoLp

/-- Named residual-score transfer inputs for Hansen Theorem 12.8.

The `residual_substitution_closeness` field is the triangular-row input: the
actual residual-score centered resample mean is close in bootstrap probability
to the true-score centered resample mean. The deterministic decomposition above
identifies this closeness with negligibility of the residual-substitution
centered resample mean under the structural equation. -/
structure TwoSLSBootstrapResidualScoreCLTInputs
    (μ : Measure Ω)
    (Z : ℕ → Ω → l → ℝ) (X : ℕ → Ω → k → ℝ)
    (Y e : ℕ → Ω → ℝ) : Prop where
  true_meas : ∀ n ω,
    Measurable
      (fun ωs =>
        twoSLSBootstrapTrueRecenteredScoreStatisticFinSucc Z e n ω ωs)
  actual_meas : ∀ n ω,
    Measurable
      (fun ωs =>
        twoSLSBootstrapRecenteredScoreStatisticFinSucc Z X Y n ω ωs)
  compact_tail : ∀ η : ℝ, 0 < η →
    ∃ K : Set (EuclideanSpace ℝ l), IsCompact K ∧
      TendstoInMeasure μ
        (fun n ω =>
          (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω) n ω).real
            {ωs |
              twoSLSBootstrapTrueRecenteredScoreStatisticFinSucc
                Z e n ω ωs ∉ K})
        atTop (fun _ => 0) ∧
      TendstoInMeasure μ
        (fun n ω =>
          (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω) n ω).real
            {ωs |
              twoSLSBootstrapRecenteredScoreStatisticFinSucc
                Z X Y n ω ωs ∉ K})
        atTop (fun _ => 0)
  residual_substitution_closeness : ∀ δ : ℝ, 0 < δ →
    TendstoInMeasure μ
      (fun n ω =>
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω) n ω).real
          {ωs |
            δ ≤
              dist (twoSLSBootstrapRecenteredScoreStatisticFinSucc
                  Z X Y n ω ωs)
                (twoSLSBootstrapTrueRecenteredScoreStatisticFinSucc
                  Z e n ω ωs)})
      atTop (fun _ => 0)

/-- Concrete residual-substitution inputs for Hansen Theorem 12.8.

This removes the automatic measurability fields from
`TwoSLSBootstrapResidualScoreCLTInputs` and states the stochastic gap using the
actual residual-substitution statistic isolated by the deterministic
decomposition above. -/
structure TwoSLSBootstrapResidualSubstitutionInputs
    (μ : Measure Ω)
    (Z : ℕ → Ω → l → ℝ) (X : ℕ → Ω → k → ℝ)
    (Y e : ℕ → Ω → ℝ) (β : k → ℝ) : Prop where
  compact_tail : ∀ η : ℝ, 0 < η →
    ∃ K : Set (EuclideanSpace ℝ l), IsCompact K ∧
      TendstoInMeasure μ
        (fun n ω =>
          (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω) n ω).real
            {ωs |
              twoSLSBootstrapTrueRecenteredScoreStatisticFinSucc
                Z e n ω ωs ∉ K})
        atTop (fun _ => 0) ∧
      TendstoInMeasure μ
        (fun n ω =>
          (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω) n ω).real
            {ωs |
              twoSLSBootstrapRecenteredScoreStatisticFinSucc
                Z X Y n ω ωs ∉ K})
        atTop (fun _ => 0)
  residual_substitution_negligible : ∀ δ : ℝ, 0 < δ →
    TendstoInMeasure μ
      (fun n ω =>
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω) n ω).real
          {ωs |
            δ ≤
              ‖twoSLSBootstrapResidualSubstitutionRecenteredScoreStatisticFinSucc
                Z X Y β n ω ωs‖})
      atTop (fun _ => 0)

/-- Narrow residual-substitution stochastic input for Hansen Theorem 12.8.

This package isolates the only residual-substitution field in
`TwoSLSBootstrapResidualSubstitutionInputs`.  Assumption 12.2 and the
deterministic structural-equation decomposition supply the true-score CLT and
the score/residual-substitution identity, but the current development still
needs compact-tail control for the true and feasible centered bootstrap score
statistics.  Use
`TwoSLSBootstrapResidualSubstitutionNegligibilityInputs.toResidualSubstitutionInputs`
when that compact-tail field is available separately. -/
structure TwoSLSBootstrapResidualSubstitutionNegligibilityInputs
    (μ : Measure Ω)
    (Z : ℕ → Ω → l → ℝ) (X : ℕ → Ω → k → ℝ)
    (Y : ℕ → Ω → ℝ) (β : k → ℝ) : Prop where
  residual_substitution_negligible : ∀ δ : ℝ, 0 < δ →
    TendstoInMeasure μ
      (fun n ω =>
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω) n ω).real
          {ωs |
            δ ≤
              ‖twoSLSBootstrapResidualSubstitutionRecenteredScoreStatisticFinSucc
                Z X Y β n ω ωs‖})
      atTop (fun _ => 0)

namespace TwoSLSBootstrapResidualSubstitutionNegligibilityInputs

omit [MeasurableSpace Ω] in
private theorem residualSubstitution_secondMoment_le_quadraticRemainder
    (Z : ℕ → Ω → l → ℝ) (X : ℕ → Ω → k → ℝ)
    (Y : ℕ → Ω → ℝ) (β : k → ℝ)
    (n : ℕ) (ω : Ω) :
    (∫ ωs : Fin (n + 1) → Fin (n + 1),
      ‖twoSLSBootstrapResidualSubstitutionRecenteredScoreStatisticFinSucc
        Z X Y β n ω ωs‖ ^ 2
      ∂(twoSLSBootstrapUniformPstarFinSucc (Ω := Ω) n ω)) ≤
      Matrix.trace
        (twoSLSOmegaQuadraticRemainder
          (stackRegressors Z (n + 1) ω)
          (stackRegressors X (n + 1) ω)
          (twoSLSBetaStar
            (stackRegressors Z (n + 1) ω)
            (stackRegressors X (n + 1) ω)
            (stackOutcomes Y (n + 1) ω) - β)) := by
  classical
  let d : k → ℝ :=
    twoSLSBetaStar
      (stackRegressors Z (n + 1) ω)
      (stackRegressors X (n + 1) ω)
      (stackOutcomes Y (n + 1) ω) - β
  let rows : Fin (n + 1) → l → ℝ := fun i =>
    ((X i.val ω) ⬝ᵥ d) • Z i.val ω
  let rowsE : Fin (n + 1) → EuclideanSpace ℝ l := fun i =>
    WithLp.toLp 2 (rows i)
  have hstat :
      (fun ωs : Fin (n + 1) → Fin (n + 1) =>
        twoSLSBootstrapResidualSubstitutionRecenteredScoreStatisticFinSucc
          Z X Y β n ω ωs) =
        (fun ωs => Real.sqrt (n + 1 : ℝ) •
          (empiricalBootstrapResampleMean rowsE (fun ωs t => ωs t) ωs -
            empiricalMean rowsE)) := by
    funext ωs
    apply WithLp.ofLp_injective (p := (2 : ℝ≥0∞))
    simp [twoSLSBootstrapResidualSubstitutionRecenteredScoreStatisticFinSucc,
      twoSLSBootstrapResidualSubstitutionRecenteredScoreFinSucc,
      twoSLSBootstrapResidualSubstitutionRowsFinSucc, rowsE, rows, d,
      empiricalBootstrapResampleMean, empiricalMean]
  simp_rw [congrFun hstat]
  rw [twoSLSBootstrapUniformPstarFinSucc]
  calc
    (∫ ωs : Fin (n + 1) → Fin (n + 1),
        ‖Real.sqrt (n + 1 : ℝ) •
          (empiricalBootstrapResampleMean rowsE (fun ωs t => ωs t) ωs -
            empiricalMean rowsE)‖ ^ 2
        ∂(ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))))) =
        Matrix.trace
          (covMat
            (ProbabilityTheory.uniformOn (Set.univ : Set (Fin (n + 1))) :
              Measure (Fin (n + 1)))
            (fun i a => rowsE i a)) := by
      simpa [Fintype.card_fin, Nat.cast_add, Nat.cast_one] using
        (integral_norm_sq_normalized_empiricalBootstrapResampleMean_uniformOn_fun_eq_trace_covMat
          (κ := Fin (n + 1)) (ι := Fin (n + 1)) (Y := rowsE))
    _ ≤ ((Fintype.card (Fin (n + 1)) : ℝ≥0∞)⁻¹).toReal •
          ∑ i : Fin (n + 1), ∑ a : l, (rowsE i a) ^ 2 :=
      trace_covMat_uniformOn_univ_le_card_inv_smul_sum_sq
        (Y := fun i a => rowsE i a)
    _ = Matrix.trace
        (twoSLSOmegaQuadraticRemainder
          (stackRegressors Z (n + 1) ω)
          (stackRegressors X (n + 1) ω) d) := by
      have htoReal : ((n : ℝ≥0∞) + 1).toReal = (n : ℝ) + 1 := by
        rw [ENNReal.toReal_add (by simp) (by simp)]
        simp [ENNReal.toReal_natCast]
      simp [twoSLSOmegaQuadraticRemainder, Matrix.trace, rowsE, rows,
        stackRegressors, Matrix.smul_apply, Matrix.sum_apply,
        Matrix.vecMulVec_apply, Fintype.card_fin, smul_eq_mul,
        Finset.mul_sum, htoReal]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro i _
      have hrow :
          (Matrix.of fun i : Fin (n + 1) => fun j : k => X i.val ω j) i =
            X i.val ω := rfl
      rw [hrow]
      ring
    _ = _ := rfl

/-- The conditional second moment of Hansen's centered residual-substitution
score is `o_p(1)` under Assumption 12.2 and its scalar fourth-moment WLLNs.

The conditional covariance trace is bounded by the existing Chapter 12
quadratic residual remainder, so no bootstrap-consistency conclusion is
assumed. -/
theorem residualSubstitution_secondMoment_tendstoInMeasure_zero
    [IsProbabilityMeasure μ]
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {e Y : ℕ → Ω → ℝ} {β : k → ℝ}
    (h : TwoSLSAssumption12_2IidFourthConditions μ Z X e)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hw : TwoSLSCovarianceWeightWLLNConditions μ Z X e) :
    TendstoInMeasure μ
      (fun n ω =>
        ∫ ωs : Fin (n + 1) → Fin (n + 1),
          ‖twoSLSBootstrapResidualSubstitutionRecenteredScoreStatisticFinSucc
            Z X Y β n ω ωs‖ ^ 2
          ∂(twoSLSBootstrapUniformPstarFinSucc (Ω := Ω) n ω))
      atTop (fun _ => 0) := by
  classical
  have hquad :=
    TwoSLSCovarianceRemainderConditions.omegaQuadratic_tendstoInMeasure_zero_of_bounded_weights
      (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y)
      h.toGramConditions.toSampleMomentConvergenceConditions β hmodel
      (TwoSLSCovarianceRemainderBoundedWeightConditions.of_assumption12_2_iid_weight_wlln
        (μ := μ) (Z := Z) (X := X) (e := e) h hw)
  have hquadSucc : TendstoInMeasure μ
      (fun n ω =>
        twoSLSOmegaQuadraticRemainder
          (stackRegressors Z (n + 1) ω)
          (stackRegressors X (n + 1) ω)
          (twoSLSBetaStar
            (stackRegressors Z (n + 1) ω)
            (stackRegressors X (n + 1) ω)
            (stackOutcomes Y (n + 1) ω) - β))
      atTop (fun _ => 0) := by
    rw [tendstoInMeasure_iff_dist] at hquad ⊢
    intro ε hε
    simpa [stackRegressors, stackOutcomes] using
      (hquad ε hε).comp (tendsto_add_atTop_nat 1)
  have htrace : TendstoInMeasure μ
      (fun n ω => Matrix.trace
        (twoSLSOmegaQuadraticRemainder
          (stackRegressors Z (n + 1) ω)
          (stackRegressors X (n + 1) ω)
          (twoSLSBetaStar
            (stackRegressors Z (n + 1) ω)
            (stackRegressors X (n + 1) ω)
            (stackOutcomes Y (n + 1) ω) - β)))
      atTop (fun _ => 0) := by
    have hdiag : ∀ a ∈ (Finset.univ : Finset l), TendstoInMeasure μ
        (fun n ω =>
          twoSLSOmegaQuadraticRemainder
            (stackRegressors Z (n + 1) ω)
            (stackRegressors X (n + 1) ω)
            (twoSLSBetaStar
              (stackRegressors Z (n + 1) ω)
              (stackRegressors X (n + 1) ω)
              (stackOutcomes Y (n + 1) ω) - β) a a)
        atTop (fun _ => 0) := by
      intro a _
      exact TendstoInMeasure.pi_apply
        (TendstoInMeasure.pi_apply hquadSucc a) a
    simpa [Matrix.trace] using
      tendstoInMeasure_finset_sum_zero_real (μ := μ)
        (s := (Finset.univ : Finset l)) hdiag
  refine tendstoInMeasure_zero_of_nonneg_le (μ := μ) ?_ ?_ htrace
  · intro n ω
    exact integral_nonneg fun _ => sq_nonneg _
  · exact residualSubstitution_secondMoment_le_quadraticRemainder Z X Y β

omit [MeasurableSpace Ω] in
private theorem residualSubstitution_tail_le_secondMoment
    (Z : ℕ → Ω → l → ℝ) (X : ℕ → Ω → k → ℝ)
    (Y : ℕ → Ω → ℝ) (β : k → ℝ)
    {δ : ℝ} (hδ : 0 < δ) (n : ℕ) (ω : Ω) :
    (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω) n ω).real
        {ωs | δ ≤
          ‖twoSLSBootstrapResidualSubstitutionRecenteredScoreStatisticFinSucc
            Z X Y β n ω ωs‖} ≤
      (∫ ωs : Fin (n + 1) → Fin (n + 1),
        ‖twoSLSBootstrapResidualSubstitutionRecenteredScoreStatisticFinSucc
          Z X Y β n ω ωs‖ ^ 2
        ∂(twoSLSBootstrapUniformPstarFinSucc (Ω := Ω) n ω)) / δ ^ 2 := by
  let Pconst : ℕ → Ω → Measure (Fin (n + 1) → Fin (n + 1)) := fun _ _ =>
    twoSLSBootstrapUniformPstarFinSucc (Ω := Ω) n ω
  let Zconst : ℕ → Ω → (Fin (n + 1) → Fin (n + 1)) → EuclideanSpace ℝ l :=
    fun _ _ ωs =>
      twoSLSBootstrapResidualSubstitutionRecenteredScoreStatisticFinSucc
        Z X Y β n ω ωs
  have hPconst : ∀ m ω', IsProbabilityMeasure (Pconst m ω') := fun _ _ =>
    twoSLSBootstrapUniformPstarFinSucc_isProbabilityMeasure (Ω := Ω) n ω
  have hZconst : ∀ m ω', MemLp (Zconst m ω') 2 (Pconst m ω') := fun _ _ => by
    simpa only [Pconst, Zconst, twoSLSBootstrapUniformPstarFinSucc] using
      (memLp_two_uniformOn_univ
        (Y := fun ωs : Fin (n + 1) → Fin (n + 1) =>
          twoSLSBootstrapResidualSubstitutionRecenteredScoreStatisticFinSucc
            Z X Y β n ω ωs))
  have htail := bootstrapTailProb_zero_le_integral_norm_sq_div
    (Pstar := Pconst) (Zstar := Zconst) hPconst hZconst hδ 0 ω
  simpa [bootstrapTailProb, Pconst, Zconst, Real.dist_eq] using htail

/-- Hansen equation (12.45)'s centered residual-substitution term is
negligible under Assumption 12.2 and the scalar WLLNs implied by its mixed
fourth moments. This derives the conditional tail by conditional Markov. -/
theorem of_assumption12_2_iid_weight_wlln
    [IsProbabilityMeasure μ]
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {e Y : ℕ → Ω → ℝ} {β : k → ℝ}
    (h : TwoSLSAssumption12_2IidFourthConditions μ Z X e)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hw : TwoSLSCovarianceWeightWLLNConditions μ Z X e) :
    TwoSLSBootstrapResidualSubstitutionNegligibilityInputs μ Z X Y β where
  residual_substitution_negligible := by
    intro δ hδ
    have hsecond := residualSubstitution_secondMoment_tendstoInMeasure_zero
      (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y) (β := β)
      h hmodel hw
    have hscaled : TendstoInMeasure μ
        (fun n ω =>
          (∫ ωs : Fin (n + 1) → Fin (n + 1),
            ‖twoSLSBootstrapResidualSubstitutionRecenteredScoreStatisticFinSucc
              Z X Y β n ω ωs‖ ^ 2
            ∂(twoSLSBootstrapUniformPstarFinSucc (Ω := Ω) n ω)) / δ ^ 2)
        atTop (fun _ => 0) := by
      have hs :=
        TendstoInMeasure.const_mul_zero_real (μ := μ) (δ ^ 2)⁻¹ hsecond
      refine hs.congr_left (fun n => ae_of_all μ fun ω => ?_)
      simp [div_eq_mul_inv, mul_comm]
    refine tendstoInMeasure_zero_of_nonneg_le (μ := μ) ?_ ?_ hscaled
    · intro n ω
      exact measureReal_nonneg
    · exact residualSubstitution_tail_le_secondMoment Z X Y β hδ

/-- Residual-substitution negligibility directly from Hansen's literal
finite-fourth Assumption 12.2 package. -/
theorem of_textbook_fourth
    [IsProbabilityMeasure μ]
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {e Y : ℕ → Ω → ℝ} {β : k → ℝ}
    (h : TwoSLSAssumption12_2JointIidTextbookFourthConditions μ Z X e Y β) :
    TwoSLSBootstrapResidualSubstitutionNegligibilityInputs μ Z X Y β := by
  let hMixed := h.toJointIidMixedMomentConditions
  exact of_assumption12_2_iid_weight_wlln
    (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y) (β := β)
    hMixed.toTwoSLSAssumption12_2JointIidFourthConditions.toIidFourthConditions
    h.model hMixed.toWeightWLLNConditions

/-- Build the concrete Hansen 12.8 residual-substitution input package from
the residual-substitution negligibility condition plus the still-independent
compact-tail condition.

This constructor closes the primitive residual-substitution field: callers no
longer need to build `TwoSLSBootstrapResidualSubstitutionInputs` directly when
they already have the concrete centered residual-substitution negligibility
statement.  The remaining field is exactly joint compact-tail control for
`twoSLSBootstrapTrueRecenteredScoreStatisticFinSucc` and
`twoSLSBootstrapRecenteredScoreStatisticFinSucc`; deriving that tail condition
from Assumption 12.2 alone would require an additional bootstrap tightness
argument not currently present in the Chapter 10/12 API. -/
theorem toResidualSubstitutionInputs
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {Y e : ℕ → Ω → ℝ} {β : k → ℝ}
    (h : TwoSLSBootstrapResidualSubstitutionNegligibilityInputs μ Z X Y β)
    (hTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set (EuclideanSpace ℝ l), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω =>
            (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω) n ω).real
              {ωs |
                twoSLSBootstrapTrueRecenteredScoreStatisticFinSucc
                  Z e n ω ωs ∉ K})
          atTop (fun _ => 0) ∧
        TendstoInMeasure μ
          (fun n ω =>
            (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω) n ω).real
              {ωs |
                twoSLSBootstrapRecenteredScoreStatisticFinSucc
                  Z X Y n ω ωs ∉ K})
          atTop (fun _ => 0)) :
    TwoSLSBootstrapResidualSubstitutionInputs μ Z X Y e β where
  compact_tail := hTail
  residual_substitution_negligible := h.residual_substitution_negligible

/-- Build the concrete residual-substitution package from true-score compact
tail control and residual-substitution negligibility.

The feasible residual-score compact tail is not an independent input once the
true-score centered bootstrap statistic is tight and the centered
residual-substitution statistic is `o_{P*}(1)`.  Under the structural equation,
`actual = true - residualSubstitution`; enlarging the compact true-score set to
a closed ball and using a union bound transfers the tail to the feasible
score. -/
theorem toResidualSubstitutionInputs_of_trueScore_compactTail
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {Y e : ℕ → Ω → ℝ} {β : k → ℝ}
    (h : TwoSLSBootstrapResidualSubstitutionNegligibilityInputs μ Z X Y β)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hTrueTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set (EuclideanSpace ℝ l), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω =>
            (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω) n ω).real
              {ωs |
                twoSLSBootstrapTrueRecenteredScoreStatisticFinSucc
                  Z e n ω ωs ∉ K})
          atTop (fun _ => 0)) :
    TwoSLSBootstrapResidualSubstitutionInputs μ Z X Y e β where
  compact_tail := by
    intro η hη
    rcases hTrueTail η hη with ⟨Ktrue, hKtrue, hTrue⟩
    obtain ⟨M, hMpos, hKball⟩ :=
      hKtrue.isBounded.subset_ball_lt 0
        (0 : EuclideanSpace ℝ l)
    let Kactual : Set (EuclideanSpace ℝ l) :=
      Metric.closedBall (0 : EuclideanSpace ℝ l) (M + 1)
    have hKtrue_subset_Kactual : Ktrue ⊆ Kactual := by
      intro x hx
      have hxball := hKball hx
      have hxnorm : ‖x‖ < M := by
        simpa [Metric.mem_ball, dist_zero_right] using hxball
      have hxnorm_le : ‖x‖ ≤ M + 1 := by
        linarith
      dsimp [Kactual]
      simpa [Metric.mem_closedBall, dist_zero_right] using hxnorm_le
    have hTrueActual :
        TendstoInMeasure μ
          (fun n ω =>
            (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω) n ω).real
              {ωs |
                twoSLSBootstrapTrueRecenteredScoreStatisticFinSucc
                  Z e n ω ωs ∉ Kactual})
          atTop (fun _ => 0) := by
      refine tendstoInMeasure_zero_of_nonneg_le
        (μ := μ)
        (f := fun n ω =>
          (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω) n ω).real
            {ωs |
              twoSLSBootstrapTrueRecenteredScoreStatisticFinSucc
                Z e n ω ωs ∉ Kactual})
        (g := fun n ω =>
          (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω) n ω).real
            {ωs |
              twoSLSBootstrapTrueRecenteredScoreStatisticFinSucc
                Z e n ω ωs ∉ Ktrue})
        (fun _ _ => measureReal_nonneg) ?_ hTrue
      intro n ω
      let P : Measure (Fin (n + 1) → Fin (n + 1)) :=
        twoSLSBootstrapUniformPstarFinSucc (Ω := Ω) n ω
      let Aactual : Set (Fin (n + 1) → Fin (n + 1)) :=
        {ωs |
          twoSLSBootstrapTrueRecenteredScoreStatisticFinSucc
            Z e n ω ωs ∉ Kactual}
      let Atrue : Set (Fin (n + 1) → Fin (n + 1)) :=
        {ωs |
          twoSLSBootstrapTrueRecenteredScoreStatisticFinSucc
            Z e n ω ωs ∉ Ktrue}
      have hsubset : Aactual ⊆ Atrue := by
        intro ωs hωs hmem
        exact hωs (hKtrue_subset_Kactual hmem)
      haveI : IsProbabilityMeasure P :=
        twoSLSBootstrapUniformPstarFinSucc_isProbabilityMeasure (Ω := Ω) n ω
      calc
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω) n ω).real Aactual =
            (P Aactual).toReal := rfl
        _ ≤ (P Atrue).toReal :=
            ENNReal.toReal_mono (measure_ne_top P Atrue)
              (measure_mono hsubset)
        _ =
            (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω) n ω).real
              {ωs |
                twoSLSBootstrapTrueRecenteredScoreStatisticFinSucc
                  Z e n ω ωs ∉ Ktrue} := rfl
    refine ⟨Kactual, isCompact_closedBall (0 : EuclideanSpace ℝ l) (M + 1),
      hTrueActual, ?_⟩
    have hSubst :=
      h.residual_substitution_negligible 1 zero_lt_one
    have hsum :
        TendstoInMeasure μ
          (fun n ω =>
            (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω) n ω).real
                {ωs |
                  twoSLSBootstrapTrueRecenteredScoreStatisticFinSucc
                    Z e n ω ωs ∉ Ktrue} +
              (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω) n ω).real
                {ωs |
                  (1 : ℝ) ≤
                    ‖twoSLSBootstrapResidualSubstitutionRecenteredScoreStatisticFinSucc
                      Z X Y β n ω ωs‖})
          atTop (fun _ => 0) :=
      tendstoInMeasure_add_nonneg_zero
        (fun _ _ => measureReal_nonneg)
        (fun _ _ => measureReal_nonneg)
        hTrue hSubst
    refine tendstoInMeasure_zero_of_nonneg_le
      (μ := μ)
      (f := fun n ω =>
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω) n ω).real
          {ωs |
            twoSLSBootstrapRecenteredScoreStatisticFinSucc
              Z X Y n ω ωs ∉ Kactual})
      (g := fun n ω =>
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω) n ω).real
            {ωs |
              twoSLSBootstrapTrueRecenteredScoreStatisticFinSucc
                Z e n ω ωs ∉ Ktrue} +
          (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω) n ω).real
            {ωs |
              (1 : ℝ) ≤
                ‖twoSLSBootstrapResidualSubstitutionRecenteredScoreStatisticFinSucc
                  Z X Y β n ω ωs‖})
      (fun _ _ => measureReal_nonneg) ?_ hsum
    intro n ω
    let P : Measure (Fin (n + 1) → Fin (n + 1)) :=
      twoSLSBootstrapUniformPstarFinSucc (Ω := Ω) n ω
    let C : Set (Fin (n + 1) → Fin (n + 1)) :=
      {ωs |
        twoSLSBootstrapRecenteredScoreStatisticFinSucc
          Z X Y n ω ωs ∉ Kactual}
    let A : Set (Fin (n + 1) → Fin (n + 1)) :=
      {ωs |
        twoSLSBootstrapTrueRecenteredScoreStatisticFinSucc
          Z e n ω ωs ∉ Ktrue}
    let B : Set (Fin (n + 1) → Fin (n + 1)) :=
      {ωs |
        (1 : ℝ) ≤
          ‖twoSLSBootstrapResidualSubstitutionRecenteredScoreStatisticFinSucc
            Z X Y β n ω ωs‖}
    have hsubset : C ⊆ A ∪ B := by
      intro ωs hωs
      by_cases htrue_mem :
          twoSLSBootstrapTrueRecenteredScoreStatisticFinSucc
            Z e n ω ωs ∈ Ktrue
      · right
        by_contra hsmall_not
        have hsmall :
            ‖twoSLSBootstrapResidualSubstitutionRecenteredScoreStatisticFinSucc
              Z X Y β n ω ωs‖ < 1 := not_le.mp hsmall_not
        have htrue_ball := hKball htrue_mem
        have htrue_norm :
            ‖twoSLSBootstrapTrueRecenteredScoreStatisticFinSucc
              Z e n ω ωs‖ < M := by
          simpa [Metric.mem_ball, dist_zero_right] using htrue_ball
        have hdecomp :=
          twoSLSBootstrapRecenteredScoreStatisticFinSucc_eq_true_sub_residualSubstitution
            Z X Y e β hmodel n ω ωs
        have hactual_norm_le :
            ‖twoSLSBootstrapRecenteredScoreStatisticFinSucc Z X Y n ω ωs‖ ≤
              ‖twoSLSBootstrapTrueRecenteredScoreStatisticFinSucc Z e n ω ωs‖ +
                ‖twoSLSBootstrapResidualSubstitutionRecenteredScoreStatisticFinSucc
                  Z X Y β n ω ωs‖ := by
          rw [hdecomp]
          exact norm_sub_le
            (twoSLSBootstrapTrueRecenteredScoreStatisticFinSucc Z e n ω ωs)
            (twoSLSBootstrapResidualSubstitutionRecenteredScoreStatisticFinSucc
              Z X Y β n ω ωs)
        have hactual_norm_lt :
            ‖twoSLSBootstrapRecenteredScoreStatisticFinSucc Z X Y n ω ωs‖ <
              M + 1 :=
          lt_of_le_of_lt hactual_norm_le (add_lt_add htrue_norm hsmall)
        have hactual_mem :
            twoSLSBootstrapRecenteredScoreStatisticFinSucc
              Z X Y n ω ωs ∈ Kactual := by
          dsimp [Kactual]
          simpa [Metric.mem_closedBall, dist_zero_right] using
            hactual_norm_lt.le
        exact hωs hactual_mem
      · left
        exact htrue_mem
    haveI : IsProbabilityMeasure P :=
      twoSLSBootstrapUniformPstarFinSucc_isProbabilityMeasure (Ω := Ω) n ω
    calc
      (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω) n ω).real C =
          (P C).toReal := rfl
      _ ≤ (P (A ∪ B)).toReal :=
          ENNReal.toReal_mono (measure_ne_top P (A ∪ B))
            (measure_mono hsubset)
      _ ≤ (P A + P B).toReal :=
          ENNReal.toReal_mono
            (ENNReal.add_ne_top.2
              ⟨measure_ne_top P A, measure_ne_top P B⟩)
            (measure_union_le A B)
      _ ≤ (P A).toReal + (P B).toReal :=
          ENNReal.toReal_add_le
      _ =
          (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω) n ω).real
              {ωs |
                twoSLSBootstrapTrueRecenteredScoreStatisticFinSucc
                  Z e n ω ωs ∉ Ktrue} +
            (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω) n ω).real
              {ωs |
                (1 : ℝ) ≤
                  ‖twoSLSBootstrapResidualSubstitutionRecenteredScoreStatisticFinSucc
                    Z X Y β n ω ωs‖} := rfl
  residual_substitution_negligible := h.residual_substitution_negligible

end TwoSLSBootstrapResidualSubstitutionNegligibilityInputs

set_option linter.style.longLine false in
/-- Residual-substitution negligibility from the exact primitive bootstrap
tail statement for the centered substitution statistic. -/
theorem TwoSLSBootstrapResidualSubstitutionNegligibilityInputs.of_norm_tail
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {Y : ℕ → Ω → ℝ} {β : k → ℝ}
    (htail : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω) n ω).real
            {ωs |
              δ ≤
                ‖twoSLSBootstrapResidualSubstitutionRecenteredScoreStatisticFinSucc
                  Z X Y β n ω ωs‖})
        atTop (fun _ => 0)) :
    TwoSLSBootstrapResidualSubstitutionNegligibilityInputs μ Z X Y β where
  residual_substitution_negligible := htail

set_option linter.style.longLine false in
omit [DecidableEq l] in
/-- True-score compact-tail control from an eventual deterministic norm bound.

This is a primitive tightness constructor for Hansen Theorem 12.8's
ordinary-bootstrap true-score statistic. It is intentionally separate from
Assumption 12.2: proving such a bound or tail condition from a concrete
empirical-process argument remains the caller's responsibility. -/
theorem
    twoSLSBootstrapTrueRecenteredScoreStatisticFinSucc_compactTail_uniform_of_eventually_norm_bound
    {Z : ℕ → Ω → l → ℝ} {e : ℕ → Ω → ℝ} {C : ℝ}
    (hbound :
      ∀ᶠ n in atTop,
        ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
          ‖twoSLSBootstrapTrueRecenteredScoreStatisticFinSucc
            Z e n ω ωs‖ ≤ C) :
    ∀ η : ℝ, 0 < η →
      ∃ K : Set (EuclideanSpace ℝ l), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω =>
            (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω) n ω).real
              {ωs |
                twoSLSBootstrapTrueRecenteredScoreStatisticFinSucc
                  Z e n ω ωs ∉ K})
          atTop (fun _ => 0) := by
  simpa using
    (chapter10_indexed_bootstrap_euclidean_compactTail_of_eventually_norm_bound
      (μ := μ)
      (Pstar := twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
      (Zstar := fun n ω ωs =>
        twoSLSBootstrapTrueRecenteredScoreStatisticFinSucc Z e n ω ωs)
      hbound)

private theorem indexed_bootstrap_tail_mono_of_subset
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {A B : ∀ n, Ω → Set (Ωboot n)}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hsubset : ∀ n ω, A n ω ⊆ B n ω)
    (hB : TendstoInMeasure μ
      (fun n ω => (Pstar n ω).real (B n ω)) atTop (fun _ => 0)) :
    TendstoInMeasure μ
      (fun n ω => (Pstar n ω).real (A n ω)) atTop (fun _ => 0) := by
  refine tendstoInMeasure_zero_of_nonneg_le
    (μ := μ)
    (f := fun n ω => (Pstar n ω).real (A n ω))
    (g := fun n ω => (Pstar n ω).real (B n ω))
    (fun _ _ => measureReal_nonneg) ?_ hB
  intro n ω
  haveI : IsProbabilityMeasure (Pstar n ω) := hPstar n ω
  exact ENNReal.toReal_mono (measure_ne_top (Pstar n ω) (B n ω))
    (measure_mono (hsubset n ω))

private theorem indexed_bootstrap_tail_of_bound
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {S T : ∀ n, Ω → Ωboot n → ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hbound : ∀ n ω ωs, S n ω ωs ≤ T n ω ωs)
    (hTtail : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω => (Pstar n ω).real {ωs | δ ≤ T n ω ωs})
        atTop (fun _ => 0)) :
    ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω => (Pstar n ω).real {ωs | δ ≤ S n ω ωs})
        atTop (fun _ => 0) := by
  intro δ hδ
  exact indexed_bootstrap_tail_mono_of_subset
    (μ := μ) (Pstar := Pstar)
    (A := fun n ω => {ωs | δ ≤ S n ω ωs})
    (B := fun n ω => {ωs | δ ≤ T n ω ωs})
      hPstar
      (by
        intro n ω ωs hS
        exact le_trans hS (hbound n ω ωs))
    (hTtail δ hδ)

private theorem indexed_bootstrap_tail_of_eventually_lt
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {B : ∀ n, Ω → Ωboot n → ℝ}
    (hsmall : ∀ δ : ℝ, 0 < δ →
      ∀ᶠ n in atTop, ∀ ω ωs, B n ω ωs < δ) :
    ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω => (Pstar n ω).real {ωs | δ ≤ B n ω ωs})
        atTop (fun _ => 0) := by
  intro δ hδ
  have hzero :
      TendstoInMeasure μ (fun _ (_ : Ω) => (0 : ℝ)) atTop (fun _ => 0) :=
    tendstoInMeasure_const_real (μ := μ) tendsto_const_nhds
  refine TendstoInMeasure.congr'
    (f := fun _ (_ : Ω) => (0 : ℝ))
    (f' := fun n ω => (Pstar n ω).real {ωs | δ ≤ B n ω ωs})
    (g := fun _ : Ω => (0 : ℝ)) (g' := fun _ : Ω => 0)
    ?_ EventuallyEq.rfl hzero
  filter_upwards [hsmall δ hδ] with n hn
  exact ae_of_all μ fun ω => by
    have hset : {ωs | δ ≤ B n ω ωs} = ∅ := by
      ext ωs
      have hnot : ¬ δ ≤ B n ω ωs := not_le_of_gt (hn ω ωs)
      simp [hnot]
    simp [hset]

private theorem indexed_bootstrap_pair_compactTail_of_eventually_norm_bound
    {E : Type*} [NormedAddCommGroup E] [ProperSpace E]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Xstar Ystar : ∀ n, Ω → Ωboot n → E} {C D : ℝ}
    (hX : ∀ᶠ n in atTop, ∀ ω ωs, ‖Xstar n ω ωs‖ ≤ C)
    (hY : ∀ᶠ n in atTop, ∀ ω ωs, ‖Ystar n ω ωs‖ ≤ D) :
    ∀ η : ℝ, 0 < η →
      ∃ K : Set E, IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω => (Pstar n ω).real {ωs | Xstar n ω ωs ∉ K})
          atTop (fun _ => 0) ∧
        TendstoInMeasure μ
          (fun n ω => (Pstar n ω).real {ωs | Ystar n ω ωs ∉ K})
          atTop (fun _ => 0) := by
  intro η hη
  let M : ℝ := max C D
  let K : Set E := Metric.closedBall (0 : E) M
  have hzero :
      TendstoInMeasure μ (fun _ (_ : Ω) => (0 : ℝ)) atTop (fun _ => 0) :=
    tendstoInMeasure_const_real (μ := μ) tendsto_const_nhds
  refine ⟨K, isCompact_closedBall (0 : E) M, ?_, ?_⟩
  · refine TendstoInMeasure.congr'
      (f := fun _ (_ : Ω) => (0 : ℝ))
      (f' := fun n ω => (Pstar n ω).real {ωs | Xstar n ω ωs ∉ K})
      (g := fun _ : Ω => (0 : ℝ)) (g' := fun _ : Ω => 0)
      ?_ EventuallyEq.rfl hzero
    filter_upwards [hX] with n hn
    exact ae_of_all μ fun ω => by
      have hset : {ωs | Xstar n ω ωs ∉ K} = ∅ := by
        ext ωs
        have hxmem : Xstar n ω ωs ∈ K := by
          dsimp [K, M]
          simpa [Metric.mem_closedBall, dist_zero_right] using
            (hn ω ωs).trans (le_max_left C D)
        simp [hxmem]
      simp [hset]
  · refine TendstoInMeasure.congr'
      (f := fun _ (_ : Ω) => (0 : ℝ))
      (f' := fun n ω => (Pstar n ω).real {ωs | Ystar n ω ωs ∉ K})
      (g := fun _ : Ω => (0 : ℝ)) (g' := fun _ : Ω => 0)
      ?_ EventuallyEq.rfl hzero
    filter_upwards [hY] with n hn
    exact ae_of_all μ fun ω => by
      have hset : {ωs | Ystar n ω ωs ∉ K} = ∅ := by
        ext ωs
        have hymem : Ystar n ω ωs ∈ K := by
          dsimp [K, M]
          simpa [Metric.mem_closedBall, dist_zero_right] using
            (hn ω ωs).trans (le_max_right C D)
        simp [hymem]
      simp [hset]

set_option linter.style.longLine false in
/-- Residual-substitution negligibility from a bootstrap empirical-process
envelope bound.

The input `B` is a scalar remainder envelope for the centered
residual-substitution statistic. This is the usual Hansen 12.8 proof shape:
show the concrete centered substitution term is bounded by an
empirical-process remainder whose bootstrap tail is `o_p(1)`. -/
theorem TwoSLSBootstrapResidualSubstitutionNegligibilityInputs.of_norm_bound
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {Y : ℕ → Ω → ℝ} {β : k → ℝ}
    {B : ∀ n, Ω → (Fin (n + 1) → Fin (n + 1)) → ℝ}
    (hBtail : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω) n ω).real
            {ωs | δ ≤ B n ω ωs})
        atTop (fun _ => 0))
    (hbound : ∀ n ω (ωs : Fin (n + 1) → Fin (n + 1)),
      ‖twoSLSBootstrapResidualSubstitutionRecenteredScoreStatisticFinSucc
        Z X Y β n ω ωs‖ ≤ B n ω ωs) :
    TwoSLSBootstrapResidualSubstitutionNegligibilityInputs μ Z X Y β where
  residual_substitution_negligible :=
    indexed_bootstrap_tail_of_bound
      (μ := μ) (Pstar := twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
      (S := fun n ω ωs =>
        ‖twoSLSBootstrapResidualSubstitutionRecenteredScoreStatisticFinSucc
          Z X Y β n ω ωs‖)
      (T := B)
      (fun n ω =>
        twoSLSBootstrapUniformPstarFinSucc_isProbabilityMeasure (Ω := Ω) n ω)
      hbound hBtail

set_option linter.style.longLine false in
/-- Residual-substitution negligibility from a uniform `o(1)` pathwise bound.

This is the direct deterministic-envelope version of Hansen Theorem 12.8's
centered residual-substitution step: if the concrete centered substitution
statistic is eventually smaller than every positive threshold uniformly over
original samples and resamples, then its conditional bootstrap tail is
`o_p(1)`. -/
theorem
    TwoSLSBootstrapResidualSubstitutionNegligibilityInputs.of_uniform_norm_vanish
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {Y : ℕ → Ω → ℝ} {β : k → ℝ}
    (hsmall : ∀ δ : ℝ, 0 < δ →
      ∀ᶠ n in atTop,
        ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
          ‖twoSLSBootstrapResidualSubstitutionRecenteredScoreStatisticFinSucc
            Z X Y β n ω ωs‖ < δ) :
    TwoSLSBootstrapResidualSubstitutionNegligibilityInputs μ Z X Y β where
  residual_substitution_negligible :=
    indexed_bootstrap_tail_of_eventually_lt
      (μ := μ) (Pstar := twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
      (B := fun n ω ωs =>
        ‖twoSLSBootstrapResidualSubstitutionRecenteredScoreStatisticFinSucc
          Z X Y β n ω ωs‖)
      hsmall

/-- Build the score-level residual transfer package from concrete
residual-substitution negligibility. -/
theorem twoSLSBootstrapResidualScoreCLTInputs_of_residualSubstitutionInputs
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {Y e : ℕ → Ω → ℝ} {β : k → ℝ}
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (h : TwoSLSBootstrapResidualSubstitutionInputs μ Z X Y e β) :
    TwoSLSBootstrapResidualScoreCLTInputs μ Z X Y e where
  true_meas := by
    intro n ω
    fun_prop
  actual_meas := by
    intro n ω
    fun_prop
  compact_tail := h.compact_tail
  residual_substitution_closeness := by
    intro δ hδ
    have hdist : ∀ n ω ωs,
        dist (twoSLSBootstrapRecenteredScoreStatisticFinSucc Z X Y n ω ωs)
          (twoSLSBootstrapTrueRecenteredScoreStatisticFinSucc Z e n ω ωs) =
          ‖twoSLSBootstrapResidualSubstitutionRecenteredScoreStatisticFinSucc
            Z X Y β n ω ωs‖ := by
      intro n ω ωs
      rw [twoSLSBootstrapRecenteredScoreStatisticFinSucc_eq_true_sub_residualSubstitution
        Z X Y e β hmodel]
      simp
    simpa [hdist] using h.residual_substitution_negligible δ hδ

/-- Residual-score ordinary-bootstrap CLT from the true-score CLT plus the
named residual-substitution transfer inputs. -/
theorem
    twoSLSBootstrapRecenteredScoreStatisticFinSucc_tendstoInBootstrapWeakDistribution_uniform_of_trueScore_residualSubstitution
    [IsProbabilityMeasure μ]
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {Y e : ℕ → Ω → ℝ} {Omega : Matrix l l ℝ}
    (htrue :
      TendstoInBootstrapWeakDistributionIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs =>
          twoSLSBootstrapTrueRecenteredScoreStatisticFinSucc Z e n ω ωs)
        (multivariateGaussian (0 : EuclideanSpace ℝ l) Omega)
        (fun z : EuclideanSpace ℝ l => z))
    (hresid : TwoSLSBootstrapResidualScoreCLTInputs μ Z X Y e) :
    TendstoInBootstrapWeakDistributionIndexed μ
      (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
      (fun n ω ωs =>
        twoSLSBootstrapRecenteredScoreStatisticFinSucc Z X Y n ω ωs)
      (multivariateGaussian (0 : EuclideanSpace ℝ l) Omega)
      (fun z : EuclideanSpace ℝ l => z) :=
  TendstoInBootstrapWeakDistributionIndexed.of_bootstrap_dist_tendsto_zero_tight
    (μ := μ) (Pstar := twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
    (Zstar := fun n ω ωs =>
      twoSLSBootstrapTrueRecenteredScoreStatisticFinSucc Z e n ω ωs)
    (Zstar' := fun n ω ωs =>
      twoSLSBootstrapRecenteredScoreStatisticFinSucc Z X Y n ω ωs)
    htrue
    (fun n ω =>
      twoSLSBootstrapUniformPstarFinSucc_isProbabilityMeasure (Ω := Ω) n ω)
    hresid.true_meas hresid.actual_meas hresid.compact_tail
    hresid.residual_substitution_closeness

/-- Assumption-12.2-facing residual-score ordinary-bootstrap CLT.

This composes the Chapter 10 true-score CLT with the named triangular
residual-substitution input. The remaining hypotheses are measurability,
compact-tail control for the true and residual-score statistics, and
negligibility of the residual-substitution centered resample mean. -/
theorem
    twoSLSBootstrapRecenteredScoreStatisticFinSucc_tendstoInBootstrapWeakDistribution_uniform_of_assumption12_2_residualSubstitution
    [IsProbabilityMeasure μ]
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {Y e : ℕ → Ω → ℝ}
    (h : TwoSLSAssumption12_2IidFourthConditions μ Z X e)
    (hresid : TwoSLSBootstrapResidualScoreCLTInputs μ Z X Y e) :
    TendstoInBootstrapWeakDistributionIndexed μ
      (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
      (fun n ω ωs =>
        twoSLSBootstrapRecenteredScoreStatisticFinSucc Z X Y n ω ωs)
      (multivariateGaussian (0 : EuclideanSpace ℝ l) (scoreCovMat μ Z e))
      (fun z : EuclideanSpace ℝ l => z) :=
  twoSLSBootstrapRecenteredScoreStatisticFinSucc_tendstoInBootstrapWeakDistribution_uniform_of_trueScore_residualSubstitution
    (μ := μ) (Z := Z) (X := X) (Y := Y) (e := e)
    (twoSLSBootstrapTrueRecenteredScoreStatisticFinSucc_tendstoInBootstrapWeakDistribution_uniform_of_assumption12_2
      (μ := μ) (Z := Z) (X := X) (e := e) h)
    hresid

/-- Assumption-12.2-facing residual-score ordinary-bootstrap CLT from the
concrete residual-substitution statistic. -/
theorem
    twoSLSBootstrapRecenteredScoreStatisticFinSucc_tendstoInBootstrapWeakDistribution_uniform_of_assumption12_2_residualSubstitutionInputs
    [IsProbabilityMeasure μ]
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {Y e : ℕ → Ω → ℝ} {β : k → ℝ}
    (h : TwoSLSAssumption12_2IidFourthConditions μ Z X e)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hresid : TwoSLSBootstrapResidualSubstitutionInputs μ Z X Y e β) :
    TendstoInBootstrapWeakDistributionIndexed μ
      (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
      (fun n ω ωs =>
        twoSLSBootstrapRecenteredScoreStatisticFinSucc Z X Y n ω ωs)
      (multivariateGaussian (0 : EuclideanSpace ℝ l) (scoreCovMat μ Z e))
      (fun z : EuclideanSpace ℝ l => z) :=
  twoSLSBootstrapRecenteredScoreStatisticFinSucc_tendstoInBootstrapWeakDistribution_uniform_of_assumption12_2_residualSubstitution
    (μ := μ) (Z := Z) (X := X) (Y := Y) (e := e) h
    (twoSLSBootstrapResidualScoreCLTInputs_of_residualSubstitutionInputs
      (μ := μ) (Z := Z) (X := X) (Y := Y) (e := e) hmodel hresid)

set_option linter.style.longLine false in
/-- Assumption-12.2-facing residual-score ordinary-bootstrap CLT from the
narrow residual-substitution negligibility package.

This is the theorem-facing constructor for the currently formalized part of
Hansen Theorem 12.8's residual-substitution step.  Assumption 12.2 supplies
the true-score bootstrap CLT, and `hresid` supplies exactly the concrete
centered residual-substitution negligibility field.  The remaining primitive
input is `hTail`, the joint compact-tail condition for the true and feasible
centered bootstrap score statistics; removing it needs a separate bootstrap
tightness transfer result. -/
theorem
    twoSLSBootstrapRecenteredScoreStatisticFinSucc_tendstoInBootstrapWeakDistribution_uniform_of_assumption12_2_residualSubstitutionNegligibility
    [IsProbabilityMeasure μ]
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {Y e : ℕ → Ω → ℝ} {β : k → ℝ}
    (h : TwoSLSAssumption12_2IidFourthConditions μ Z X e)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hresid :
      TwoSLSBootstrapResidualSubstitutionNegligibilityInputs μ Z X Y β)
    (hTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set (EuclideanSpace ℝ l), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω =>
            (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω) n ω).real
              {ωs |
                twoSLSBootstrapTrueRecenteredScoreStatisticFinSucc
                  Z e n ω ωs ∉ K})
          atTop (fun _ => 0) ∧
        TendstoInMeasure μ
          (fun n ω =>
            (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω) n ω).real
              {ωs |
                twoSLSBootstrapRecenteredScoreStatisticFinSucc
                  Z X Y n ω ωs ∉ K})
          atTop (fun _ => 0)) :
    TendstoInBootstrapWeakDistributionIndexed μ
      (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
      (fun n ω ωs =>
        twoSLSBootstrapRecenteredScoreStatisticFinSucc Z X Y n ω ωs)
      (multivariateGaussian (0 : EuclideanSpace ℝ l) (scoreCovMat μ Z e))
      (fun z : EuclideanSpace ℝ l => z) :=
  twoSLSBootstrapRecenteredScoreStatisticFinSucc_tendstoInBootstrapWeakDistribution_uniform_of_assumption12_2_residualSubstitutionInputs
    (μ := μ) (Z := Z) (X := X) (Y := Y) (e := e)
    h hmodel
    (hresid.toResidualSubstitutionInputs (μ := μ) (Z := Z) (X := X)
      (Y := Y) (e := e) (β := β) hTail)

set_option linter.style.longLine false in
/-- Assumption-12.2-facing residual-score ordinary-bootstrap CLT from true-score
compact-tail control and centered residual-substitution negligibility.

Unlike `..._residualSubstitutionNegligibility`, this wrapper does not require
callers to supply feasible residual-score compact-tail control separately. It
derives that feasible tail from the true-score tail, the structural equation,
and the centered residual-substitution negligibility bridge. -/
theorem
    twoSLSBootstrapRecenteredScoreStatisticFinSucc_tendstoInBootstrapWeakDistribution_uniform_of_assumption12_2_residualSubstitutionNegligibility_trueScoreTail
    [IsProbabilityMeasure μ]
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {Y e : ℕ → Ω → ℝ} {β : k → ℝ}
    (h : TwoSLSAssumption12_2IidFourthConditions μ Z X e)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hresid :
      TwoSLSBootstrapResidualSubstitutionNegligibilityInputs μ Z X Y β)
    (hTrueTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set (EuclideanSpace ℝ l), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω =>
            (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω) n ω).real
              {ωs |
                twoSLSBootstrapTrueRecenteredScoreStatisticFinSucc
                  Z e n ω ωs ∉ K})
          atTop (fun _ => 0)) :
    TendstoInBootstrapWeakDistributionIndexed μ
      (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
      (fun n ω ωs =>
        twoSLSBootstrapRecenteredScoreStatisticFinSucc Z X Y n ω ωs)
      (multivariateGaussian (0 : EuclideanSpace ℝ l) (scoreCovMat μ Z e))
      (fun z : EuclideanSpace ℝ l => z) :=
  twoSLSBootstrapRecenteredScoreStatisticFinSucc_tendstoInBootstrapWeakDistribution_uniform_of_assumption12_2_residualSubstitutionInputs
    (μ := μ) (Z := Z) (X := X) (Y := Y) (e := e)
    h hmodel
    (hresid.toResidualSubstitutionInputs_of_trueScore_compactTail
      (μ := μ) (Z := Z) (X := X) (Y := Y) (e := e) (β := β)
      hmodel hTrueTail)

/-- Population-linearized coefficient CLT from the recentered-score bootstrap
CLT.

This is the Chapter 10 Delta-method step for Hansen Theorem 12.8, before the
population linearization matrix is replaced by the bootstrap-sample
linearization matrix. -/
theorem
    twoSLSBootstrapPopulationLinearizedGapFinSucc_tendstoInBootstrapWeakDistribution_formula
    {Pstar : ∀ n, Ω → Measure (Fin (n + 1) → Fin (n + 1))}
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {QXZ : Matrix k l ℝ} {QZZ Omega : Matrix l l ℝ} {QZX : Matrix l k ℝ}
    (hOmega : Omega.PosSemidef)
    (hQZZ_symm : QZZᵀ = QZZ) (hQZX : QZX = QXZᵀ)
    (hscore :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar
        (fun n ω ωs =>
          twoSLSBootstrapRecenteredScoreStatisticFinSucc Z X Y n ω ωs)
        (multivariateGaussian (0 : EuclideanSpace ℝ l) Omega)
        (fun z : EuclideanSpace ℝ l => z)) :
    TendstoInBootstrapWeakDistributionIndexed μ Pstar
      (fun n ω ωs =>
        twoSLSBootstrapPopulationLinearizedGapFinSucc
          QXZ QZZ QZX Z X Y n ω ωs)
      (multivariateGaussian (0 : EuclideanSpace ℝ k)
        (twoSLSAsymptoticVariance QXZ QZZ Omega QZX))
      (fun z : EuclideanSpace ℝ k => (z : k → ℝ)) := by
  let G : Matrix k l ℝ := twoSLSPopulationLinearizationMatrix QXZ QZZ QZX
  have hdelta :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar
        (fun n ω ωs =>
          twoSLSBootstrapPopulationLinearizedStatisticFinSucc
            QXZ QZZ QZX Z X Y n ω ωs)
        (multivariateGaussian (0 : EuclideanSpace ℝ k) (G * Omega * Gᵀ))
        (fun z : EuclideanSpace ℝ k => z) := by
    simpa [twoSLSBootstrapPopulationLinearizedStatisticFinSucc, G] using
      chapter10_indexed_bootstrap_delta_method_gaussian
        (μ := μ) (Pstar := Pstar)
        (Tstar := fun n ω ωs =>
          twoSLSBootstrapRecenteredScoreStatisticFinSucc Z X Y n ω ωs)
        (V := Omega) G hOmega hscore
  have hgap :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar
        (fun n ω ωs =>
          (twoSLSBootstrapPopulationLinearizedStatisticFinSucc
            QXZ QZZ QZX Z X Y n ω ωs : k → ℝ))
        (multivariateGaussian (0 : EuclideanSpace ℝ k) (G * Omega * Gᵀ))
        (fun z : EuclideanSpace ℝ k => (z : k → ℝ)) :=
    chapter10_indexed_bootstrap_continuous_mapping_distribution
      (μ := μ) (Pstar := Pstar)
      (Zstar := fun n ω ωs =>
        twoSLSBootstrapPopulationLinearizedStatisticFinSucc
          QXZ QZZ QZX Z X Y n ω ωs)
      (ν := multivariateGaussian (0 : EuclideanSpace ℝ k) (G * Omega * Gᵀ))
      (Z := fun z : EuclideanSpace ℝ k => z)
      (g := fun z : EuclideanSpace ℝ k => (z : k → ℝ))
      hdelta (PiLp.continuous_ofLp 2 (fun _ : k => ℝ))
  have hcov :
      twoSLSAsymptoticVariance QXZ QZZ Omega QZX = G * Omega * Gᵀ := by
    simpa [G] using
      twoSLSAsymptoticVariance_eq_linearization_covariance
        QXZ QZZ Omega QZX hQZZ_symm hQZX
  simpa [twoSLSBootstrapPopulationLinearizedGapFinSucc, hcov] using hgap

/-- Theorem-facing coefficient CLT inputs for Hansen Theorem 12.8.

The package exposes the exact proof boundary after reusing Chapter 10's
ordinary-bootstrap score CLT: score convergence, replacement of the population
linearization by the bootstrap-sample linearization, and replacement of the
linearized statistic by the actual bootstrap coefficient statistic. -/
structure TwoSLSBootstrapFormulaCoefficientCLTInputs
    (μ : Measure Ω)
    (Pstar : ∀ n, Ω → Measure (Fin (n + 1) → Fin (n + 1)))
    (Z : ℕ → Ω → l → ℝ) (X : ℕ → Ω → k → ℝ) (Y : ℕ → Ω → ℝ)
    (QXZ : Matrix k l ℝ) (QZZ Omega : Matrix l l ℝ) (QZX : Matrix l k ℝ) :
    Prop where
  bootstrap_probability : ∀ n ω, IsProbabilityMeasure (Pstar n ω)
  omega_posSemidef : Omega.PosSemidef
  qzz_symm : QZZᵀ = QZZ
  qzx_eq_qxz_transpose : QZX = QXZᵀ
  score_limit : TendstoInBootstrapWeakDistributionIndexed μ Pstar
    (fun n ω ωs =>
      twoSLSBootstrapRecenteredScoreStatisticFinSucc Z X Y n ω ωs)
    (multivariateGaussian (0 : EuclideanSpace ℝ l) Omega)
    (fun z : EuclideanSpace ℝ l => z)
  population_linearized_meas : ∀ n ω,
    Measurable
      (fun ωs =>
        twoSLSBootstrapPopulationLinearizedGapFinSucc
          QXZ QZZ QZX Z X Y n ω ωs)
  linearized_meas : ∀ n ω,
    Measurable (fun ωs => twoSLSBootstrapLinearizedGapFinSucc Z X Y n ω ωs)
  statistic_meas : ∀ n ω,
    Measurable (fun ωs => twoSLSBootstrapBetaGapFinSucc Z X Y n ω ωs)
  population_to_sample_tail : ∀ η : ℝ, 0 < η →
    ∃ K : Set (k → ℝ), IsCompact K ∧
      TendstoInMeasure μ
        (fun n ω =>
          (Pstar n ω).real
            {ωs |
              twoSLSBootstrapPopulationLinearizedGapFinSucc
                QXZ QZZ QZX Z X Y n ω ωs ∉ K})
        atTop (fun _ => 0) ∧
      TendstoInMeasure μ
        (fun n ω =>
          (Pstar n ω).real
            {ωs | twoSLSBootstrapLinearizedGapFinSucc Z X Y n ω ωs ∉ K})
        atTop (fun _ => 0)
  population_to_sample_closeness : ∀ δ : ℝ, 0 < δ →
    TendstoInMeasure μ
      (fun n ω =>
        (Pstar n ω).real
          {ωs |
            δ ≤ dist (twoSLSBootstrapLinearizedGapFinSucc Z X Y n ω ωs)
              (twoSLSBootstrapPopulationLinearizedGapFinSucc
                QXZ QZZ QZX Z X Y n ω ωs)})
      atTop (fun _ => 0)
  compact_tail : ∀ η : ℝ, 0 < η →
    ∃ K : Set (k → ℝ), IsCompact K ∧
      TendstoInMeasure μ
        (fun n ω =>
          (Pstar n ω).real
            {ωs | twoSLSBootstrapLinearizedGapFinSucc Z X Y n ω ωs ∉ K})
        atTop (fun _ => 0) ∧
      TendstoInMeasure μ
        (fun n ω =>
          (Pstar n ω).real
            {ωs | twoSLSBootstrapBetaGapFinSucc Z X Y n ω ωs ∉ K})
        atTop (fun _ => 0)
  linearized_closeness : ∀ δ : ℝ, 0 < δ →
    TendstoInMeasure μ
      (fun n ω =>
        (Pstar n ω).real
          {ωs |
            δ ≤ dist (twoSLSBootstrapBetaGapFinSucc Z X Y n ω ωs)
              (twoSLSBootstrapLinearizedGapFinSucc Z X Y n ω ωs)})
      atTop (fun _ => 0)
  gaussian_frontier_null : ∀ x : k → ℝ,
    ContinuousAt
        (fun y =>
          vectorCDF
            (multivariateGaussian (0 : EuclideanSpace ℝ k)
              (twoSLSAsymptoticVariance QXZ QZZ Omega QZX))
            (fun z : EuclideanSpace ℝ k => (z : k → ℝ)) y) x →
      ((multivariateGaussian (0 : EuclideanSpace ℝ k)
          (twoSLSAsymptoticVariance QXZ QZZ Omega QZX)).map
          (fun z : EuclideanSpace ℝ k => (z : k → ℝ)))
        (frontier {z : k → ℝ | coordinateLE z x}) = 0

/-- Remaining coefficient-linearization inputs for Hansen Theorem 12.8.

Compared with `TwoSLSBootstrapFormulaCoefficientCLTInputs`, this package does
not ask for the ordinary-bootstrap law, covariance positivity, population block
symmetry, score CLT, Gaussian frontier-null facts, or measurability fields.
Those are derived by the Assumption-12.2 constructor below. -/
structure TwoSLSBootstrapCoefficientLinearizationInputs
    (μ : Measure Ω)
    (Pstar : ∀ n, Ω → Measure (Fin (n + 1) → Fin (n + 1)))
    (Z : ℕ → Ω → l → ℝ) (X : ℕ → Ω → k → ℝ) (Y : ℕ → Ω → ℝ)
    (QXZ : Matrix k l ℝ) (QZZ Omega : Matrix l l ℝ) (QZX : Matrix l k ℝ) :
    Prop where
  population_to_sample_tail : ∀ η : ℝ, 0 < η →
    ∃ K : Set (k → ℝ), IsCompact K ∧
      TendstoInMeasure μ
        (fun n ω =>
          (Pstar n ω).real
            {ωs |
              twoSLSBootstrapPopulationLinearizedGapFinSucc
                QXZ QZZ QZX Z X Y n ω ωs ∉ K})
        atTop (fun _ => 0) ∧
      TendstoInMeasure μ
        (fun n ω =>
          (Pstar n ω).real
            {ωs | twoSLSBootstrapLinearizedGapFinSucc Z X Y n ω ωs ∉ K})
        atTop (fun _ => 0)
  population_to_sample_closeness : ∀ δ : ℝ, 0 < δ →
    TendstoInMeasure μ
      (fun n ω =>
        (Pstar n ω).real
          {ωs |
            δ ≤ dist (twoSLSBootstrapLinearizedGapFinSucc Z X Y n ω ωs)
              (twoSLSBootstrapPopulationLinearizedGapFinSucc
                QXZ QZZ QZX Z X Y n ω ωs)})
      atTop (fun _ => 0)
  compact_tail : ∀ η : ℝ, 0 < η →
    ∃ K : Set (k → ℝ), IsCompact K ∧
      TendstoInMeasure μ
        (fun n ω =>
          (Pstar n ω).real
            {ωs | twoSLSBootstrapLinearizedGapFinSucc Z X Y n ω ωs ∉ K})
        atTop (fun _ => 0) ∧
      TendstoInMeasure μ
        (fun n ω =>
          (Pstar n ω).real
            {ωs | twoSLSBootstrapBetaGapFinSucc Z X Y n ω ωs ∉ K})
        atTop (fun _ => 0)
  linearized_closeness : ∀ δ : ℝ, 0 < δ →
    TendstoInMeasure μ
      (fun n ω =>
        (Pstar n ω).real
          {ωs |
            δ ≤ dist (twoSLSBootstrapBetaGapFinSucc Z X Y n ω ωs)
              (twoSLSBootstrapLinearizedGapFinSucc Z X Y n ω ωs)})
      atTop (fun _ => 0)

private theorem indexed_bootstrap_compactTail_of_continuous_image
    {E F : Type*} [TopologicalSpace E] [TopologicalSpace F]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Xstar : ∀ n, Ω → Ωboot n → E}
    {g : E → F}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hg : Continuous g)
    (hTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set E, IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω => (Pstar n ω).real {ωs | Xstar n ω ωs ∉ K})
          atTop (fun _ => 0)) :
    ∀ η : ℝ, 0 < η →
      ∃ K : Set F, IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω => (Pstar n ω).real {ωs | g (Xstar n ω ωs) ∉ K})
          atTop (fun _ => 0) := by
  intro η hη
  rcases hTail η hη with ⟨K, hK, hKtail⟩
  refine ⟨g '' K, hK.image hg, ?_⟩
  refine tendstoInMeasure_zero_of_nonneg_le
    (μ := μ)
    (f := fun n ω => (Pstar n ω).real {ωs | g (Xstar n ω ωs) ∉ g '' K})
    (g := fun n ω => (Pstar n ω).real {ωs | Xstar n ω ωs ∉ K})
    (fun _ _ => measureReal_nonneg) ?_ hKtail
  intro n ω
  haveI : IsProbabilityMeasure (Pstar n ω) := hPstar n ω
  refine ENNReal.toReal_mono
    (measure_ne_top (Pstar n ω) {ωs | Xstar n ω ωs ∉ K})
    (measure_mono ?_)
  intro ωs hωs hx
  exact hωs ⟨Xstar n ω ωs, hx, rfl⟩

set_option linter.style.longLine false in
/-- Population-linearized coefficient tightness from recentered-score
tightness.

For Hansen Theorem 12.8 the population-linearized coefficient statistic is a
fixed continuous linear image of the recentered bootstrap score. Hence its
compact-tail field is not an independent empirical-process primitive once
recentered-score compact-tail control is available. -/
theorem
    twoSLSBootstrapPopulationLinearizedGapFinSucc_compactTail_of_recenteredScore_compactTail
    {Pstar : ∀ n, Ω → Measure (Fin (n + 1) → Fin (n + 1))}
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {QXZ : Matrix k l ℝ} {QZZ : Matrix l l ℝ} {QZX : Matrix l k ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hScoreTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set (EuclideanSpace ℝ l), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω =>
            (Pstar n ω).real
              {ωs |
                twoSLSBootstrapRecenteredScoreStatisticFinSucc
                  Z X Y n ω ωs ∉ K})
          atTop (fun _ => 0)) :
    ∀ η : ℝ, 0 < η →
      ∃ K : Set (k → ℝ), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω =>
            (Pstar n ω).real
              {ωs |
                twoSLSBootstrapPopulationLinearizedGapFinSucc
                  QXZ QZZ QZX Z X Y n ω ωs ∉ K})
          atTop (fun _ => 0) := by
  let G : Matrix k l ℝ := twoSLSPopulationLinearizationMatrix QXZ QZZ QZX
  have hcont :
      Continuous
        (fun z : EuclideanSpace ℝ l =>
          (matrixContinuousLinearMap G z : k → ℝ)) :=
    (PiLp.continuous_ofLp 2 (fun _ : k => ℝ)).comp
      (matrixContinuousLinearMap G).continuous
  simpa [twoSLSBootstrapPopulationLinearizedGapFinSucc,
    twoSLSBootstrapPopulationLinearizedStatisticFinSucc, G] using
    (indexed_bootstrap_compactTail_of_continuous_image
      (μ := μ) (Pstar := Pstar)
      (Xstar := fun n ω ωs =>
        twoSLSBootstrapRecenteredScoreStatisticFinSucc Z X Y n ω ωs)
      (g := fun z : EuclideanSpace ℝ l =>
        (matrixContinuousLinearMap G z : k → ℝ))
      hPstar hcont hScoreTail)

private theorem indexed_bootstrap_compactTail_of_compactTail_closeness
    {E : Type*} [PseudoMetricSpace E] [Zero E] [ProperSpace E]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Xstar Ystar : ∀ n, Ω → Ωboot n → E}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hXtail : ∀ η : ℝ, 0 < η →
      ∃ K : Set E, IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω => (Pstar n ω).real {ωs | Xstar n ω ωs ∉ K})
          atTop (fun _ => 0))
    (hclose : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          (Pstar n ω).real
            {ωs | δ ≤ dist (Ystar n ω ωs) (Xstar n ω ωs)})
        atTop (fun _ => 0)) :
    ∀ η : ℝ, 0 < η →
      ∃ K : Set E, IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω => (Pstar n ω).real {ωs | Xstar n ω ωs ∉ K})
          atTop (fun _ => 0) ∧
        TendstoInMeasure μ
          (fun n ω => (Pstar n ω).real {ωs | Ystar n ω ωs ∉ K})
          atTop (fun _ => 0) := by
  intro η hη
  rcases hXtail η hη with ⟨Kx, hKx, hXK⟩
  obtain ⟨M, _hMpos, hKball⟩ := hKx.isBounded.subset_ball_lt 0 (0 : E)
  let K : Set E := Metric.closedBall (0 : E) (M + 1)
  have hKx_subset_K : Kx ⊆ K := by
    intro x hx
    have hxball := hKball hx
    have hxle : dist x (0 : E) ≤ M + 1 := by
      have hxlt : dist x (0 : E) < M := by
        simpa [Metric.mem_ball] using hxball
      linarith
    simpa [K, Metric.mem_closedBall] using hxle
  have hXKlarge :
      TendstoInMeasure μ
        (fun n ω => (Pstar n ω).real {ωs | Xstar n ω ωs ∉ K})
        atTop (fun _ => 0) := by
    refine tendstoInMeasure_zero_of_nonneg_le
      (μ := μ)
      (f := fun n ω => (Pstar n ω).real {ωs | Xstar n ω ωs ∉ K})
      (g := fun n ω => (Pstar n ω).real {ωs | Xstar n ω ωs ∉ Kx})
      (fun _ _ => measureReal_nonneg) ?_ hXK
    intro n ω
    haveI : IsProbabilityMeasure (Pstar n ω) := hPstar n ω
    refine ENNReal.toReal_mono
      (measure_ne_top (Pstar n ω) {ωs | Xstar n ω ωs ∉ Kx})
      (measure_mono ?_)
    intro ωs hωs hx
    exact hωs (hKx_subset_K hx)
  refine ⟨K, isCompact_closedBall (0 : E) (M + 1), hXKlarge, ?_⟩
  have hclose_one := hclose 1 zero_lt_one
  have hsum :
      TendstoInMeasure μ
        (fun n ω =>
          (Pstar n ω).real {ωs | Xstar n ω ωs ∉ Kx} +
            (Pstar n ω).real
              {ωs | (1 : ℝ) ≤ dist (Ystar n ω ωs) (Xstar n ω ωs)})
        atTop (fun _ => 0) :=
    tendstoInMeasure_add_nonneg_zero
      (fun _ _ => measureReal_nonneg)
      (fun _ _ => measureReal_nonneg)
      hXK hclose_one
  refine tendstoInMeasure_zero_of_nonneg_le
    (μ := μ)
    (f := fun n ω => (Pstar n ω).real {ωs | Ystar n ω ωs ∉ K})
    (g := fun n ω =>
      (Pstar n ω).real {ωs | Xstar n ω ωs ∉ Kx} +
        (Pstar n ω).real
          {ωs | (1 : ℝ) ≤ dist (Ystar n ω ωs) (Xstar n ω ωs)})
    (fun _ _ => measureReal_nonneg) ?_ hsum
  intro n ω
  let C : Set (Ωboot n) := {ωs | Ystar n ω ωs ∉ K}
  let A : Set (Ωboot n) := {ωs | Xstar n ω ωs ∉ Kx}
  let B : Set (Ωboot n) :=
    {ωs | (1 : ℝ) ≤ dist (Ystar n ω ωs) (Xstar n ω ωs)}
  have hsubset : C ⊆ A ∪ B := by
    intro ωs hωs
    by_cases hx : Xstar n ω ωs ∈ Kx
    · right
      by_contra hsmall_not
      have hsmall : dist (Ystar n ω ωs) (Xstar n ω ωs) < 1 :=
        not_le.mp hsmall_not
      have hxball := hKball hx
      have hxM : dist (Xstar n ω ωs) (0 : E) < M := by
        simpa [Metric.mem_ball] using hxball
      have hy0_le :
          dist (Ystar n ω ωs) (0 : E) ≤
            dist (Ystar n ω ωs) (Xstar n ω ωs) +
              dist (Xstar n ω ωs) (0 : E) :=
        dist_triangle (Ystar n ω ωs) (Xstar n ω ωs) 0
      have hy0_lt : dist (Ystar n ω ωs) (0 : E) < M + 1 :=
        lt_of_le_of_lt hy0_le (by linarith)
      have hyK : Ystar n ω ωs ∈ K := by
        simpa [K, Metric.mem_closedBall] using hy0_lt.le
      exact hωs hyK
    · left
      exact hx
  haveI : IsProbabilityMeasure (Pstar n ω) := hPstar n ω
  calc
    (Pstar n ω).real C = ((Pstar n ω) C).toReal := rfl
    _ ≤ ((Pstar n ω) (A ∪ B)).toReal :=
        ENNReal.toReal_mono (measure_ne_top (Pstar n ω) (A ∪ B))
          (measure_mono hsubset)
    _ ≤ ((Pstar n ω) A + (Pstar n ω) B).toReal :=
        ENNReal.toReal_mono
          (ENNReal.add_ne_top.2
            ⟨measure_ne_top (Pstar n ω) A, measure_ne_top (Pstar n ω) B⟩)
          (measure_union_le A B)
    _ ≤ ((Pstar n ω) A).toReal + ((Pstar n ω) B).toReal :=
        ENNReal.toReal_add_le
    _ =
        (Pstar n ω).real {ωs | Xstar n ω ωs ∉ Kx} +
          (Pstar n ω).real
            {ωs | (1 : ℝ) ≤ dist (Ystar n ω ωs) (Xstar n ω ωs)} := rfl

set_option linter.style.longLine false in
/-- Primitive coefficient-linearization inputs for Hansen Theorem 12.8.

This is the smaller empirical-process surface behind
`TwoSLSBootstrapCoefficientLinearizationInputs`: it asks only for compact-tail
control of the population-linearized statistic and the two bootstrap
probability closeness statements. Compact-tail control for the feasible
linearized and actual coefficient statistics is derived by a compact-tail
transfer lemma. -/
structure TwoSLSBootstrapCoefficientLinearizationPrimitiveInputs
    (μ : Measure Ω)
    (Pstar : ∀ n, Ω → Measure (Fin (n + 1) → Fin (n + 1)))
    (Z : ℕ → Ω → l → ℝ) (X : ℕ → Ω → k → ℝ) (Y : ℕ → Ω → ℝ)
    (QXZ : Matrix k l ℝ) (QZZ Omega : Matrix l l ℝ) (QZX : Matrix l k ℝ) :
    Prop where
  population_linearized_tail : ∀ η : ℝ, 0 < η →
    ∃ K : Set (k → ℝ), IsCompact K ∧
      TendstoInMeasure μ
        (fun n ω =>
          (Pstar n ω).real
            {ωs |
              twoSLSBootstrapPopulationLinearizedGapFinSucc
                QXZ QZZ QZX Z X Y n ω ωs ∉ K})
        atTop (fun _ => 0)
  population_to_sample_closeness : ∀ δ : ℝ, 0 < δ →
    TendstoInMeasure μ
      (fun n ω =>
        (Pstar n ω).real
          {ωs |
            δ ≤ dist (twoSLSBootstrapLinearizedGapFinSucc Z X Y n ω ωs)
              (twoSLSBootstrapPopulationLinearizedGapFinSucc
                QXZ QZZ QZX Z X Y n ω ωs)})
      atTop (fun _ => 0)
  linearized_closeness : ∀ δ : ℝ, 0 < δ →
    TendstoInMeasure μ
      (fun n ω =>
        (Pstar n ω).real
          {ωs |
            δ ≤ dist (twoSLSBootstrapBetaGapFinSucc Z X Y n ω ωs)
              (twoSLSBootstrapLinearizedGapFinSucc Z X Y n ω ωs)})
      atTop (fun _ => 0)

set_option linter.style.longLine false in
/-- Smallest coefficient-linearization empirical-process surface currently
used by Hansen Theorem 12.8.

The population-linearized compact-tail field is deliberately absent: it is
derived from compact-tail control of the recentered bootstrap score by
`twoSLSBootstrapPopulationLinearizedGapFinSucc_compactTail_of_recenteredScore_compactTail`.
-/
structure TwoSLSBootstrapCoefficientLinearizationClosenessInputs
    (μ : Measure Ω)
    (Pstar : ∀ n, Ω → Measure (Fin (n + 1) → Fin (n + 1)))
    (Z : ℕ → Ω → l → ℝ) (X : ℕ → Ω → k → ℝ) (Y : ℕ → Ω → ℝ)
    (QXZ : Matrix k l ℝ) (QZZ Omega : Matrix l l ℝ) (QZX : Matrix l k ℝ) :
    Prop where
  population_to_sample_closeness : ∀ δ : ℝ, 0 < δ →
    TendstoInMeasure μ
      (fun n ω =>
        (Pstar n ω).real
          {ωs |
            δ ≤ dist (twoSLSBootstrapLinearizedGapFinSucc Z X Y n ω ωs)
              (twoSLSBootstrapPopulationLinearizedGapFinSucc
                QXZ QZZ QZX Z X Y n ω ωs)})
      atTop (fun _ => 0)
  linearized_closeness : ∀ δ : ℝ, 0 < δ →
    TendstoInMeasure μ
      (fun n ω =>
        (Pstar n ω).real
          {ωs |
            δ ≤ dist (twoSLSBootstrapBetaGapFinSucc Z X Y n ω ωs)
              (twoSLSBootstrapLinearizedGapFinSucc Z X Y n ω ωs)})
      atTop (fun _ => 0)

namespace TwoSLSBootstrapCoefficientLinearizationClosenessInputs

set_option linter.style.longLine false in
/-- Build coefficient-linearization closeness inputs from empirical-process
envelope bounds for the two linearization errors.

`Bpop` controls the distance between the bootstrap-sample linearized statistic
and the fixed population-linearized statistic. `Bcoef` controls the distance
between the actual bootstrap 2SLS coefficient statistic and the bootstrap-sample
linearized statistic. This is a sharper proof boundary than assuming the two
bootstrap closeness tails directly. -/
theorem of_dist_bounds
    {Pstar : ∀ n, Ω → Measure (Fin (n + 1) → Fin (n + 1))}
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {QXZ : Matrix k l ℝ} {QZZ Omega : Matrix l l ℝ} {QZX : Matrix l k ℝ}
    {Bpop Bcoef : ∀ n, Ω → (Fin (n + 1) → Fin (n + 1)) → ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hBpopTail : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω => (Pstar n ω).real {ωs | δ ≤ Bpop n ω ωs})
        atTop (fun _ => 0))
    (hBcoefTail : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω => (Pstar n ω).real {ωs | δ ≤ Bcoef n ω ωs})
        atTop (fun _ => 0))
    (hBpopBound : ∀ n ω (ωs : Fin (n + 1) → Fin (n + 1)),
      dist (twoSLSBootstrapLinearizedGapFinSucc Z X Y n ω ωs)
        (twoSLSBootstrapPopulationLinearizedGapFinSucc
          QXZ QZZ QZX Z X Y n ω ωs) ≤ Bpop n ω ωs)
    (hBcoefBound : ∀ n ω (ωs : Fin (n + 1) → Fin (n + 1)),
      dist (twoSLSBootstrapBetaGapFinSucc Z X Y n ω ωs)
        (twoSLSBootstrapLinearizedGapFinSucc Z X Y n ω ωs) ≤
          Bcoef n ω ωs) :
    TwoSLSBootstrapCoefficientLinearizationClosenessInputs
      μ Pstar Z X Y QXZ QZZ Omega QZX where
  population_to_sample_closeness :=
    indexed_bootstrap_tail_of_bound
      (μ := μ) (Pstar := Pstar)
      (S := fun n ω ωs =>
        dist (twoSLSBootstrapLinearizedGapFinSucc Z X Y n ω ωs)
          (twoSLSBootstrapPopulationLinearizedGapFinSucc
            QXZ QZZ QZX Z X Y n ω ωs))
      (T := Bpop) hPstar hBpopBound hBpopTail
  linearized_closeness :=
    indexed_bootstrap_tail_of_bound
      (μ := μ) (Pstar := Pstar)
      (S := fun n ω ωs =>
        dist (twoSLSBootstrapBetaGapFinSucc Z X Y n ω ωs)
          (twoSLSBootstrapLinearizedGapFinSucc Z X Y n ω ωs))
      (T := Bcoef) hPstar hBcoefBound hBcoefTail

set_option linter.style.longLine false in
/-- Build coefficient-linearization closeness inputs from uniform `o(1)`
distance bounds.

This is the deterministic-envelope analogue of `of_dist_bounds`: it closes
the two conditional bootstrap tail fields when the population-to-sample
linearization error and the coefficient-linearization error are eventually
smaller than every positive threshold uniformly over original samples and
resamples. -/
theorem of_uniform_dist_vanish
    {Pstar : ∀ n, Ω → Measure (Fin (n + 1) → Fin (n + 1))}
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {QXZ : Matrix k l ℝ} {QZZ Omega : Matrix l l ℝ} {QZX : Matrix l k ℝ}
    (hPopSmall : ∀ δ : ℝ, 0 < δ →
      ∀ᶠ n in atTop,
        ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
          dist (twoSLSBootstrapLinearizedGapFinSucc Z X Y n ω ωs)
            (twoSLSBootstrapPopulationLinearizedGapFinSucc
              QXZ QZZ QZX Z X Y n ω ωs) < δ)
    (hCoefSmall : ∀ δ : ℝ, 0 < δ →
      ∀ᶠ n in atTop,
        ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
          dist (twoSLSBootstrapBetaGapFinSucc Z X Y n ω ωs)
            (twoSLSBootstrapLinearizedGapFinSucc Z X Y n ω ωs) < δ) :
    TwoSLSBootstrapCoefficientLinearizationClosenessInputs
      μ Pstar Z X Y QXZ QZZ Omega QZX where
  population_to_sample_closeness :=
    indexed_bootstrap_tail_of_eventually_lt
      (μ := μ) (Pstar := Pstar)
      (B := fun n ω ωs =>
        dist (twoSLSBootstrapLinearizedGapFinSucc Z X Y n ω ωs)
          (twoSLSBootstrapPopulationLinearizedGapFinSucc
            QXZ QZZ QZX Z X Y n ω ωs))
      hPopSmall
  linearized_closeness :=
    indexed_bootstrap_tail_of_eventually_lt
      (μ := μ) (Pstar := Pstar)
      (B := fun n ω ωs =>
        dist (twoSLSBootstrapBetaGapFinSucc Z X Y n ω ωs)
          (twoSLSBootstrapLinearizedGapFinSucc Z X Y n ω ωs))
      hCoefSmall

set_option linter.style.longLine false in
/-- Build the primitive coefficient-linearization package from score tightness
and the two bootstrap closeness fields.

This removes the population-linearized compact tail as an independent field:
it is just the continuous-image tail of the recentered bootstrap score. -/
theorem toPrimitiveInputs_of_scoreTail
    {Pstar : ∀ n, Ω → Measure (Fin (n + 1) → Fin (n + 1))}
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {QXZ : Matrix k l ℝ} {QZZ Omega : Matrix l l ℝ} {QZX : Matrix l k ℝ}
    (h : TwoSLSBootstrapCoefficientLinearizationClosenessInputs
      μ Pstar Z X Y QXZ QZZ Omega QZX)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hScoreTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set (EuclideanSpace ℝ l), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω =>
            (Pstar n ω).real
              {ωs |
                twoSLSBootstrapRecenteredScoreStatisticFinSucc
                  Z X Y n ω ωs ∉ K})
          atTop (fun _ => 0)) :
    TwoSLSBootstrapCoefficientLinearizationPrimitiveInputs
      μ Pstar Z X Y QXZ QZZ Omega QZX where
  population_linearized_tail :=
    twoSLSBootstrapPopulationLinearizedGapFinSucc_compactTail_of_recenteredScore_compactTail
      (μ := μ) (Pstar := Pstar) (Z := Z) (X := X) (Y := Y)
      (QXZ := QXZ) (QZZ := QZZ) (QZX := QZX)
      hPstar hScoreTail
  population_to_sample_closeness := h.population_to_sample_closeness
  linearized_closeness := h.linearized_closeness

set_option linter.style.longLine false in
/-- Build primitive coefficient-linearization inputs from true-score tightness
and residual-substitution negligibility.

The structural equation transfers true-score compact-tail control to feasible
recentered-score compact-tail control before applying
`toPrimitiveInputs_of_scoreTail`. -/
theorem toPrimitiveInputs_of_residualSubstitution_trueScoreTail
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {Y e : ℕ → Ω → ℝ} {β : k → ℝ}
    {QXZ : Matrix k l ℝ} {QZZ Omega : Matrix l l ℝ} {QZX : Matrix l k ℝ}
    (h : TwoSLSBootstrapCoefficientLinearizationClosenessInputs μ
      (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω)) Z X Y
      QXZ QZZ Omega QZX)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hresid :
      TwoSLSBootstrapResidualSubstitutionNegligibilityInputs μ Z X Y β)
    (hTrueTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set (EuclideanSpace ℝ l), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω =>
            (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω) n ω).real
              {ωs |
                twoSLSBootstrapTrueRecenteredScoreStatisticFinSucc
                  Z e n ω ωs ∉ K})
          atTop (fun _ => 0)) :
    TwoSLSBootstrapCoefficientLinearizationPrimitiveInputs μ
      (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω)) Z X Y
      QXZ QZZ Omega QZX := by
  let hresidFull :
      TwoSLSBootstrapResidualSubstitutionInputs μ Z X Y e β :=
    hresid.toResidualSubstitutionInputs_of_trueScore_compactTail
      (μ := μ) (Z := Z) (X := X) (Y := Y) (e := e) (β := β)
      hmodel hTrueTail
  have hScoreTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set (EuclideanSpace ℝ l), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω =>
            (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω) n ω).real
              {ωs |
                twoSLSBootstrapRecenteredScoreStatisticFinSucc
                  Z X Y n ω ωs ∉ K})
          atTop (fun _ => 0) := by
    intro η hη
    rcases hresidFull.compact_tail η hη with ⟨K, hK, _hTrue, hActual⟩
    exact ⟨K, hK, hActual⟩
  exact
    h.toPrimitiveInputs_of_scoreTail
      (μ := μ)
      (Pstar := twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
      (Z := Z) (X := X) (Y := Y)
      (QXZ := QXZ) (QZZ := QZZ) (Omega := Omega) (QZX := QZX)
      (fun n ω =>
        twoSLSBootstrapUniformPstarFinSucc_isProbabilityMeasure (Ω := Ω) n ω)
      hScoreTail

end TwoSLSBootstrapCoefficientLinearizationClosenessInputs

namespace TwoSLSBootstrapCoefficientLinearizationPrimitiveInputs

set_option linter.style.longLine false in
/-- Build the established coefficient-linearization package from primitive
population-linearized tightness and two bootstrap closeness statements. -/
theorem toCoefficientLinearizationInputs
    {Pstar : ∀ n, Ω → Measure (Fin (n + 1) → Fin (n + 1))}
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {QXZ : Matrix k l ℝ} {QZZ Omega : Matrix l l ℝ} {QZX : Matrix l k ℝ}
    (h : TwoSLSBootstrapCoefficientLinearizationPrimitiveInputs
      μ Pstar Z X Y QXZ QZZ Omega QZX)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω)) :
    TwoSLSBootstrapCoefficientLinearizationInputs
      μ Pstar Z X Y QXZ QZZ Omega QZX := by
  have hpop_to_sample_tail :
      ∀ η : ℝ, 0 < η →
        ∃ K : Set (k → ℝ), IsCompact K ∧
          TendstoInMeasure μ
            (fun n ω =>
              (Pstar n ω).real
                {ωs |
                  twoSLSBootstrapPopulationLinearizedGapFinSucc
                    QXZ QZZ QZX Z X Y n ω ωs ∉ K})
            atTop (fun _ => 0) ∧
          TendstoInMeasure μ
            (fun n ω =>
              (Pstar n ω).real
                {ωs | twoSLSBootstrapLinearizedGapFinSucc Z X Y n ω ωs ∉ K})
            atTop (fun _ => 0) :=
    indexed_bootstrap_compactTail_of_compactTail_closeness
      (μ := μ) (Pstar := Pstar)
      (Xstar := fun n ω ωs =>
        twoSLSBootstrapPopulationLinearizedGapFinSucc
          QXZ QZZ QZX Z X Y n ω ωs)
      (Ystar := fun n ω ωs =>
        twoSLSBootstrapLinearizedGapFinSucc Z X Y n ω ωs)
      hPstar h.population_linearized_tail h.population_to_sample_closeness
  have hlinearized_tail :
      ∀ η : ℝ, 0 < η →
        ∃ K : Set (k → ℝ), IsCompact K ∧
          TendstoInMeasure μ
            (fun n ω =>
              (Pstar n ω).real
                {ωs | twoSLSBootstrapLinearizedGapFinSucc Z X Y n ω ωs ∉ K})
            atTop (fun _ => 0) := by
    intro η hη
    rcases hpop_to_sample_tail η hη with ⟨K, hK, _hpop, hlin⟩
    exact ⟨K, hK, hlin⟩
  exact
    { population_to_sample_tail := hpop_to_sample_tail
      population_to_sample_closeness := h.population_to_sample_closeness
      compact_tail :=
        indexed_bootstrap_compactTail_of_compactTail_closeness
          (μ := μ) (Pstar := Pstar)
          (Xstar := fun n ω ωs =>
            twoSLSBootstrapLinearizedGapFinSucc Z X Y n ω ωs)
          (Ystar := fun n ω ωs =>
            twoSLSBootstrapBetaGapFinSucc Z X Y n ω ωs)
          hPstar hlinearized_tail h.linearized_closeness
      linearized_closeness := h.linearized_closeness }

end TwoSLSBootstrapCoefficientLinearizationPrimitiveInputs

set_option linter.style.longLine false in
/-- Build coefficient-linearization inputs from deterministic norm bounds and
the two bootstrap closeness fields.

This is the bounded-statistic face of Hansen Theorem 12.8's coefficient
linearization step.  It discharges both compact-tail fields of
`TwoSLSBootstrapCoefficientLinearizationInputs`; the remaining stochastic work
is exactly the population-to-sample and coefficient-linearization closeness. -/
theorem TwoSLSBootstrapCoefficientLinearizationInputs.of_eventually_norm_bounds
    {Pstar : ∀ n, Ω → Measure (Fin (n + 1) → Fin (n + 1))}
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {QXZ : Matrix k l ℝ} {QZZ Omega : Matrix l l ℝ} {QZX : Matrix l k ℝ}
    {Cpop Clin Cbeta : ℝ}
    (hPopBound : ∀ᶠ n in atTop,
      ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
        ‖twoSLSBootstrapPopulationLinearizedGapFinSucc
          QXZ QZZ QZX Z X Y n ω ωs‖ ≤ Cpop)
    (hLinBound : ∀ᶠ n in atTop,
      ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
        ‖twoSLSBootstrapLinearizedGapFinSucc Z X Y n ω ωs‖ ≤ Clin)
    (hBetaBound : ∀ᶠ n in atTop,
      ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
        ‖twoSLSBootstrapBetaGapFinSucc Z X Y n ω ωs‖ ≤ Cbeta)
    (hPopClose : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          (Pstar n ω).real
            {ωs |
              δ ≤ dist (twoSLSBootstrapLinearizedGapFinSucc Z X Y n ω ωs)
                (twoSLSBootstrapPopulationLinearizedGapFinSucc
                  QXZ QZZ QZX Z X Y n ω ωs)})
        atTop (fun _ => 0))
    (hCoefClose : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          (Pstar n ω).real
            {ωs |
              δ ≤ dist (twoSLSBootstrapBetaGapFinSucc Z X Y n ω ωs)
                (twoSLSBootstrapLinearizedGapFinSucc Z X Y n ω ωs)})
        atTop (fun _ => 0)) :
    TwoSLSBootstrapCoefficientLinearizationInputs
      μ Pstar Z X Y QXZ QZZ Omega QZX where
  population_to_sample_tail :=
    indexed_bootstrap_pair_compactTail_of_eventually_norm_bound
      (μ := μ) (Pstar := Pstar)
      (Xstar := fun n ω ωs =>
        twoSLSBootstrapPopulationLinearizedGapFinSucc
          QXZ QZZ QZX Z X Y n ω ωs)
      (Ystar := fun n ω ωs =>
        twoSLSBootstrapLinearizedGapFinSucc Z X Y n ω ωs)
      hPopBound hLinBound
  population_to_sample_closeness := hPopClose
  compact_tail :=
    indexed_bootstrap_pair_compactTail_of_eventually_norm_bound
      (μ := μ) (Pstar := Pstar)
      (Xstar := fun n ω ωs =>
        twoSLSBootstrapLinearizedGapFinSucc Z X Y n ω ωs)
      (Ystar := fun n ω ωs =>
        twoSLSBootstrapBetaGapFinSucc Z X Y n ω ωs)
      hLinBound hBetaBound
  linearized_closeness := hCoefClose

set_option linter.style.longLine false in
/-- Build coefficient-linearization inputs from deterministic norm bounds and
uniform `o(1)` distance bounds.

Compared with `of_eventually_norm_bounds`, this constructor also converts the
two closeness fields from pathwise uniform remainders to conditional bootstrap
tails. -/
theorem
    TwoSLSBootstrapCoefficientLinearizationInputs.of_eventually_norm_bounds_uniform_closeness
    {Pstar : ∀ n, Ω → Measure (Fin (n + 1) → Fin (n + 1))}
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {QXZ : Matrix k l ℝ} {QZZ Omega : Matrix l l ℝ} {QZX : Matrix l k ℝ}
    {Cpop Clin Cbeta : ℝ}
    (hPopBound : ∀ᶠ n in atTop,
      ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
        ‖twoSLSBootstrapPopulationLinearizedGapFinSucc
          QXZ QZZ QZX Z X Y n ω ωs‖ ≤ Cpop)
    (hLinBound : ∀ᶠ n in atTop,
      ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
        ‖twoSLSBootstrapLinearizedGapFinSucc Z X Y n ω ωs‖ ≤ Clin)
    (hBetaBound : ∀ᶠ n in atTop,
      ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
        ‖twoSLSBootstrapBetaGapFinSucc Z X Y n ω ωs‖ ≤ Cbeta)
    (hPopSmall : ∀ δ : ℝ, 0 < δ →
      ∀ᶠ n in atTop,
        ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
          dist (twoSLSBootstrapLinearizedGapFinSucc Z X Y n ω ωs)
            (twoSLSBootstrapPopulationLinearizedGapFinSucc
              QXZ QZZ QZX Z X Y n ω ωs) < δ)
    (hCoefSmall : ∀ δ : ℝ, 0 < δ →
      ∀ᶠ n in atTop,
        ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
          dist (twoSLSBootstrapBetaGapFinSucc Z X Y n ω ωs)
            (twoSLSBootstrapLinearizedGapFinSucc Z X Y n ω ωs) < δ) :
    TwoSLSBootstrapCoefficientLinearizationInputs
      μ Pstar Z X Y QXZ QZZ Omega QZX :=
  TwoSLSBootstrapCoefficientLinearizationInputs.of_eventually_norm_bounds
    (μ := μ) (Pstar := Pstar) (Z := Z) (X := X) (Y := Y)
    (QXZ := QXZ) (QZZ := QZZ) (Omega := Omega) (QZX := QZX)
    hPopBound hLinBound hBetaBound
    (indexed_bootstrap_tail_of_eventually_lt
      (μ := μ) (Pstar := Pstar)
      (B := fun n ω ωs =>
        dist (twoSLSBootstrapLinearizedGapFinSucc Z X Y n ω ωs)
          (twoSLSBootstrapPopulationLinearizedGapFinSucc
            QXZ QZZ QZX Z X Y n ω ωs))
      hPopSmall)
    (indexed_bootstrap_tail_of_eventually_lt
      (μ := μ) (Pstar := Pstar)
      (B := fun n ω ωs =>
        dist (twoSLSBootstrapBetaGapFinSucc Z X Y n ω ωs)
          (twoSLSBootstrapLinearizedGapFinSucc Z X Y n ω ωs))
      hCoefSmall)

omit [DecidableEq k] in
private theorem continuous_linearRestrictionEstimate (R : Matrix Unit k ℝ) :
    Continuous (linearRestrictionEstimate R) := by
  unfold linearRestrictionEstimate
  fun_prop

omit [DecidableEq k] in
private theorem continuous_linearRestrictionStdError (R : Matrix Unit k ℝ) :
    Continuous (fun V : Matrix k k ℝ => linearRestrictionStdError R V) := by
  have hcov : Continuous (fun V : Matrix k k ℝ => R * V * Rᵀ) :=
    Continuous.matrix_mul (Continuous.matrix_mul continuous_const continuous_id)
      continuous_const
  have hentry : Continuous (fun M : Matrix Unit Unit ℝ => M () ()) :=
    (continuous_apply ()).comp (continuous_apply ())
  unfold linearRestrictionStdError
  exact Real.continuous_sqrt.comp (hentry.comp hcov)

set_option linter.style.longLine false in
/-- The coefficient compact-tail field implies compact-tail control for any
fixed one-row bootstrap restriction numerator.

This is a reusable tightness bridge for Hansen Theorem 12.8: the scalar
numerator tail needed by Chapter 10 studentization is not an independent
empirical-process input once the coefficient statistic itself is tight. -/
theorem
    TwoSLSBootstrapCoefficientLinearizationInputs.linearRestrictionStatistic_compactTail
    {Pstar : ∀ n, Ω → Measure (Fin (n + 1) → Fin (n + 1))}
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {QXZ : Matrix k l ℝ} {QZZ Omega : Matrix l l ℝ} {QZX : Matrix l k ℝ}
    (h : TwoSLSBootstrapCoefficientLinearizationInputs μ Pstar Z X Y
      QXZ QZZ Omega QZX)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (R : Matrix Unit k ℝ) :
    ∀ η : ℝ, 0 < η →
      ∃ Kx : Set ℝ, IsCompact Kx ∧
        TendstoInMeasure μ
          (fun n ω =>
            (Pstar n ω).real
              {ωs |
                twoSLSBootstrapLinearRestrictionStatisticFinSucc
                  R Z X Y n ω ωs ∉ Kx})
          atTop (fun _ => 0) := by
  intro η hη
  rcases h.compact_tail η hη with ⟨K, hK, _hlin, hβ⟩
  let Kx : Set ℝ := linearRestrictionEstimate R '' K
  refine ⟨Kx, hK.image (continuous_linearRestrictionEstimate R), ?_⟩
  refine tendstoInMeasure_zero_of_nonneg_le
    (μ := μ)
    (f := fun n ω =>
      (Pstar n ω).real
        {ωs |
          twoSLSBootstrapLinearRestrictionStatisticFinSucc R Z X Y n ω ωs ∉ Kx})
    (g := fun n ω =>
      (Pstar n ω).real
        {ωs | twoSLSBootstrapBetaGapFinSucc Z X Y n ω ωs ∉ K})
    ?_ ?_ hβ
  · intro n ω
    exact measureReal_nonneg
  · intro n ω
    haveI : IsProbabilityMeasure (Pstar n ω) := hPstar n ω
    refine ENNReal.toReal_mono
      (measure_ne_top (Pstar n ω)
        {ωs | twoSLSBootstrapBetaGapFinSucc Z X Y n ω ωs ∉ K})
      (measure_mono ?_)
    intro ωs hωs hβmem
    exact hωs ⟨twoSLSBootstrapBetaGapFinSucc Z X Y n ω ωs, hβmem, rfl⟩

/-- Proof-facing condition package for Hansen Theorem 12.8.

The fields separate the two real pieces of the proof: the recentered bootstrap
linearization has the same Gaussian limit as 2SLS, and the actual bootstrap
2SLS statistic is asymptotically equivalent to that linearization. The
condition package deliberately exposes the closeness and tightness premises
rather than assuming the final coefficient statistic limit directly. -/
structure TwoSLSBootstrapAsymptoticNormalConditions
    (μ : Measure Ω)
    (Pstar : ∀ n, Ω → Measure (Fin (n + 1) → Fin (n + 1)))
    (Z : ℕ → Ω → l → ℝ) (X : ℕ → Ω → k → ℝ) (Y : ℕ → Ω → ℝ)
    (Vβ : Matrix k k ℝ) : Prop where
  bootstrap_probability : ∀ n ω, IsProbabilityMeasure (Pstar n ω)
  linearized_meas : ∀ n ω,
    Measurable (fun ωs => twoSLSBootstrapLinearizedGapFinSucc Z X Y n ω ωs)
  statistic_meas : ∀ n ω,
    Measurable (fun ωs => twoSLSBootstrapBetaGapFinSucc Z X Y n ω ωs)
  linearized_limit : TendstoInBootstrapWeakDistributionIndexed μ Pstar
    (fun n ω ωs => twoSLSBootstrapLinearizedGapFinSucc Z X Y n ω ωs)
    (multivariateGaussian (0 : EuclideanSpace ℝ k) Vβ)
    (fun z : EuclideanSpace ℝ k => (z : k → ℝ))
  compact_tail : ∀ η : ℝ, 0 < η →
    ∃ K : Set (k → ℝ), IsCompact K ∧
      TendstoInMeasure μ
        (fun n ω =>
          (Pstar n ω).real
            {ωs | twoSLSBootstrapLinearizedGapFinSucc Z X Y n ω ωs ∉ K})
        atTop (fun _ => 0) ∧
      TendstoInMeasure μ
        (fun n ω =>
          (Pstar n ω).real
            {ωs | twoSLSBootstrapBetaGapFinSucc Z X Y n ω ωs ∉ K})
        atTop (fun _ => 0)
  linearized_closeness : ∀ δ : ℝ, 0 < δ →
    TendstoInMeasure μ
      (fun n ω =>
        (Pstar n ω).real
          {ωs |
            δ ≤ dist (twoSLSBootstrapBetaGapFinSucc Z X Y n ω ωs)
              (twoSLSBootstrapLinearizedGapFinSucc Z X Y n ω ωs)})
      atTop (fun _ => 0)
  gaussian_frontier_null : ∀ x : k → ℝ,
    ContinuousAt
        (fun y =>
          vectorCDF
            (multivariateGaussian (0 : EuclideanSpace ℝ k) Vβ)
            (fun z : EuclideanSpace ℝ k => (z : k → ℝ)) y) x →
      ((multivariateGaussian (0 : EuclideanSpace ℝ k) Vβ).map
          (fun z : EuclideanSpace ℝ k => (z : k → ℝ)))
        (frontier {z : k → ℝ | coordinateLE z x}) = 0

/-- Weak bootstrap version of Hansen Theorem 12.8's coefficient endpoint,
proved from the linearized bootstrap statistic plus bootstrap-probability
closeness. -/
theorem twoSLSBootstrapBetaGapFinSucc_tendstoInBootstrapWeakDistribution
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {Vβ : Matrix k k ℝ}
    (h : TwoSLSBootstrapAsymptoticNormalConditions μ Pstar Z X Y Vβ) :
    TendstoInBootstrapWeakDistributionIndexed μ Pstar
      (fun n ω ωs => twoSLSBootstrapBetaGapFinSucc Z X Y n ω ωs)
      (multivariateGaussian (0 : EuclideanSpace ℝ k) Vβ)
      (fun z : EuclideanSpace ℝ k => (z : k → ℝ)) :=
  TendstoInBootstrapWeakDistributionIndexed.of_bootstrap_dist_tendsto_zero_tight
    (μ := μ) (Pstar := Pstar)
    (Zstar := fun n ω ωs => twoSLSBootstrapLinearizedGapFinSucc Z X Y n ω ωs)
    (Zstar' := fun n ω ωs => twoSLSBootstrapBetaGapFinSucc Z X Y n ω ωs)
    (ν := multivariateGaussian (0 : EuclideanSpace ℝ k) Vβ)
    (Z := fun z : EuclideanSpace ℝ k => (z : k → ℝ))
    h.linearized_limit h.bootstrap_probability h.linearized_meas h.statistic_meas
    h.compact_tail h.linearized_closeness

/-- Hansen Theorem 12.8 coefficient-distribution interface: the ordinary
bootstrap 2SLS statistic converges in bootstrap distribution to the same
Gaussian law as the sample 2SLS estimator. -/
theorem twoSLSBootstrapBetaGapFinSucc_tendstoInBootstrapDistribution
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {Vβ : Matrix k k ℝ}
    (h : TwoSLSBootstrapAsymptoticNormalConditions μ Pstar Z X Y Vβ) :
    TendstoInBootstrapDistributionIndexed μ Pstar
      (fun n ω ωs => twoSLSBootstrapBetaGapFinSucc Z X Y n ω ωs)
      (multivariateGaussian (0 : EuclideanSpace ℝ k) Vβ)
      (fun z : EuclideanSpace ℝ k => (z : k → ℝ)) :=
  chapter10_indexed_bootstrap_clt_gaussian_of_weakDistribution
    (μ := μ) (Pstar := Pstar)
    (Zstar := fun n ω ωs => twoSLSBootstrapBetaGapFinSucc Z X Y n ω ωs)
    (S := Vβ)
    (twoSLSBootstrapBetaGapFinSucc_tendstoInBootstrapWeakDistribution
      (μ := μ) (Pstar := Pstar) h)
    (fun n ω => by
      letI : IsProbabilityMeasure (Pstar n ω) := h.bootstrap_probability n ω
      infer_instance)
    h.statistic_meas h.gaussian_frontier_null

/-- Hansen-formula version of the bootstrap condition package for Theorem 12.8.

This fixes the bootstrap Gaussian limit to the same 2SLS covariance formula as
Theorem 12.2, rather than leaving the covariance matrix arbitrary. -/
abbrev TwoSLSBootstrapFormulaAsymptoticNormalConditions
    (μ : Measure Ω)
    (Pstar : ∀ n, Ω → Measure (Fin (n + 1) → Fin (n + 1)))
    (Z : ℕ → Ω → l → ℝ) (X : ℕ → Ω → k → ℝ) (Y : ℕ → Ω → ℝ)
    (QXZ : Matrix k l ℝ) (QZZ Omega : Matrix l l ℝ) (QZX : Matrix l k ℝ) : Prop :=
  TwoSLSBootstrapAsymptoticNormalConditions μ Pstar Z X Y
    (twoSLSAsymptoticVariance QXZ QZZ Omega QZX)

/-- Constructor for the existing Hansen Theorem 12.8 coefficient condition
package from score-level and linearization-level inputs.

This theorem is the tightened coefficient-bootstrap route: it no longer asks
for the coefficient CLT directly, but builds it from the recentered-score CLT,
population-to-bootstrap-sample linearization closeness, and the final
coefficient linearization closeness. -/
theorem
    twoSLSBootstrapFormulaAsymptoticNormalConditions_of_score_clt_inputs
    {Pstar : ∀ n, Ω → Measure (Fin (n + 1) → Fin (n + 1))}
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {QXZ : Matrix k l ℝ} {QZZ Omega : Matrix l l ℝ} {QZX : Matrix l k ℝ}
    (h : TwoSLSBootstrapFormulaCoefficientCLTInputs
      μ Pstar Z X Y QXZ QZZ Omega QZX) :
    TwoSLSBootstrapFormulaAsymptoticNormalConditions
      μ Pstar Z X Y QXZ QZZ Omega QZX := by
  have hpop :=
    twoSLSBootstrapPopulationLinearizedGapFinSucc_tendstoInBootstrapWeakDistribution_formula
      (Pstar := Pstar) (Z := Z) (X := X) (Y := Y)
      (QXZ := QXZ) (QZZ := QZZ) (Omega := Omega) (QZX := QZX)
      h.omega_posSemidef h.qzz_symm h.qzx_eq_qxz_transpose h.score_limit
  have hlinearized :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar
        (fun n ω ωs => twoSLSBootstrapLinearizedGapFinSucc Z X Y n ω ωs)
        (multivariateGaussian (0 : EuclideanSpace ℝ k)
          (twoSLSAsymptoticVariance QXZ QZZ Omega QZX))
        (fun z : EuclideanSpace ℝ k => (z : k → ℝ)) :=
    TendstoInBootstrapWeakDistributionIndexed.of_bootstrap_dist_tendsto_zero_tight
      (μ := μ) (Pstar := Pstar)
      (Zstar := fun n ω ωs =>
        twoSLSBootstrapPopulationLinearizedGapFinSucc
          QXZ QZZ QZX Z X Y n ω ωs)
      (Zstar' := fun n ω ωs =>
        twoSLSBootstrapLinearizedGapFinSucc Z X Y n ω ωs)
      hpop h.bootstrap_probability h.population_linearized_meas h.linearized_meas
      h.population_to_sample_tail h.population_to_sample_closeness
  exact
    { bootstrap_probability := h.bootstrap_probability
      linearized_meas := h.linearized_meas
      statistic_meas := h.statistic_meas
      linearized_limit := hlinearized
      compact_tail := h.compact_tail
      linearized_closeness := h.linearized_closeness
      gaussian_frontier_null := h.gaussian_frontier_null }

/-- Ordinary-bootstrap formula coefficient inputs from Assumption 12.2, concrete
residual-substitution negligibility, and the remaining coefficient
linearization inputs. -/
theorem
    twoSLSBootstrapFormulaCoefficientCLTInputs_uniform_of_assumption12_2_residualSubstitution_linearization
    [IsProbabilityMeasure μ]
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y e : ℕ → Ω → ℝ}
    {β : k → ℝ}
    (h : TwoSLSAssumption12_2IidFourthConditions μ Z X e)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hresid : TwoSLSBootstrapResidualSubstitutionInputs μ Z X Y e β)
    (hlin : TwoSLSBootstrapCoefficientLinearizationInputs μ
      (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω)) Z X Y
      (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
      (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
      (scoreCovMat μ Z e)
      (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))) :
    TwoSLSBootstrapFormulaCoefficientCLTInputs μ
      (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω)) Z X Y
      (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
      (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
      (scoreCovMat μ Z e)
      (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X))) := by
  let hGram := h.toGramConditions
  have hVβ_pos :
      (twoSLSAsymptoticVariance
        (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
        (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
        (scoreCovMat μ Z e)
        (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))).PosDef := by
    exact
      twoSLSAsymptoticVariance_posDef_of_qzz_omega_rank
        (QXZ := twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
        (QZZ := twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
        (Omega := scoreCovMat μ Z e)
        (QZX := twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))
        (twoSLSCombinedQXZ_eq_transpose_QZX_of_popGram_wlln
          (μ := μ) (Z := Z) (X := X)
          hGram.toTwoSLSAssumption12_1GramConditions.combined_gram)
        h.qzz_posDef h.omega_posDef h.qzx_rank
  exact
    { bootstrap_probability := fun n ω =>
        twoSLSBootstrapUniformPstarFinSucc_isProbabilityMeasure (Ω := Ω) n ω
      omega_posSemidef := h.omega_posDef.posSemidef
      qzz_symm := by
        simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using h.qzz_posDef.1.eq
      qzx_eq_qxz_transpose :=
        twoSLSCombinedQZX_eq_transpose_QXZ_of_popGram_wlln
          (μ := μ) (Z := Z) (X := X)
          hGram.toTwoSLSAssumption12_1GramConditions.combined_gram
      score_limit :=
        twoSLSBootstrapRecenteredScoreStatisticFinSucc_tendstoInBootstrapWeakDistribution_uniform_of_assumption12_2_residualSubstitutionInputs
          (μ := μ) (Z := Z) (X := X) (Y := Y) (e := e)
          h hmodel hresid
      population_linearized_meas := by
        intro n ω
        fun_prop
      linearized_meas := by
        intro n ω
        fun_prop
      statistic_meas := by
        intro n ω
        fun_prop
      population_to_sample_tail := hlin.population_to_sample_tail
      population_to_sample_closeness := hlin.population_to_sample_closeness
      compact_tail := hlin.compact_tail
      linearized_closeness := hlin.linearized_closeness
      gaussian_frontier_null := fun x _hx =>
        multivariateGaussian_coordinateLE_frontier_null_of_posDef hVβ_pos x }

/-- Ordinary-bootstrap formula coefficient condition package from the smallest
Theorem-12.8 coefficient proof inputs left in this file. -/
theorem
    twoSLSBootstrapFormulaAsymptoticNormalConditions_uniform_of_assumption12_2_residualSubstitution_linearization
    [IsProbabilityMeasure μ]
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y e : ℕ → Ω → ℝ}
    {β : k → ℝ}
    (h : TwoSLSAssumption12_2IidFourthConditions μ Z X e)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hresid : TwoSLSBootstrapResidualSubstitutionInputs μ Z X Y e β)
    (hlin : TwoSLSBootstrapCoefficientLinearizationInputs μ
      (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω)) Z X Y
      (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
      (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
      (scoreCovMat μ Z e)
      (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))) :
    TwoSLSBootstrapFormulaAsymptoticNormalConditions μ
      (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω)) Z X Y
      (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
      (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
      (scoreCovMat μ Z e)
      (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X))) :=
  twoSLSBootstrapFormulaAsymptoticNormalConditions_of_score_clt_inputs
    (μ := μ) (Pstar := twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
    (Z := Z) (X := X) (Y := Y)
    (QXZ := twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
    (QZZ := twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
    (Omega := scoreCovMat μ Z e)
    (QZX := twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))
    (twoSLSBootstrapFormulaCoefficientCLTInputs_uniform_of_assumption12_2_residualSubstitution_linearization
      (μ := μ) (Z := Z) (X := X) (Y := Y) (e := e)
      h hmodel hresid hlin)

/-- Hansen Theorem 12.8 coefficient-distribution endpoint with the covariance
target fixed to Hansen's 2SLS asymptotic variance formula. -/
theorem twoSLSBootstrapBetaGapFinSucc_tendstoInBootstrapDistribution_formula
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {QXZ : Matrix k l ℝ} {QZZ Omega : Matrix l l ℝ} {QZX : Matrix l k ℝ}
    (h : TwoSLSBootstrapFormulaAsymptoticNormalConditions
      μ Pstar Z X Y QXZ QZZ Omega QZX) :
    TendstoInBootstrapDistributionIndexed μ Pstar
      (fun n ω ωs => twoSLSBootstrapBetaGapFinSucc Z X Y n ω ωs)
      (multivariateGaussian (0 : EuclideanSpace ℝ k)
        (twoSLSAsymptoticVariance QXZ QZZ Omega QZX))
      (fun z : EuclideanSpace ℝ k => (z : k → ℝ)) :=
  twoSLSBootstrapBetaGapFinSucc_tendstoInBootstrapDistribution
    (μ := μ) (Pstar := Pstar) h

/-- Ordinary-bootstrap specialization of Hansen Theorem 12.8's coefficient
endpoint, using `uniformOn Set.univ` over `Fin (n+1) → Fin (n+1)`. -/
theorem twoSLSBootstrapBetaGapFinSucc_tendstoInBootstrapDistribution_uniform
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {Vβ : Matrix k k ℝ}
    (h : TwoSLSBootstrapAsymptoticNormalConditions μ
      (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω)) Z X Y Vβ) :
    TendstoInBootstrapDistributionIndexed μ
      (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
      (fun n ω ωs => twoSLSBootstrapBetaGapFinSucc Z X Y n ω ωs)
      (multivariateGaussian (0 : EuclideanSpace ℝ k) Vβ)
      (fun z : EuclideanSpace ℝ k => (z : k → ℝ)) :=
  twoSLSBootstrapBetaGapFinSucc_tendstoInBootstrapDistribution
    (μ := μ) (Pstar := twoSLSBootstrapUniformPstarFinSucc (Ω := Ω)) h

/-- Ordinary-bootstrap, formula-covariance specialization of Hansen Theorem
12.8's coefficient endpoint. -/
theorem twoSLSBootstrapBetaGapFinSucc_tendstoInBootstrapDistribution_formula_uniform
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {QXZ : Matrix k l ℝ} {QZZ Omega : Matrix l l ℝ} {QZX : Matrix l k ℝ}
    (h : TwoSLSBootstrapFormulaAsymptoticNormalConditions μ
      (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω)) Z X Y
      QXZ QZZ Omega QZX) :
    TendstoInBootstrapDistributionIndexed μ
      (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
      (fun n ω ωs => twoSLSBootstrapBetaGapFinSucc Z X Y n ω ωs)
      (multivariateGaussian (0 : EuclideanSpace ℝ k)
        (twoSLSAsymptoticVariance QXZ QZZ Omega QZX))
      (fun z : EuclideanSpace ℝ k => (z : k → ℝ)) :=
  twoSLSBootstrapBetaGapFinSucc_tendstoInBootstrapDistribution_formula
    (μ := μ) (Pstar := twoSLSBootstrapUniformPstarFinSucc (Ω := Ω)) h

/-- Coefficient-distribution endpoint from the score-level and
linearization-level inputs. -/
theorem
    twoSLSBootstrapBetaGapFinSucc_tendstoInBootstrapDistribution_formula_of_score_clt_inputs
    {Pstar : ∀ n, Ω → Measure (Fin (n + 1) → Fin (n + 1))}
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {QXZ : Matrix k l ℝ} {QZZ Omega : Matrix l l ℝ} {QZX : Matrix l k ℝ}
    (h : TwoSLSBootstrapFormulaCoefficientCLTInputs
      μ Pstar Z X Y QXZ QZZ Omega QZX) :
    TendstoInBootstrapDistributionIndexed μ Pstar
      (fun n ω ωs => twoSLSBootstrapBetaGapFinSucc Z X Y n ω ωs)
      (multivariateGaussian (0 : EuclideanSpace ℝ k)
        (twoSLSAsymptoticVariance QXZ QZZ Omega QZX))
      (fun z : EuclideanSpace ℝ k => (z : k → ℝ)) :=
  twoSLSBootstrapBetaGapFinSucc_tendstoInBootstrapDistribution_formula
    (μ := μ) (Pstar := Pstar)
    (twoSLSBootstrapFormulaAsymptoticNormalConditions_of_score_clt_inputs
      (μ := μ) (Pstar := Pstar) h)

/-- Ordinary-bootstrap coefficient-distribution endpoint from the score-level
and linearization-level inputs. -/
theorem
    twoSLSBootstrapBetaGapFinSucc_tendstoInBootstrapDistribution_formula_uniform_of_score_clt_inputs
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {QXZ : Matrix k l ℝ} {QZZ Omega : Matrix l l ℝ} {QZX : Matrix l k ℝ}
    (h : TwoSLSBootstrapFormulaCoefficientCLTInputs μ
      (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω)) Z X Y
      QXZ QZZ Omega QZX) :
    TendstoInBootstrapDistributionIndexed μ
      (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
      (fun n ω ωs => twoSLSBootstrapBetaGapFinSucc Z X Y n ω ωs)
      (multivariateGaussian (0 : EuclideanSpace ℝ k)
        (twoSLSAsymptoticVariance QXZ QZZ Omega QZX))
      (fun z : EuclideanSpace ℝ k => (z : k → ℝ)) :=
  twoSLSBootstrapBetaGapFinSucc_tendstoInBootstrapDistribution_formula_of_score_clt_inputs
    (μ := μ) (Pstar := twoSLSBootstrapUniformPstarFinSucc (Ω := Ω)) h

/-- Assumption-12.2-facing ordinary-bootstrap coefficient endpoint from the
concrete residual-substitution statistic and the remaining coefficient
linearization inputs. -/
theorem
    twoSLSBootstrapBetaGapFinSucc_tendstoInBootstrapDistribution_formula_uniform_of_assumption12_2_residualSubstitution_linearization
    [IsProbabilityMeasure μ]
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y e : ℕ → Ω → ℝ}
    {β : k → ℝ}
    (h : TwoSLSAssumption12_2IidFourthConditions μ Z X e)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hresid : TwoSLSBootstrapResidualSubstitutionInputs μ Z X Y e β)
    (hlin : TwoSLSBootstrapCoefficientLinearizationInputs μ
      (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω)) Z X Y
      (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
      (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
      (scoreCovMat μ Z e)
      (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))) :
    TendstoInBootstrapDistributionIndexed μ
      (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
      (fun n ω ωs => twoSLSBootstrapBetaGapFinSucc Z X Y n ω ωs)
      (multivariateGaussian (0 : EuclideanSpace ℝ k)
        (twoSLSAsymptoticVariance
          (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
          (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
          (scoreCovMat μ Z e)
          (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))))
      (fun z : EuclideanSpace ℝ k => (z : k → ℝ)) :=
  twoSLSBootstrapBetaGapFinSucc_tendstoInBootstrapDistribution_formula_uniform
    (μ := μ) (Z := Z) (X := X) (Y := Y)
    (QXZ := twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
    (QZZ := twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
    (Omega := scoreCovMat μ Z e)
    (QZX := twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))
    (twoSLSBootstrapFormulaAsymptoticNormalConditions_uniform_of_assumption12_2_residualSubstitution_linearization
      (μ := μ) (Z := Z) (X := X) (Y := Y) (e := e)
      h hmodel hresid hlin)

set_option linter.style.longLine false in
/-- Ordinary-bootstrap formula coefficient inputs from the narrower
residual-substitution and coefficient-closeness primitives.

This is the coefficient-only counterpart of the score-tail primitive Theorem
12.8 route below.  The feasible residual-score compact-tail field is derived
from true-score compact-tail control and centered residual-substitution
negligibility; the coefficient compact-tail fields are then derived from the
two coefficient-linearization closeness statements. -/
theorem
    twoSLSBootstrapFormulaCoefficientCLTInputs_uniform_of_assumption12_2_residualSubstitutionNegligibility_trueScoreTail_closeness
    [IsProbabilityMeasure μ]
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y e : ℕ → Ω → ℝ}
    {β : k → ℝ}
    (h : TwoSLSAssumption12_2IidFourthConditions μ Z X e)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hresid :
      TwoSLSBootstrapResidualSubstitutionNegligibilityInputs μ Z X Y β)
    (hTrueTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set (EuclideanSpace ℝ l), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω =>
            (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω) n ω).real
              {ωs |
                twoSLSBootstrapTrueRecenteredScoreStatisticFinSucc
                  Z e n ω ωs ∉ K})
          atTop (fun _ => 0))
    (hcoef :
      TwoSLSBootstrapCoefficientLinearizationClosenessInputs μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω)) Z X Y
        (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
        (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
        (scoreCovMat μ Z e)
        (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))) :
    TwoSLSBootstrapFormulaCoefficientCLTInputs μ
      (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω)) Z X Y
      (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
      (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
      (scoreCovMat μ Z e)
      (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X))) := by
  let hresidFull :
      TwoSLSBootstrapResidualSubstitutionInputs μ Z X Y e β :=
    hresid.toResidualSubstitutionInputs_of_trueScore_compactTail
      (μ := μ) (Z := Z) (X := X) (Y := Y) (e := e) (β := β)
      hmodel hTrueTail
  let hlinPrimitive :
      TwoSLSBootstrapCoefficientLinearizationPrimitiveInputs μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω)) Z X Y
        (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
        (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
        (scoreCovMat μ Z e)
        (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X))) :=
    hcoef.toPrimitiveInputs_of_residualSubstitution_trueScoreTail
      (μ := μ) (Z := Z) (X := X) (Y := Y) (e := e) (β := β)
      (QXZ := twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
      (QZZ := twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
      (Omega := scoreCovMat μ Z e)
      (QZX := twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))
      hmodel hresid hTrueTail
  let hlin :
      TwoSLSBootstrapCoefficientLinearizationInputs μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω)) Z X Y
        (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
        (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
        (scoreCovMat μ Z e)
        (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X))) :=
    hlinPrimitive.toCoefficientLinearizationInputs
      (μ := μ)
      (Pstar := twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
      (Z := Z) (X := X) (Y := Y)
      (QXZ := twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
      (QZZ := twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
      (Omega := scoreCovMat μ Z e)
      (QZX := twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))
      (fun n ω =>
        twoSLSBootstrapUniformPstarFinSucc_isProbabilityMeasure (Ω := Ω) n ω)
  exact
    twoSLSBootstrapFormulaCoefficientCLTInputs_uniform_of_assumption12_2_residualSubstitution_linearization
      (μ := μ) (Z := Z) (X := X) (Y := Y) (e := e)
      h hmodel hresidFull hlin

set_option linter.style.longLine false in
/-- Ordinary-bootstrap formula coefficient condition package from the narrower
residual-substitution and coefficient-closeness primitives. -/
theorem
    twoSLSBootstrapFormulaAsymptoticNormalConditions_uniform_of_assumption12_2_residualSubstitutionNegligibility_trueScoreTail_closeness
    [IsProbabilityMeasure μ]
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y e : ℕ → Ω → ℝ}
    {β : k → ℝ}
    (h : TwoSLSAssumption12_2IidFourthConditions μ Z X e)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hresid :
      TwoSLSBootstrapResidualSubstitutionNegligibilityInputs μ Z X Y β)
    (hTrueTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set (EuclideanSpace ℝ l), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω =>
            (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω) n ω).real
              {ωs |
                twoSLSBootstrapTrueRecenteredScoreStatisticFinSucc
                  Z e n ω ωs ∉ K})
          atTop (fun _ => 0))
    (hcoef :
      TwoSLSBootstrapCoefficientLinearizationClosenessInputs μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω)) Z X Y
        (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
        (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
        (scoreCovMat μ Z e)
        (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))) :
    TwoSLSBootstrapFormulaAsymptoticNormalConditions μ
      (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω)) Z X Y
      (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
      (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
      (scoreCovMat μ Z e)
      (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X))) :=
  twoSLSBootstrapFormulaAsymptoticNormalConditions_of_score_clt_inputs
    (μ := μ) (Pstar := twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
    (Z := Z) (X := X) (Y := Y)
    (QXZ := twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
    (QZZ := twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
    (Omega := scoreCovMat μ Z e)
    (QZX := twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))
    (twoSLSBootstrapFormulaCoefficientCLTInputs_uniform_of_assumption12_2_residualSubstitutionNegligibility_trueScoreTail_closeness
      (μ := μ) (Z := Z) (X := X) (Y := Y) (e := e)
      h hmodel hresid hTrueTail hcoef)

set_option linter.style.longLine false in
/-- Assumption-12.2-facing ordinary-bootstrap coefficient endpoint from the
narrow residual-substitution negligibility and coefficient-closeness inputs.

This endpoint no longer asks callers to assemble either the full
`TwoSLSBootstrapResidualSubstitutionInputs` package or the full
`TwoSLSBootstrapCoefficientLinearizationInputs` package. -/
theorem
    twoSLSBootstrapBetaGapFinSucc_tendstoInBootstrapDistribution_formula_uniform_of_assumption12_2_residualSubstitutionNegligibility_trueScoreTail_closeness
    [IsProbabilityMeasure μ]
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y e : ℕ → Ω → ℝ}
    {β : k → ℝ}
    (h : TwoSLSAssumption12_2IidFourthConditions μ Z X e)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hresid :
      TwoSLSBootstrapResidualSubstitutionNegligibilityInputs μ Z X Y β)
    (hTrueTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set (EuclideanSpace ℝ l), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω =>
            (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω) n ω).real
              {ωs |
                twoSLSBootstrapTrueRecenteredScoreStatisticFinSucc
                  Z e n ω ωs ∉ K})
          atTop (fun _ => 0))
    (hcoef :
      TwoSLSBootstrapCoefficientLinearizationClosenessInputs μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω)) Z X Y
        (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
        (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
        (scoreCovMat μ Z e)
        (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))) :
    TendstoInBootstrapDistributionIndexed μ
      (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
      (fun n ω ωs => twoSLSBootstrapBetaGapFinSucc Z X Y n ω ωs)
      (multivariateGaussian (0 : EuclideanSpace ℝ k)
        (twoSLSAsymptoticVariance
          (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
          (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
          (scoreCovMat μ Z e)
          (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))))
      (fun z : EuclideanSpace ℝ k => (z : k → ℝ)) :=
  twoSLSBootstrapBetaGapFinSucc_tendstoInBootstrapDistribution_formula_uniform
    (μ := μ) (Z := Z) (X := X) (Y := Y)
    (QXZ := twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
    (QZZ := twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
    (Omega := scoreCovMat μ Z e)
    (QZX := twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))
    (twoSLSBootstrapFormulaAsymptoticNormalConditions_uniform_of_assumption12_2_residualSubstitutionNegligibility_trueScoreTail_closeness
      (μ := μ) (Z := Z) (X := X) (Y := Y) (e := e)
      h hmodel hresid hTrueTail hcoef)

omit [DecidableEq k] in
/-- Standard-error consistency interface for Hansen Theorem 12.8.

Any bootstrap covariance estimator that converges in bootstrap probability to
the population 2SLS covariance gives convergence of the one-row restriction
standard error by the fixed Chapter 7 standard-error map. -/
theorem twoSLSBootstrapLinearRestrictionStdErrorFinSucc_tendstoInBootstrapProbability
    {R : Matrix Unit k ℝ}
    {Vstar : ∀ n, Ω → (Fin (n + 1) → Fin (n + 1)) → Matrix k k ℝ}
    {Vβ : Matrix k k ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hV :
      TendstoInBootstrapProbabilityIndexed μ Pstar Vstar (fun _ => Vβ)) :
    TendstoInBootstrapProbabilityIndexed μ Pstar
      (fun n ω ωs =>
        twoSLSBootstrapLinearRestrictionStdErrorFinSucc R Vstar n ω ωs)
      (fun _ => linearRestrictionStdError R Vβ) := by
  simpa [twoSLSBootstrapLinearRestrictionStdErrorFinSucc] using
    TendstoInBootstrapProbabilityIndexed.continuousAt_const_comp
      (Pstar := Pstar) (Zstar := Vstar) (c := Vβ)
      (g := fun V : Matrix k k ℝ => linearRestrictionStdError R V)
      hPstar hV (continuous_linearRestrictionStdError R).continuousAt

omit [DecidableEq k] in
/-- Standard-error consistency when the covariance input is an original-sample
sequence viewed as constant under the bootstrap law. This reuses Hansen
Theorem 10.1's bootstrap-probability bridge. -/
theorem
    twoSLSBootstrapLinearRestrictionStdErrorFinSucc_tendstoInBootstrapProbability_of_tendstoInMeasure
    {R : Matrix Unit k ℝ}
    {Vseq : ℕ → Ω → Matrix k k ℝ} {Vβ : Matrix k k ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hV : TendstoInMeasure μ Vseq atTop (fun _ => Vβ)) :
    TendstoInBootstrapProbabilityIndexed μ Pstar
      (fun n ω ωs =>
        twoSLSBootstrapLinearRestrictionStdErrorFinSucc R
          (fun n ω _ => Vseq n ω) n ω ωs)
      (fun _ => linearRestrictionStdError R Vβ) :=
  twoSLSBootstrapLinearRestrictionStdErrorFinSucc_tendstoInBootstrapProbability
    (μ := μ) (Pstar := Pstar) hPstar
    (tendstoInBootstrapProbabilityIndexed_of_tendstoInMeasure
      (μ := μ) (Pstar := Pstar) hPstar hV)

/-- Formula-covariance version of the standard-error consistency bridge. -/
theorem
    twoSLSBootstrapLinearRestrictionStdErrorFinSucc_tendstoInBootstrapProbability_formula
    {R : Matrix Unit k ℝ}
    {Vstar : ∀ n, Ω → (Fin (n + 1) → Fin (n + 1)) → Matrix k k ℝ}
    {QXZ : Matrix k l ℝ} {QZZ Omega : Matrix l l ℝ} {QZX : Matrix l k ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hV :
      TendstoInBootstrapProbabilityIndexed μ Pstar Vstar
        (fun _ => twoSLSAsymptoticVariance QXZ QZZ Omega QZX)) :
    TendstoInBootstrapProbabilityIndexed μ Pstar
      (fun n ω ωs =>
        twoSLSBootstrapLinearRestrictionStdErrorFinSucc R Vstar n ω ωs)
      (fun _ =>
        linearRestrictionStdError R
          (twoSLSAsymptoticVariance QXZ QZZ Omega QZX)) :=
  twoSLSBootstrapLinearRestrictionStdErrorFinSucc_tendstoInBootstrapProbability
    (μ := μ) (Pstar := Pstar) hPstar hV

/-- Ordinary-bootstrap, formula-covariance version of the standard-error
consistency bridge. -/
theorem
    twoSLSBootstrapLinearRestrictionStdErrorFinSucc_tendstoInBootstrapProbability_formula_uniform
    {R : Matrix Unit k ℝ}
    {Vstar : ∀ n, Ω → (Fin (n + 1) → Fin (n + 1)) → Matrix k k ℝ}
    {QXZ : Matrix k l ℝ} {QZZ Omega : Matrix l l ℝ} {QZX : Matrix l k ℝ}
    (hV :
      TendstoInBootstrapProbabilityIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω)) Vstar
        (fun _ => twoSLSAsymptoticVariance QXZ QZZ Omega QZX)) :
    TendstoInBootstrapProbabilityIndexed μ
      (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
      (fun n ω ωs =>
        twoSLSBootstrapLinearRestrictionStdErrorFinSucc R Vstar n ω ωs)
      (fun _ =>
        linearRestrictionStdError R
          (twoSLSAsymptoticVariance QXZ QZZ Omega QZX)) :=
  twoSLSBootstrapLinearRestrictionStdErrorFinSucc_tendstoInBootstrapProbability_formula
    (μ := μ) (Pstar := twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
    (fun n ω =>
      twoSLSBootstrapUniformPstarFinSucc_isProbabilityMeasure (Ω := Ω) n ω)
    hV

/-- Concrete robust bootstrap standard-error consistency from convergence of
the resampled robust 2SLS covariance estimator. -/
theorem
    twoSLSBootstrapRobustLinearRestrictionStdErrorFinSucc_tendstoInBootstrapProbability_formula
    {R : Matrix Unit k ℝ}
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {QXZ : Matrix k l ℝ} {QZZ Omega : Matrix l l ℝ} {QZX : Matrix l k ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hV :
      TendstoInBootstrapProbabilityIndexed μ Pstar
        (fun n ω ωs => twoSLSBootstrapVHatStarFinSucc Z X Y n ω ωs)
        (fun _ => twoSLSAsymptoticVariance QXZ QZZ Omega QZX)) :
    TendstoInBootstrapProbabilityIndexed μ Pstar
      (fun n ω ωs =>
        twoSLSBootstrapRobustLinearRestrictionStdErrorFinSucc R Z X Y n ω ωs)
      (fun _ =>
        linearRestrictionStdError R
          (twoSLSAsymptoticVariance QXZ QZZ Omega QZX)) := by
  simpa [twoSLSBootstrapRobustLinearRestrictionStdErrorFinSucc_eq_generic] using
    twoSLSBootstrapLinearRestrictionStdErrorFinSucc_tendstoInBootstrapProbability_formula
      (μ := μ) (Pstar := Pstar) (R := R)
      (Vstar := fun n ω ωs => twoSLSBootstrapVHatStarFinSucc Z X Y n ω ωs)
      (QXZ := QXZ) (QZZ := QZZ) (Omega := Omega) (QZX := QZX)
      hPstar hV

/-- Ordinary-bootstrap concrete robust standard-error consistency from
convergence of the resampled robust 2SLS covariance estimator. -/
theorem
    twoSLSBootstrapRobustLinearRestrictionStdErrorFinSucc_tendstoInBootstrapProbability_formula_uniform
    {R : Matrix Unit k ℝ}
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {QXZ : Matrix k l ℝ} {QZZ Omega : Matrix l l ℝ} {QZX : Matrix l k ℝ}
    (hV :
      TendstoInBootstrapProbabilityIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs => twoSLSBootstrapVHatStarFinSucc Z X Y n ω ωs)
        (fun _ => twoSLSAsymptoticVariance QXZ QZZ Omega QZX)) :
    TendstoInBootstrapProbabilityIndexed μ
      (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
      (fun n ω ωs =>
        twoSLSBootstrapRobustLinearRestrictionStdErrorFinSucc R Z X Y n ω ωs)
      (fun _ =>
        linearRestrictionStdError R
          (twoSLSAsymptoticVariance QXZ QZZ Omega QZX)) :=
  twoSLSBootstrapRobustLinearRestrictionStdErrorFinSucc_tendstoInBootstrapProbability_formula
    (μ := μ) (Pstar := twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
    (fun n ω =>
      twoSLSBootstrapUniformPstarFinSucc_isProbabilityMeasure (Ω := Ω) n ω)
    hV

/-- The remaining robust-covariance resampling input for Hansen Theorem 12.8.

The field states that recomputing the robust 2SLS covariance estimator on the
ordinary bootstrap sample is asymptotically equivalent, in bootstrap
probability, to the original-sample robust covariance estimator. -/
structure TwoSLSBootstrapRobustCovarianceResampleCloseness
    (μ : Measure Ω)
    (Z : ℕ → Ω → l → ℝ) (X : ℕ → Ω → k → ℝ) (Y : ℕ → Ω → ℝ) : Prop where
  covariance_closeness :
    TendstoInBootstrapProbabilityIndexed μ
      (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
      (fun n ω ωs =>
        twoSLSBootstrapVHatStarFinSucc Z X Y n ω ωs -
          twoSLSVHatStar
            (stackRegressors Z (n + 1) ω) (stackRegressors X (n + 1) ω)
            (stackOutcomes Y (n + 1) ω))
      (fun _ => 0)

namespace TwoSLSBootstrapRobustCovarianceResampleCloseness

set_option linter.style.longLine false in
/-- Robust covariance resampling closeness from original-sample and resampled
covariance consistency to the same limit.

This is the direct closeness bridge for the robust endpoint: once the
resampled robust covariance and the original robust covariance both converge
to `Vβ` in the appropriate bootstrap/original probability senses, their
difference is `o_{P*}(1)`. -/
theorem of_sample_and_bootstrap_consistency
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {Vβ : Matrix k k ℝ}
    (hV_sample : TendstoInMeasure μ
      (fun n ω =>
        twoSLSVHatStar
          (stackRegressors Z (n + 1) ω) (stackRegressors X (n + 1) ω)
          (stackOutcomes Y (n + 1) ω))
      atTop (fun _ => Vβ))
    (hV_boot :
      TendstoInBootstrapProbabilityIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs => twoSLSBootstrapVHatStarFinSucc Z X Y n ω ωs)
        (fun _ => Vβ)) :
    TwoSLSBootstrapRobustCovarianceResampleCloseness μ Z X Y where
  covariance_closeness := by
    have hPstar : ∀ n (ω : Ω),
        IsProbabilityMeasure
          (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω) n ω) :=
      fun n ω =>
        twoSLSBootstrapUniformPstarFinSucc_isProbabilityMeasure (Ω := Ω) n ω
    have hV_sample_boot :
        TendstoInBootstrapProbabilityIndexed μ
          (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
          (fun n ω _ =>
            twoSLSVHatStar
              (stackRegressors Z (n + 1) ω)
              (stackRegressors X (n + 1) ω)
              (stackOutcomes Y (n + 1) ω))
          (fun _ => Vβ) :=
      tendstoInBootstrapProbabilityIndexed_of_tendstoInMeasure
        (μ := μ) (Pstar := twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        hPstar hV_sample
    have hsub :=
      TendstoInBootstrapProbabilityIndexed.sub
        (μ := μ) (Pstar := twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        hPstar hV_boot hV_sample_boot
    exact hsub.congr
      (fun _ _ _ => rfl)
      (fun _ => by simp)

set_option linter.style.longLine false in
/-- Assumption-12.2-facing robust covariance resampling closeness from direct
resampled robust-covariance consistency.

Assumption 12.2 plus the Chapter 12 covariance weight WLLNs supply the
original-sample robust covariance limit; the remaining bootstrap input is only
the concrete resampled covariance consistency to the same formula limit. -/
theorem of_assumption12_2_iid_weight_wlln_bootstrap_consistency
    [IsProbabilityMeasure μ]
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    (h : TwoSLSAssumption12_2IidFourthConditions μ Z X e)
    (β : k → ℝ)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hw : TwoSLSCovarianceWeightWLLNConditions μ Z X e)
    (hV_boot :
      TendstoInBootstrapProbabilityIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs => twoSLSBootstrapVHatStarFinSucc Z X Y n ω ωs)
        (fun _ =>
          twoSLSAsymptoticVariance
            (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (scoreCovMat μ Z e)
            (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X))))) :
    TwoSLSBootstrapRobustCovarianceResampleCloseness μ Z X Y := by
  have hV_unshifted :=
    (twoSLSCovariances_tendstoInMeasure_formula_of_assumption12_2_iid_weight_wlln
      (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y) h β hmodel hw).1
  have hV_shifted : TendstoInMeasure μ
      (fun n ω =>
        twoSLSVHatStar
          (stackRegressors Z (n + 1) ω) (stackRegressors X (n + 1) ω)
          (stackOutcomes Y (n + 1) ω))
      atTop
      (fun _ =>
        twoSLSAsymptoticVariance
          (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
          (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
          (scoreCovMat μ Z e)
          (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))) := by
    intro ε hε
    simpa [stackRegressors, stackOutcomes] using
      (hV_unshifted ε hε).comp (tendsto_add_atTop_nat 1)
  exact
    of_sample_and_bootstrap_consistency
      (μ := μ) (Z := Z) (X := X) (Y := Y)
      (Vβ :=
        twoSLSAsymptoticVariance
          (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
          (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
          (scoreCovMat μ Z e)
          (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X))))
      hV_shifted hV_boot

set_option linter.style.longLine false in
/-- Mixed-moment Assumption-12.2 wrapper for robust covariance resampling
closeness from direct resampled robust-covariance consistency.

The mixed-moment package supplies the covariance weight WLLNs used for the
original-sample robust covariance limit. The only bootstrap covariance premise
left is consistency of the resampled robust covariance estimator to the same
Hansen formula limit. -/
theorem of_mixed_moment_conditions_bootstrap_consistency
    [IsProbabilityMeasure μ]
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    (h : TwoSLSAssumption12_2JointIidMixedMomentConditions μ Z X e)
    (β : k → ℝ)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hV_boot :
      TendstoInBootstrapProbabilityIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs => twoSLSBootstrapVHatStarFinSucc Z X Y n ω ωs)
        (fun _ =>
          twoSLSAsymptoticVariance
            (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (scoreCovMat μ Z e)
            (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X))))) :
    TwoSLSBootstrapRobustCovarianceResampleCloseness μ Z X Y :=
  of_assumption12_2_iid_weight_wlln_bootstrap_consistency
    (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y)
    h.toTwoSLSAssumption12_2JointIidFourthConditions.toIidFourthConditions
    β hmodel
    (h.toWeightWLLNConditions (μ := μ) (Z := Z) (X := X) (e := e))
    hV_boot

set_option linter.style.longLine false in
/-- Literal textbook-fourth Assumption-12.2 wrapper for robust covariance
resampling closeness from direct resampled robust-covariance consistency. -/
theorem of_textbook_fourth_bootstrap_consistency
    [IsProbabilityMeasure μ]
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {β : k → ℝ}
    (h : TwoSLSAssumption12_2JointIidTextbookFourthConditions μ Z X e Y β)
    (hV_boot :
      TendstoInBootstrapProbabilityIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs => twoSLSBootstrapVHatStarFinSucc Z X Y n ω ωs)
        (fun _ =>
          twoSLSAsymptoticVariance
            (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (scoreCovMat μ Z e)
            (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X))))) :
    TwoSLSBootstrapRobustCovarianceResampleCloseness μ Z X Y :=
  of_mixed_moment_conditions_bootstrap_consistency
    (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y)
    h.toJointIidMixedMomentConditions β h.model hV_boot

end TwoSLSBootstrapRobustCovarianceResampleCloseness

set_option linter.style.longLine false in
/-- Primitive robust-covariance resampling input for Hansen Theorem 12.8.

This states the empirical-process tail bound for the norm of the
resampled-minus-original robust covariance estimator. The named closeness
package below converts it to Chapter 10's bootstrap-probability interface. -/
structure TwoSLSBootstrapRobustCovarianceResamplePrimitiveInputs
    (μ : Measure Ω)
    (Z : ℕ → Ω → l → ℝ) (X : ℕ → Ω → k → ℝ) (Y : ℕ → Ω → ℝ) : Prop where
  covariance_tail : ∀ δ : ℝ, 0 < δ →
    TendstoInMeasure μ
      (fun n ω =>
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω) n ω).real
          {ωs |
            δ ≤
              ‖twoSLSBootstrapVHatStarFinSucc Z X Y n ω ωs -
                twoSLSVHatStar
                  (stackRegressors Z (n + 1) ω)
                  (stackRegressors X (n + 1) ω)
                  (stackOutcomes Y (n + 1) ω)‖})
      atTop (fun _ => 0)

namespace TwoSLSBootstrapRobustCovarianceResamplePrimitiveInputs

set_option linter.style.longLine false in
/-- Build primitive robust-covariance resampling inputs from an
empirical-process envelope bound.

The envelope `B` controls the norm of the resampled-minus-original robust
covariance estimator. Proving the bootstrap tail for `B` is the remaining
empirical-process task; this constructor performs the monotone tail transfer to
the concrete Hansen 12.8 covariance statistic. -/
theorem of_norm_bound
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {B : ∀ n, Ω → (Fin (n + 1) → Fin (n + 1)) → ℝ}
    (hBtail : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω) n ω).real
            {ωs | δ ≤ B n ω ωs})
        atTop (fun _ => 0))
    (hbound : ∀ n ω (ωs : Fin (n + 1) → Fin (n + 1)),
      ‖twoSLSBootstrapVHatStarFinSucc Z X Y n ω ωs -
        twoSLSVHatStar
          (stackRegressors Z (n + 1) ω)
          (stackRegressors X (n + 1) ω)
          (stackOutcomes Y (n + 1) ω)‖ ≤ B n ω ωs) :
    TwoSLSBootstrapRobustCovarianceResamplePrimitiveInputs μ Z X Y where
  covariance_tail :=
    indexed_bootstrap_tail_of_bound
      (μ := μ) (Pstar := twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
      (S := fun n ω ωs =>
        ‖twoSLSBootstrapVHatStarFinSucc Z X Y n ω ωs -
          twoSLSVHatStar
            (stackRegressors Z (n + 1) ω)
            (stackRegressors X (n + 1) ω)
            (stackOutcomes Y (n + 1) ω)‖)
      (T := B)
      (fun n ω =>
        twoSLSBootstrapUniformPstarFinSucc_isProbabilityMeasure (Ω := Ω) n ω)
      hbound hBtail

set_option linter.style.longLine false in
/-- Primitive robust-covariance resampling control from a uniform `o(1)`
pathwise bound.

This avoids introducing a separate scalar covariance envelope when the
resampled-minus-original robust covariance norm is already known to vanish
uniformly over original samples and resamples. -/
theorem of_uniform_norm_vanish
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    (hsmall : ∀ δ : ℝ, 0 < δ →
      ∀ᶠ n in atTop,
        ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
          ‖twoSLSBootstrapVHatStarFinSucc Z X Y n ω ωs -
            twoSLSVHatStar
              (stackRegressors Z (n + 1) ω)
              (stackRegressors X (n + 1) ω)
              (stackOutcomes Y (n + 1) ω)‖ < δ) :
    TwoSLSBootstrapRobustCovarianceResamplePrimitiveInputs μ Z X Y where
  covariance_tail :=
    indexed_bootstrap_tail_of_eventually_lt
      (μ := μ) (Pstar := twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
      (B := fun n ω ωs =>
        ‖twoSLSBootstrapVHatStarFinSucc Z X Y n ω ωs -
          twoSLSVHatStar
            (stackRegressors Z (n + 1) ω)
            (stackRegressors X (n + 1) ω)
            (stackOutcomes Y (n + 1) ω)‖)
      hsmall

set_option linter.style.longLine false in
/-- Convert primitive norm-tail covariance resampling control to the named
bootstrap-probability closeness package. -/
theorem toResampleCloseness
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    (h : TwoSLSBootstrapRobustCovarianceResamplePrimitiveInputs μ Z X Y) :
    TwoSLSBootstrapRobustCovarianceResampleCloseness μ Z X Y where
  covariance_closeness := by
    intro δ hδ
    simpa [TendstoInBootstrapProbabilityIndexed, bootstrapTailProbIndexed,
      dist_zero_right] using h.covariance_tail δ hδ

end TwoSLSBootstrapRobustCovarianceResamplePrimitiveInputs

/-- Concrete robust bootstrap covariance consistency from original-sample
covariance consistency plus resampling stability.

The first premise is an ordinary-sample Hansen 12.3 covariance consistency
statement, shifted to the `Fin (n+1)` indexing used by Chapter 10. The second
premise is the genuinely bootstrap part: the robust covariance recomputed on
the resampled triples is asymptotically close, in bootstrap probability, to
the original-sample robust covariance. Together they give the concrete
ordinary-bootstrap covariance input required by Hansen Theorem 12.8, without
assuming standard-error or t-statistic consistency directly. -/
theorem
    twoSLSBootstrapVHatStarFinSucc_tendstoInBootstrapProbability_uniform_of_sample_and_resample_closeness
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {Vβ : Matrix k k ℝ}
    (hV_sample : TendstoInMeasure μ
      (fun n ω =>
        twoSLSVHatStar
          (stackRegressors Z (n + 1) ω) (stackRegressors X (n + 1) ω)
          (stackOutcomes Y (n + 1) ω))
      atTop (fun _ => Vβ))
    (hV_resample_close :
      TendstoInBootstrapProbabilityIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs =>
          twoSLSBootstrapVHatStarFinSucc Z X Y n ω ωs -
            twoSLSVHatStar
              (stackRegressors Z (n + 1) ω) (stackRegressors X (n + 1) ω)
              (stackOutcomes Y (n + 1) ω))
        (fun _ => 0)) :
    TendstoInBootstrapProbabilityIndexed μ
      (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
      (fun n ω ωs => twoSLSBootstrapVHatStarFinSucc Z X Y n ω ωs)
      (fun _ => Vβ) := by
  have hPstar : ∀ n (ω : Ω),
      IsProbabilityMeasure (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω) n ω) :=
    fun n ω => twoSLSBootstrapUniformPstarFinSucc_isProbabilityMeasure (Ω := Ω) n ω
  have hV_sample_boot :
      TendstoInBootstrapProbabilityIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω _ =>
          twoSLSVHatStar
            (stackRegressors Z (n + 1) ω) (stackRegressors X (n + 1) ω)
            (stackOutcomes Y (n + 1) ω))
        (fun _ => Vβ) :=
    tendstoInBootstrapProbabilityIndexed_of_tendstoInMeasure
      (μ := μ) (Pstar := twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
      hPstar hV_sample
  have hsum :=
    TendstoInBootstrapProbabilityIndexed.add
      (μ := μ) (Pstar := twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
      hPstar hV_resample_close hV_sample_boot
  exact hsum.congr
    (fun n ω ωs => by simp)
    (fun _ => by simp)

/-- Assumption-12.2-facing robust bootstrap covariance consistency.

Primitive iid finite-fourth Assumption 12.2 and the existing Chapter 12
weight-WLLN constructor give the original-sample Hansen 12.3 robust covariance
limit. The only remaining bootstrap-specific input is the concrete
resampled-vs-original covariance closeness field. -/
theorem
    twoSLSBootstrapVHatStarFinSucc_tendstoInBootstrapProbability_formula_uniform_of_assumption12_2_iid_weight_wlln
    [IsProbabilityMeasure μ]
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    (h : TwoSLSAssumption12_2IidFourthConditions μ Z X e)
    (β : k → ℝ)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hw : TwoSLSCovarianceWeightWLLNConditions μ Z X e)
    (hV_resample_close :
      TendstoInBootstrapProbabilityIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs =>
          twoSLSBootstrapVHatStarFinSucc Z X Y n ω ωs -
            twoSLSVHatStar
              (stackRegressors Z (n + 1) ω) (stackRegressors X (n + 1) ω)
              (stackOutcomes Y (n + 1) ω))
        (fun _ => 0)) :
    TendstoInBootstrapProbabilityIndexed μ
      (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
      (fun n ω ωs => twoSLSBootstrapVHatStarFinSucc Z X Y n ω ωs)
      (fun _ =>
        twoSLSAsymptoticVariance
          (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
          (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
          (scoreCovMat μ Z e)
          (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))) := by
  have hV_unshifted :=
    (twoSLSCovariances_tendstoInMeasure_formula_of_assumption12_2_iid_weight_wlln
      (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y) h β hmodel hw).1
  have hV_shifted : TendstoInMeasure μ
      (fun n ω =>
        twoSLSVHatStar
          (stackRegressors Z (n + 1) ω) (stackRegressors X (n + 1) ω)
          (stackOutcomes Y (n + 1) ω))
      atTop
      (fun _ =>
        twoSLSAsymptoticVariance
          (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
          (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
          (scoreCovMat μ Z e)
          (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))) := by
    intro ε hε
    simpa [stackRegressors, stackOutcomes] using
      (hV_unshifted ε hε).comp (tendsto_add_atTop_nat 1)
  exact
    twoSLSBootstrapVHatStarFinSucc_tendstoInBootstrapProbability_uniform_of_sample_and_resample_closeness
      (μ := μ) (Z := Z) (X := X) (Y := Y)
      (Vβ :=
        twoSLSAsymptoticVariance
          (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
          (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
          (scoreCovMat μ Z e)
          (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X))))
      hV_shifted hV_resample_close

/-- Assumption-12.2-facing robust covariance consistency using the named
resampled-vs-original covariance closeness package. -/
theorem
    twoSLSBootstrapVHatStarFinSucc_tendstoInBootstrapProbability_formula_uniform_of_assumption12_2_iid_weight_wlln_resampleCloseness
    [IsProbabilityMeasure μ]
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    (h : TwoSLSAssumption12_2IidFourthConditions μ Z X e)
    (β : k → ℝ)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hw : TwoSLSCovarianceWeightWLLNConditions μ Z X e)
    (hV : TwoSLSBootstrapRobustCovarianceResampleCloseness μ Z X Y) :
    TendstoInBootstrapProbabilityIndexed μ
      (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
      (fun n ω ωs => twoSLSBootstrapVHatStarFinSucc Z X Y n ω ωs)
      (fun _ =>
        twoSLSAsymptoticVariance
          (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
          (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
          (scoreCovMat μ Z e)
          (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))) :=
  twoSLSBootstrapVHatStarFinSucc_tendstoInBootstrapProbability_formula_uniform_of_assumption12_2_iid_weight_wlln
    (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y)
    h β hmodel hw hV.covariance_closeness

set_option linter.style.longLine false in
/-- Assumption-12.2-facing robust bootstrap covariance consistency from the
primitive covariance-resampling tail package.

This is the covariance part of Hansen Theorem 12.8 with the resampling input
kept at the empirical-process tail level: the primitive norm-tail package is
converted to the named resampled-vs-original closeness package and then
composed with the existing Chapter 12 covariance WLLN bridge. -/
theorem
    twoSLSBootstrapVHatStarFinSucc_tendstoInBootstrapProbability_formula_uniform_of_assumption12_2_iid_weight_wlln_resamplePrimitive
    [IsProbabilityMeasure μ]
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    (h : TwoSLSAssumption12_2IidFourthConditions μ Z X e)
    (β : k → ℝ)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hw : TwoSLSCovarianceWeightWLLNConditions μ Z X e)
    (hV : TwoSLSBootstrapRobustCovarianceResamplePrimitiveInputs μ Z X Y) :
    TendstoInBootstrapProbabilityIndexed μ
      (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
      (fun n ω ωs => twoSLSBootstrapVHatStarFinSucc Z X Y n ω ωs)
      (fun _ =>
        twoSLSAsymptoticVariance
          (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
          (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
          (scoreCovMat μ Z e)
          (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))) :=
  twoSLSBootstrapVHatStarFinSucc_tendstoInBootstrapProbability_formula_uniform_of_assumption12_2_iid_weight_wlln_resampleCloseness
    (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y)
    h β hmodel hw
    (hV.toResampleCloseness
      (μ := μ) (Z := Z) (X := X) (Y := Y))

/-- Hansen Theorem 12.8 scalar one-row numerator endpoint. This is just the
coefficient bootstrap CLT passed through the fixed restriction map
`b ↦ R b`; no bootstrap theory is duplicated here. -/
theorem twoSLSBootstrapLinearRestrictionStatisticFinSucc_tendstoInBootstrapWeakDistribution
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {R : Matrix Unit k ℝ} {Vβ : Matrix k k ℝ}
    (h : TwoSLSBootstrapAsymptoticNormalConditions μ Pstar Z X Y Vβ) :
    TendstoInBootstrapWeakDistributionIndexed μ Pstar
      (fun n ω ωs =>
        twoSLSBootstrapLinearRestrictionStatisticFinSucc R Z X Y n ω ωs)
      (multivariateGaussian (0 : EuclideanSpace ℝ k) Vβ)
      (fun z : EuclideanSpace ℝ k =>
        linearRestrictionEstimate R (z : k → ℝ)) := by
  have hβ :=
    twoSLSBootstrapBetaGapFinSucc_tendstoInBootstrapWeakDistribution
      (μ := μ) (Pstar := Pstar) h
  simpa [twoSLSBootstrapLinearRestrictionStatisticFinSucc] using
    chapter10_indexed_bootstrap_continuous_mapping_distribution
      (μ := μ) (Pstar := Pstar)
      (Zstar := fun n ω ωs => twoSLSBootstrapBetaGapFinSucc Z X Y n ω ωs)
      (ν := multivariateGaussian (0 : EuclideanSpace ℝ k) Vβ)
      (Z := fun z : EuclideanSpace ℝ k => (z : k → ℝ))
      (g := linearRestrictionEstimate R) hβ
      (continuous_linearRestrictionEstimate R)

/-- Formula-covariance version of the scalar one-row numerator endpoint. -/
theorem
    twoSLSBootstrapLinearRestrictionStatisticFinSucc_tendstoInBootstrapWeakDistribution_formula
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {R : Matrix Unit k ℝ}
    {QXZ : Matrix k l ℝ} {QZZ Omega : Matrix l l ℝ} {QZX : Matrix l k ℝ}
    (h : TwoSLSBootstrapFormulaAsymptoticNormalConditions
      μ Pstar Z X Y QXZ QZZ Omega QZX) :
    TendstoInBootstrapWeakDistributionIndexed μ Pstar
      (fun n ω ωs =>
        twoSLSBootstrapLinearRestrictionStatisticFinSucc R Z X Y n ω ωs)
      (multivariateGaussian (0 : EuclideanSpace ℝ k)
        (twoSLSAsymptoticVariance QXZ QZZ Omega QZX))
      (fun z : EuclideanSpace ℝ k =>
        linearRestrictionEstimate R (z : k → ℝ)) :=
  twoSLSBootstrapLinearRestrictionStatisticFinSucc_tendstoInBootstrapWeakDistribution
    (μ := μ) (Pstar := Pstar) h

/-- Ordinary-bootstrap version of the scalar one-row numerator endpoint. -/
theorem
    twoSLSBootstrapLinearRestrictionStatisticFinSucc_tendstoInBootstrapWeakDistribution_uniform
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {R : Matrix Unit k ℝ} {Vβ : Matrix k k ℝ}
    (h : TwoSLSBootstrapAsymptoticNormalConditions μ
      (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω)) Z X Y Vβ) :
    TendstoInBootstrapWeakDistributionIndexed μ
      (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
      (fun n ω ωs =>
        twoSLSBootstrapLinearRestrictionStatisticFinSucc R Z X Y n ω ωs)
      (multivariateGaussian (0 : EuclideanSpace ℝ k) Vβ)
      (fun z : EuclideanSpace ℝ k =>
        linearRestrictionEstimate R (z : k → ℝ)) :=
  twoSLSBootstrapLinearRestrictionStatisticFinSucc_tendstoInBootstrapWeakDistribution
    (μ := μ) (Pstar := twoSLSBootstrapUniformPstarFinSucc (Ω := Ω)) h

/-- Ordinary-bootstrap, formula-covariance version of the scalar one-row
numerator endpoint. -/
theorem
    twoSLSBootstrapLinearRestrictionStatisticFinSucc_tendstoInBootstrapWeakDistribution_formula_uniform
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {R : Matrix Unit k ℝ}
    {QXZ : Matrix k l ℝ} {QZZ Omega : Matrix l l ℝ} {QZX : Matrix l k ℝ}
    (h : TwoSLSBootstrapFormulaAsymptoticNormalConditions μ
      (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω)) Z X Y
      QXZ QZZ Omega QZX) :
    TendstoInBootstrapWeakDistributionIndexed μ
      (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
      (fun n ω ωs =>
        twoSLSBootstrapLinearRestrictionStatisticFinSucc R Z X Y n ω ωs)
      (multivariateGaussian (0 : EuclideanSpace ℝ k)
        (twoSLSAsymptoticVariance QXZ QZZ Omega QZX))
      (fun z : EuclideanSpace ℝ k =>
        linearRestrictionEstimate R (z : k → ℝ)) :=
  twoSLSBootstrapLinearRestrictionStatisticFinSucc_tendstoInBootstrapWeakDistribution_formula
    (μ := μ) (Pstar := twoSLSBootstrapUniformPstarFinSucc (Ω := Ω)) h

set_option linter.style.longLine false in
/-- Law of a fixed one-row linear restriction of a centered Gaussian vector.

This is the non-studentized scalar-law counterpart of the standard-normal
restriction bridge below. -/
theorem linearRestrictionEstimate_hasLaw_gaussianReal_of_posSemidef
    {R : Matrix Unit k ℝ} {Vβ : Matrix k k ℝ}
    (hVβ : Vβ.PosSemidef) :
    HasLaw
      (fun z : EuclideanSpace ℝ k =>
        linearRestrictionEstimate R (z : k → ℝ))
      (gaussianReal 0 (linearRestrictionStdError R Vβ ^ 2).toNNReal)
      (multivariateGaussian (0 : EuclideanSpace ℝ k) Vβ) := by
  let S : Matrix Unit Unit ℝ := R * Vβ * Rᵀ
  have hS : S.PosSemidef := by
    simpa [S, Matrix.conjTranspose] using
      Matrix.PosSemidef.conjTranspose_mul_mul_same hVβ Rᵀ
  have hlinLaw :
      HasLaw (fun z : EuclideanSpace ℝ k => WithLp.toLp 2 (R *ᵥ z.ofLp))
        (multivariateGaussian (0 : EuclideanSpace ℝ Unit) S)
        (multivariateGaussian (0 : EuclideanSpace ℝ k) Vβ) := by
    simpa [S] using
      hasLaw_multivariateGaussian_zero_linearMap
        (n := k) (q := Unit) hVβ R
  have hcoordLawUnit :
      HasLaw (fun z : EuclideanSpace ℝ Unit => z.ofLp ())
        (gaussianReal 0 (S () ()).toNNReal)
        (multivariateGaussian (0 : EuclideanSpace ℝ Unit) S) := by
    simpa using
      multivariateGaussian_eval_hasLaw
        (μ := (0 : EuclideanSpace ℝ Unit)) (S := S) hS ()
  have hcoordLaw :
      HasLaw
        (fun z : EuclideanSpace ℝ k =>
          (WithLp.toLp 2 (R *ᵥ z.ofLp) : EuclideanSpace ℝ Unit).ofLp ())
        (gaussianReal 0 (S () ()).toNNReal)
        (multivariateGaussian (0 : EuclideanSpace ℝ k) Vβ) := by
    simpa [Function.comp_def] using HasLaw.comp hcoordLawUnit hlinLaw
  have hZlaw :
      HasLaw
        (fun z : EuclideanSpace ℝ k =>
          linearRestrictionEstimate R (z : k → ℝ))
        (gaussianReal 0 (S () ()).toNNReal)
        (multivariateGaussian (0 : EuclideanSpace ℝ k) Vβ) := by
    refine hcoordLaw.congr ?_
    filter_upwards with z
    simp [linearRestrictionEstimate]
  have hσ :
      S () () = linearRestrictionStdError R Vβ ^ 2 := by
    simpa [S, linearRestrictionStdError] using
      (Real.sq_sqrt (hS.diag_nonneg (i := ()))).symm
  rw [hσ] at hZlaw
  exact hZlaw

/-- Standard-normal scalar numerator bridge for Hansen Theorem 12.8.

The coefficient bootstrap CLT implies the one-row restriction numerator CLT in
the studentized scale.  The only extra input is positive semidefiniteness of
the coefficient covariance, used to identify the scalar linear image of the
Gaussian limit with `seθ * N(0,1)`. -/
theorem
    twoSLSBootstrapLinearRestrictionStatisticFinSucc_tendstoInBootstrapWeakDistribution_standardNormal_of_coefficient
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {R : Matrix Unit k ℝ} {Vβ : Matrix k k ℝ}
    (hVβ : Vβ.PosSemidef)
    (hβ :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar
        (fun n ω ωs => twoSLSBootstrapBetaGapFinSucc Z X Y n ω ωs)
        (multivariateGaussian (0 : EuclideanSpace ℝ k) Vβ)
        (fun z : EuclideanSpace ℝ k => (z : k → ℝ))) :
    TendstoInBootstrapWeakDistributionIndexed μ Pstar
      (fun n ω ωs =>
        twoSLSBootstrapLinearRestrictionStatisticFinSucc R Z X Y n ω ωs)
      (gaussianReal 0 1)
      (fun z : ℝ => linearRestrictionStdError R Vβ * z) := by
  have hlinear :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar
        (fun n ω ωs =>
          twoSLSBootstrapLinearRestrictionStatisticFinSucc R Z X Y n ω ωs)
        (multivariateGaussian (0 : EuclideanSpace ℝ k) Vβ)
        (fun z : EuclideanSpace ℝ k =>
          linearRestrictionEstimate R (z : k → ℝ)) := by
    simpa [twoSLSBootstrapLinearRestrictionStatisticFinSucc] using
      chapter10_indexed_bootstrap_continuous_mapping_distribution
        (μ := μ) (Pstar := Pstar)
        (Zstar := fun n ω ωs => twoSLSBootstrapBetaGapFinSucc Z X Y n ω ωs)
        (ν := multivariateGaussian (0 : EuclideanSpace ℝ k) Vβ)
        (Z := fun z : EuclideanSpace ℝ k => (z : k → ℝ))
        (g := linearRestrictionEstimate R) hβ
        (continuous_linearRestrictionEstimate R)
  have hZlaw :
      HasLaw
        (fun z : EuclideanSpace ℝ k =>
          linearRestrictionEstimate R (z : k → ℝ))
        (gaussianReal 0 (linearRestrictionStdError R Vβ ^ 2).toNNReal)
        (multivariateGaussian (0 : EuclideanSpace ℝ k) Vβ) :=
    linearRestrictionEstimate_hasLaw_gaussianReal_of_posSemidef
      (R := R) hVβ
  have hstdLaw :
      HasLaw (fun z : ℝ => linearRestrictionStdError R Vβ * z)
        (gaussianReal 0 (linearRestrictionStdError R Vβ ^ 2).toNNReal)
        (gaussianReal 0 1) :=
    hasLaw_const_mul_id_gaussianReal_of_variance_eq rfl
  exact hlinear.congr_limit_law hZlaw hstdLaw

/-- Hansen Theorem 12.8 scalar numerator endpoint, derived from the
coefficient bootstrap condition package rather than assumed separately. -/
theorem
    twoSLSBootstrapLinearRestrictionStatisticFinSucc_tendstoInBootstrapWeakDistribution_standardNormal
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {R : Matrix Unit k ℝ} {Vβ : Matrix k k ℝ}
    (hVβ : Vβ.PosSemidef)
    (h : TwoSLSBootstrapAsymptoticNormalConditions μ Pstar Z X Y Vβ) :
    TendstoInBootstrapWeakDistributionIndexed μ Pstar
      (fun n ω ωs =>
        twoSLSBootstrapLinearRestrictionStatisticFinSucc R Z X Y n ω ωs)
      (gaussianReal 0 1)
      (fun z : ℝ => linearRestrictionStdError R Vβ * z) :=
  twoSLSBootstrapLinearRestrictionStatisticFinSucc_tendstoInBootstrapWeakDistribution_standardNormal_of_coefficient
    (μ := μ) (Pstar := Pstar) hVβ
    (twoSLSBootstrapBetaGapFinSucc_tendstoInBootstrapWeakDistribution
      (μ := μ) (Pstar := Pstar) h)

/-- Formula-covariance version of the standard-normal scalar numerator
endpoint for Hansen Theorem 12.8. -/
theorem
    twoSLSBootstrapLinearRestrictionStatisticFinSucc_tendstoInBootstrapWeakDistribution_standardNormal_formula
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {R : Matrix Unit k ℝ}
    {QXZ : Matrix k l ℝ} {QZZ Omega : Matrix l l ℝ} {QZX : Matrix l k ℝ}
    (hVβ : (twoSLSAsymptoticVariance QXZ QZZ Omega QZX).PosSemidef)
    (h : TwoSLSBootstrapFormulaAsymptoticNormalConditions
      μ Pstar Z X Y QXZ QZZ Omega QZX) :
    TendstoInBootstrapWeakDistributionIndexed μ Pstar
      (fun n ω ωs =>
        twoSLSBootstrapLinearRestrictionStatisticFinSucc R Z X Y n ω ωs)
      (gaussianReal 0 1)
      (fun z : ℝ =>
        linearRestrictionStdError R
          (twoSLSAsymptoticVariance QXZ QZZ Omega QZX) * z) :=
  twoSLSBootstrapLinearRestrictionStatisticFinSucc_tendstoInBootstrapWeakDistribution_standardNormal
    (μ := μ) (Pstar := Pstar)
    (Vβ := twoSLSAsymptoticVariance QXZ QZZ Omega QZX) hVβ h

/-- Ordinary-bootstrap, formula-covariance version of the standard-normal
scalar numerator endpoint for Hansen Theorem 12.8. -/
theorem
    twoSLSBootstrapLinearRestrictionStatisticFinSucc_tendstoInBootstrapWeakDistribution_standardNormal_formula_uniform
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {R : Matrix Unit k ℝ}
    {QXZ : Matrix k l ℝ} {QZZ Omega : Matrix l l ℝ} {QZX : Matrix l k ℝ}
    (hVβ : (twoSLSAsymptoticVariance QXZ QZZ Omega QZX).PosSemidef)
    (h : TwoSLSBootstrapFormulaAsymptoticNormalConditions μ
      (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω)) Z X Y
      QXZ QZZ Omega QZX) :
    TendstoInBootstrapWeakDistributionIndexed μ
      (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
      (fun n ω ωs =>
        twoSLSBootstrapLinearRestrictionStatisticFinSucc R Z X Y n ω ωs)
      (gaussianReal 0 1)
      (fun z : ℝ =>
        linearRestrictionStdError R
          (twoSLSAsymptoticVariance QXZ QZZ Omega QZX) * z) :=
  twoSLSBootstrapLinearRestrictionStatisticFinSucc_tendstoInBootstrapWeakDistribution_standardNormal_formula
    (μ := μ) (Pstar := twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
    hVβ h

/-- Hansen Theorem 12.8 bootstrap t-ratio endpoint. The hard IV work is the
joint bootstrap weak limit for the scalar numerator and feasible standard
error, plus bootstrap-probability consistency of that standard error. The
studentization step is exactly the Chapter 10 generic indexed regression
studentization theorem. -/
theorem twoSLSBootstrapLinearTStatFinSucc_tendstoInBootstrapDistribution_standardNormal
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {R : Matrix Unit k ℝ}
    {Vβ : Matrix k k ℝ}
    {Vstar : ∀ n, Ω → (Fin (n + 1) → Fin (n + 1)) → Matrix k k ℝ}
    (hseθ : 0 < linearRestrictionStdError R Vβ)
    (hjoint :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar
        (fun n ω ωs =>
          (twoSLSBootstrapLinearRestrictionStatisticFinSucc R Z X Y n ω ωs,
            twoSLSBootstrapLinearRestrictionStdErrorFinSucc R Vstar n ω ωs))
        (gaussianReal 0 1)
        (fun z : ℝ => (linearRestrictionStdError R Vβ * z,
          linearRestrictionStdError R Vβ)))
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hT : ∀ n ω,
      Measurable
        (fun ωs => twoSLSBootstrapLinearRestrictionStatisticFinSucc R Z X Y n ω ωs))
    (hse : ∀ n ω,
      Measurable
        (fun ωs => twoSLSBootstrapLinearRestrictionStdErrorFinSucc R Vstar n ω ωs))
    (hse_consistent :
      TendstoInBootstrapProbabilityIndexed μ Pstar
        (fun n ω ωs =>
          twoSLSBootstrapLinearRestrictionStdErrorFinSucc R Vstar n ω ωs)
        (fun _ => linearRestrictionStdError R Vβ)) :
    TendstoInBootstrapDistributionIndexed μ Pstar
      (fun n ω ωs (_ : Unit) =>
        twoSLSBootstrapLinearTStatFinSucc R Z X Y Vstar n ω ωs)
      (gaussianReal 0 1) (fun z : ℝ => fun _ : Unit => z) := by
  simpa [twoSLSBootstrapLinearTStatFinSucc] using
    chapter10_indexed_bootstrap_regression_tstat_distribution_standardNormal
      (μ := μ) (Pstar := Pstar)
      (TthetaStar := fun n ω ωs =>
        twoSLSBootstrapLinearRestrictionStatisticFinSucc R Z X Y n ω ωs)
      (seThetaStar := fun n ω ωs =>
        twoSLSBootstrapLinearRestrictionStdErrorFinSucc R Vstar n ω ωs)
      (seθ := linearRestrictionStdError R Vβ)
      hseθ hjoint hPstar hT hse hse_consistent

/-- Formula-covariance version of Hansen Theorem 12.8's bootstrap t-ratio
endpoint. The limiting standard-error scale is computed from Hansen's
displayed robust 2SLS covariance formula. -/
theorem
    twoSLSBootstrapLinearTStatFinSucc_tendstoInBootstrapDistribution_standardNormal_formula
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {R : Matrix Unit k ℝ}
    {QXZ : Matrix k l ℝ} {QZZ Omega : Matrix l l ℝ} {QZX : Matrix l k ℝ}
    {Vstar : ∀ n, Ω → (Fin (n + 1) → Fin (n + 1)) → Matrix k k ℝ}
    (hseθ : 0 <
      linearRestrictionStdError R (twoSLSAsymptoticVariance QXZ QZZ Omega QZX))
    (hjoint :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar
        (fun n ω ωs =>
          (twoSLSBootstrapLinearRestrictionStatisticFinSucc R Z X Y n ω ωs,
            twoSLSBootstrapLinearRestrictionStdErrorFinSucc R Vstar n ω ωs))
        (gaussianReal 0 1)
        (fun z : ℝ =>
          (linearRestrictionStdError R
              (twoSLSAsymptoticVariance QXZ QZZ Omega QZX) * z,
            linearRestrictionStdError R
              (twoSLSAsymptoticVariance QXZ QZZ Omega QZX))))
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hT : ∀ n ω,
      Measurable
        (fun ωs => twoSLSBootstrapLinearRestrictionStatisticFinSucc R Z X Y n ω ωs))
    (hse : ∀ n ω,
      Measurable
        (fun ωs => twoSLSBootstrapLinearRestrictionStdErrorFinSucc R Vstar n ω ωs))
    (hse_consistent :
      TendstoInBootstrapProbabilityIndexed μ Pstar
        (fun n ω ωs =>
          twoSLSBootstrapLinearRestrictionStdErrorFinSucc R Vstar n ω ωs)
        (fun _ =>
          linearRestrictionStdError R
            (twoSLSAsymptoticVariance QXZ QZZ Omega QZX))) :
    TendstoInBootstrapDistributionIndexed μ Pstar
      (fun n ω ωs (_ : Unit) =>
        twoSLSBootstrapLinearTStatFinSucc R Z X Y Vstar n ω ωs)
      (gaussianReal 0 1) (fun z : ℝ => fun _ : Unit => z) :=
  twoSLSBootstrapLinearTStatFinSucc_tendstoInBootstrapDistribution_standardNormal
    (μ := μ) (Pstar := Pstar) (Vβ := twoSLSAsymptoticVariance QXZ QZZ Omega QZX)
    hseθ hjoint hPstar hT hse hse_consistent

/-- Ordinary-bootstrap formula-covariance version of Hansen Theorem 12.8's
bootstrap t-ratio endpoint. -/
theorem
    twoSLSBootstrapLinearTStatFinSucc_tendstoInBootstrapDistribution_standardNormal_formula_uniform
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {R : Matrix Unit k ℝ}
    {QXZ : Matrix k l ℝ} {QZZ Omega : Matrix l l ℝ} {QZX : Matrix l k ℝ}
    {Vstar : ∀ n, Ω → (Fin (n + 1) → Fin (n + 1)) → Matrix k k ℝ}
    (hseθ : 0 <
      linearRestrictionStdError R (twoSLSAsymptoticVariance QXZ QZZ Omega QZX))
    (hjoint :
      TendstoInBootstrapWeakDistributionIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs =>
          (twoSLSBootstrapLinearRestrictionStatisticFinSucc R Z X Y n ω ωs,
            twoSLSBootstrapLinearRestrictionStdErrorFinSucc R Vstar n ω ωs))
        (gaussianReal 0 1)
        (fun z : ℝ =>
          (linearRestrictionStdError R
              (twoSLSAsymptoticVariance QXZ QZZ Omega QZX) * z,
            linearRestrictionStdError R
              (twoSLSAsymptoticVariance QXZ QZZ Omega QZX))))
    (hT : ∀ n ω,
      Measurable
        (fun ωs => twoSLSBootstrapLinearRestrictionStatisticFinSucc R Z X Y n ω ωs))
    (hse : ∀ n ω,
      Measurable
        (fun ωs => twoSLSBootstrapLinearRestrictionStdErrorFinSucc R Vstar n ω ωs))
    (hse_consistent :
      TendstoInBootstrapProbabilityIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs =>
          twoSLSBootstrapLinearRestrictionStdErrorFinSucc R Vstar n ω ωs)
        (fun _ =>
          linearRestrictionStdError R
            (twoSLSAsymptoticVariance QXZ QZZ Omega QZX))) :
    TendstoInBootstrapDistributionIndexed μ
      (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
      (fun n ω ωs (_ : Unit) =>
        twoSLSBootstrapLinearTStatFinSucc R Z X Y Vstar n ω ωs)
      (gaussianReal 0 1) (fun z : ℝ => fun _ : Unit => z) :=
  twoSLSBootstrapLinearTStatFinSucc_tendstoInBootstrapDistribution_standardNormal_formula
    (μ := μ) (Pstar := twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
    hseθ hjoint
    (fun n ω =>
      twoSLSBootstrapUniformPstarFinSucc_isProbabilityMeasure (Ω := Ω) n ω)
    hT hse hse_consistent

/-- Hansen Theorem 12.8 bootstrap t-ratio endpoint from a marginal numerator
CLT plus feasible-standard-error consistency. This delegates the Slutsky /
studentization step to the Chapter 10 indexed regression theorem, leaving the
IV-specific numerator CLT and standard-error consistency as explicit premises. -/
theorem
    twoSLSBootstrapLinearTStatFinSucc_tendstoInBootstrapDistribution_of_numerator_tight
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {R : Matrix Unit k ℝ}
    {Vβ : Matrix k k ℝ}
    {Vstar : ∀ n, Ω → (Fin (n + 1) → Fin (n + 1)) → Matrix k k ℝ}
    (hseθ : 0 < linearRestrictionStdError R Vβ)
    (hT :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar
        (fun n ω ωs =>
          twoSLSBootstrapLinearRestrictionStatisticFinSucc R Z X Y n ω ωs)
        (gaussianReal 0 1)
        (fun z : ℝ => linearRestrictionStdError R Vβ * z))
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hT_meas : ∀ n ω,
      Measurable
        (fun ωs => twoSLSBootstrapLinearRestrictionStatisticFinSucc R Z X Y n ω ωs))
    (hse_meas : ∀ n ω,
      Measurable
        (fun ωs => twoSLSBootstrapLinearRestrictionStdErrorFinSucc R Vstar n ω ωs))
    (hTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set (ℝ × ℝ), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω =>
            (Pstar n ω).real
              {ωs |
                (twoSLSBootstrapLinearRestrictionStatisticFinSucc R Z X Y n ω ωs,
                  linearRestrictionStdError R Vβ) ∉ K})
          atTop (fun _ => 0) ∧
        TendstoInMeasure μ
          (fun n ω =>
            (Pstar n ω).real
              {ωs |
                (twoSLSBootstrapLinearRestrictionStatisticFinSucc R Z X Y n ω ωs,
                  twoSLSBootstrapLinearRestrictionStdErrorFinSucc R Vstar n ω ωs) ∉ K})
          atTop (fun _ => 0))
    (hse_consistent :
      TendstoInBootstrapProbabilityIndexed μ Pstar
        (fun n ω ωs =>
          twoSLSBootstrapLinearRestrictionStdErrorFinSucc R Vstar n ω ωs)
        (fun _ => linearRestrictionStdError R Vβ)) :
    TendstoInBootstrapDistributionIndexed μ Pstar
      (fun n ω ωs (_ : Unit) =>
        twoSLSBootstrapLinearTStatFinSucc R Z X Y Vstar n ω ωs)
      (gaussianReal 0 1) (fun z : ℝ => fun _ : Unit => z) := by
  simpa [twoSLSBootstrapLinearTStatFinSucc] using
    chapter10_indexed_bootstrap_regression_tstat_distribution_standardNormal_of_numerator_tight
      (μ := μ) (Pstar := Pstar)
      (TthetaStar := fun n ω ωs =>
        twoSLSBootstrapLinearRestrictionStatisticFinSucc R Z X Y n ω ωs)
      (seThetaStar := fun n ω ωs =>
        twoSLSBootstrapLinearRestrictionStdErrorFinSucc R Vstar n ω ωs)
      (seθ := linearRestrictionStdError R Vβ)
      hseθ hT hPstar hT_meas hse_meas hTail hse_consistent

/-- Formula-covariance version of the marginal-numerator route for Hansen
Theorem 12.8's bootstrap t-ratio. -/
theorem
    twoSLSBootstrapLinearTStatFinSucc_tendstoInBootstrapDistribution_formula_of_numerator_tight
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {R : Matrix Unit k ℝ}
    {QXZ : Matrix k l ℝ} {QZZ Omega : Matrix l l ℝ} {QZX : Matrix l k ℝ}
    {Vstar : ∀ n, Ω → (Fin (n + 1) → Fin (n + 1)) → Matrix k k ℝ}
    (hseθ : 0 <
      linearRestrictionStdError R (twoSLSAsymptoticVariance QXZ QZZ Omega QZX))
    (hT :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar
        (fun n ω ωs =>
          twoSLSBootstrapLinearRestrictionStatisticFinSucc R Z X Y n ω ωs)
        (gaussianReal 0 1)
        (fun z : ℝ =>
          linearRestrictionStdError R
              (twoSLSAsymptoticVariance QXZ QZZ Omega QZX) * z))
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hT_meas : ∀ n ω,
      Measurable
        (fun ωs => twoSLSBootstrapLinearRestrictionStatisticFinSucc R Z X Y n ω ωs))
    (hse_meas : ∀ n ω,
      Measurable
        (fun ωs => twoSLSBootstrapLinearRestrictionStdErrorFinSucc R Vstar n ω ωs))
    (hTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set (ℝ × ℝ), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω =>
            (Pstar n ω).real
              {ωs |
                (twoSLSBootstrapLinearRestrictionStatisticFinSucc R Z X Y n ω ωs,
                  linearRestrictionStdError R
                    (twoSLSAsymptoticVariance QXZ QZZ Omega QZX)) ∉ K})
          atTop (fun _ => 0) ∧
        TendstoInMeasure μ
          (fun n ω =>
            (Pstar n ω).real
              {ωs |
                (twoSLSBootstrapLinearRestrictionStatisticFinSucc R Z X Y n ω ωs,
                  twoSLSBootstrapLinearRestrictionStdErrorFinSucc R Vstar n ω ωs) ∉ K})
          atTop (fun _ => 0))
    (hse_consistent :
      TendstoInBootstrapProbabilityIndexed μ Pstar
        (fun n ω ωs =>
          twoSLSBootstrapLinearRestrictionStdErrorFinSucc R Vstar n ω ωs)
        (fun _ =>
          linearRestrictionStdError R
            (twoSLSAsymptoticVariance QXZ QZZ Omega QZX))) :
    TendstoInBootstrapDistributionIndexed μ Pstar
      (fun n ω ωs (_ : Unit) =>
        twoSLSBootstrapLinearTStatFinSucc R Z X Y Vstar n ω ωs)
      (gaussianReal 0 1) (fun z : ℝ => fun _ : Unit => z) :=
  twoSLSBootstrapLinearTStatFinSucc_tendstoInBootstrapDistribution_of_numerator_tight
    (μ := μ) (Pstar := Pstar)
    (Vβ := twoSLSAsymptoticVariance QXZ QZZ Omega QZX)
    hseθ hT hPstar hT_meas hse_meas hTail hse_consistent

/-- Ordinary-bootstrap specialization of the marginal-numerator route for
Hansen Theorem 12.8's bootstrap t-ratio. -/
theorem
    twoSLSBootstrapLinearTStatFinSucc_tendstoInBootstrapDistribution_uniform_of_numerator_tight
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {R : Matrix Unit k ℝ}
    {Vβ : Matrix k k ℝ}
    {Vstar : ∀ n, Ω → (Fin (n + 1) → Fin (n + 1)) → Matrix k k ℝ}
    (hseθ : 0 < linearRestrictionStdError R Vβ)
    (hT :
      TendstoInBootstrapWeakDistributionIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs =>
          twoSLSBootstrapLinearRestrictionStatisticFinSucc R Z X Y n ω ωs)
        (gaussianReal 0 1)
        (fun z : ℝ => linearRestrictionStdError R Vβ * z))
    (hT_meas : ∀ n ω,
      Measurable
        (fun ωs => twoSLSBootstrapLinearRestrictionStatisticFinSucc R Z X Y n ω ωs))
    (hse_meas : ∀ n ω,
      Measurable
        (fun ωs => twoSLSBootstrapLinearRestrictionStdErrorFinSucc R Vstar n ω ωs))
    (hTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set (ℝ × ℝ), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω =>
            (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω) n ω).real
              {ωs |
                (twoSLSBootstrapLinearRestrictionStatisticFinSucc R Z X Y n ω ωs,
                  linearRestrictionStdError R Vβ) ∉ K})
          atTop (fun _ => 0) ∧
        TendstoInMeasure μ
          (fun n ω =>
            (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω) n ω).real
              {ωs |
                (twoSLSBootstrapLinearRestrictionStatisticFinSucc R Z X Y n ω ωs,
                  twoSLSBootstrapLinearRestrictionStdErrorFinSucc R Vstar n ω ωs) ∉ K})
          atTop (fun _ => 0))
    (hse_consistent :
      TendstoInBootstrapProbabilityIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs =>
          twoSLSBootstrapLinearRestrictionStdErrorFinSucc R Vstar n ω ωs)
        (fun _ => linearRestrictionStdError R Vβ)) :
    TendstoInBootstrapDistributionIndexed μ
      (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
      (fun n ω ωs (_ : Unit) =>
        twoSLSBootstrapLinearTStatFinSucc R Z X Y Vstar n ω ωs)
      (gaussianReal 0 1) (fun z : ℝ => fun _ : Unit => z) :=
  twoSLSBootstrapLinearTStatFinSucc_tendstoInBootstrapDistribution_of_numerator_tight
    (μ := μ) (Pstar := twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
    hseθ hT
    (fun n ω =>
      twoSLSBootstrapUniformPstarFinSucc_isProbabilityMeasure (Ω := Ω) n ω)
    hT_meas hse_meas hTail hse_consistent

/-- Ordinary-bootstrap, formula-covariance specialization of the
marginal-numerator route for Hansen Theorem 12.8's bootstrap t-ratio. -/
theorem
    twoSLSBootstrapLinearTStatFinSucc_tendstoInBootstrapDistribution_formula_uniform_of_numerator_tight
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {R : Matrix Unit k ℝ}
    {QXZ : Matrix k l ℝ} {QZZ Omega : Matrix l l ℝ} {QZX : Matrix l k ℝ}
    {Vstar : ∀ n, Ω → (Fin (n + 1) → Fin (n + 1)) → Matrix k k ℝ}
    (hseθ : 0 <
      linearRestrictionStdError R (twoSLSAsymptoticVariance QXZ QZZ Omega QZX))
    (hT :
      TendstoInBootstrapWeakDistributionIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs =>
          twoSLSBootstrapLinearRestrictionStatisticFinSucc R Z X Y n ω ωs)
        (gaussianReal 0 1)
        (fun z : ℝ =>
          linearRestrictionStdError R
              (twoSLSAsymptoticVariance QXZ QZZ Omega QZX) * z))
    (hT_meas : ∀ n ω,
      Measurable
        (fun ωs => twoSLSBootstrapLinearRestrictionStatisticFinSucc R Z X Y n ω ωs))
    (hse_meas : ∀ n ω,
      Measurable
        (fun ωs => twoSLSBootstrapLinearRestrictionStdErrorFinSucc R Vstar n ω ωs))
    (hTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set (ℝ × ℝ), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω =>
            (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω) n ω).real
              {ωs |
                (twoSLSBootstrapLinearRestrictionStatisticFinSucc R Z X Y n ω ωs,
                  linearRestrictionStdError R
                    (twoSLSAsymptoticVariance QXZ QZZ Omega QZX)) ∉ K})
          atTop (fun _ => 0) ∧
        TendstoInMeasure μ
          (fun n ω =>
            (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω) n ω).real
              {ωs |
                (twoSLSBootstrapLinearRestrictionStatisticFinSucc R Z X Y n ω ωs,
                  twoSLSBootstrapLinearRestrictionStdErrorFinSucc R Vstar n ω ωs) ∉ K})
          atTop (fun _ => 0))
    (hse_consistent :
      TendstoInBootstrapProbabilityIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs =>
          twoSLSBootstrapLinearRestrictionStdErrorFinSucc R Vstar n ω ωs)
        (fun _ =>
          linearRestrictionStdError R
            (twoSLSAsymptoticVariance QXZ QZZ Omega QZX))) :
    TendstoInBootstrapDistributionIndexed μ
      (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
      (fun n ω ωs (_ : Unit) =>
        twoSLSBootstrapLinearTStatFinSucc R Z X Y Vstar n ω ωs)
      (gaussianReal 0 1) (fun z : ℝ => fun _ : Unit => z) :=
  twoSLSBootstrapLinearTStatFinSucc_tendstoInBootstrapDistribution_formula_of_numerator_tight
    (μ := μ) (Pstar := twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
    hseθ hT
    (fun n ω =>
      twoSLSBootstrapUniformPstarFinSucc_isProbabilityMeasure (Ω := Ω) n ω)
    hT_meas hse_meas hTail hse_consistent

/-- Concrete robust ordinary-bootstrap t-ratio route for Hansen Theorem 12.8.
The caller supplies the IV numerator CLT, compact-tail control, and bootstrap
covariance consistency; this theorem derives the robust standard-error
consistency and delegates studentization to Chapter 10. -/
theorem
    twoSLSBootstrapRobustLinearTStatFinSucc_tendstoInBootstrapDistribution_formula_uniform_of_numerator_tight
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {R : Matrix Unit k ℝ}
    {QXZ : Matrix k l ℝ} {QZZ Omega : Matrix l l ℝ} {QZX : Matrix l k ℝ}
    (hseθ : 0 <
      linearRestrictionStdError R (twoSLSAsymptoticVariance QXZ QZZ Omega QZX))
    (hT :
      TendstoInBootstrapWeakDistributionIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs =>
          twoSLSBootstrapLinearRestrictionStatisticFinSucc R Z X Y n ω ωs)
        (gaussianReal 0 1)
        (fun z : ℝ =>
          linearRestrictionStdError R
              (twoSLSAsymptoticVariance QXZ QZZ Omega QZX) * z))
    (hT_meas : ∀ n ω,
      Measurable
        (fun ωs => twoSLSBootstrapLinearRestrictionStatisticFinSucc R Z X Y n ω ωs))
    (hse_meas : ∀ n ω,
      Measurable
        (fun ωs =>
          twoSLSBootstrapRobustLinearRestrictionStdErrorFinSucc R Z X Y n ω ωs))
    (hTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set (ℝ × ℝ), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω =>
            (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω) n ω).real
              {ωs |
                (twoSLSBootstrapLinearRestrictionStatisticFinSucc R Z X Y n ω ωs,
                  linearRestrictionStdError R
                    (twoSLSAsymptoticVariance QXZ QZZ Omega QZX)) ∉ K})
          atTop (fun _ => 0) ∧
        TendstoInMeasure μ
          (fun n ω =>
            (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω) n ω).real
              {ωs |
                (twoSLSBootstrapLinearRestrictionStatisticFinSucc R Z X Y n ω ωs,
                  twoSLSBootstrapRobustLinearRestrictionStdErrorFinSucc
                    R Z X Y n ω ωs) ∉ K})
          atTop (fun _ => 0))
    (hV :
      TendstoInBootstrapProbabilityIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs => twoSLSBootstrapVHatStarFinSucc Z X Y n ω ωs)
        (fun _ => twoSLSAsymptoticVariance QXZ QZZ Omega QZX)) :
    TendstoInBootstrapDistributionIndexed μ
      (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
      (fun n ω ωs (_ : Unit) =>
        twoSLSBootstrapRobustLinearTStatFinSucc R Z X Y n ω ωs)
      (gaussianReal 0 1) (fun z : ℝ => fun _ : Unit => z) := by
  have hse_consistent :=
    twoSLSBootstrapRobustLinearRestrictionStdErrorFinSucc_tendstoInBootstrapProbability_formula_uniform
      (μ := μ) (R := R) (Z := Z) (X := X) (Y := Y)
      (QXZ := QXZ) (QZZ := QZZ) (Omega := Omega) (QZX := QZX) hV
  simpa [twoSLSBootstrapRobustLinearTStatFinSucc,
    twoSLSBootstrapRobustLinearRestrictionStdErrorFinSucc_eq_generic] using
    twoSLSBootstrapLinearTStatFinSucc_tendstoInBootstrapDistribution_formula_uniform_of_numerator_tight
      (μ := μ) (Z := Z) (X := X) (Y := Y) (R := R)
      (QXZ := QXZ) (QZZ := QZZ) (Omega := Omega) (QZX := QZX)
      (Vstar := fun n ω ωs => twoSLSBootstrapVHatStarFinSucc Z X Y n ω ωs)
      hseθ hT hT_meas hse_meas hTail hse_consistent

set_option linter.style.longLine false in
/-- Hansen Theorem 12.8 percentile-`t` interval coverage endpoint from the
ordinary-bootstrap robust 2SLS t-ratio limit.

The theorem reuses Chapter 10's indexed percentile-`t` coverage theorem.  The
sample-side t-ratio limit and the bootstrap t-ratio distribution are explicit
premises, so this wrapper does not assume interval coverage directly. -/
theorem
    twoSLSBootstrapRobustPercentileTCIEventFinSucc_tendsto_one_sub_alpha_uniform
    [IsProbabilityMeasure μ]
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {R : Matrix Unit k ℝ} {β : k → ℝ} {q α : ℝ}
    (hsampleSe : ∀ n ω,
      0 < twoSLSRobustLinearRestrictionEstimatorStdErrorFinSucc R Z X Y n ω)
    (htstat :
      TendstoInDistribution
        (fun n ω =>
          percentileTStatistic (linearRestrictionEstimate R β)
            (twoSLSLinearRestrictionEstimateFinSucc R Z X Y n ω)
            (twoSLSRobustLinearRestrictionEstimatorStdErrorFinSucc R Z X Y n ω))
        atTop (fun x : ℝ => x) (fun _ => μ) (gaussianReal 0 1))
    (hTstar_meas : ∀ n ω,
      AEMeasurable
        (fun ωs => twoSLSBootstrapRobustLinearTStatFinSucc R Z X Y n ω ωs)
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω) n ω))
    (hTstar :
      TendstoInBootstrapDistributionIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs (_ : Unit) =>
          twoSLSBootstrapRobustLinearTStatFinSucc R Z X Y n ω ωs)
        (gaussianReal 0 1) (fun z : ℝ => fun _ : Unit => z))
    (hα_pos : 0 < α) (hα_lt_one : α < 1)
    (hstrict : StrictMono (fun x => cdf (gaussianReal 0 1) x))
    (hlower_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed
            (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
            (fun n ω ωs =>
              twoSLSBootstrapRobustLinearTStatFinSucc R Z X Y n ω ωs)
            (α / 2) n) μ)
    (hupper_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed
            (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
            (fun n ω ωs =>
              twoSLSBootstrapRobustLinearTStatFinSucc R Z X Y n ω ωs)
            (1 - α / 2) n) μ)
    (hq_nonneg : 0 ≤ q)
    (hcdfLower : cdf (gaussianReal 0 1) (-q) = α / 2)
    (hcdfUpper : cdf (gaussianReal 0 1) q = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω |
          twoSLSBootstrapRobustPercentileTCIEventFinSucc
            R Z X Y β α n ω})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) := by
  haveI : NoAtoms (gaussianReal 0 1) :=
    noAtoms_gaussianReal (μ := 0) (v := 1) (by norm_num)
  have hξ : HasLaw (fun x : ℝ => x) (gaussianReal 0 1) (gaussianReal 0 1) := by
    simpa [id] using (HasLaw.id (μ := gaussianReal 0 1))
  have hcoverage :=
    chapter10_percentileTCI_coverage_tendsto_one_sub_alpha_indexed_bootstrapDistribution_quantile_prob
      (μ := μ) (ν := gaussianReal 0 1) (η := gaussianReal 0 1)
      (Pstar := twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
      (Tstar := fun n ω ωs =>
        twoSLSBootstrapRobustLinearTStatFinSucc R Z X Y n ω ωs)
      (θ := linearRestrictionEstimate R β)
      (θhat := fun n ω =>
        twoSLSLinearRestrictionEstimateFinSucc R Z X Y n ω)
      (se := fun n ω =>
        twoSLSRobustLinearRestrictionEstimatorStdErrorFinSucc R Z X Y n ω)
      (ξ := fun x : ℝ => x) (q := q) (α := α)
      hsampleSe htstat
      (fun n ω =>
        twoSLSBootstrapUniformPstarFinSucc_isProbabilityMeasure (Ω := Ω) n ω)
      hTstar_meas hα_pos hα_lt_one hstrict hTstar
      (fun x => continuousAt_cdf_standardNormal x)
      hlower_meas hupper_meas hξ hq_nonneg hcdfLower hcdfUpper
  simpa [twoSLSBootstrapRobustPercentileTCIEventFinSucc] using hcoverage

set_option linter.style.longLine false in
/-- Hansen Theorem 12.8 percentile-`t` coverage when nonpositive realized
sample standard errors occur with probability tending to zero.

This is the asymptotic counterpart of
`twoSLSBootstrapRobustPercentileTCIEventFinSucc_tendsto_one_sub_alpha_uniform`.
It replaces positivity at every sample size and outcome by the high-probability
nondegeneracy condition actually needed to identify the confidence-interval
event with the studentized-statistic event. -/
theorem
    twoSLSBootstrapRobustPercentileTCIEventFinSucc_tendsto_one_sub_alpha_uniform_of_standardError_nonpos_tendsto_zero
    [IsProbabilityMeasure μ]
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {R : Matrix Unit k ℝ} {β : k → ℝ} {q α : ℝ}
    (hsampleSe :
      Tendsto
        (fun n =>
          μ {ω |
            twoSLSRobustLinearRestrictionEstimatorStdErrorFinSucc
              R Z X Y n ω ≤ 0})
        atTop (𝓝 0))
    (htstat :
      TendstoInDistribution
        (fun n ω =>
          percentileTStatistic (linearRestrictionEstimate R β)
            (twoSLSLinearRestrictionEstimateFinSucc R Z X Y n ω)
            (twoSLSRobustLinearRestrictionEstimatorStdErrorFinSucc
              R Z X Y n ω))
        atTop (fun x : ℝ => x) (fun _ => μ) (gaussianReal 0 1))
    (hTstar_meas : ∀ n ω,
      AEMeasurable
        (fun ωs => twoSLSBootstrapRobustLinearTStatFinSucc R Z X Y n ω ωs)
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω) n ω))
    (hTstar :
      TendstoInBootstrapDistributionIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs (_ : Unit) =>
          twoSLSBootstrapRobustLinearTStatFinSucc R Z X Y n ω ωs)
        (gaussianReal 0 1) (fun z : ℝ => fun _ : Unit => z))
    (hα_pos : 0 < α) (hα_lt_one : α < 1)
    (hstrict : StrictMono (fun x => cdf (gaussianReal 0 1) x))
    (hlower_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed
            (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
            (fun n ω ωs =>
              twoSLSBootstrapRobustLinearTStatFinSucc R Z X Y n ω ωs)
            (α / 2) n) μ)
    (hupper_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed
            (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
            (fun n ω ωs =>
              twoSLSBootstrapRobustLinearTStatFinSucc R Z X Y n ω ωs)
            (1 - α / 2) n) μ)
    (hq_nonneg : 0 ≤ q)
    (hcdfLower : cdf (gaussianReal 0 1) (-q) = α / 2)
    (hcdfUpper : cdf (gaussianReal 0 1) q = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω |
          twoSLSBootstrapRobustPercentileTCIEventFinSucc
            R Z X Y β α n ω})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) := by
  let θ : ℝ := linearRestrictionEstimate R β
  let θhat : ℕ → Ω → ℝ := fun n ω =>
    twoSLSLinearRestrictionEstimateFinSucc R Z X Y n ω
  let se : ℕ → Ω → ℝ := fun n ω =>
    twoSLSRobustLinearRestrictionEstimatorStdErrorFinSucc R Z X Y n ω
  let tstat : ℕ → Ω → ℝ := fun n ω =>
    percentileTStatistic θ (θhat n ω) (se n ω)
  let sePos : ℕ → Ω → ℝ := fun n ω => if 0 < se n ω then se n ω else 1
  let θhatPos : ℕ → Ω → ℝ := fun n ω => θ + tstat n ω * sePos n ω
  let qLower : ℕ → Ω → ℝ :=
    bootstrapScalarLowerQuantileIndexed
      (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
      (fun n ω ωs =>
        twoSLSBootstrapRobustLinearTStatFinSucc R Z X Y n ω ωs)
      (α / 2)
  let qUpper : ℕ → Ω → ℝ :=
    bootstrapScalarLowerQuantileIndexed
      (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
      (fun n ω ωs =>
        twoSLSBootstrapRobustLinearTStatFinSucc R Z X Y n ω ωs)
      (1 - α / 2)
  let actual : ℕ → Set Ω := fun n =>
    {ω | percentileTCIEvent θ (θhat n ω) (se n ω)
      (qLower n ω) (qUpper n ω)}
  let reference : ℕ → Set Ω := fun n =>
    {ω | percentileTCIEvent θ (θhatPos n ω) (sePos n ω)
      (qLower n ω) (qUpper n ω)}
  let bad : ℕ → Set Ω := fun n => {ω | se n ω ≤ 0}
  have hsePos : ∀ n ω, 0 < sePos n ω := by
    intro n ω
    simp only [sePos]
    split_ifs with h
    · exact h
    · norm_num
  have htstat' :
      TendstoInDistribution tstat atTop (fun x : ℝ => x)
        (fun _ => μ) (gaussianReal 0 1) := by
    simpa [tstat, θ, θhat, se] using htstat
  have htstatPos :
      TendstoInDistribution
        (fun n ω => percentileTStatistic θ (θhatPos n ω) (sePos n ω))
        atTop (fun x : ℝ => x) (fun _ => μ) (gaussianReal 0 1) := by
    refine TendstoInDistribution.congr (fun n => ae_of_all μ fun ω => ?_)
      EventuallyEq.rfl htstat'
    dsimp [θhatPos, percentileTStatistic]
    field_simp [(hsePos n ω).ne']
    ring
  haveI : NoAtoms (gaussianReal 0 1) :=
    noAtoms_gaussianReal (μ := 0) (v := 1) (by norm_num)
  have hξ : HasLaw (fun x : ℝ => x) (gaussianReal 0 1) (gaussianReal 0 1) := by
    simpa [id] using (HasLaw.id (μ := gaussianReal 0 1))
  have hreference :
      Tendsto (fun n => μ (reference n)) atTop
        (𝓝 (ENNReal.ofReal (1 - α))) := by
    have hcoverage :=
      chapter10_percentileTCI_coverage_tendsto_one_sub_alpha_indexed_bootstrapDistribution_quantile_prob
        (μ := μ) (ν := gaussianReal 0 1) (η := gaussianReal 0 1)
        (Pstar := twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (Tstar := fun n ω ωs =>
          twoSLSBootstrapRobustLinearTStatFinSucc R Z X Y n ω ωs)
        (θ := θ) (θhat := θhatPos) (se := sePos)
        (ξ := fun x : ℝ => x) (q := q) (α := α)
        hsePos htstatPos
        (fun n ω =>
          twoSLSBootstrapUniformPstarFinSucc_isProbabilityMeasure (Ω := Ω) n ω)
        hTstar_meas hα_pos hα_lt_one hstrict hTstar
        (fun x => continuousAt_cdf_standardNormal x)
        hlower_meas hupper_meas hξ hq_nonneg hcdfLower hcdfUpper
    simpa [reference, qLower, qUpper] using hcoverage
  have hsymm_subset : ∀ n, actual n ∆ reference n ⊆ bad n := by
    intro n ω hω
    by_cases hpos : 0 < se n ω
    · have hseEq : sePos n ω = se n ω := by simp [sePos, hpos]
      have hθhatEq : θhatPos n ω = θhat n ω := by
        dsimp [θhatPos, tstat, percentileTStatistic]
        rw [hseEq]
        field_simp [hpos.ne']
        ring
      have heq : ω ∈ actual n ↔ ω ∈ reference n := by
        simp only [actual, reference, Set.mem_setOf_eq, hseEq, hθhatEq]
      rw [Set.mem_symmDiff] at hω
      rcases hω with hω | hω
      · exact False.elim (hω.2 (heq.mp hω.1))
      · exact False.elim (hω.2 (heq.mpr hω.1))
    · exact not_lt.mp hpos
  have hbad : Tendsto (fun n => μ (bad n)) atTop (𝓝 0) := by
    simpa [bad, se] using hsampleSe
  have hdiff : Tendsto (fun n => μ (actual n ∆ reference n)) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hbad
      (Eventually.of_forall fun n => zero_le _) ?_
    exact Eventually.of_forall fun n => measure_mono (hsymm_subset n)
  let L : ℝ≥0∞ := ENNReal.ofReal (1 - α)
  have hL_ne_top : L ≠ ∞ := by simp [L]
  have hlower :
      Tendsto (fun n => μ (reference n) - μ (actual n ∆ reference n))
        atTop (𝓝 L) := by
    simpa [L] using ENNReal.Tendsto.sub hreference hdiff (Or.inl hL_ne_top)
  have hupper :
      Tendsto (fun n => μ (reference n) + μ (actual n ∆ reference n))
        atTop (𝓝 L) := by
    simpa [L] using hreference.add hdiff
  have hactual : Tendsto (fun n => μ (actual n)) atTop (𝓝 L) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower hupper ?_ ?_
    · exact Eventually.of_forall fun n => by
        have href_le :
            μ (reference n) ≤ μ (actual n) + μ (actual n ∆ reference n) := by
          calc
            μ (reference n) ≤ μ ((actual n ∆ reference n) ∪ actual n) :=
              measure_mono (le_symmDiff_sup_left (actual n) (reference n))
            _ ≤ μ (actual n ∆ reference n) + μ (actual n) := measure_union_le _ _
            _ = μ (actual n) + μ (actual n ∆ reference n) := by rw [add_comm]
        exact tsub_le_iff_right.mpr href_le
    · exact Eventually.of_forall fun n => by
        calc
          μ (actual n) ≤ μ ((actual n ∆ reference n) ∪ reference n) :=
            measure_mono (le_symmDiff_sup_right (actual n) (reference n))
          _ ≤ μ (actual n ∆ reference n) + μ (reference n) := measure_union_le _ _
          _ = μ (reference n) + μ (actual n ∆ reference n) := by rw [add_comm]
  simpa [actual, θ, θhat, se, qLower, qUpper, L,
    twoSLSBootstrapRobustPercentileTCIEventFinSucc] using hactual

set_option linter.style.longLine false in
/-- Hansen Theorem 12.8 non-studentized percentile interval coverage endpoint
from the ordinary-bootstrap one-row numerator limit.

This is the percentile, rather than percentile-`t`, counterpart of
`twoSLSBootstrapRobustPercentileTCIEventFinSucc_tendsto_one_sub_alpha_uniform`.
The scalar limit law is kept generic: the sample statistic and the bootstrap
numerator may live on different auxiliary limit spaces, but both must have the
same scalar law `η`. -/
theorem
    twoSLSBootstrapLinearRestrictionPercentileCIEventFinSucc_tendsto_one_sub_alpha_uniform
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {νstar : Measure Ωstar} [IsProbabilityMeasure νstar]
    {η : Measure ℝ} [IsProbabilityMeasure η] [NoAtoms η]
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {R : Matrix Unit k ℝ} {β : k → ℝ} {ξ : Ωlim → ℝ}
    {Zlim : Ωstar → ℝ} {q α : ℝ}
    (hstat :
      TendstoInDistribution
        (fun n ω =>
          Real.sqrt ((n + 1 : ℕ) : ℝ) *
            (twoSLSLinearRestrictionEstimateFinSucc R Z X Y n ω -
              linearRestrictionEstimate R β))
        atTop ξ (fun _ => μ) ν)
    (hTstar :
      TendstoInBootstrapDistributionIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs (_ : Unit) =>
          twoSLSBootstrapLinearRestrictionStatisticFinSucc R Z X Y n ω ωs)
        νstar (fun ωstar (_ : Unit) => Zlim ωstar))
    (hZlaw : HasLaw Zlim η νstar)
    (hξlaw : HasLaw ξ η ν)
    (hα_pos : 0 < α) (hα_lt_one : α < 1)
    (hstrict : StrictMono (fun x => cdf η x))
    (hlower_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed
            (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
            (fun n ω ωs =>
              twoSLSBootstrapLinearRestrictionStatisticFinSucc
                R Z X Y n ω ωs)
            (α / 2) n) μ)
    (hupper_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed
            (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
            (fun n ω ωs =>
              twoSLSBootstrapLinearRestrictionStatisticFinSucc
                R Z X Y n ω ωs)
            (1 - α / 2) n) μ)
    (hq_nonneg : 0 ≤ q)
    (hcdfLower : cdf η (-q) = α / 2)
    (hcdfUpper : cdf η q = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω |
          twoSLSBootstrapLinearRestrictionPercentileCIEventFinSucc
            R Z X Y β α n ω})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) := by
  have ha : ∀ n, 0 < Real.sqrt ((n + 1 : ℕ) : ℝ) := by
    intro n
    exact Real.sqrt_pos.mpr (by exact_mod_cast Nat.succ_pos n)
  have hPstar : ∀ n (ω : Ω),
      IsProbabilityMeasure
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω) n ω) :=
    fun n ω =>
      twoSLSBootstrapUniformPstarFinSucc_isProbabilityMeasure (Ω := Ω) n ω
  have hTmeas : ∀ n (ω : Ω),
      AEMeasurable
        (fun ωs =>
          twoSLSBootstrapLinearRestrictionStatisticFinSucc
            R Z X Y n ω ωs)
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω) n ω) :=
    fun n ω =>
      (twoSLSBootstrapLinearRestrictionStatisticFinSucc_measurable
        (R := R) (Z := Z) (X := X) (Y := Y) n ω).aemeasurable
  have hcoverage :=
    chapter10_indexed_percentileCI_coverage_bootstrapDistribution_law_quantile_prob
      (μ := μ) (ν := ν) (Ωstar := Ωstar) (νstar := νstar)
      (η := η)
      (Pstar := twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
      (Tstar := fun n ω ωs =>
        twoSLSBootstrapLinearRestrictionStatisticFinSucc R Z X Y n ω ωs)
      (a := fun n => Real.sqrt ((n + 1 : ℕ) : ℝ)) ha
      (θ := linearRestrictionEstimate R β)
      (θhat := fun n ω =>
        twoSLSLinearRestrictionEstimateFinSucc R Z X Y n ω)
      (ξ := ξ) (Zlim := Zlim) (q := q) (α := α)
      hstat hPstar hTmeas hα_pos hα_lt_one hstrict hTstar hZlaw
      (fun x => continuousAt_cdf_of_noAtoms η x)
      hlower_meas hupper_meas hξlaw hq_nonneg hcdfLower hcdfUpper
  simpa [twoSLSBootstrapLinearRestrictionPercentileCIEventFinSucc] using hcoverage

/-- Bootstrap quantile calibration inputs for Hansen Theorem 12.8's
non-studentized percentile interval.

The fields are exactly the Chapter 10 percentile calibration hypotheses for
the ordinary-bootstrap one-row numerator. -/
structure TwoSLSBootstrapLinearRestrictionPercentileQuantileCalibrationInputs
    (μ : Measure Ω)
    (Z : ℕ → Ω → l → ℝ) (X : ℕ → Ω → k → ℝ) (Y : ℕ → Ω → ℝ)
    (R : Matrix Unit k ℝ) (η : Measure ℝ) (q α : ℝ) : Prop where
  alpha_pos : 0 < α
  alpha_lt_one : α < 1
  limit_cdf_strictMono : StrictMono (fun x => cdf η x)
  lower_quantile_aemeasurable :
    ∀ n,
      AEMeasurable
        (bootstrapScalarLowerQuantileIndexed
          (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
          (fun n ω ωs =>
            twoSLSBootstrapLinearRestrictionStatisticFinSucc R Z X Y n ω ωs)
          (α / 2) n) μ
  upper_quantile_aemeasurable :
    ∀ n,
      AEMeasurable
        (bootstrapScalarLowerQuantileIndexed
          (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
          (fun n ω ωs =>
            twoSLSBootstrapLinearRestrictionStatisticFinSucc R Z X Y n ω ωs)
          (1 - α / 2) n) μ
  critical_nonneg : 0 ≤ q
  cdf_lower : cdf η (-q) = α / 2
  cdf_upper : cdf η q = 1 - α / 2

set_option linter.style.longLine false in
/-- Field-level constructor for the non-studentized percentile calibration
package in Hansen Theorem 12.8. -/
theorem TwoSLSBootstrapLinearRestrictionPercentileQuantileCalibrationInputs.of_fields
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {R : Matrix Unit k ℝ} {η : Measure ℝ} {q α : ℝ}
    (hα_pos : 0 < α) (hα_lt_one : α < 1)
    (hstrict : StrictMono (fun x => cdf η x))
    (hlower_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed
            (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
            (fun n ω ωs =>
              twoSLSBootstrapLinearRestrictionStatisticFinSucc
                R Z X Y n ω ωs)
            (α / 2) n) μ)
    (hupper_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed
            (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
            (fun n ω ωs =>
              twoSLSBootstrapLinearRestrictionStatisticFinSucc
                R Z X Y n ω ωs)
            (1 - α / 2) n) μ)
    (hq_nonneg : 0 ≤ q)
    (hcdfLower : cdf η (-q) = α / 2)
    (hcdfUpper : cdf η q = 1 - α / 2) :
    TwoSLSBootstrapLinearRestrictionPercentileQuantileCalibrationInputs
      μ Z X Y R η q α where
  alpha_pos := hα_pos
  alpha_lt_one := hα_lt_one
  limit_cdf_strictMono := hstrict
  lower_quantile_aemeasurable := hlower_meas
  upper_quantile_aemeasurable := hupper_meas
  critical_nonneg := hq_nonneg
  cdf_lower := hcdfLower
  cdf_upper := hcdfUpper

set_option linter.style.longLine false in
/-- Non-studentized percentile interval coverage from sample and bootstrap
scalar-law limits plus the named quantile-calibration package. -/
theorem
    twoSLSBootstrapLinearRestrictionPercentileCIEventFinSucc_tendsto_one_sub_alpha_uniform_of_quantileCalibration
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {νstar : Measure Ωstar} [IsProbabilityMeasure νstar]
    {η : Measure ℝ} [IsProbabilityMeasure η] [NoAtoms η]
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {R : Matrix Unit k ℝ} {β : k → ℝ} {ξ : Ωlim → ℝ}
    {Zlim : Ωstar → ℝ} {q α : ℝ}
    (hstat :
      TendstoInDistribution
        (fun n ω =>
          Real.sqrt ((n + 1 : ℕ) : ℝ) *
            (twoSLSLinearRestrictionEstimateFinSucc R Z X Y n ω -
              linearRestrictionEstimate R β))
        atTop ξ (fun _ => μ) ν)
    (hTstar :
      TendstoInBootstrapDistributionIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs (_ : Unit) =>
          twoSLSBootstrapLinearRestrictionStatisticFinSucc R Z X Y n ω ωs)
        νstar (fun ωstar (_ : Unit) => Zlim ωstar))
    (hZlaw : HasLaw Zlim η νstar)
    (hξlaw : HasLaw ξ η ν)
    (hquantile :
      TwoSLSBootstrapLinearRestrictionPercentileQuantileCalibrationInputs
        μ Z X Y R η q α) :
    Tendsto
      (fun n =>
        μ {ω |
          twoSLSBootstrapLinearRestrictionPercentileCIEventFinSucc
            R Z X Y β α n ω})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) :=
  twoSLSBootstrapLinearRestrictionPercentileCIEventFinSucc_tendsto_one_sub_alpha_uniform
    (μ := μ) (ν := ν) (Ωstar := Ωstar) (νstar := νstar)
    (η := η) (Z := Z) (X := X) (Y := Y) (R := R) (β := β)
    (ξ := ξ) (Zlim := Zlim) (q := q) (α := α)
    hstat hTstar hZlaw hξlaw hquantile.alpha_pos hquantile.alpha_lt_one
    hquantile.limit_cdf_strictMono
    hquantile.lower_quantile_aemeasurable
    hquantile.upper_quantile_aemeasurable
    hquantile.critical_nonneg hquantile.cdf_lower hquantile.cdf_upper

/-- Sample-side inputs for Hansen Theorem 12.8's percentile-`t` interval.

These are the original-sample pieces in the final interval sentence: finite
sample positivity of the robust one-row 2SLS standard error and the limiting
standard-normal law of the sample robust t-ratio. -/
structure TwoSLSBootstrapRobustPercentileTSampleInputs
    (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (Z : ℕ → Ω → l → ℝ) (X : ℕ → Ω → k → ℝ) (Y : ℕ → Ω → ℝ)
    (β : k → ℝ) (R : Matrix Unit k ℝ) : Prop where
  standard_error_pos : ∀ n ω,
    0 < twoSLSRobustLinearRestrictionEstimatorStdErrorFinSucc R Z X Y n ω
  statistic_limit :
    TendstoInDistribution
      (fun n ω =>
        percentileTStatistic (linearRestrictionEstimate R β)
          (twoSLSLinearRestrictionEstimateFinSucc R Z X Y n ω)
          (twoSLSRobustLinearRestrictionEstimatorStdErrorFinSucc R Z X Y n ω))
      atTop (fun x : ℝ => x) (fun _ => μ) (gaussianReal 0 1)

/-- Asymptotic sample-side inputs for Hansen Theorem 12.8's percentile-`t`
interval.

Unlike `TwoSLSBootstrapRobustPercentileTSampleInputs`, this package does not
require the realized standard error to be positive at every finite sample.
It records the statistically natural replacement: the probability of a
nonpositive standard error tends to zero. -/
structure TwoSLSBootstrapRobustPercentileTAsymptoticSampleInputs
    (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (Z : ℕ → Ω → l → ℝ) (X : ℕ → Ω → k → ℝ) (Y : ℕ → Ω → ℝ)
    (β : k → ℝ) (R : Matrix Unit k ℝ) : Prop where
  standard_error_nonpos_probability_tendsto_zero :
    Tendsto
      (fun n =>
        μ {ω |
          twoSLSRobustLinearRestrictionEstimatorStdErrorFinSucc
            R Z X Y n ω ≤ 0})
      atTop (𝓝 0)
  statistic_limit :
    TendstoInDistribution
      (fun n ω =>
        percentileTStatistic (linearRestrictionEstimate R β)
          (twoSLSLinearRestrictionEstimateFinSucc R Z X Y n ω)
          (twoSLSRobustLinearRestrictionEstimatorStdErrorFinSucc R Z X Y n ω))
      atTop (fun x : ℝ => x) (fun _ => μ) (gaussianReal 0 1)

/-- Bootstrap quantile calibration inputs for Hansen Theorem 12.8's
percentile-`t` interval.

The fields are exactly the Chapter 10 percentile-`t` calibration hypotheses for
the robust bootstrap 2SLS t-ratio: admissible level, measurability of the two
bootstrap quantile processes, and the displayed standard-normal quantile
equations. -/
structure TwoSLSBootstrapRobustPercentileTQuantileCalibrationInputs
    (μ : Measure Ω)
    (Z : ℕ → Ω → l → ℝ) (X : ℕ → Ω → k → ℝ) (Y : ℕ → Ω → ℝ)
    (R : Matrix Unit k ℝ) (q α : ℝ) : Prop where
  alpha_pos : 0 < α
  alpha_lt_one : α < 1
  standardNormal_cdf_strictMono :
    StrictMono (fun x => cdf (gaussianReal 0 1) x)
  lower_quantile_aemeasurable :
    ∀ n,
      AEMeasurable
        (bootstrapScalarLowerQuantileIndexed
          (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
          (fun n ω ωs =>
            twoSLSBootstrapRobustLinearTStatFinSucc R Z X Y n ω ωs)
          (α / 2) n) μ
  upper_quantile_aemeasurable :
    ∀ n,
      AEMeasurable
        (bootstrapScalarLowerQuantileIndexed
          (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
          (fun n ω ωs =>
            twoSLSBootstrapRobustLinearTStatFinSucc R Z X Y n ω ωs)
          (1 - α / 2) n) μ
  critical_nonneg : 0 ≤ q
  cdf_lower : cdf (gaussianReal 0 1) (-q) = α / 2
  cdf_upper : cdf (gaussianReal 0 1) q = 1 - α / 2

/-- Named interval-side input package for Hansen Theorem 12.8.

This package is deliberately narrower than the bootstrap empirical-process
package: it contains only the original-sample robust t-ratio facts and the
bootstrap quantile calibration needed to turn the already-proved robust
bootstrap t-ratio limit into percentile-`t` coverage. -/
structure TwoSLSBootstrapRobustPercentileTCoverageInputs
    (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (Z : ℕ → Ω → l → ℝ) (X : ℕ → Ω → k → ℝ) (Y : ℕ → Ω → ℝ)
    (β : k → ℝ) (R : Matrix Unit k ℝ) (q α : ℝ) : Prop where
  sample :
    TwoSLSBootstrapRobustPercentileTSampleInputs μ Z X Y β R
  quantile :
    TwoSLSBootstrapRobustPercentileTQuantileCalibrationInputs
      μ Z X Y R q α

/-- Asymptotic interval-side package for Hansen Theorem 12.8.

The sample component uses high-probability standard-error nondegeneracy rather
than finite-sample pathwise positivity. -/
structure TwoSLSBootstrapRobustPercentileTAsymptoticCoverageInputs
    (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (Z : ℕ → Ω → l → ℝ) (X : ℕ → Ω → k → ℝ) (Y : ℕ → Ω → ℝ)
    (β : k → ℝ) (R : Matrix Unit k ℝ) (q α : ℝ) : Prop where
  sample :
    TwoSLSBootstrapRobustPercentileTAsymptoticSampleInputs μ Z X Y β R
  quantile :
    TwoSLSBootstrapRobustPercentileTQuantileCalibrationInputs
      μ Z X Y R q α

/-- Constructor for the named percentile-`t` interval-side package. -/
theorem TwoSLSBootstrapRobustPercentileTCoverageInputs.of_sample_quantile
    [IsProbabilityMeasure μ]
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {β : k → ℝ} {R : Matrix Unit k ℝ} {q α : ℝ}
    (hsample :
      TwoSLSBootstrapRobustPercentileTSampleInputs μ Z X Y β R)
    (hquantile :
      TwoSLSBootstrapRobustPercentileTQuantileCalibrationInputs
        μ Z X Y R q α) :
    TwoSLSBootstrapRobustPercentileTCoverageInputs
      μ Z X Y β R q α where
  sample := hsample
  quantile := hquantile

/-- Constructor for the asymptotic percentile-`t` interval-side package. -/
theorem TwoSLSBootstrapRobustPercentileTAsymptoticCoverageInputs.of_sample_quantile
    [IsProbabilityMeasure μ]
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {β : k → ℝ} {R : Matrix Unit k ℝ} {q α : ℝ}
    (hsample :
      TwoSLSBootstrapRobustPercentileTAsymptoticSampleInputs μ Z X Y β R)
    (hquantile :
      TwoSLSBootstrapRobustPercentileTQuantileCalibrationInputs
        μ Z X Y R q α) :
    TwoSLSBootstrapRobustPercentileTAsymptoticCoverageInputs
      μ Z X Y β R q α where
  sample := hsample
  quantile := hquantile

set_option linter.style.longLine false in
/-- Field-level constructor for the original-sample side of Hansen
Theorem 12.8's percentile-`t` coverage input package. -/
theorem TwoSLSBootstrapRobustPercentileTSampleInputs.of_fields
    [IsProbabilityMeasure μ]
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {β : k → ℝ} {R : Matrix Unit k ℝ}
    (hse : ∀ n ω,
      0 < twoSLSRobustLinearRestrictionEstimatorStdErrorFinSucc R Z X Y n ω)
    (htstat :
      TendstoInDistribution
        (fun n ω =>
          percentileTStatistic (linearRestrictionEstimate R β)
            (twoSLSLinearRestrictionEstimateFinSucc R Z X Y n ω)
            (twoSLSRobustLinearRestrictionEstimatorStdErrorFinSucc R Z X Y n ω))
        atTop (fun x : ℝ => x) (fun _ => μ) (gaussianReal 0 1)) :
    TwoSLSBootstrapRobustPercentileTSampleInputs μ Z X Y β R where
  standard_error_pos := hse
  statistic_limit := htstat

omit [MeasurableSpace Ω] in
set_option linter.style.longLine false in
/-- Finite-sample positive definiteness of the robust one-row covariance
implies positivity of the unscaled robust 2SLS standard-error scale. -/
theorem twoSLSRobustLinearRestrictionStdErrorFinSucc_pos_of_restrictionCov_posDef
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {R : Matrix Unit k ℝ}
    (hVhat : ∀ n ω,
      (R *
          twoSLSVHatStar
            (stackRegressors Z (n + 1) ω) (stackRegressors X (n + 1) ω)
            (stackOutcomes Y (n + 1) ω) *
        Rᵀ).PosDef) :
    ∀ n ω, 0 < twoSLSRobustLinearRestrictionStdErrorFinSucc R Z X Y n ω := by
  intro n ω
  simpa [twoSLSRobustLinearRestrictionStdErrorFinSucc] using
    linearRestrictionStdError_pos_of_restrictionCov_posDef R (hVhat n ω)

omit [MeasurableSpace Ω] in
set_option linter.style.longLine false in
/-- Finite-sample positive definiteness of the robust one-row covariance
implies positivity of Hansen's sample-side percentile-`t` standard error. -/
theorem
    twoSLSRobustLinearRestrictionEstimatorStdErrorFinSucc_pos_of_restrictionCov_posDef
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {R : Matrix Unit k ℝ}
    (hVhat : ∀ n ω,
      (R *
          twoSLSVHatStar
            (stackRegressors Z (n + 1) ω) (stackRegressors X (n + 1) ω)
            (stackOutcomes Y (n + 1) ω) *
        Rᵀ).PosDef) :
    ∀ n ω,
      0 < twoSLSRobustLinearRestrictionEstimatorStdErrorFinSucc R Z X Y n ω := by
  intro n ω
  have hse :
      0 < twoSLSRobustLinearRestrictionStdErrorFinSucc R Z X Y n ω :=
    twoSLSRobustLinearRestrictionStdErrorFinSucc_pos_of_restrictionCov_posDef
      (R := R) hVhat n ω
  have hn : 0 < (n + 1 : ℝ) := by
    exact_mod_cast Nat.succ_pos n
  exact div_pos hse (Real.sqrt_pos.mpr hn)

omit [MeasurableSpace Ω] in
set_option linter.style.longLine false in
/-- Finite-sample positive definiteness of the robust coefficient covariance,
together with full rank of the one-row restriction, implies positive
definiteness of the finite-sample restriction covariance. -/
theorem twoSLSRobustRestrictionCovFinSucc_posDef_of_cov_posDef
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {R : Matrix Unit k ℝ}
    (hR : Function.Injective Rᵀ.mulVec)
    (hVhat : ∀ n ω,
      (twoSLSVHatStar
        (stackRegressors Z (n + 1) ω) (stackRegressors X (n + 1) ω)
        (stackOutcomes Y (n + 1) ω)).PosDef) :
    ∀ n ω,
      (R *
          twoSLSVHatStar
            (stackRegressors Z (n + 1) ω) (stackRegressors X (n + 1) ω)
            (stackOutcomes Y (n + 1) ω) *
        Rᵀ).PosDef := by
  intro n ω
  have hcov :
      ((Rᵀ)ᵀ *
          twoSLSVHatStar
            (stackRegressors Z (n + 1) ω) (stackRegressors X (n + 1) ω)
            (stackOutcomes Y (n + 1) ω) *
        Rᵀ).PosDef :=
    restrictionCov_posDef_of_cov_posDef
      (twoSLSVHatStar
        (stackRegressors Z (n + 1) ω) (stackRegressors X (n + 1) ω)
        (stackOutcomes Y (n + 1) ω))
      Rᵀ (hVhat n ω) hR
  simpa using hcov

omit [MeasurableSpace Ω] in
set_option linter.style.longLine false in
/-- Finite-sample positive definiteness of the robust coefficient covariance
and full rank of the one-row restriction imply positivity of the unscaled
robust 2SLS restriction standard-error scale. -/
theorem twoSLSRobustLinearRestrictionStdErrorFinSucc_pos_of_cov_posDef
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {R : Matrix Unit k ℝ}
    (hR : Function.Injective Rᵀ.mulVec)
    (hVhat : ∀ n ω,
      (twoSLSVHatStar
        (stackRegressors Z (n + 1) ω) (stackRegressors X (n + 1) ω)
        (stackOutcomes Y (n + 1) ω)).PosDef) :
    ∀ n ω, 0 < twoSLSRobustLinearRestrictionStdErrorFinSucc R Z X Y n ω :=
  twoSLSRobustLinearRestrictionStdErrorFinSucc_pos_of_restrictionCov_posDef
    (R := R)
    (twoSLSRobustRestrictionCovFinSucc_posDef_of_cov_posDef
      (R := R) hR hVhat)

omit [MeasurableSpace Ω] in
set_option linter.style.longLine false in
/-- Finite-sample positive definiteness of the robust coefficient covariance
and full rank of the one-row restriction imply positivity of Hansen's
sample-side percentile-`t` standard error. -/
theorem twoSLSRobustLinearRestrictionEstimatorStdErrorFinSucc_pos_of_cov_posDef
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {R : Matrix Unit k ℝ}
    (hR : Function.Injective Rᵀ.mulVec)
    (hVhat : ∀ n ω,
      (twoSLSVHatStar
        (stackRegressors Z (n + 1) ω) (stackRegressors X (n + 1) ω)
        (stackOutcomes Y (n + 1) ω)).PosDef) :
    ∀ n ω,
      0 < twoSLSRobustLinearRestrictionEstimatorStdErrorFinSucc R Z X Y n ω :=
  twoSLSRobustLinearRestrictionEstimatorStdErrorFinSucc_pos_of_restrictionCov_posDef
    (R := R)
    (twoSLSRobustRestrictionCovFinSucc_posDef_of_cov_posDef
      (R := R) hR hVhat)

omit [MeasurableSpace Ω] in
set_option linter.style.longLine false in
/-- The Chapter 10 percentile-`t` statistic with Hansen's unscaled standard
error divided by `sqrt(n+1)` is the Chapter 12 robust 2SLS t-ratio. -/
@[simp]
theorem percentileTStatistic_twoSLSRobustLinearRestrictionEstimatorStdErrorFinSucc
    (R : Matrix Unit k ℝ)
    (Z : ℕ → Ω → l → ℝ) (X : ℕ → Ω → k → ℝ) (Y : ℕ → Ω → ℝ)
    (β : k → ℝ) (n : ℕ) (ω : Ω) :
    percentileTStatistic (linearRestrictionEstimate R β)
      (twoSLSLinearRestrictionEstimateFinSucc R Z X Y n ω)
      (twoSLSRobustLinearRestrictionEstimatorStdErrorFinSucc R Z X Y n ω) =
      twoSLSRobustLinearTStatFinSucc R Z X Y β n ω := by
  dsimp [percentileTStatistic, twoSLSRobustLinearTStatFinSucc,
    scalarFunctionTStat,
    twoSLSRobustLinearRestrictionEstimatorStdErrorFinSucc]
  by_cases hroot : Real.sqrt (n + 1 : ℝ) = 0
  · simp [hroot]
  · by_cases hse :
      twoSLSRobustLinearRestrictionStdErrorFinSucc R Z X Y n ω = 0
    · simp [hse]
    · field_simp [hroot, hse]

omit [MeasurableSpace Ω] [DecidableEq k] in
private theorem linearRestrictionEstimate_smul_sub
    (R : Matrix Unit k ℝ) (b β : k → ℝ) (root : ℝ) :
    linearRestrictionEstimate R (root • (b - β)) =
      root * (linearRestrictionEstimate R b - linearRestrictionEstimate R β) := by
  simpa [linearRestrictionEstimate, Matrix.mulVec_smul] using
    linearMapUnit_smul_sub_dot_one R b β root

set_option linter.style.longLine false in
/-- Sample-side one-row restriction CLT from the coefficient CLT.

This is the non-studentized scalar sample input for Hansen Theorem 12.8's
percentile interval: no covariance or standard-error consistency is used, only
the fixed linear restriction map applied to the coefficient limit. -/
theorem
    twoSLSLinearRestrictionEstimateFinSucc_tendstoInDistribution_of_coefficient
    [IsProbabilityMeasure μ]
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {β : k → ℝ} {R : Matrix Unit k ℝ} {Vβ : Matrix k k ℝ}
    (hβ :
      TendstoInDistribution
        (fun (n : ℕ) ω =>
          Real.sqrt ((n + 1 : ℕ) : ℝ) •
            (twoSLSBetaStar
              (stackRegressors Z (n + 1) ω) (stackRegressors X (n + 1) ω)
              (stackOutcomes Y (n + 1) ω) - β))
        atTop (fun z : EuclideanSpace ℝ k => z.ofLp) (fun _ => μ)
        (multivariateGaussian 0 Vβ)) :
    TendstoInDistribution
      (fun n ω =>
        Real.sqrt ((n + 1 : ℕ) : ℝ) *
          (twoSLSLinearRestrictionEstimateFinSucc R Z X Y n ω -
            linearRestrictionEstimate R β))
      atTop
      (fun z : EuclideanSpace ℝ k =>
        linearRestrictionEstimate R (z : k → ℝ))
      (fun _ => μ) (multivariateGaussian 0 Vβ) := by
  let rawNum : ℕ → Ω → ℝ := fun n ω =>
    linearRestrictionEstimate R
      (Real.sqrt ((n + 1 : ℕ) : ℝ) •
        (twoSLSBetaStar
          (stackRegressors Z (n + 1) ω) (stackRegressors X (n + 1) ω)
          (stackOutcomes Y (n + 1) ω) - β))
  let num : ℕ → Ω → ℝ := fun n ω =>
    Real.sqrt ((n + 1 : ℕ) : ℝ) *
      (twoSLSLinearRestrictionEstimateFinSucc R Z X Y n ω -
        linearRestrictionEstimate R β)
  have hlinear :
      TendstoInDistribution rawNum atTop
        (fun z : EuclideanSpace ℝ k => linearRestrictionEstimate R (z : k → ℝ))
        (fun _ => μ) (multivariateGaussian 0 Vβ) := by
    simpa [rawNum, Function.comp_def] using
      hβ.continuous_comp (continuous_linearRestrictionEstimate R)
  have hnum_eq : ∀ n, rawNum n =ᵐ[μ] num n := by
    intro n
    filter_upwards with ω
    simpa [rawNum, num, twoSLSLinearRestrictionEstimateFinSucc] using
      linearRestrictionEstimate_smul_sub R
        (twoSLSBetaStar
          (stackRegressors Z (n + 1) ω) (stackRegressors X (n + 1) ω)
          (stackOutcomes Y (n + 1) ω))
        β (Real.sqrt ((n + 1 : ℕ) : ℝ))
  exact TendstoInDistribution.congr hnum_eq Filter.EventuallyEq.rfl hlinear

set_option linter.style.longLine false in
/-- Non-studentized percentile interval coverage from a sample coefficient CLT
and a scalar ordinary-bootstrap weak limit.

This is the direct Chapter 12.8 bridge from coefficient-level asymptotics to
Hansen's non-studentized bootstrap percentile interval: the original-sample
restriction CLT is derived internally by applying `R` to the coefficient CLT,
and the bootstrap scalar weak limit is converted to Chapter 10's indexed CDF
API by the scalar-law bridge above. -/
theorem
    twoSLSBootstrapLinearRestrictionPercentileCIEventFinSucc_tendsto_one_sub_alpha_uniform_of_coefficient_weakDistribution_quantileCalibration
    [IsProbabilityMeasure μ]
    {νstar : Measure Ωstar} [IsProbabilityMeasure νstar]
    {η : Measure ℝ} [IsProbabilityMeasure η] [NoAtoms η]
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {R : Matrix Unit k ℝ} {β : k → ℝ} {Vβ : Matrix k k ℝ}
    {Zlim : Ωstar → ℝ} {q α : ℝ}
    (hβ :
      TendstoInDistribution
        (fun (n : ℕ) ω =>
          Real.sqrt ((n + 1 : ℕ) : ℝ) •
            (twoSLSBetaStar
              (stackRegressors Z (n + 1) ω) (stackRegressors X (n + 1) ω)
              (stackOutcomes Y (n + 1) ω) - β))
        atTop (fun z : EuclideanSpace ℝ k => z.ofLp) (fun _ => μ)
        (multivariateGaussian 0 Vβ))
    (hTstarWeak :
      TendstoInBootstrapWeakDistributionIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs =>
          twoSLSBootstrapLinearRestrictionStatisticFinSucc R Z X Y n ω ωs)
        νstar Zlim)
    (hZlaw : HasLaw Zlim η νstar)
    (hξlaw :
      HasLaw
        (fun z : EuclideanSpace ℝ k =>
          linearRestrictionEstimate R (z : k → ℝ))
        η (multivariateGaussian 0 Vβ))
    (hquantile :
      TwoSLSBootstrapLinearRestrictionPercentileQuantileCalibrationInputs
        μ Z X Y R η q α) :
    Tendsto
      (fun n =>
        μ {ω |
          twoSLSBootstrapLinearRestrictionPercentileCIEventFinSucc
            R Z X Y β α n ω})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) := by
  have hstat :=
    twoSLSLinearRestrictionEstimateFinSucc_tendstoInDistribution_of_coefficient
      (μ := μ) (Z := Z) (X := X) (Y := Y) (β := β)
      (R := R) (Vβ := Vβ) hβ
  have hPstar : ∀ n (ω : Ω),
      IsProbabilityMeasure
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω) n ω) :=
    fun n ω =>
      twoSLSBootstrapUniformPstarFinSucc_isProbabilityMeasure (Ω := Ω) n ω
  have hTmeas : ∀ n (ω : Ω),
      Measurable
        (fun ωs =>
          twoSLSBootstrapLinearRestrictionStatisticFinSucc R Z X Y n ω ωs) :=
    fun n ω =>
      twoSLSBootstrapLinearRestrictionStatisticFinSucc_measurable
        (R := R) (Z := Z) (X := X) (Y := Y) n ω
  have hTstar :
      TendstoInBootstrapDistributionIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs (_ : Unit) =>
          twoSLSBootstrapLinearRestrictionStatisticFinSucc R Z X Y n ω ωs)
        νstar (fun ωstar (_ : Unit) => Zlim ωstar) :=
    scalarBootstrapWeakDistribution_to_unitDistribution_of_hasLaw
      (μ := μ) (Pstar := twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
      (νstar := νstar) (η := η)
      (Tstar := fun n ω ωs =>
        twoSLSBootstrapLinearRestrictionStatisticFinSucc R Z X Y n ω ωs)
      (Zlim := Zlim) hTstarWeak hPstar hTmeas hZlaw
  exact
    twoSLSBootstrapLinearRestrictionPercentileCIEventFinSucc_tendsto_one_sub_alpha_uniform_of_quantileCalibration
      (μ := μ) (ν := multivariateGaussian 0 Vβ)
      (Ωstar := Ωstar) (νstar := νstar) (η := η)
      (Z := Z) (X := X) (Y := Y) (R := R) (β := β)
      (ξ := fun z : EuclideanSpace ℝ k =>
        linearRestrictionEstimate R (z : k → ℝ))
      (Zlim := Zlim) (q := q) (α := α)
      hstat hTstar hZlaw hξlaw hquantile

set_option linter.style.longLine false in
/-- Hansen Theorem 12.8 non-studentized percentile interval coverage from
sample and bootstrap coefficient CLTs.

Compared with the scalar-law bridge, this wrapper also derives the bootstrap
one-row numerator limit from the ordinary-bootstrap coefficient condition
package. The only remaining interval-side inputs are the scalar linear-image
law's nonatomicity and the Chapter 10 percentile quantile calibration fields. -/
theorem
    twoSLSBootstrapLinearRestrictionPercentileCIEventFinSucc_theorem12_8_of_coefficient_bootstrap_quantileCalibration
    [IsProbabilityMeasure μ]
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {R : Matrix Unit k ℝ} {β : k → ℝ} {Vβ : Matrix k k ℝ}
    {q α : ℝ}
    (hη_noAtoms :
      NoAtoms
        ((multivariateGaussian (0 : EuclideanSpace ℝ k) Vβ).map
          (fun z : EuclideanSpace ℝ k =>
            linearRestrictionEstimate R (z : k → ℝ))))
    (hβ_sample :
      TendstoInDistribution
        (fun (n : ℕ) ω =>
          Real.sqrt ((n + 1 : ℕ) : ℝ) •
            (twoSLSBetaStar
              (stackRegressors Z (n + 1) ω) (stackRegressors X (n + 1) ω)
              (stackOutcomes Y (n + 1) ω) - β))
        atTop (fun z : EuclideanSpace ℝ k => z.ofLp) (fun _ => μ)
        (multivariateGaussian 0 Vβ))
    (hβ_boot :
      TwoSLSBootstrapAsymptoticNormalConditions μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω)) Z X Y Vβ)
    (hquantile :
      TwoSLSBootstrapLinearRestrictionPercentileQuantileCalibrationInputs
        μ Z X Y R
        ((multivariateGaussian (0 : EuclideanSpace ℝ k) Vβ).map
          (fun z : EuclideanSpace ℝ k =>
            linearRestrictionEstimate R (z : k → ℝ)))
        q α) :
    Tendsto
      (fun n =>
        μ {ω |
          twoSLSBootstrapLinearRestrictionPercentileCIEventFinSucc
            R Z X Y β α n ω})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) := by
  let η : Measure ℝ :=
    (multivariateGaussian (0 : EuclideanSpace ℝ k) Vβ).map
      (fun z : EuclideanSpace ℝ k =>
        linearRestrictionEstimate R (z : k → ℝ))
  have hlin_cont :
      Continuous
        (fun z : EuclideanSpace ℝ k =>
          linearRestrictionEstimate R (z : k → ℝ)) := by
    exact (continuous_linearRestrictionEstimate R).comp
      (PiLp.continuous_ofLp 2 (fun _ : k => ℝ))
  letI : IsProbabilityMeasure η :=
    Measure.isProbabilityMeasure_map hlin_cont.aemeasurable
  letI : NoAtoms η := hη_noAtoms
  have hlaw :
      HasLaw
        (fun z : EuclideanSpace ℝ k =>
          linearRestrictionEstimate R (z : k → ℝ))
        η (multivariateGaussian 0 Vβ) := by
    exact ⟨hlin_cont.aemeasurable, rfl⟩
  have hTstarWeak :
      TendstoInBootstrapWeakDistributionIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs =>
          twoSLSBootstrapLinearRestrictionStatisticFinSucc R Z X Y n ω ωs)
        (multivariateGaussian (0 : EuclideanSpace ℝ k) Vβ)
        (fun z : EuclideanSpace ℝ k =>
          linearRestrictionEstimate R (z : k → ℝ)) :=
    twoSLSBootstrapLinearRestrictionStatisticFinSucc_tendstoInBootstrapWeakDistribution_uniform
      (μ := μ) (Z := Z) (X := X) (Y := Y) (R := R)
      (Vβ := Vβ) hβ_boot
  exact
    twoSLSBootstrapLinearRestrictionPercentileCIEventFinSucc_tendsto_one_sub_alpha_uniform_of_coefficient_weakDistribution_quantileCalibration
      (μ := μ)
      (νstar := multivariateGaussian (0 : EuclideanSpace ℝ k) Vβ)
      (η := η) (Z := Z) (X := X) (Y := Y) (R := R)
      (β := β) (Vβ := Vβ)
      (Zlim := fun z : EuclideanSpace ℝ k =>
        linearRestrictionEstimate R (z : k → ℝ))
      (q := q) (α := α)
      hβ_sample hTstarWeak hlaw hlaw hquantile

set_option linter.style.longLine false in
/-- Hansen Theorem 12.8 non-studentized percentile interval coverage with the
scalar Gaussian limit law identified as `N(0, seθ²)`.

This wrapper removes the abstract linear-image nonatomicity input from
`..._coefficient_bootstrap_quantileCalibration`: positive asymptotic
restriction standard error supplies the no-atoms instance for the scalar
Gaussian law, while positive semidefiniteness identifies the law of `RZ`. -/
theorem
    twoSLSBootstrapLinearRestrictionPercentileCIEventFinSucc_theorem12_8_of_coefficient_bootstrap_gaussian_quantileCalibration
    [IsProbabilityMeasure μ]
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {R : Matrix Unit k ℝ} {β : k → ℝ} {Vβ : Matrix k k ℝ}
    {q α : ℝ}
    (hVβ : Vβ.PosSemidef)
    (hseθ : 0 < linearRestrictionStdError R Vβ)
    (hβ_sample :
      TendstoInDistribution
        (fun (n : ℕ) ω =>
          Real.sqrt ((n + 1 : ℕ) : ℝ) •
            (twoSLSBetaStar
              (stackRegressors Z (n + 1) ω) (stackRegressors X (n + 1) ω)
              (stackOutcomes Y (n + 1) ω) - β))
        atTop (fun z : EuclideanSpace ℝ k => z.ofLp) (fun _ => μ)
        (multivariateGaussian 0 Vβ))
    (hβ_boot :
      TwoSLSBootstrapAsymptoticNormalConditions μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω)) Z X Y Vβ)
    (hquantile :
      TwoSLSBootstrapLinearRestrictionPercentileQuantileCalibrationInputs
        μ Z X Y R
        (gaussianReal 0 (linearRestrictionStdError R Vβ ^ 2).toNNReal)
        q α) :
    Tendsto
      (fun n =>
        μ {ω |
          twoSLSBootstrapLinearRestrictionPercentileCIEventFinSucc
            R Z X Y β α n ω})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) := by
  haveI :
      NoAtoms
        (gaussianReal 0 (linearRestrictionStdError R Vβ ^ 2).toNNReal) :=
    noAtoms_gaussianReal
      (ne_of_gt (Real.toNNReal_pos.mpr (sq_pos_of_pos hseθ)))
  have hscalarLaw :
      HasLaw
        (fun z : EuclideanSpace ℝ k =>
          linearRestrictionEstimate R (z : k → ℝ))
        (gaussianReal 0 (linearRestrictionStdError R Vβ ^ 2).toNNReal)
        (multivariateGaussian 0 Vβ) :=
    linearRestrictionEstimate_hasLaw_gaussianReal_of_posSemidef
      (R := R) hVβ
  have hTstarWeak :
      TendstoInBootstrapWeakDistributionIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs =>
          twoSLSBootstrapLinearRestrictionStatisticFinSucc R Z X Y n ω ωs)
        (multivariateGaussian (0 : EuclideanSpace ℝ k) Vβ)
        (fun z : EuclideanSpace ℝ k =>
          linearRestrictionEstimate R (z : k → ℝ)) :=
    twoSLSBootstrapLinearRestrictionStatisticFinSucc_tendstoInBootstrapWeakDistribution_uniform
      (μ := μ) (Z := Z) (X := X) (Y := Y) (R := R)
      (Vβ := Vβ) hβ_boot
  exact
    twoSLSBootstrapLinearRestrictionPercentileCIEventFinSucc_tendsto_one_sub_alpha_uniform_of_coefficient_weakDistribution_quantileCalibration
      (μ := μ)
      (νstar := multivariateGaussian (0 : EuclideanSpace ℝ k) Vβ)
      (η := gaussianReal 0 (linearRestrictionStdError R Vβ ^ 2).toNNReal)
      (Z := Z) (X := X) (Y := Y) (R := R) (β := β) (Vβ := Vβ)
      (Zlim := fun z : EuclideanSpace ℝ k =>
        linearRestrictionEstimate R (z : k → ℝ))
      (q := q) (α := α)
      hβ_sample hTstarWeak hscalarLaw hscalarLaw hquantile

set_option linter.style.longLine false in
/-- Hansen Theorem 12.8 non-studentized percentile interval coverage with
asymptotic restriction nondegeneracy derived from a positive-definite
coefficient covariance and a nonzero one-row restriction.

This is the row-nonzero companion to
`twoSLSBootstrapLinearRestrictionPercentileCIEventFinSucc_theorem12_8_of_coefficient_bootstrap_gaussian_quantileCalibration`:
the only changed input is that callers provide the Hansen-style nonzero row
condition instead of the derived scalar standard-error positivity field. -/
theorem
    twoSLSBootstrapLinearRestrictionPercentileCIEventFinSucc_theorem12_8_of_coefficient_bootstrap_gaussian_quantileCalibration_row_ne_zero
    [IsProbabilityMeasure μ]
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {R : Matrix Unit k ℝ} {β : k → ℝ} {Vβ : Matrix k k ℝ}
    {q α : ℝ}
    (hVβ : Vβ.PosDef)
    (hR : ∃ j : k, R () j ≠ 0)
    (hβ_sample :
      TendstoInDistribution
        (fun (n : ℕ) ω =>
          Real.sqrt ((n + 1 : ℕ) : ℝ) •
            (twoSLSBetaStar
              (stackRegressors Z (n + 1) ω) (stackRegressors X (n + 1) ω)
              (stackOutcomes Y (n + 1) ω) - β))
        atTop (fun z : EuclideanSpace ℝ k => z.ofLp) (fun _ => μ)
        (multivariateGaussian 0 Vβ))
    (hβ_boot :
      TwoSLSBootstrapAsymptoticNormalConditions μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω)) Z X Y Vβ)
    (hquantile :
      TwoSLSBootstrapLinearRestrictionPercentileQuantileCalibrationInputs
        μ Z X Y R
        (gaussianReal 0 (linearRestrictionStdError R Vβ ^ 2).toNNReal)
        q α) :
    Tendsto
      (fun n =>
        μ {ω |
          twoSLSBootstrapLinearRestrictionPercentileCIEventFinSucc
            R Z X Y β α n ω})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) := by
  let hRinj : Function.Injective Rᵀ.mulVec :=
    oneRow_transpose_mulVec_injective_of_exists_ne_zero hR
  have hVθ : (R * Vβ * Rᵀ).PosDef := by
    have hcov : ((Rᵀ)ᵀ * Vβ * Rᵀ).PosDef :=
      restrictionCov_posDef_of_cov_posDef Vβ Rᵀ hVβ hRinj
    simpa using hcov
  exact
    twoSLSBootstrapLinearRestrictionPercentileCIEventFinSucc_theorem12_8_of_coefficient_bootstrap_gaussian_quantileCalibration
      (μ := μ) (Z := Z) (X := X) (Y := Y) (R := R)
      (β := β) (Vβ := Vβ) (q := q) (α := α)
      hVβ.posSemidef
      (linearRestrictionStdError_pos_of_restrictionCov_posDef R hVθ)
      hβ_sample hβ_boot hquantile

set_option linter.style.longLine false in
/-- Residual-row textbook-fourth Assumption 12.2 non-studentized percentile
interval coverage for Hansen Theorem 12.8.

The sample coefficient CLT is supplied by the textbook Theorem 12.2 wrapper;
the bootstrap coefficient package is assembled from the existing
true-score-bound and uniform-remainder route. Quantile calibration for the
scalar Gaussian limit remains the interval-side primitive. -/
theorem
    twoSLSBootstrapLinearRestrictionPercentileCIEventFinSucc_theorem12_8_of_textbook_fourth_uniform_remainders_trueScore_norm_bound_quantileCalibration_row_ne_zero
    [IsProbabilityMeasure μ]
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {R : Matrix Unit k ℝ} {β : k → ℝ} {q α C : ℝ}
    (h : TwoSLSAssumption12_2JointIidTextbookFourthConditions μ Z X e Y β)
    (hR : ∃ j : k, R () j ≠ 0)
    (hTrueBound :
      ∀ᶠ n in atTop,
        ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
          ‖twoSLSBootstrapTrueRecenteredScoreStatisticFinSucc
            Z e n ω ωs‖ ≤ C)
    (hResidSmall : ∀ δ : ℝ, 0 < δ →
      ∀ᶠ n in atTop,
        ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
          ‖twoSLSBootstrapResidualSubstitutionRecenteredScoreStatisticFinSucc
            Z X Y β n ω ωs‖ < δ)
    (hPopSmall : ∀ δ : ℝ, 0 < δ →
      ∀ᶠ n in atTop,
        ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
          dist (twoSLSBootstrapLinearizedGapFinSucc Z X Y n ω ωs)
            (twoSLSBootstrapPopulationLinearizedGapFinSucc
              (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
              (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
              (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))
              Z X Y n ω ωs) < δ)
    (hCoefSmall : ∀ δ : ℝ, 0 < δ →
      ∀ᶠ n in atTop,
        ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
          dist (twoSLSBootstrapBetaGapFinSucc Z X Y n ω ωs)
            (twoSLSBootstrapLinearizedGapFinSucc Z X Y n ω ωs) < δ)
    (hquantile :
      TwoSLSBootstrapLinearRestrictionPercentileQuantileCalibrationInputs
        μ Z X Y R
        (gaussianReal 0
          (linearRestrictionStdError R
            (twoSLSAsymptoticVariance
              (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
              (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
              (scoreCovMat μ Z e)
              (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))) ^
            2).toNNReal)
        q α) :
    Tendsto
      (fun n =>
        μ {ω |
          twoSLSBootstrapLinearRestrictionPercentileCIEventFinSucc
            R Z X Y β α n ω})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) := by
  let Vβ : Matrix k k ℝ :=
    twoSLSAsymptoticVariance
      (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
      (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
      (scoreCovMat μ Z e)
      (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))
  let hiid : TwoSLSAssumption12_2IidFourthConditions μ Z X e :=
    h.toJointIidMixedMomentConditions.toTwoSLSAssumption12_2JointIidFourthConditions.toIidFourthConditions
  let hGram := hiid.toGramConditions
  have hVβ_pos : Vβ.PosDef := by
    dsimp [Vβ]
    exact
      twoSLSAsymptoticVariance_posDef_of_qzz_omega_rank
        (QXZ := twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
        (QZZ := twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
        (Omega := scoreCovMat μ Z e)
        (QZX := twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))
        (twoSLSCombinedQXZ_eq_transpose_QZX_of_popGram_wlln
          (μ := μ) (Z := Z) (X := X)
          hGram.toTwoSLSAssumption12_1GramConditions.combined_gram)
        hiid.qzz_posDef hiid.omega_posDef hiid.qzx_rank
  have hβ0 :=
    twoSLSBetaStar_tendstoInDistribution_formula_of_textbook12_2_joint_iid_fourth
      (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y) h
  have hβ_shift :
      TendstoInDistribution
        (fun (n : ℕ) ω =>
          Real.sqrt ((n + 1 : ℕ) : ℝ) •
            (twoSLSBetaStar
              (stackRegressors Z (n + 1) ω) (stackRegressors X (n + 1) ω)
              (stackOutcomes Y (n + 1) ω) - β))
        atTop (fun z : EuclideanSpace ℝ k => z.ofLp) (fun _ => μ)
        (multivariateGaussian 0 Vβ) := by
    refine
      { forall_aemeasurable := ?_
        aemeasurable_limit := by
          simpa [Vβ] using hβ0.aemeasurable_limit
        tendsto := ?_ }
    · intro n
      simpa [Vβ, stackRegressors, stackOutcomes] using
        hβ0.forall_aemeasurable (n + 1)
    · have hcomp := hβ0.tendsto.comp (tendsto_add_atTop_nat 1)
      convert hcomp using 1 with n
  let hresid :
      TwoSLSBootstrapResidualSubstitutionNegligibilityInputs μ Z X Y β :=
    TwoSLSBootstrapResidualSubstitutionNegligibilityInputs.of_uniform_norm_vanish
      (μ := μ) (Z := Z) (X := X) (Y := Y) (β := β) hResidSmall
  let hcoef :
      TwoSLSBootstrapCoefficientLinearizationClosenessInputs μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω)) Z X Y
        (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
        (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
        (scoreCovMat μ Z e)
        (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X))) :=
    TwoSLSBootstrapCoefficientLinearizationClosenessInputs.of_uniform_dist_vanish
      (μ := μ) (Pstar := twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
      (Z := Z) (X := X) (Y := Y)
      (QXZ := twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
      (QZZ := twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
      (Omega := scoreCovMat μ Z e)
      (QZX := twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))
      hPopSmall hCoefSmall
  let hTrueTail := by
    exact
      twoSLSBootstrapTrueRecenteredScoreStatisticFinSucc_compactTail_uniform_of_eventually_norm_bound
        (μ := μ) (Z := Z) (e := e) hTrueBound
  let hβ_boot :
      TwoSLSBootstrapFormulaAsymptoticNormalConditions μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω)) Z X Y
        (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
        (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
        (scoreCovMat μ Z e)
        (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X))) :=
    twoSLSBootstrapFormulaAsymptoticNormalConditions_uniform_of_assumption12_2_residualSubstitutionNegligibility_trueScoreTail_closeness
      (μ := μ) (Z := Z) (X := X) (Y := Y) (e := e)
      hiid h.model hresid hTrueTail hcoef
  exact
    twoSLSBootstrapLinearRestrictionPercentileCIEventFinSucc_theorem12_8_of_coefficient_bootstrap_gaussian_quantileCalibration_row_ne_zero
      (μ := μ) (Z := Z) (X := X) (Y := Y) (R := R)
      (β := β) (Vβ := Vβ) (q := q) (α := α)
      hVβ_pos hR hβ_shift hβ_boot
      (by simpa [Vβ] using hquantile)

set_option linter.style.longLine false in
/-- Observed-row textbook-fourth Assumption 12.2 non-studentized percentile
interval coverage for Hansen Theorem 12.8.

This observed-data facade reuses the residual-row theorem through
`toResidualTextbookFourthConditions`, matching the observed-row style used by
the coefficient and robust percentile-`t` endpoints. -/
theorem
    twoSLSBootstrapLinearRestrictionPercentileCIEventFinSucc_theorem12_8_of_observed_textbook_fourth_uniform_remainders_trueScore_norm_bound_quantileCalibration_row_ne_zero
    [IsProbabilityMeasure μ]
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {R : Matrix Unit k ℝ} {β : k → ℝ} {q α C : ℝ}
    (h : TwoSLSAssumption12_2ObservedIidTextbookFourthConditions μ Z X e Y β)
    (hR : ∃ j : k, R () j ≠ 0)
    (hTrueBound :
      ∀ᶠ n in atTop,
        ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
          ‖twoSLSBootstrapTrueRecenteredScoreStatisticFinSucc
            Z e n ω ωs‖ ≤ C)
    (hResidSmall : ∀ δ : ℝ, 0 < δ →
      ∀ᶠ n in atTop,
        ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
          ‖twoSLSBootstrapResidualSubstitutionRecenteredScoreStatisticFinSucc
            Z X Y β n ω ωs‖ < δ)
    (hPopSmall : ∀ δ : ℝ, 0 < δ →
      ∀ᶠ n in atTop,
        ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
          dist (twoSLSBootstrapLinearizedGapFinSucc Z X Y n ω ωs)
            (twoSLSBootstrapPopulationLinearizedGapFinSucc
              (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
              (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
              (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))
              Z X Y n ω ωs) < δ)
    (hCoefSmall : ∀ δ : ℝ, 0 < δ →
      ∀ᶠ n in atTop,
        ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
          dist (twoSLSBootstrapBetaGapFinSucc Z X Y n ω ωs)
            (twoSLSBootstrapLinearizedGapFinSucc Z X Y n ω ωs) < δ)
    (hquantile :
      TwoSLSBootstrapLinearRestrictionPercentileQuantileCalibrationInputs
        μ Z X Y R
        (gaussianReal 0
          (linearRestrictionStdError R
            (twoSLSAsymptoticVariance
              (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
              (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
              (scoreCovMat μ Z e)
              (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))) ^
            2).toNNReal)
        q α) :
    Tendsto
      (fun n =>
        μ {ω |
          twoSLSBootstrapLinearRestrictionPercentileCIEventFinSucc
            R Z X Y β α n ω})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) :=
  twoSLSBootstrapLinearRestrictionPercentileCIEventFinSucc_theorem12_8_of_textbook_fourth_uniform_remainders_trueScore_norm_bound_quantileCalibration_row_ne_zero
    (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y)
    (R := R) (β := β) (q := q) (α := α) (C := C)
    h.toResidualTextbookFourthConditions hR hTrueBound hResidSmall
    hPopSmall hCoefSmall hquantile

set_option linter.style.longLine false in
/-- Sample-side robust 2SLS t-ratio limit derived from a coefficient CLT and
robust covariance consistency.

This is the original-sample analogue of the bootstrap studentization bridges:
the scalar numerator is obtained by applying the fixed one-row restriction to
the coefficient CLT, while the denominator is the continuous image of the
robust covariance estimator. -/
theorem
    twoSLSRobustLinearTStatFinSucc_tendstoInDistribution_standardNormal_of_coefficient_covariance
    [IsProbabilityMeasure μ]
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {β : k → ℝ} {R : Matrix Unit k ℝ} {Vβ : Matrix k k ℝ}
    (hVβ : Vβ.PosSemidef)
    (hseθ : 0 < linearRestrictionStdError R Vβ)
    (hβ :
      TendstoInDistribution
        (fun (n : ℕ) ω =>
          Real.sqrt ((n + 1 : ℕ) : ℝ) •
            (twoSLSBetaStar
              (stackRegressors Z (n + 1) ω) (stackRegressors X (n + 1) ω)
              (stackOutcomes Y (n + 1) ω) - β))
        atTop (fun z : EuclideanSpace ℝ k => z.ofLp) (fun _ => μ)
        (multivariateGaussian 0 Vβ))
    (hV_meas : ∀ n,
      AEStronglyMeasurable
        (fun ω =>
          twoSLSVHatStar
            (stackRegressors Z (n + 1) ω) (stackRegressors X (n + 1) ω)
            (stackOutcomes Y (n + 1) ω)) μ)
    (hV :
      TendstoInMeasure μ
        (fun n ω =>
          twoSLSVHatStar
            (stackRegressors Z (n + 1) ω) (stackRegressors X (n + 1) ω)
            (stackOutcomes Y (n + 1) ω))
        atTop (fun _ => Vβ)) :
    TendstoInDistribution
      (fun n ω => twoSLSRobustLinearTStatFinSucc R Z X Y β n ω)
      atTop (fun x : ℝ => x) (fun _ => μ) (gaussianReal 0 1) := by
  let S : Matrix Unit Unit ℝ := R * Vβ * Rᵀ
  let c : ℝ := linearRestrictionStdError R Vβ
  let rawNum : ℕ → Ω → ℝ := fun n ω =>
    linearRestrictionEstimate R
      (Real.sqrt ((n + 1 : ℕ) : ℝ) •
        (twoSLSBetaStar
          (stackRegressors Z (n + 1) ω) (stackRegressors X (n + 1) ω)
          (stackOutcomes Y (n + 1) ω) - β))
  let num : ℕ → Ω → ℝ := fun n ω =>
    Real.sqrt ((n + 1 : ℕ) : ℝ) *
      (twoSLSLinearRestrictionEstimateFinSucc R Z X Y n ω -
        linearRestrictionEstimate R β)
  let se : ℕ → Ω → ℝ := fun n ω =>
    twoSLSRobustLinearRestrictionStdErrorFinSucc R Z X Y n ω
  have hlinear :
      TendstoInDistribution rawNum atTop
        (fun z : EuclideanSpace ℝ k => linearRestrictionEstimate R (z : k → ℝ))
        (fun _ => μ) (multivariateGaussian 0 Vβ) := by
    simpa [rawNum, Function.comp_def] using
      hβ.continuous_comp (continuous_linearRestrictionEstimate R)
  have hS : S.PosSemidef := by
    simpa [S, Matrix.conjTranspose] using
      Matrix.PosSemidef.conjTranspose_mul_mul_same hVβ Rᵀ
  have hlinLaw :
      HasLaw (fun z : EuclideanSpace ℝ k => WithLp.toLp 2 (R *ᵥ z.ofLp))
        (multivariateGaussian (0 : EuclideanSpace ℝ Unit) S)
        (multivariateGaussian (0 : EuclideanSpace ℝ k) Vβ) := by
    simpa [S] using
      hasLaw_multivariateGaussian_zero_linearMap
        (n := k) (q := Unit) hVβ R
  have hcoordLawUnit :
      HasLaw (fun z : EuclideanSpace ℝ Unit => z.ofLp ())
        (gaussianReal 0 (S () ()).toNNReal)
        (multivariateGaussian (0 : EuclideanSpace ℝ Unit) S) := by
    simpa using
      multivariateGaussian_eval_hasLaw
        (μ := (0 : EuclideanSpace ℝ Unit)) (S := S) hS ()
  have hcoordLaw :
      HasLaw
        (fun z : EuclideanSpace ℝ k =>
          (WithLp.toLp 2 (R *ᵥ z.ofLp) : EuclideanSpace ℝ Unit).ofLp ())
        (gaussianReal 0 (S () ()).toNNReal)
        (multivariateGaussian (0 : EuclideanSpace ℝ k) Vβ) := by
    simpa [Function.comp_def] using HasLaw.comp hcoordLawUnit hlinLaw
  have hZlaw :
      HasLaw
        (fun z : EuclideanSpace ℝ k =>
          linearRestrictionEstimate R (z : k → ℝ))
        (gaussianReal 0 (S () ()).toNNReal)
        (multivariateGaussian (0 : EuclideanSpace ℝ k) Vβ) := by
    refine hcoordLaw.congr ?_
    filter_upwards with z
    simp [linearRestrictionEstimate]
  have hσ :
      S () () = c ^ 2 := by
    simpa [S, c, linearRestrictionStdError] using
      (Real.sq_sqrt (hS.diag_nonneg (i := ()))).symm
  have hstdLaw :
      HasLaw (fun z : ℝ => c * z)
        (gaussianReal 0 (S () ()).toNNReal) (gaussianReal 0 1) :=
    hasLaw_const_mul_id_gaussianReal_of_variance_eq hσ
  have hrawNum :
      TendstoInDistribution rawNum atTop (fun z : ℝ => c * z)
        (fun _ => μ) (gaussianReal 0 1) := by
    refine
      { forall_aemeasurable := hlinear.forall_aemeasurable
        aemeasurable_limit := hstdLaw.aemeasurable
        tendsto := ?_ }
    have hlimit :
        (⟨(multivariateGaussian 0 Vβ).map
            (fun z : EuclideanSpace ℝ k => linearRestrictionEstimate R (z : k → ℝ)),
          Measure.isProbabilityMeasure_map hlinear.aemeasurable_limit⟩ :
            ProbabilityMeasure ℝ) =
          ⟨(gaussianReal 0 1).map (fun z : ℝ => c * z),
            Measure.isProbabilityMeasure_map hstdLaw.aemeasurable⟩ := by
      apply Subtype.ext
      simpa [linearRestrictionEstimate] using
        hZlaw.map_eq.trans hstdLaw.map_eq.symm
    rw [← hlimit]
    exact hlinear.tendsto
  have hnum_eq : ∀ n, rawNum n =ᵐ[μ] num n := by
    intro n
    filter_upwards with ω
    simpa [rawNum, num, twoSLSLinearRestrictionEstimateFinSucc] using
      linearRestrictionEstimate_smul_sub R
        (twoSLSBetaStar
          (stackRegressors Z (n + 1) ω) (stackRegressors X (n + 1) ω)
          (stackOutcomes Y (n + 1) ω))
        β (Real.sqrt ((n + 1 : ℕ) : ℝ))
  have hnum :
      TendstoInDistribution num atTop (fun z : ℝ => c * z)
        (fun _ => μ) (gaussianReal 0 1) :=
    TendstoInDistribution.congr hnum_eq Filter.EventuallyEq.rfl hrawNum
  have hse :
      TendstoInMeasure μ se atTop (fun _ => c) := by
    simpa [se, c, twoSLSRobustLinearRestrictionStdErrorFinSucc] using
      tendstoInMeasure_continuous_comp
        (μ := μ)
        (f := fun n ω =>
          twoSLSVHatStar
            (stackRegressors Z (n + 1) ω) (stackRegressors X (n + 1) ω)
            (stackOutcomes Y (n + 1) ω))
        (g := fun _ => Vβ)
        (h := fun V : Matrix k k ℝ => linearRestrictionStdError R V)
        hV_meas hV (continuous_linearRestrictionStdError R)
  have hse_meas : ∀ n, AEMeasurable (se n) μ := by
    intro n
    simpa [se, twoSLSRobustLinearRestrictionStdErrorFinSucc] using
      linearCovarianceStdError_aemeasurable
        (μ := μ) (R := R)
        (Vhat := fun ω =>
          twoSLSVHatStar
            (stackRegressors Z (n + 1) ω) (stackRegressors X (n + 1) ω)
            (stackOutcomes Y (n + 1) ω))
        (hV_meas n)
  have hratio :=
    studentizedLimit_tendstoInDistribution
      (μ := μ) (ν := gaussianReal 0 1) (num := num) (se := se)
      (Z := fun x : ℝ => c * x) (c := c)
      (by simpa [c] using hseθ) hnum hse hse_meas
  have hstat :
      TendstoInDistribution
        (fun n ω => twoSLSRobustLinearTStatFinSucc R Z X Y β n ω)
        atTop (fun x : ℝ => c * x / c) (fun _ => μ) (gaussianReal 0 1) := by
    simpa [num, se, c, twoSLSRobustLinearTStatFinSucc, scalarFunctionTStat,
      twoSLSLinearRestrictionEstimateFinSucc, linearRestrictionEstimate,
      linearMapUnit_smul_sub_dot_one] using hratio
  convert hstat using 2
  · rename_i x
    dsimp [c]
    exact (mul_div_cancel_left₀ x hseθ.ne').symm

set_option linter.style.longLine false in
/-- Build the asymptotic sample-side percentile-`t` package from coefficient
and covariance convergence.

Covariance consistency sends the unscaled restriction standard error to the
positive limit `linearRestrictionStdError R Vβ`. Consequently the probability
of a nonpositive realized standard error tends to zero; no finite-sample
positive-definiteness premise is needed. -/
theorem
    TwoSLSBootstrapRobustPercentileTAsymptoticSampleInputs.of_coefficient_clt_covariance_consistency
    [IsProbabilityMeasure μ]
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {β : k → ℝ} {R : Matrix Unit k ℝ} {Vβ : Matrix k k ℝ}
    (hVβ : Vβ.PosSemidef)
    (hseθ : 0 < linearRestrictionStdError R Vβ)
    (hβ :
      TendstoInDistribution
        (fun (n : ℕ) ω =>
          Real.sqrt ((n + 1 : ℕ) : ℝ) •
            (twoSLSBetaStar
              (stackRegressors Z (n + 1) ω) (stackRegressors X (n + 1) ω)
              (stackOutcomes Y (n + 1) ω) - β))
        atTop (fun z : EuclideanSpace ℝ k => z.ofLp) (fun _ => μ)
        (multivariateGaussian 0 Vβ))
    (hV_meas : ∀ n,
      AEStronglyMeasurable
        (fun ω =>
          twoSLSVHatStar
            (stackRegressors Z (n + 1) ω) (stackRegressors X (n + 1) ω)
            (stackOutcomes Y (n + 1) ω)) μ)
    (hV :
      TendstoInMeasure μ
        (fun n ω =>
          twoSLSVHatStar
            (stackRegressors Z (n + 1) ω) (stackRegressors X (n + 1) ω)
            (stackOutcomes Y (n + 1) ω))
        atTop (fun _ => Vβ)) :
    TwoSLSBootstrapRobustPercentileTAsymptoticSampleInputs
      μ Z X Y β R := by
  have hscale :
      TendstoInMeasure μ
        (fun n ω =>
          twoSLSRobustLinearRestrictionStdErrorFinSucc R Z X Y n ω)
        atTop (fun _ => linearRestrictionStdError R Vβ) := by
    simpa [twoSLSRobustLinearRestrictionStdErrorFinSucc] using
      tendstoInMeasure_continuous_comp
        (μ := μ)
        (f := fun n ω =>
          twoSLSVHatStar
            (stackRegressors Z (n + 1) ω) (stackRegressors X (n + 1) ω)
            (stackOutcomes Y (n + 1) ω))
        (g := fun _ => Vβ)
        (h := fun V : Matrix k k ℝ => linearRestrictionStdError R V)
        hV_meas hV (continuous_linearRestrictionStdError R)
  have hscale_nonpos :
      Tendsto
        (fun n =>
          μ {ω |
            twoSLSRobustLinearRestrictionStdErrorFinSucc R Z X Y n ω ≤ 0})
        atTop (𝓝 0) :=
    tendsto_measure_nonpos_of_tendstoInMeasure_const_pos
      (μ := μ) hseθ hscale
  have hestimator_nonpos :
      Tendsto
        (fun n =>
          μ {ω |
            twoSLSRobustLinearRestrictionEstimatorStdErrorFinSucc
              R Z X Y n ω ≤ 0})
        atTop (𝓝 0) := by
    refine hscale_nonpos.congr' ?_
    exact Eventually.of_forall fun n => by
      apply congrArg μ
      ext ω
      have hn : 0 < (n + 1 : ℝ) := by exact_mod_cast Nat.succ_pos n
      have hroot : 0 < Real.sqrt (n + 1 : ℝ) := Real.sqrt_pos.mpr hn
      change
        twoSLSRobustLinearRestrictionStdErrorFinSucc R Z X Y n ω ≤ 0 ↔
          twoSLSRobustLinearRestrictionStdErrorFinSucc R Z X Y n ω /
            Real.sqrt (n + 1 : ℝ) ≤ 0
      constructor
      · intro hnonpos
        exact div_nonpos_of_nonpos_of_nonneg hnonpos hroot.le
      · intro hdiv
        by_contra hnot
        exact (not_lt_of_ge hdiv)
          (div_pos (lt_of_not_ge hnot) hroot)
  refine
    { standard_error_nonpos_probability_tendsto_zero := hestimator_nonpos
      statistic_limit := ?_ }
  have hT :=
    twoSLSRobustLinearTStatFinSucc_tendstoInDistribution_standardNormal_of_coefficient_covariance
      (μ := μ) (Z := Z) (X := X) (Y := Y) (β := β) (R := R)
      (Vβ := Vβ) hVβ hseθ hβ hV_meas hV
  exact TendstoInDistribution.congr
    (fun n => by
      filter_upwards with ω
      exact
        (percentileTStatistic_twoSLSRobustLinearRestrictionEstimatorStdErrorFinSucc
          R Z X Y β n ω).symm)
    Filter.EventuallyEq.rfl hT

set_option linter.style.longLine false in
/-- Constructor for the original-sample percentile-`t` inputs from primitive
coefficient and covariance convergence facts.

Compared with `of_fields`, this no longer assumes the sample robust t-ratio
limit directly: the t-ratio limit is derived from the sample coefficient CLT,
robust covariance consistency, covariance measurability, and positive
restriction covariance. -/
theorem
    TwoSLSBootstrapRobustPercentileTSampleInputs.of_coefficient_clt_covariance_consistency
    [IsProbabilityMeasure μ]
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {β : k → ℝ} {R : Matrix Unit k ℝ} {Vβ : Matrix k k ℝ}
    (hVβ : Vβ.PosSemidef)
    (hseθ : 0 < linearRestrictionStdError R Vβ)
    (hβ :
      TendstoInDistribution
        (fun (n : ℕ) ω =>
          Real.sqrt ((n + 1 : ℕ) : ℝ) •
            (twoSLSBetaStar
              (stackRegressors Z (n + 1) ω) (stackRegressors X (n + 1) ω)
              (stackOutcomes Y (n + 1) ω) - β))
        atTop (fun z : EuclideanSpace ℝ k => z.ofLp) (fun _ => μ)
        (multivariateGaussian 0 Vβ))
    (hV_meas : ∀ n,
      AEStronglyMeasurable
        (fun ω =>
          twoSLSVHatStar
            (stackRegressors Z (n + 1) ω) (stackRegressors X (n + 1) ω)
            (stackOutcomes Y (n + 1) ω)) μ)
    (hV :
      TendstoInMeasure μ
        (fun n ω =>
          twoSLSVHatStar
            (stackRegressors Z (n + 1) ω) (stackRegressors X (n + 1) ω)
            (stackOutcomes Y (n + 1) ω))
        atTop (fun _ => Vβ))
    (hVhat_pos : ∀ n ω,
      (R *
          twoSLSVHatStar
            (stackRegressors Z (n + 1) ω) (stackRegressors X (n + 1) ω)
            (stackOutcomes Y (n + 1) ω) *
        Rᵀ).PosDef) :
    TwoSLSBootstrapRobustPercentileTSampleInputs μ Z X Y β R :=
  TwoSLSBootstrapRobustPercentileTSampleInputs.of_fields
    (μ := μ) (Z := Z) (X := X) (Y := Y) (β := β) (R := R)
    (twoSLSRobustLinearRestrictionEstimatorStdErrorFinSucc_pos_of_restrictionCov_posDef
      (R := R) hVhat_pos)
    (by
      have hT :=
        twoSLSRobustLinearTStatFinSucc_tendstoInDistribution_standardNormal_of_coefficient_covariance
          (μ := μ) (Z := Z) (X := X) (Y := Y) (β := β) (R := R)
          (Vβ := Vβ) hVβ hseθ hβ hV_meas hV
      exact TendstoInDistribution.congr
        (fun n => by
          filter_upwards with ω
          exact
            (percentileTStatistic_twoSLSRobustLinearRestrictionEstimatorStdErrorFinSucc
              R Z X Y β n ω).symm)
        Filter.EventuallyEq.rfl hT)

set_option linter.style.longLine false in
/-- Assumption-12.2-facing constructor for the original-sample side of Hansen
Theorem 12.8's percentile-`t` inputs.

This composes the generic sample-side bridge with the existing Chapter 12
coefficient CLT and robust covariance consistency theorem.  The remaining
explicit inputs are local to the finite-sample statistic: measurability of the
displayed robust covariance path and finite-sample positive definiteness of
the one-row restriction covariance. -/
theorem
    TwoSLSBootstrapRobustPercentileTSampleInputs.of_assumption12_2_iid_weight_wlln
    [IsProbabilityMeasure μ]
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {β : k → ℝ} {R : Matrix Unit k ℝ}
    (h : TwoSLSAssumption12_2IidFourthConditions μ Z X e)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hw : TwoSLSCovarianceWeightWLLNConditions μ Z X e)
    (hR : Function.Injective Rᵀ.mulVec)
    (hV_meas : ∀ n,
      AEStronglyMeasurable
        (fun ω =>
          twoSLSVHatStar
            (stackRegressors Z (n + 1) ω) (stackRegressors X (n + 1) ω)
            (stackOutcomes Y (n + 1) ω)) μ)
    (hVhat_pos : ∀ n ω,
      (R *
          twoSLSVHatStar
            (stackRegressors Z (n + 1) ω) (stackRegressors X (n + 1) ω)
            (stackOutcomes Y (n + 1) ω) *
        Rᵀ).PosDef) :
    TwoSLSBootstrapRobustPercentileTSampleInputs μ Z X Y β R := by
  let Vβ : Matrix k k ℝ :=
    twoSLSAsymptoticVariance
      (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
      (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
      (scoreCovMat μ Z e)
      (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))
  let hGram := h.toGramConditions
  have hVβ_pos : Vβ.PosDef := by
    dsimp [Vβ]
    exact
      twoSLSAsymptoticVariance_posDef_of_qzz_omega_rank
        (QXZ := twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
        (QZZ := twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
        (Omega := scoreCovMat μ Z e)
        (QZX := twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))
        (twoSLSCombinedQXZ_eq_transpose_QZX_of_popGram_wlln
          (μ := μ) (Z := Z) (X := X)
          hGram.toTwoSLSAssumption12_1GramConditions.combined_gram)
        h.qzz_posDef h.omega_posDef h.qzx_rank
  have hVθ : (R * Vβ * Rᵀ).PosDef := by
    have hcov : ((Rᵀ)ᵀ * Vβ * Rᵀ).PosDef :=
      restrictionCov_posDef_of_cov_posDef Vβ Rᵀ hVβ_pos hR
    simpa [Vβ] using hcov
  have hseθ : 0 < linearRestrictionStdError R Vβ :=
    linearRestrictionStdError_pos_of_restrictionCov_posDef R hVθ
  have hβ0 :=
    twoSLSBetaStar_tendstoInDistribution_formula_of_assumption12_2_iid_model
      (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y) h β hmodel
  have hβ_shift :
      TendstoInDistribution
        (fun (n : ℕ) ω =>
          Real.sqrt ((n + 1 : ℕ) : ℝ) •
            (twoSLSBetaStar
              (stackRegressors Z (n + 1) ω) (stackRegressors X (n + 1) ω)
              (stackOutcomes Y (n + 1) ω) - β))
        atTop (fun z : EuclideanSpace ℝ k => z.ofLp) (fun _ => μ)
        (multivariateGaussian 0 Vβ) := by
    refine
      { forall_aemeasurable := ?_
        aemeasurable_limit := by
          simpa [Vβ] using hβ0.aemeasurable_limit
        tendsto := ?_ }
    · intro n
      simpa [Vβ, stackRegressors, stackOutcomes] using
        hβ0.forall_aemeasurable (n + 1)
    · have hcomp := hβ0.tendsto.comp (tendsto_add_atTop_nat 1)
      convert hcomp using 1 with n
  have hV0 :=
    (twoSLSCovariances_tendstoInMeasure_formula_of_assumption12_2_iid_weight_wlln
      (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y) h β hmodel hw).1
  have hV_shift :
      TendstoInMeasure μ
        (fun n ω =>
          twoSLSVHatStar
            (stackRegressors Z (n + 1) ω) (stackRegressors X (n + 1) ω)
            (stackOutcomes Y (n + 1) ω))
        atTop (fun _ => Vβ) := by
    intro ε hε
    simpa [Vβ, stackRegressors, stackOutcomes] using
      (hV0 ε hε).comp (tendsto_add_atTop_nat 1)
  exact
    TwoSLSBootstrapRobustPercentileTSampleInputs.of_coefficient_clt_covariance_consistency
      (μ := μ) (Z := Z) (X := X) (Y := Y) (β := β) (R := R)
      (Vβ := Vβ) hVβ_pos.posSemidef hseθ hβ_shift hV_meas hV_shift
      hVhat_pos

set_option linter.style.longLine false in
/-- Assumption-12.2-facing sample-side constructor with finite-sample robust
covariance measurability derived from row measurability.

Compared with
`TwoSLSBootstrapRobustPercentileTSampleInputs.of_assumption12_2_iid_weight_wlln`,
this removes the explicit covariance-path measurability premise. The only
finite-sample side condition left is positive definiteness of the one-row
restriction covariance, which is a genuine nondegeneracy condition for the
studentized statistic. -/
theorem
    TwoSLSBootstrapRobustPercentileTSampleInputs.of_assumption12_2_iid_weight_wlln_rows
    [IsProbabilityMeasure μ]
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {β : k → ℝ} {R : Matrix Unit k ℝ}
    (h : TwoSLSAssumption12_2IidFourthConditions μ Z X e)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hw : TwoSLSCovarianceWeightWLLNConditions μ Z X e)
    (hR : Function.Injective Rᵀ.mulVec)
    (hVhat_pos : ∀ n ω,
      (R *
          twoSLSVHatStar
            (stackRegressors Z (n + 1) ω) (stackRegressors X (n + 1) ω)
            (stackOutcomes Y (n + 1) ω) *
        Rᵀ).PosDef) :
    TwoSLSBootstrapRobustPercentileTSampleInputs μ Z X Y β R := by
  have hY : ∀ i, AEStronglyMeasurable (Y i) μ :=
    outcome_aestronglyMeasurable_of_linear_model
      (μ := μ) (X := X) (e := e) (Y := Y) β
      h.x_aestronglyMeasurable h.e_aestronglyMeasurable hmodel
  have hV_meas : ∀ n,
      AEStronglyMeasurable
        (fun ω =>
          twoSLSVHatStar
            (stackRegressors Z (n + 1) ω) (stackRegressors X (n + 1) ω)
            (stackOutcomes Y (n + 1) ω)) μ := by
    intro n
    simpa [stackRegressors, stackOutcomes] using
      twoSLSVHatStar_aestronglyMeasurable_of_rows
        (μ := μ) (n := n + 1) (Z := Z) (X := X) (Y := Y)
        h.z_aestronglyMeasurable h.x_aestronglyMeasurable hY
  exact
    TwoSLSBootstrapRobustPercentileTSampleInputs.of_assumption12_2_iid_weight_wlln
      (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y)
      (β := β) (R := R) h hmodel hw hR hV_meas hVhat_pos

set_option linter.style.longLine false in
/-- Assumption-12.2-facing sample-side constructor with row measurability and
finite-sample restriction-covariance positivity derived from coefficient
covariance positive definiteness plus full rank of `Rᵀ.mulVec`.

This is the strongest local sample-side constructor currently available from
finite-sample covariance nondegeneracy: it still requires the realized robust
coefficient covariance to be positive definite, but no longer asks callers to
state the derived scalar restriction covariance separately. -/
theorem
    TwoSLSBootstrapRobustPercentileTSampleInputs.of_assumption12_2_iid_weight_wlln_rows_cov_posDef
    [IsProbabilityMeasure μ]
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {β : k → ℝ} {R : Matrix Unit k ℝ}
    (h : TwoSLSAssumption12_2IidFourthConditions μ Z X e)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hw : TwoSLSCovarianceWeightWLLNConditions μ Z X e)
    (hR : Function.Injective Rᵀ.mulVec)
    (hVhat_pos : ∀ n ω,
      (twoSLSVHatStar
        (stackRegressors Z (n + 1) ω) (stackRegressors X (n + 1) ω)
        (stackOutcomes Y (n + 1) ω)).PosDef) :
    TwoSLSBootstrapRobustPercentileTSampleInputs μ Z X Y β R :=
  TwoSLSBootstrapRobustPercentileTSampleInputs.of_assumption12_2_iid_weight_wlln_rows
    (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y)
    (β := β) (R := R) h hmodel hw hR
    (twoSLSRobustRestrictionCovFinSucc_posDef_of_cov_posDef
      (R := R) hR hVhat_pos)

set_option linter.style.longLine false in
/-- Assumption-12.2-facing sample-side constructor with the one-row restriction
rank premise stated as Hansen's natural nonzero-row condition. -/
theorem
    TwoSLSBootstrapRobustPercentileTSampleInputs.of_assumption12_2_iid_weight_wlln_rows_cov_posDef_row_ne_zero
    [IsProbabilityMeasure μ]
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {β : k → ℝ} {R : Matrix Unit k ℝ}
    (h : TwoSLSAssumption12_2IidFourthConditions μ Z X e)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hw : TwoSLSCovarianceWeightWLLNConditions μ Z X e)
    (hR : ∃ j : k, R () j ≠ 0)
    (hVhat_pos : ∀ n ω,
      (twoSLSVHatStar
        (stackRegressors Z (n + 1) ω) (stackRegressors X (n + 1) ω)
        (stackOutcomes Y (n + 1) ω)).PosDef) :
    TwoSLSBootstrapRobustPercentileTSampleInputs μ Z X Y β R :=
  TwoSLSBootstrapRobustPercentileTSampleInputs.of_assumption12_2_iid_weight_wlln_rows_cov_posDef
    (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y)
    (β := β) (R := R) h hmodel hw
    (oneRow_transpose_mulVec_injective_of_exists_ne_zero hR) hVhat_pos

set_option linter.style.longLine false in
/-- Assumption-12.2-facing asymptotic sample-side constructor.

The coefficient CLT and robust covariance consistency are the existing
Chapter 12.2/12.3 results. Assumption 12.2 makes the limiting restriction
variance positive, while covariance consistency makes nonpositive realized
standard errors a probability-zero asymptotic event. -/
theorem
    TwoSLSBootstrapRobustPercentileTAsymptoticSampleInputs.of_assumption12_2_iid_weight_wlln_rows
    [IsProbabilityMeasure μ]
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {β : k → ℝ} {R : Matrix Unit k ℝ}
    (h : TwoSLSAssumption12_2IidFourthConditions μ Z X e)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hw : TwoSLSCovarianceWeightWLLNConditions μ Z X e)
    (hR : Function.Injective Rᵀ.mulVec) :
    TwoSLSBootstrapRobustPercentileTAsymptoticSampleInputs
      μ Z X Y β R := by
  let Vβ : Matrix k k ℝ :=
    twoSLSAsymptoticVariance
      (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
      (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
      (scoreCovMat μ Z e)
      (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))
  let hGram := h.toGramConditions
  have hVβ_pos : Vβ.PosDef := by
    dsimp [Vβ]
    exact
      twoSLSAsymptoticVariance_posDef_of_qzz_omega_rank
        (QXZ := twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
        (QZZ := twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
        (Omega := scoreCovMat μ Z e)
        (QZX := twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))
        (twoSLSCombinedQXZ_eq_transpose_QZX_of_popGram_wlln
          (μ := μ) (Z := Z) (X := X)
          hGram.toTwoSLSAssumption12_1GramConditions.combined_gram)
        h.qzz_posDef h.omega_posDef h.qzx_rank
  have hVθ : (R * Vβ * Rᵀ).PosDef := by
    have hcov : ((Rᵀ)ᵀ * Vβ * Rᵀ).PosDef :=
      restrictionCov_posDef_of_cov_posDef Vβ Rᵀ hVβ_pos hR
    simpa [Vβ] using hcov
  have hseθ : 0 < linearRestrictionStdError R Vβ :=
    linearRestrictionStdError_pos_of_restrictionCov_posDef R hVθ
  have hY : ∀ i, AEStronglyMeasurable (Y i) μ :=
    outcome_aestronglyMeasurable_of_linear_model
      (μ := μ) (X := X) (e := e) (Y := Y) β
      h.x_aestronglyMeasurable h.e_aestronglyMeasurable hmodel
  have hV_meas : ∀ n,
      AEStronglyMeasurable
        (fun ω =>
          twoSLSVHatStar
            (stackRegressors Z (n + 1) ω) (stackRegressors X (n + 1) ω)
            (stackOutcomes Y (n + 1) ω)) μ := by
    intro n
    simpa [stackRegressors, stackOutcomes] using
      twoSLSVHatStar_aestronglyMeasurable_of_rows
        (μ := μ) (n := n + 1) (Z := Z) (X := X) (Y := Y)
        h.z_aestronglyMeasurable h.x_aestronglyMeasurable hY
  have hβ0 :=
    twoSLSBetaStar_tendstoInDistribution_formula_of_assumption12_2_iid_model
      (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y) h β hmodel
  have hβ_shift :
      TendstoInDistribution
        (fun (n : ℕ) ω =>
          Real.sqrt ((n + 1 : ℕ) : ℝ) •
            (twoSLSBetaStar
              (stackRegressors Z (n + 1) ω) (stackRegressors X (n + 1) ω)
              (stackOutcomes Y (n + 1) ω) - β))
        atTop (fun z : EuclideanSpace ℝ k => z.ofLp) (fun _ => μ)
        (multivariateGaussian 0 Vβ) := by
    refine
      { forall_aemeasurable := ?_
        aemeasurable_limit := by
          simpa [Vβ] using hβ0.aemeasurable_limit
        tendsto := ?_ }
    · intro n
      simpa [Vβ, stackRegressors, stackOutcomes] using
        hβ0.forall_aemeasurable (n + 1)
    · have hcomp := hβ0.tendsto.comp (tendsto_add_atTop_nat 1)
      convert hcomp using 1 with n
  have hV0 :=
    (twoSLSCovariances_tendstoInMeasure_formula_of_assumption12_2_iid_weight_wlln
      (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y) h β hmodel hw).1
  have hV_shift :
      TendstoInMeasure μ
        (fun n ω =>
          twoSLSVHatStar
            (stackRegressors Z (n + 1) ω) (stackRegressors X (n + 1) ω)
            (stackOutcomes Y (n + 1) ω))
        atTop (fun _ => Vβ) := by
    intro ε hε
    simpa [Vβ, stackRegressors, stackOutcomes] using
      (hV0 ε hε).comp (tendsto_add_atTop_nat 1)
  exact
    TwoSLSBootstrapRobustPercentileTAsymptoticSampleInputs.of_coefficient_clt_covariance_consistency
      (μ := μ) (Z := Z) (X := X) (Y := Y) (β := β) (R := R)
      (Vβ := Vβ) hVβ_pos.posSemidef hseθ hβ_shift hV_meas hV_shift

set_option linter.style.longLine false in
/-- Observed-row Assumption 12.2 constructor for the asymptotic sample-side
percentile-`t` package. -/
theorem
    TwoSLSBootstrapRobustPercentileTAsymptoticSampleInputs.of_observed_textbook_fourth
    [IsProbabilityMeasure μ]
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {β : k → ℝ} {R : Matrix Unit k ℝ}
    (h : TwoSLSAssumption12_2ObservedIidTextbookFourthConditions μ Z X e Y β)
    (hR : Function.Injective Rᵀ.mulVec) :
    TwoSLSBootstrapRobustPercentileTAsymptoticSampleInputs
      μ Z X Y β R := by
  let hmixed : TwoSLSAssumption12_2JointIidMixedMomentConditions μ Z X e :=
    h.toJointIidMixedMomentConditions
  exact
    TwoSLSBootstrapRobustPercentileTAsymptoticSampleInputs.of_assumption12_2_iid_weight_wlln_rows
      (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y)
      (β := β) (R := R)
      hmixed.toTwoSLSAssumption12_2JointIidFourthConditions.toIidFourthConditions
      h.model
      (hmixed.toWeightWLLNConditions
        (μ := μ) (Z := Z) (X := X) (e := e))
      hR

set_option linter.style.longLine false in
/-- Under observed-row Assumption 12.2, a nonzero one-row restriction has a
positive robust standard error with probability tending to one. -/
theorem
    twoSLSRobustLinearRestrictionEstimatorStdErrorFinSucc_nonpos_probability_tendsto_zero_of_observed_assumption12_2
    [IsProbabilityMeasure μ]
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {β : k → ℝ} {R : Matrix Unit k ℝ}
    (h : TwoSLSAssumption12_2ObservedIidTextbookFourthConditions μ Z X e Y β)
    (hR : ∃ j : k, R () j ≠ 0) :
    Tendsto
      (fun n =>
        μ {ω |
          twoSLSRobustLinearRestrictionEstimatorStdErrorFinSucc
            R Z X Y n ω ≤ 0})
      atTop (𝓝 0) :=
  (TwoSLSBootstrapRobustPercentileTAsymptoticSampleInputs.of_observed_textbook_fourth
    (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y)
    (β := β) (R := R) h
    (oneRow_transpose_mulVec_injective_of_exists_ne_zero hR)).standard_error_nonpos_probability_tendsto_zero

set_option linter.style.longLine false in
/-- Field-level constructor for the bootstrap quantile-calibration side of
Hansen Theorem 12.8's percentile-`t` coverage input package. -/
theorem TwoSLSBootstrapRobustPercentileTQuantileCalibrationInputs.of_fields
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {R : Matrix Unit k ℝ} {q α : ℝ}
    (hα_pos : 0 < α) (hα_lt_one : α < 1)
    (hstrict : StrictMono (fun x => cdf (gaussianReal 0 1) x))
    (hlower_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed
            (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
            (fun n ω ωs =>
              twoSLSBootstrapRobustLinearTStatFinSucc R Z X Y n ω ωs)
            (α / 2) n) μ)
    (hupper_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed
            (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
            (fun n ω ωs =>
              twoSLSBootstrapRobustLinearTStatFinSucc R Z X Y n ω ωs)
            (1 - α / 2) n) μ)
    (hq_nonneg : 0 ≤ q)
    (hcdfLower : cdf (gaussianReal 0 1) (-q) = α / 2)
    (hcdfUpper : cdf (gaussianReal 0 1) q = 1 - α / 2) :
    TwoSLSBootstrapRobustPercentileTQuantileCalibrationInputs
      μ Z X Y R q α where
  alpha_pos := hα_pos
  alpha_lt_one := hα_lt_one
  standardNormal_cdf_strictMono := hstrict
  lower_quantile_aemeasurable := hlower_meas
  upper_quantile_aemeasurable := hupper_meas
  critical_nonneg := hq_nonneg
  cdf_lower := hcdfLower
  cdf_upper := hcdfUpper

set_option linter.style.longLine false in
/-- Chapter 10 lower-quantile convergence specialized to Hansen's robust
bootstrap 2SLS percentile-`t` statistic.

The existing calibration package contains the finite-level and critical-value
facts used by the coverage theorem.  Once the bootstrap `t`-ratio itself has
the standard-normal bootstrap limit, Chapter 10's indexed lower-quantile
theorem gives convergence of both bootstrap percentile-`t` critical values:
the lower critical value converges to `-q`, and the upper critical value
converges to `q`. -/
theorem
    TwoSLSBootstrapRobustPercentileTQuantileCalibrationInputs.quantiles_tendsto_of_bootstrap_tstat
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {R : Matrix Unit k ℝ} {q α : ℝ}
    (hquantile :
      TwoSLSBootstrapRobustPercentileTQuantileCalibrationInputs
        μ Z X Y R q α)
    (hTstar :
      TendstoInBootstrapDistributionIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs (_ : Unit) =>
          twoSLSBootstrapRobustLinearTStatFinSucc R Z X Y n ω ωs)
        (gaussianReal 0 1) (fun z : ℝ => fun _ : Unit => z)) :
    TendstoInMeasure μ
        (bootstrapScalarLowerQuantileIndexed
          (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
          (fun n ω ωs =>
            twoSLSBootstrapRobustLinearTStatFinSucc R Z X Y n ω ωs)
          (α / 2))
        atTop (fun _ => -q) ∧
      TendstoInMeasure μ
        (bootstrapScalarLowerQuantileIndexed
          (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
          (fun n ω ωs =>
            twoSLSBootstrapRobustLinearTStatFinSucc R Z X Y n ω ωs)
          (1 - α / 2))
        atTop (fun _ => q) := by
  have hPstar : ∀ n (ω : Ω),
      IsProbabilityMeasure
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω) n ω) :=
    fun n ω =>
      twoSLSBootstrapUniformPstarFinSucc_isProbabilityMeasure (Ω := Ω) n ω
  have hTstar_meas : ∀ n (ω : Ω),
      AEMeasurable
        (fun ωs =>
          twoSLSBootstrapRobustLinearTStatFinSucc R Z X Y n ω ωs)
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω) n ω) :=
    fun n ω =>
      twoSLSBootstrapRobustLinearTStatFinSucc_aemeasurable
        (R := R) (Z := Z) (X := X) (Y := Y) n ω
  have hcont : ∀ x : ℝ, ContinuousAt (fun y => cdf (gaussianReal 0 1) y) x :=
    fun x => continuousAt_cdf_standardNormal x
  have hα_half_pos : 0 < α / 2 := by
    linarith [hquantile.alpha_pos]
  have hα_half_lt_one : α / 2 < 1 := by
    linarith [hquantile.alpha_lt_one]
  have hone_sub_half_pos : 0 < 1 - α / 2 := by
    linarith [hquantile.alpha_lt_one]
  have hone_sub_half_lt_one : 1 - α / 2 < 1 := by
    linarith [hquantile.alpha_pos]
  constructor
  · exact
      bootstrapScalarLowerQuantileIndexed_tendsto_of_strictMono_id_cdf_probability
        (μ := μ)
        (Pstar := twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (Zstar := fun n ω ωs =>
          twoSLSBootstrapRobustLinearTStatFinSucc R Z X Y n ω ωs)
        (η := gaussianReal 0 1) (p := α / 2) (q := -q)
        hPstar hTstar_meas hα_half_pos hα_half_lt_one
        hquantile.standardNormal_cdf_strictMono hquantile.cdf_lower
        hTstar hcont
  · exact
      bootstrapScalarLowerQuantileIndexed_tendsto_of_strictMono_id_cdf_probability
        (μ := μ)
        (Pstar := twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (Zstar := fun n ω ωs =>
          twoSLSBootstrapRobustLinearTStatFinSucc R Z X Y n ω ωs)
        (η := gaussianReal 0 1) (p := 1 - α / 2) (q := q)
        hPstar hTstar_meas hone_sub_half_pos hone_sub_half_lt_one
        hquantile.standardNormal_cdf_strictMono hquantile.cdf_upper
        hTstar hcont

set_option linter.style.longLine false in
/-- Field-level constructor for the full interval-side package in Hansen
Theorem 12.8. -/
theorem TwoSLSBootstrapRobustPercentileTCoverageInputs.of_fields
    [IsProbabilityMeasure μ]
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {β : k → ℝ} {R : Matrix Unit k ℝ} {q α : ℝ}
    (hse : ∀ n ω,
      0 < twoSLSRobustLinearRestrictionEstimatorStdErrorFinSucc R Z X Y n ω)
    (htstat :
      TendstoInDistribution
        (fun n ω =>
          percentileTStatistic (linearRestrictionEstimate R β)
            (twoSLSLinearRestrictionEstimateFinSucc R Z X Y n ω)
            (twoSLSRobustLinearRestrictionEstimatorStdErrorFinSucc R Z X Y n ω))
        atTop (fun x : ℝ => x) (fun _ => μ) (gaussianReal 0 1))
    (hα_pos : 0 < α) (hα_lt_one : α < 1)
    (hstrict : StrictMono (fun x => cdf (gaussianReal 0 1) x))
    (hlower_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed
            (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
            (fun n ω ωs =>
              twoSLSBootstrapRobustLinearTStatFinSucc R Z X Y n ω ωs)
            (α / 2) n) μ)
    (hupper_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed
            (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
            (fun n ω ωs =>
              twoSLSBootstrapRobustLinearTStatFinSucc R Z X Y n ω ωs)
            (1 - α / 2) n) μ)
    (hq_nonneg : 0 ≤ q)
    (hcdfLower : cdf (gaussianReal 0 1) (-q) = α / 2)
    (hcdfUpper : cdf (gaussianReal 0 1) q = 1 - α / 2) :
    TwoSLSBootstrapRobustPercentileTCoverageInputs
      μ Z X Y β R q α :=
  TwoSLSBootstrapRobustPercentileTCoverageInputs.of_sample_quantile
    (μ := μ) (Z := Z) (X := X) (Y := Y) (β := β) (R := R)
    (q := q) (α := α)
    (TwoSLSBootstrapRobustPercentileTSampleInputs.of_fields
      (μ := μ) (Z := Z) (X := X) (Y := Y) (β := β) (R := R)
      hse htstat)
    (TwoSLSBootstrapRobustPercentileTQuantileCalibrationInputs.of_fields
      (μ := μ) (Z := Z) (X := X) (Y := Y) (R := R)
      (q := q) (α := α)
      hα_pos hα_lt_one hstrict hlower_meas hupper_meas hq_nonneg
      hcdfLower hcdfUpper)

set_option linter.style.longLine false in
/-- Assumption-12.2-facing constructor for the full percentile-`t`
interval-side package, reusing the derived sample-side robust t-ratio theorem.

Callers provide the genuine interval calibration package and the finite-sample
restriction-covariance positivity condition; sample standard-error positivity,
sample robust t-ratio normality, and finite-sample covariance measurability are
derived from Chapter 12's coefficient CLT, robust covariance consistency, and
row-measurability infrastructure. -/
theorem
    TwoSLSBootstrapRobustPercentileTCoverageInputs.of_assumption12_2_iid_weight_wlln_quantileCalibration
    [IsProbabilityMeasure μ]
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {β : k → ℝ} {R : Matrix Unit k ℝ} {q α : ℝ}
    (h : TwoSLSAssumption12_2IidFourthConditions μ Z X e)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hw : TwoSLSCovarianceWeightWLLNConditions μ Z X e)
    (hR : Function.Injective Rᵀ.mulVec)
    (hVhat_pos : ∀ n ω,
      (R *
          twoSLSVHatStar
            (stackRegressors Z (n + 1) ω) (stackRegressors X (n + 1) ω)
            (stackOutcomes Y (n + 1) ω) *
        Rᵀ).PosDef)
    (hquantile :
      TwoSLSBootstrapRobustPercentileTQuantileCalibrationInputs
        μ Z X Y R q α) :
    TwoSLSBootstrapRobustPercentileTCoverageInputs
      μ Z X Y β R q α :=
  TwoSLSBootstrapRobustPercentileTCoverageInputs.of_sample_quantile
    (μ := μ) (Z := Z) (X := X) (Y := Y) (β := β) (R := R)
    (q := q) (α := α)
    (TwoSLSBootstrapRobustPercentileTSampleInputs.of_assumption12_2_iid_weight_wlln_rows
      (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y)
      (β := β) (R := R) h hmodel hw hR hVhat_pos)
    hquantile

set_option linter.style.longLine false in
/-- Assumption-12.2-facing full percentile-`t` coverage-input constructor
using row measurability, finite-sample robust coefficient-covariance positive
definiteness, and the named quantile-calibration package.

Compared with
`TwoSLSBootstrapRobustPercentileTCoverageInputs.of_assumption12_2_iid_weight_wlln_quantileCalibration`,
this derives the finite-sample scalar restriction-covariance positivity field
from coefficient-covariance positive definiteness and full rank of `Rᵀ.mulVec`. -/
theorem
    TwoSLSBootstrapRobustPercentileTCoverageInputs.of_assumption12_2_iid_weight_wlln_cov_posDef_quantileCalibration
    [IsProbabilityMeasure μ]
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {β : k → ℝ} {R : Matrix Unit k ℝ} {q α : ℝ}
    (h : TwoSLSAssumption12_2IidFourthConditions μ Z X e)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hw : TwoSLSCovarianceWeightWLLNConditions μ Z X e)
    (hR : Function.Injective Rᵀ.mulVec)
    (hVhat_pos : ∀ n ω,
      (twoSLSVHatStar
        (stackRegressors Z (n + 1) ω) (stackRegressors X (n + 1) ω)
        (stackOutcomes Y (n + 1) ω)).PosDef)
    (hquantile :
      TwoSLSBootstrapRobustPercentileTQuantileCalibrationInputs
        μ Z X Y R q α) :
    TwoSLSBootstrapRobustPercentileTCoverageInputs
      μ Z X Y β R q α :=
  TwoSLSBootstrapRobustPercentileTCoverageInputs.of_sample_quantile
    (μ := μ) (Z := Z) (X := X) (Y := Y) (β := β) (R := R)
    (q := q) (α := α)
    (TwoSLSBootstrapRobustPercentileTSampleInputs.of_assumption12_2_iid_weight_wlln_rows_cov_posDef
      (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y)
      (β := β) (R := R) h hmodel hw hR hVhat_pos)
    hquantile

set_option linter.style.longLine false in
/-- Mixed-moment Assumption-12.2 constructor for Hansen Theorem 12.8's
percentile-`t` interval-side package.

The mixed-moment package supplies the iid Assumption 12.2 surface and the
robust covariance weight-WLLN fields.  This wrapper derives the sample robust
`t`-ratio limit and finite-sample covariance measurability through the existing
iid constructor, while keeping the realized robust covariance nondegeneracy and
bootstrap quantile calibration as the remaining interval-side inputs. -/
theorem
    TwoSLSBootstrapRobustPercentileTCoverageInputs.of_mixed_moment_conditions_cov_posDef_quantileCalibration
    [IsProbabilityMeasure μ]
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {β : k → ℝ} {R : Matrix Unit k ℝ} {q α : ℝ}
    (h : TwoSLSAssumption12_2JointIidMixedMomentConditions μ Z X e)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hR : Function.Injective Rᵀ.mulVec)
    (hVhat_pos : ∀ n ω,
      (twoSLSVHatStar
        (stackRegressors Z (n + 1) ω) (stackRegressors X (n + 1) ω)
        (stackOutcomes Y (n + 1) ω)).PosDef)
    (hquantile :
      TwoSLSBootstrapRobustPercentileTQuantileCalibrationInputs
        μ Z X Y R q α) :
    TwoSLSBootstrapRobustPercentileTCoverageInputs
      μ Z X Y β R q α :=
  TwoSLSBootstrapRobustPercentileTCoverageInputs.of_assumption12_2_iid_weight_wlln_cov_posDef_quantileCalibration
    (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y)
    (β := β) (R := R) (q := q) (α := α)
    h.toTwoSLSAssumption12_2JointIidFourthConditions.toIidFourthConditions
    hmodel
    (h.toWeightWLLNConditions
      (μ := μ) (Z := Z) (X := X) (e := e))
    hR hVhat_pos hquantile

set_option linter.style.longLine false in
/-- Literal finite-fourth Assumption-12.2 constructor for Hansen Theorem
12.8's percentile-`t` interval-side package.

This is the textbook-facing version of
`TwoSLSBootstrapRobustPercentileTCoverageInputs.of_mixed_moment_conditions_cov_posDef_quantileCalibration`:
the literal fourth-moment package derives the mixed-moment and covariance
WLLN fields by the existing Hölder route, while realized robust covariance
positive definiteness and bootstrap quantile calibration remain explicit. -/
theorem
    TwoSLSBootstrapRobustPercentileTCoverageInputs.of_textbook_fourth_cov_posDef_quantileCalibration
    [IsProbabilityMeasure μ]
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {β : k → ℝ} {R : Matrix Unit k ℝ} {q α : ℝ}
    (h : TwoSLSAssumption12_2JointIidTextbookFourthConditions μ Z X e Y β)
    (hR : Function.Injective Rᵀ.mulVec)
    (hVhat_pos : ∀ n ω,
      (twoSLSVHatStar
        (stackRegressors Z (n + 1) ω) (stackRegressors X (n + 1) ω)
        (stackOutcomes Y (n + 1) ω)).PosDef)
    (hquantile :
      TwoSLSBootstrapRobustPercentileTQuantileCalibrationInputs
        μ Z X Y R q α) :
    TwoSLSBootstrapRobustPercentileTCoverageInputs
      μ Z X Y β R q α :=
  TwoSLSBootstrapRobustPercentileTCoverageInputs.of_mixed_moment_conditions_cov_posDef_quantileCalibration
    (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y)
    (β := β) (R := R) (q := q) (α := α)
    h.toJointIidMixedMomentConditions h.model hR hVhat_pos hquantile

set_option linter.style.longLine false in
/-- Percentile-`t` interval coverage from the robust bootstrap t-ratio limit
and the named interval-side input package.

This is the preferred direct coverage bridge for Hansen Theorem 12.8: the
bootstrap empirical-process proof supplies `hTstar`, while the package supplies
sample robust t-ratio positivity/normality and quantile calibration. -/
theorem
    twoSLSBootstrapRobustPercentileTCIEventFinSucc_tendsto_one_sub_alpha_uniform_of_coverageInputs
    [IsProbabilityMeasure μ]
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {R : Matrix Unit k ℝ} {β : k → ℝ} {q α : ℝ}
    (hTstar :
      TendstoInBootstrapDistributionIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs (_ : Unit) =>
          twoSLSBootstrapRobustLinearTStatFinSucc R Z X Y n ω ωs)
        (gaussianReal 0 1) (fun z : ℝ => fun _ : Unit => z))
    (hcoverage :
      TwoSLSBootstrapRobustPercentileTCoverageInputs
        μ Z X Y β R q α) :
    Tendsto
      (fun n =>
        μ {ω |
          twoSLSBootstrapRobustPercentileTCIEventFinSucc
            R Z X Y β α n ω})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) := by
  have hTstar_meas : ∀ n ω,
      AEMeasurable
        (fun ωs => twoSLSBootstrapRobustLinearTStatFinSucc R Z X Y n ω ωs)
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω) n ω) := by
    intro n ω
    have hT_meas :
        Measurable
          (fun ωs =>
            twoSLSBootstrapLinearRestrictionStatisticFinSucc R Z X Y n ω ωs) := by
      fun_prop
    have hse_meas :
        Measurable
          (fun ωs =>
            twoSLSBootstrapRobustLinearRestrictionStdErrorFinSucc
              R Z X Y n ω ωs) := by
      fun_prop
    simpa [twoSLSBootstrapRobustLinearTStatFinSucc,
      twoSLSBootstrapLinearTStatFinSucc] using
      (hT_meas.div hse_meas).aemeasurable
  exact
    twoSLSBootstrapRobustPercentileTCIEventFinSucc_tendsto_one_sub_alpha_uniform
      (μ := μ) (Z := Z) (X := X) (Y := Y) (R := R) (β := β)
      (q := q) (α := α)
      hcoverage.sample.standard_error_pos hcoverage.sample.statistic_limit
      hTstar_meas hTstar hcoverage.quantile.alpha_pos
      hcoverage.quantile.alpha_lt_one
      hcoverage.quantile.standardNormal_cdf_strictMono
      hcoverage.quantile.lower_quantile_aemeasurable
      hcoverage.quantile.upper_quantile_aemeasurable
      hcoverage.quantile.critical_nonneg hcoverage.quantile.cdf_lower
      hcoverage.quantile.cdf_upper

set_option linter.style.longLine false in
/-- Percentile-`t` interval coverage from the robust bootstrap t-ratio limit
and the asymptotic interval-side package.

This is the preferred Hansen Theorem 12.8 coverage bridge: finite-sample
covariance degeneracy is allowed, provided its probability vanishes. -/
theorem
    twoSLSBootstrapRobustPercentileTCIEventFinSucc_tendsto_one_sub_alpha_uniform_of_asymptoticCoverageInputs
    [IsProbabilityMeasure μ]
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {R : Matrix Unit k ℝ} {β : k → ℝ} {q α : ℝ}
    (hTstar :
      TendstoInBootstrapDistributionIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs (_ : Unit) =>
          twoSLSBootstrapRobustLinearTStatFinSucc R Z X Y n ω ωs)
        (gaussianReal 0 1) (fun z : ℝ => fun _ : Unit => z))
    (hcoverage :
      TwoSLSBootstrapRobustPercentileTAsymptoticCoverageInputs
        μ Z X Y β R q α) :
    Tendsto
      (fun n =>
        μ {ω |
          twoSLSBootstrapRobustPercentileTCIEventFinSucc
            R Z X Y β α n ω})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) :=
  twoSLSBootstrapRobustPercentileTCIEventFinSucc_tendsto_one_sub_alpha_uniform_of_standardError_nonpos_tendsto_zero
    (μ := μ) (Z := Z) (X := X) (Y := Y) (R := R) (β := β)
    (q := q) (α := α)
    hcoverage.sample.standard_error_nonpos_probability_tendsto_zero
    hcoverage.sample.statistic_limit
    (fun n ω =>
      twoSLSBootstrapRobustLinearTStatFinSucc_aemeasurable
        (R := R) (Z := Z) (X := X) (Y := Y) n ω)
    hTstar hcoverage.quantile.alpha_pos hcoverage.quantile.alpha_lt_one
    hcoverage.quantile.standardNormal_cdf_strictMono
    hcoverage.quantile.lower_quantile_aemeasurable
    hcoverage.quantile.upper_quantile_aemeasurable
    hcoverage.quantile.critical_nonneg hcoverage.quantile.cdf_lower
    hcoverage.quantile.cdf_upper

set_option linter.style.longLine false in
/-- Bootstrap percentile-`t` critical-value convergence and interval coverage
under high-probability sample covariance nondegeneracy. -/
theorem
    twoSLSBootstrapRobustPercentileTCIEventFinSucc_quantiles_tendsto_and_coverage_of_asymptotic_sample_quantile
    [IsProbabilityMeasure μ]
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {R : Matrix Unit k ℝ} {β : k → ℝ} {q α : ℝ}
    (hTstar :
      TendstoInBootstrapDistributionIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs (_ : Unit) =>
          twoSLSBootstrapRobustLinearTStatFinSucc R Z X Y n ω ωs)
        (gaussianReal 0 1) (fun z : ℝ => fun _ : Unit => z))
    (hsample :
      TwoSLSBootstrapRobustPercentileTAsymptoticSampleInputs μ Z X Y β R)
    (hquantile :
      TwoSLSBootstrapRobustPercentileTQuantileCalibrationInputs
        μ Z X Y R q α) :
    (TendstoInMeasure μ
        (bootstrapScalarLowerQuantileIndexed
          (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
          (fun n ω ωs =>
            twoSLSBootstrapRobustLinearTStatFinSucc R Z X Y n ω ωs)
          (α / 2))
        atTop (fun _ => -q) ∧
      TendstoInMeasure μ
        (bootstrapScalarLowerQuantileIndexed
          (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
          (fun n ω ωs =>
            twoSLSBootstrapRobustLinearTStatFinSucc R Z X Y n ω ωs)
          (1 - α / 2))
        atTop (fun _ => q)) ∧
      Tendsto
        (fun n =>
          μ {ω |
            twoSLSBootstrapRobustPercentileTCIEventFinSucc
              R Z X Y β α n ω})
        atTop (𝓝 (ENNReal.ofReal (1 - α))) := by
  constructor
  · exact
      hquantile.quantiles_tendsto_of_bootstrap_tstat
        (μ := μ) (Z := Z) (X := X) (Y := Y) (R := R) hTstar
  · exact
      twoSLSBootstrapRobustPercentileTCIEventFinSucc_tendsto_one_sub_alpha_uniform_of_asymptoticCoverageInputs
        (μ := μ) (Z := Z) (X := X) (Y := Y) (R := R)
        (β := β) (q := q) (α := α) hTstar
        (TwoSLSBootstrapRobustPercentileTAsymptoticCoverageInputs.of_sample_quantile
          (μ := μ) (Z := Z) (X := X) (Y := Y) (β := β)
          (R := R) (q := q) (α := α) hsample hquantile)

set_option linter.style.longLine false in
/-- Percentile-`t` quantile convergence and interval coverage from the
sample-side package, the bootstrap t-ratio limit, and the named quantile
calibration package.

This theorem exposes the Chapter 10 quantile step used in Hansen Theorem
12.8 before returning the final coverage endpoint: the two bootstrap
percentile-`t` critical values converge to `-q` and `q`, and the resulting
interval has limiting coverage `1 - α`. -/
theorem
    twoSLSBootstrapRobustPercentileTCIEventFinSucc_quantiles_tendsto_and_coverage_of_sample_quantile
    [IsProbabilityMeasure μ]
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {R : Matrix Unit k ℝ} {β : k → ℝ} {q α : ℝ}
    (hTstar :
      TendstoInBootstrapDistributionIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs (_ : Unit) =>
          twoSLSBootstrapRobustLinearTStatFinSucc R Z X Y n ω ωs)
        (gaussianReal 0 1) (fun z : ℝ => fun _ : Unit => z))
    (hsample :
      TwoSLSBootstrapRobustPercentileTSampleInputs μ Z X Y β R)
    (hquantile :
      TwoSLSBootstrapRobustPercentileTQuantileCalibrationInputs
        μ Z X Y R q α) :
    (TendstoInMeasure μ
        (bootstrapScalarLowerQuantileIndexed
          (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
          (fun n ω ωs =>
            twoSLSBootstrapRobustLinearTStatFinSucc R Z X Y n ω ωs)
          (α / 2))
        atTop (fun _ => -q) ∧
      TendstoInMeasure μ
        (bootstrapScalarLowerQuantileIndexed
          (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
          (fun n ω ωs =>
            twoSLSBootstrapRobustLinearTStatFinSucc R Z X Y n ω ωs)
          (1 - α / 2))
        atTop (fun _ => q)) ∧
      Tendsto
        (fun n =>
          μ {ω |
            twoSLSBootstrapRobustPercentileTCIEventFinSucc
              R Z X Y β α n ω})
        atTop (𝓝 (ENNReal.ofReal (1 - α))) := by
  constructor
  · exact
      hquantile.quantiles_tendsto_of_bootstrap_tstat
        (μ := μ) (Z := Z) (X := X) (Y := Y) (R := R)
        hTstar
  · exact
      twoSLSBootstrapRobustPercentileTCIEventFinSucc_tendsto_one_sub_alpha_uniform_of_coverageInputs
        (μ := μ) (Z := Z) (X := X) (Y := Y) (R := R)
        (β := β) (q := q) (α := α) hTstar
        (TwoSLSBootstrapRobustPercentileTCoverageInputs.of_sample_quantile
          (μ := μ) (Z := Z) (X := X) (Y := Y) (β := β)
          (R := R) (q := q) (α := α) hsample hquantile)

/-- Remaining studentization inputs for the robust ordinary-bootstrap
Theorem 12.8 t-ratio.

The positivity field rules out a degenerate one-row restriction limit. The
tail field is the exact compact-tightness input needed to combine the scalar
numerator and bootstrap robust standard error. -/
structure TwoSLSBootstrapRobustStudentizationInputs
    (μ : Measure Ω)
    (Z : ℕ → Ω → l → ℝ) (X : ℕ → Ω → k → ℝ) (Y : ℕ → Ω → ℝ)
    (R : Matrix Unit k ℝ) (Vβ : Matrix k k ℝ) : Prop where
  limit_se_pos : 0 < linearRestrictionStdError R Vβ
  joint_tail : ∀ η : ℝ, 0 < η →
    ∃ K : Set (ℝ × ℝ), IsCompact K ∧
      TendstoInMeasure μ
        (fun n ω =>
          (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω) n ω).real
            {ωs |
              (twoSLSBootstrapLinearRestrictionStatisticFinSucc R Z X Y n ω ωs,
                linearRestrictionStdError R Vβ) ∉ K})
        atTop (fun _ => 0) ∧
      TendstoInMeasure μ
        (fun n ω =>
          (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω) n ω).real
            {ωs |
              (twoSLSBootstrapLinearRestrictionStatisticFinSucc R Z X Y n ω ωs,
                twoSLSBootstrapRobustLinearRestrictionStdErrorFinSucc
                  R Z X Y n ω ωs) ∉ K})
        atTop (fun _ => 0)

/-- Build the robust-bootstrap studentization package from positive-definite
restriction covariance plus the compact joint-tail input.

This keeps Theorem 12.8's nondegeneracy condition in covariance form instead
of asking callers to prove positivity of the square-root standard error
directly. -/
theorem TwoSLSBootstrapRobustStudentizationInputs.of_restrictionCov_posDef
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {R : Matrix Unit k ℝ} {Vβ : Matrix k k ℝ}
    (hVθ : (R * Vβ * Rᵀ).PosDef)
    (hTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set (ℝ × ℝ), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω =>
            (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω) n ω).real
              {ωs |
                (twoSLSBootstrapLinearRestrictionStatisticFinSucc R Z X Y n ω ωs,
                  linearRestrictionStdError R Vβ) ∉ K})
          atTop (fun _ => 0) ∧
        TendstoInMeasure μ
          (fun n ω =>
            (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω) n ω).real
              {ωs |
                (twoSLSBootstrapLinearRestrictionStatisticFinSucc R Z X Y n ω ωs,
                  twoSLSBootstrapRobustLinearRestrictionStdErrorFinSucc
                    R Z X Y n ω ωs) ∉ K})
          atTop (fun _ => 0)) :
    TwoSLSBootstrapRobustStudentizationInputs μ Z X Y R Vβ where
  limit_se_pos := linearRestrictionStdError_pos_of_restrictionCov_posDef R hVθ
  joint_tail := hTail

set_option linter.style.longLine false in
/-- Build robust-bootstrap studentization from coefficient tightness and
standard-error consistency.

The coefficient linearization input already contains compact-tail control for
the bootstrap coefficient statistic.  Chapter 10's indexed product-tail
constructor upgrades that scalar numerator tail, together with robust
standard-error consistency, into the joint tail required by the
studentization package. -/
theorem
    TwoSLSBootstrapRobustStudentizationInputs.of_restrictionCov_posDef_coefficientLinearization
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {R : Matrix Unit k ℝ} {Vβ : Matrix k k ℝ}
    {QXZ : Matrix k l ℝ} {QZZ Omega : Matrix l l ℝ} {QZX : Matrix l k ℝ}
    (hVθ : (R * Vβ * Rᵀ).PosDef)
    (hlin : TwoSLSBootstrapCoefficientLinearizationInputs μ
      (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω)) Z X Y
      QXZ QZZ Omega QZX)
    (hse :
      TendstoInBootstrapProbabilityIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs =>
          twoSLSBootstrapRobustLinearRestrictionStdErrorFinSucc R Z X Y n ω ωs)
        (fun _ => linearRestrictionStdError R Vβ)) :
    TwoSLSBootstrapRobustStudentizationInputs μ Z X Y R Vβ :=
  TwoSLSBootstrapRobustStudentizationInputs.of_restrictionCov_posDef
    (μ := μ) (Z := Z) (X := X) (Y := Y) (R := R) (Vβ := Vβ)
    hVθ
    (chapter10_indexed_bootstrap_pair_compactTail_of_scalar_compactTail
      (μ := μ)
      (Pstar := twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
      (Xstar := fun n ω ωs =>
        twoSLSBootstrapLinearRestrictionStatisticFinSucc R Z X Y n ω ωs)
      (Ystar := fun n ω ωs =>
        twoSLSBootstrapRobustLinearRestrictionStdErrorFinSucc R Z X Y n ω ωs)
      (c := linearRestrictionStdError R Vβ)
      (fun n ω =>
        twoSLSBootstrapUniformPstarFinSucc_isProbabilityMeasure (Ω := Ω) n ω)
      (TwoSLSBootstrapCoefficientLinearizationInputs.linearRestrictionStatistic_compactTail
        (μ := μ)
        (Pstar := twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (Z := Z) (X := X) (Y := Y)
        (QXZ := QXZ) (QZZ := QZZ) (Omega := Omega) (QZX := QZX)
        hlin
        (fun n ω =>
          twoSLSBootstrapUniformPstarFinSucc_isProbabilityMeasure (Ω := Ω) n ω)
        R)
      hse)

set_option linter.style.longLine false in
/-- Assumption 12.2 nondegeneracy bridge for one-row bootstrap
studentization.

The iid Assumption 12.2 package supplies positive definiteness of Hansen's
2SLS coefficient covariance. A full-rank one-row restriction, stated as
injectivity of `Rᵀ.mulVec`, turns this into positive definiteness of
`R Vβ Rᵀ`, the covariance-form condition consumed by the robust bootstrap
t-ratio wrapper. -/
theorem twoSLSBootstrapRestrictionCov_posDef_of_assumption12_2
    [IsProbabilityMeasure μ]
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e : ℕ → Ω → ℝ}
    {R : Matrix Unit k ℝ}
    (h : TwoSLSAssumption12_2IidFourthConditions μ Z X e)
    (hR : Function.Injective Rᵀ.mulVec) :
    (R *
        twoSLSAsymptoticVariance
          (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
          (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
          (scoreCovMat μ Z e)
          (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X))) *
      Rᵀ).PosDef := by
  let Vβ : Matrix k k ℝ :=
    twoSLSAsymptoticVariance
      (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
      (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
      (scoreCovMat μ Z e)
      (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))
  let hGram := h.toGramConditions
  have hVβ : Vβ.PosDef := by
    dsimp [Vβ]
    exact
      twoSLSAsymptoticVariance_posDef_of_qzz_omega_rank
        (QXZ := twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
        (QZZ := twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
        (Omega := scoreCovMat μ Z e)
        (QZX := twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))
        (twoSLSCombinedQXZ_eq_transpose_QZX_of_popGram_wlln
          (μ := μ) (Z := Z) (X := X)
          hGram.toTwoSLSAssumption12_1GramConditions.combined_gram)
        h.qzz_posDef h.omega_posDef h.qzx_rank
  have hcov : ((Rᵀ)ᵀ * Vβ * Rᵀ).PosDef :=
    restrictionCov_posDef_of_cov_posDef Vβ Rᵀ hVβ hR
  simpa [Vβ] using hcov

set_option linter.style.longLine false in
/-- Assumption-12.2-facing nondegeneracy of the one-row robust bootstrap
studentization scale.

The iid Assumption 12.2 package gives positive definiteness of Hansen's 2SLS
coefficient covariance, and full rank of the row restriction transfers it to
the scalar restriction covariance. This wrapper exposes the derived positive
standard-error scale directly for theorem statements that still consume the
Chapter 10 studentization hypothesis in standard-error form. -/
theorem twoSLSBootstrapLinearRestrictionStdError_pos_of_assumption12_2
    [IsProbabilityMeasure μ]
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e : ℕ → Ω → ℝ}
    {R : Matrix Unit k ℝ}
    (h : TwoSLSAssumption12_2IidFourthConditions μ Z X e)
    (hR : Function.Injective Rᵀ.mulVec) :
    0 <
      linearRestrictionStdError R
        (twoSLSAsymptoticVariance
          (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
          (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
          (scoreCovMat μ Z e)
          (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))) :=
  linearRestrictionStdError_pos_of_restrictionCov_posDef R
    (twoSLSBootstrapRestrictionCov_posDef_of_assumption12_2
      (μ := μ) (Z := Z) (X := X) (e := e) (R := R) h hR)

set_option linter.style.longLine false in
/-- Assumption-12.2-facing robust studentization constructor.

This derives all studentization fields from existing pieces: Assumption 12.2
and full rank of the one-row restriction give nondegeneracy, Chapter 12 robust
covariance consistency gives bootstrap standard-error consistency, and the
coefficient linearization package supplies the scalar numerator tightness
through
`TwoSLSBootstrapCoefficientLinearizationInputs.linearRestrictionStatistic_compactTail`.
-/
theorem
    TwoSLSBootstrapRobustStudentizationInputs.of_assumption12_2_weight_wlln_coefficientLinearization_resampleCloseness
    [IsProbabilityMeasure μ]
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {R : Matrix Unit k ℝ}
    (h : TwoSLSAssumption12_2IidFourthConditions μ Z X e)
    (β : k → ℝ)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hw : TwoSLSCovarianceWeightWLLNConditions μ Z X e)
    (hlin : TwoSLSBootstrapCoefficientLinearizationInputs μ
      (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω)) Z X Y
      (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
      (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
      (scoreCovMat μ Z e)
      (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X))))
    (hR : Function.Injective Rᵀ.mulVec)
    (hV : TwoSLSBootstrapRobustCovarianceResampleCloseness μ Z X Y) :
    TwoSLSBootstrapRobustStudentizationInputs μ Z X Y R
      (twoSLSAsymptoticVariance
        (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
        (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
        (scoreCovMat μ Z e)
        (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))) := by
  have hVθ :
      (R *
          twoSLSAsymptoticVariance
            (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (scoreCovMat μ Z e)
            (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X))) *
        Rᵀ).PosDef :=
    twoSLSBootstrapRestrictionCov_posDef_of_assumption12_2
      (μ := μ) (Z := Z) (X := X) (e := e) (R := R) h hR
  have hVconv :=
    twoSLSBootstrapVHatStarFinSucc_tendstoInBootstrapProbability_formula_uniform_of_assumption12_2_iid_weight_wlln_resampleCloseness
      (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y)
      h β hmodel hw hV
  have hse :=
    twoSLSBootstrapRobustLinearRestrictionStdErrorFinSucc_tendstoInBootstrapProbability_formula_uniform
      (μ := μ) (R := R) (Z := Z) (X := X) (Y := Y)
      (QXZ := twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
      (QZZ := twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
      (Omega := scoreCovMat μ Z e)
      (QZX := twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))
      hVconv
  exact
    TwoSLSBootstrapRobustStudentizationInputs.of_restrictionCov_posDef_coefficientLinearization
      (μ := μ) (Z := Z) (X := X) (Y := Y) (R := R)
      (Vβ :=
        twoSLSAsymptoticVariance
          (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
          (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
          (scoreCovMat μ Z e)
          (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X))))
      (QXZ := twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
      (QZZ := twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
      (Omega := scoreCovMat μ Z e)
      (QZX := twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))
      hVθ hlin hse

set_option linter.style.longLine false in
/-- Assumption-12.2-facing robust studentization constructor from primitive
covariance-resampling tails.

This version keeps the covariance resampling input at the empirical-process
tail layer. It first converts the primitive norm-tail package to the named
closeness package, then reuses the established studentization constructor. -/
theorem
    TwoSLSBootstrapRobustStudentizationInputs.of_assumption12_2_weight_wlln_coefficientLinearization_resamplePrimitive
    [IsProbabilityMeasure μ]
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {R : Matrix Unit k ℝ}
    (h : TwoSLSAssumption12_2IidFourthConditions μ Z X e)
    (β : k → ℝ)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hw : TwoSLSCovarianceWeightWLLNConditions μ Z X e)
    (hlin : TwoSLSBootstrapCoefficientLinearizationInputs μ
      (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω)) Z X Y
      (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
      (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
      (scoreCovMat μ Z e)
      (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X))))
    (hR : Function.Injective Rᵀ.mulVec)
    (hV : TwoSLSBootstrapRobustCovarianceResamplePrimitiveInputs μ Z X Y) :
    TwoSLSBootstrapRobustStudentizationInputs μ Z X Y R
      (twoSLSAsymptoticVariance
        (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
        (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
        (scoreCovMat μ Z e)
        (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))) :=
  TwoSLSBootstrapRobustStudentizationInputs.of_assumption12_2_weight_wlln_coefficientLinearization_resampleCloseness
    (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y)
    (R := R) h β hmodel hw hlin hR
    (hV.toResampleCloseness
      (μ := μ) (Z := Z) (X := X) (Y := Y))

/-- Assumption-12.2-facing robust ordinary-bootstrap t-ratio route for Hansen
Theorem 12.8.

This composes the robust covariance consistency derived from the iid
Assumption 12.2 package and the Chapter 12 weighted residual-substitution WLLN
with the existing numerator-tight studentization theorem.  The remaining
bootstrap-specific hypotheses are exactly the scalar numerator CLT/tail
control and the concrete resampled-vs-original covariance closeness. -/
theorem
    twoSLSBootstrapRobustLinearTStatFinSucc_theorem12_8_of_assumption12_2_weight_wlln
    [IsProbabilityMeasure μ]
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {R : Matrix Unit k ℝ}
    (h : TwoSLSAssumption12_2IidFourthConditions μ Z X e)
    (β : k → ℝ)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hw : TwoSLSCovarianceWeightWLLNConditions μ Z X e)
    (hseθ : 0 <
      linearRestrictionStdError R
        (twoSLSAsymptoticVariance
          (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
          (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
          (scoreCovMat μ Z e)
          (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))))
    (hT :
      TendstoInBootstrapWeakDistributionIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs =>
          twoSLSBootstrapLinearRestrictionStatisticFinSucc R Z X Y n ω ωs)
        (gaussianReal 0 1)
        (fun z : ℝ =>
          linearRestrictionStdError R
              (twoSLSAsymptoticVariance
                (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
                (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
                (scoreCovMat μ Z e)
                (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))) * z))
    (hT_meas : ∀ n ω,
      Measurable
        (fun ωs => twoSLSBootstrapLinearRestrictionStatisticFinSucc R Z X Y n ω ωs))
    (hse_meas : ∀ n ω,
      Measurable
        (fun ωs =>
          twoSLSBootstrapRobustLinearRestrictionStdErrorFinSucc R Z X Y n ω ωs))
    (hTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set (ℝ × ℝ), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω =>
            (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω) n ω).real
              {ωs |
                (twoSLSBootstrapLinearRestrictionStatisticFinSucc R Z X Y n ω ωs,
                  linearRestrictionStdError R
                    (twoSLSAsymptoticVariance
                      (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
                      (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
                      (scoreCovMat μ Z e)
                      (twoSLSCombinedQZX
                        (popGram μ (twoSLSCombinedRegressors Z X))))) ∉ K})
          atTop (fun _ => 0) ∧
        TendstoInMeasure μ
          (fun n ω =>
            (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω) n ω).real
              {ωs |
                (twoSLSBootstrapLinearRestrictionStatisticFinSucc R Z X Y n ω ωs,
                  twoSLSBootstrapRobustLinearRestrictionStdErrorFinSucc
                    R Z X Y n ω ωs) ∉ K})
          atTop (fun _ => 0))
    (hV_resample_close :
      TendstoInBootstrapProbabilityIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs =>
          twoSLSBootstrapVHatStarFinSucc Z X Y n ω ωs -
            twoSLSVHatStar
              (stackRegressors Z (n + 1) ω) (stackRegressors X (n + 1) ω)
              (stackOutcomes Y (n + 1) ω))
        (fun _ => 0)) :
    TendstoInBootstrapDistributionIndexed μ
      (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
      (fun n ω ωs (_ : Unit) =>
        twoSLSBootstrapRobustLinearTStatFinSucc R Z X Y n ω ωs)
      (gaussianReal 0 1) (fun z : ℝ => fun _ : Unit => z) := by
  have hV :=
    twoSLSBootstrapVHatStarFinSucc_tendstoInBootstrapProbability_formula_uniform_of_assumption12_2_iid_weight_wlln
      (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y)
      h β hmodel hw hV_resample_close
  exact
    twoSLSBootstrapRobustLinearTStatFinSucc_tendstoInBootstrapDistribution_formula_uniform_of_numerator_tight
      (μ := μ) (Z := Z) (X := X) (Y := Y) (R := R)
      (QXZ := twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
      (QZZ := twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
      (Omega := scoreCovMat μ Z e)
      (QZX := twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))
      hseθ hT hT_meas hse_meas hTail hV

/-- Robust ordinary-bootstrap t-ratio route with the named robust covariance
resampling package. -/
theorem
    twoSLSBootstrapRobustLinearTStatFinSucc_theorem12_8_of_assumption12_2_weight_wlln_resampleCloseness
    [IsProbabilityMeasure μ]
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {R : Matrix Unit k ℝ}
    (h : TwoSLSAssumption12_2IidFourthConditions μ Z X e)
    (β : k → ℝ)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hw : TwoSLSCovarianceWeightWLLNConditions μ Z X e)
    (hseθ : 0 <
      linearRestrictionStdError R
        (twoSLSAsymptoticVariance
          (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
          (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
          (scoreCovMat μ Z e)
          (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))))
    (hT :
      TendstoInBootstrapWeakDistributionIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs =>
          twoSLSBootstrapLinearRestrictionStatisticFinSucc R Z X Y n ω ωs)
        (gaussianReal 0 1)
        (fun z : ℝ =>
          linearRestrictionStdError R
              (twoSLSAsymptoticVariance
                (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
                (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
                (scoreCovMat μ Z e)
                (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))) * z))
    (hT_meas : ∀ n ω,
      Measurable
        (fun ωs => twoSLSBootstrapLinearRestrictionStatisticFinSucc R Z X Y n ω ωs))
    (hse_meas : ∀ n ω,
      Measurable
        (fun ωs =>
          twoSLSBootstrapRobustLinearRestrictionStdErrorFinSucc R Z X Y n ω ωs))
    (hTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set (ℝ × ℝ), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω =>
            (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω) n ω).real
              {ωs |
                (twoSLSBootstrapLinearRestrictionStatisticFinSucc R Z X Y n ω ωs,
                  linearRestrictionStdError R
                    (twoSLSAsymptoticVariance
                      (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
                      (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
                      (scoreCovMat μ Z e)
                      (twoSLSCombinedQZX
                        (popGram μ (twoSLSCombinedRegressors Z X))))) ∉ K})
          atTop (fun _ => 0) ∧
        TendstoInMeasure μ
          (fun n ω =>
            (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω) n ω).real
              {ωs |
                (twoSLSBootstrapLinearRestrictionStatisticFinSucc R Z X Y n ω ωs,
                  twoSLSBootstrapRobustLinearRestrictionStdErrorFinSucc
                    R Z X Y n ω ωs) ∉ K})
          atTop (fun _ => 0))
    (hV : TwoSLSBootstrapRobustCovarianceResampleCloseness μ Z X Y) :
    TendstoInBootstrapDistributionIndexed μ
      (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
      (fun n ω ωs (_ : Unit) =>
        twoSLSBootstrapRobustLinearTStatFinSucc R Z X Y n ω ωs)
      (gaussianReal 0 1) (fun z : ℝ => fun _ : Unit => z) :=
  twoSLSBootstrapRobustLinearTStatFinSucc_theorem12_8_of_assumption12_2_weight_wlln
    (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y) (R := R)
    h β hmodel hw hseθ hT hT_meas hse_meas hTail hV.covariance_closeness

/-- Robust ordinary-bootstrap t-ratio route with named studentization and
robust covariance resampling inputs. -/
theorem
    twoSLSBootstrapRobustLinearTStatFinSucc_theorem12_8_of_assumption12_2_weight_wlln_studentization_resampleCloseness
    [IsProbabilityMeasure μ]
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {R : Matrix Unit k ℝ}
    (h : TwoSLSAssumption12_2IidFourthConditions μ Z X e)
    (β : k → ℝ)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hw : TwoSLSCovarianceWeightWLLNConditions μ Z X e)
    (hT :
      TendstoInBootstrapWeakDistributionIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs =>
          twoSLSBootstrapLinearRestrictionStatisticFinSucc R Z X Y n ω ωs)
        (gaussianReal 0 1)
        (fun z : ℝ =>
          linearRestrictionStdError R
              (twoSLSAsymptoticVariance
                (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
                (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
                (scoreCovMat μ Z e)
                (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))) * z))
    (hstudent :
      TwoSLSBootstrapRobustStudentizationInputs μ Z X Y R
        (twoSLSAsymptoticVariance
          (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
          (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
          (scoreCovMat μ Z e)
          (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))))
    (hV : TwoSLSBootstrapRobustCovarianceResampleCloseness μ Z X Y) :
    TendstoInBootstrapDistributionIndexed μ
      (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
      (fun n ω ωs (_ : Unit) =>
        twoSLSBootstrapRobustLinearTStatFinSucc R Z X Y n ω ωs)
      (gaussianReal 0 1) (fun z : ℝ => fun _ : Unit => z) :=
  twoSLSBootstrapRobustLinearTStatFinSucc_theorem12_8_of_assumption12_2_weight_wlln
    (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y) (R := R)
    h β hmodel hw hstudent.limit_se_pos hT
    (by
      intro n ω
      fun_prop)
    (by
      intro n ω
      fun_prop)
hstudent.joint_tail hV.covariance_closeness

set_option linter.style.longLine false in
/-- Robust ordinary-bootstrap t-ratio route with covariance-form
nondegeneracy of the one-row restriction.

This is the same endpoint as
`twoSLSBootstrapRobustLinearTStatFinSucc_theorem12_8_of_assumption12_2_weight_wlln_studentization_resampleCloseness`,
but callers provide the Hansen-style positive-definite restriction covariance
instead of the derived standard-error positivity field. -/
theorem
    twoSLSBootstrapRobustLinearTStatFinSucc_theorem12_8_of_assumption12_2_weight_wlln_restrictionCov_resampleCloseness
    [IsProbabilityMeasure μ]
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {R : Matrix Unit k ℝ}
    (h : TwoSLSAssumption12_2IidFourthConditions μ Z X e)
    (β : k → ℝ)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hw : TwoSLSCovarianceWeightWLLNConditions μ Z X e)
    (hT :
      TendstoInBootstrapWeakDistributionIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs =>
          twoSLSBootstrapLinearRestrictionStatisticFinSucc R Z X Y n ω ωs)
        (gaussianReal 0 1)
        (fun z : ℝ =>
          linearRestrictionStdError R
              (twoSLSAsymptoticVariance
                (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
                (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
                (scoreCovMat μ Z e)
                (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))) * z))
    (hVθ :
      (R *
          twoSLSAsymptoticVariance
            (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (scoreCovMat μ Z e)
            (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X))) *
        Rᵀ).PosDef)
    (hTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set (ℝ × ℝ), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω =>
            (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω) n ω).real
              {ωs |
                (twoSLSBootstrapLinearRestrictionStatisticFinSucc R Z X Y n ω ωs,
                  linearRestrictionStdError R
                    (twoSLSAsymptoticVariance
                      (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
                      (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
                      (scoreCovMat μ Z e)
                      (twoSLSCombinedQZX
                        (popGram μ (twoSLSCombinedRegressors Z X))))) ∉ K})
          atTop (fun _ => 0) ∧
        TendstoInMeasure μ
          (fun n ω =>
            (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω) n ω).real
              {ωs |
                (twoSLSBootstrapLinearRestrictionStatisticFinSucc R Z X Y n ω ωs,
                  twoSLSBootstrapRobustLinearRestrictionStdErrorFinSucc
                    R Z X Y n ω ωs) ∉ K})
          atTop (fun _ => 0))
    (hV : TwoSLSBootstrapRobustCovarianceResampleCloseness μ Z X Y) :
    TendstoInBootstrapDistributionIndexed μ
      (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
      (fun n ω ωs (_ : Unit) =>
        twoSLSBootstrapRobustLinearTStatFinSucc R Z X Y n ω ωs)
      (gaussianReal 0 1) (fun z : ℝ => fun _ : Unit => z) :=
  twoSLSBootstrapRobustLinearTStatFinSucc_theorem12_8_of_assumption12_2_weight_wlln_studentization_resampleCloseness
    (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y) (R := R)
    h β hmodel hw hT
    (TwoSLSBootstrapRobustStudentizationInputs.of_restrictionCov_posDef
      (μ := μ) (Z := Z) (X := X) (Y := Y) (R := R)
      (Vβ :=
        twoSLSAsymptoticVariance
          (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
          (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
          (scoreCovMat μ Z e)
          (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X))))
      hVθ hTail)
    hV

set_option linter.style.longLine false in
/-- Robust ordinary-bootstrap t-ratio route with full-rank one-row restriction
nondegeneracy derived from Assumption 12.2.

This is the marginal-numerator counterpart of the bundled full-rank Theorem
12.8 wrapper: callers provide the scalar numerator CLT, the joint compact-tail
input, and robust covariance resampling closeness, while Assumption 12.2 plus
full rank of `Rᵀ.mulVec` supplies the limiting standard-error positivity. -/
theorem
    twoSLSBootstrapRobustLinearTStatFinSucc_theorem12_8_of_assumption12_2_weight_wlln_fullRank_resampleCloseness
    [IsProbabilityMeasure μ]
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {R : Matrix Unit k ℝ}
    (h : TwoSLSAssumption12_2IidFourthConditions μ Z X e)
    (β : k → ℝ)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hw : TwoSLSCovarianceWeightWLLNConditions μ Z X e)
    (hT :
      TendstoInBootstrapWeakDistributionIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs =>
          twoSLSBootstrapLinearRestrictionStatisticFinSucc R Z X Y n ω ωs)
        (gaussianReal 0 1)
        (fun z : ℝ =>
          linearRestrictionStdError R
              (twoSLSAsymptoticVariance
                (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
                (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
                (scoreCovMat μ Z e)
                (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))) * z))
    (hR : Function.Injective Rᵀ.mulVec)
    (hTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set (ℝ × ℝ), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω =>
            (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω) n ω).real
              {ωs |
                (twoSLSBootstrapLinearRestrictionStatisticFinSucc R Z X Y n ω ωs,
                  linearRestrictionStdError R
                    (twoSLSAsymptoticVariance
                      (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
                      (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
                      (scoreCovMat μ Z e)
                      (twoSLSCombinedQZX
                        (popGram μ (twoSLSCombinedRegressors Z X))))) ∉ K})
          atTop (fun _ => 0) ∧
        TendstoInMeasure μ
          (fun n ω =>
            (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω) n ω).real
              {ωs |
                (twoSLSBootstrapLinearRestrictionStatisticFinSucc R Z X Y n ω ωs,
                  twoSLSBootstrapRobustLinearRestrictionStdErrorFinSucc
                    R Z X Y n ω ωs) ∉ K})
          atTop (fun _ => 0))
    (hV : TwoSLSBootstrapRobustCovarianceResampleCloseness μ Z X Y) :
    TendstoInBootstrapDistributionIndexed μ
      (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
      (fun n ω ωs (_ : Unit) =>
        twoSLSBootstrapRobustLinearTStatFinSucc R Z X Y n ω ωs)
      (gaussianReal 0 1) (fun z : ℝ => fun _ : Unit => z) :=
  twoSLSBootstrapRobustLinearTStatFinSucc_theorem12_8_of_assumption12_2_weight_wlln_restrictionCov_resampleCloseness
    (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y) (R := R)
    h β hmodel hw hT
    (twoSLSBootstrapRestrictionCov_posDef_of_assumption12_2
      (μ := μ) (Z := Z) (X := X) (e := e) (R := R) h hR)
    hTail hV

/-- Hansen Theorem 12.8, bundled ordinary-bootstrap endpoint.

This is the theorem-facing wrapper matching Hansen's two conclusions: the
ordinary bootstrap coefficient statistic has the same Gaussian limit as 2SLS,
and the robust studentized one-row restriction has a standard-normal bootstrap
limit.  The scalar numerator CLT used by the t-ratio is derived from the
coefficient bootstrap condition package above; the remaining hypotheses are the
genuinely bootstrap-specific tightness and robust-covariance closeness inputs
not yet derived from primitive Assumption 12.2 in this file. -/
theorem
    twoSLSBootstrap_theorem12_8_of_assumption12_2_weight_wlln
    [IsProbabilityMeasure μ]
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {R : Matrix Unit k ℝ}
    (h : TwoSLSAssumption12_2IidFourthConditions μ Z X e)
    (β : k → ℝ)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hw : TwoSLSCovarianceWeightWLLNConditions μ Z X e)
    (hcoef :
      TwoSLSBootstrapFormulaAsymptoticNormalConditions μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω)) Z X Y
        (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
        (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
        (scoreCovMat μ Z e)
        (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X))))
    (hseθ : 0 <
      linearRestrictionStdError R
        (twoSLSAsymptoticVariance
          (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
          (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
          (scoreCovMat μ Z e)
          (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))))
    (hT_meas : ∀ n ω,
      Measurable
        (fun ωs => twoSLSBootstrapLinearRestrictionStatisticFinSucc R Z X Y n ω ωs))
    (hse_meas : ∀ n ω,
      Measurable
        (fun ωs =>
          twoSLSBootstrapRobustLinearRestrictionStdErrorFinSucc R Z X Y n ω ωs))
    (hTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set (ℝ × ℝ), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω =>
            (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω) n ω).real
              {ωs |
                (twoSLSBootstrapLinearRestrictionStatisticFinSucc R Z X Y n ω ωs,
                  linearRestrictionStdError R
                    (twoSLSAsymptoticVariance
                      (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
                      (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
                      (scoreCovMat μ Z e)
                      (twoSLSCombinedQZX
                        (popGram μ (twoSLSCombinedRegressors Z X))))) ∉ K})
          atTop (fun _ => 0) ∧
        TendstoInMeasure μ
          (fun n ω =>
            (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω) n ω).real
              {ωs |
                (twoSLSBootstrapLinearRestrictionStatisticFinSucc R Z X Y n ω ωs,
                  twoSLSBootstrapRobustLinearRestrictionStdErrorFinSucc
                    R Z X Y n ω ωs) ∉ K})
          atTop (fun _ => 0))
    (hV_resample_close :
      TendstoInBootstrapProbabilityIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs =>
          twoSLSBootstrapVHatStarFinSucc Z X Y n ω ωs -
            twoSLSVHatStar
              (stackRegressors Z (n + 1) ω) (stackRegressors X (n + 1) ω)
              (stackOutcomes Y (n + 1) ω))
        (fun _ => 0)) :
    TendstoInBootstrapDistributionIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs => twoSLSBootstrapBetaGapFinSucc Z X Y n ω ωs)
        (multivariateGaussian (0 : EuclideanSpace ℝ k)
          (twoSLSAsymptoticVariance
            (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (scoreCovMat μ Z e)
            (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))))
        (fun z : EuclideanSpace ℝ k => (z : k → ℝ)) ∧
      TendstoInBootstrapDistributionIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs (_ : Unit) =>
          twoSLSBootstrapRobustLinearTStatFinSucc R Z X Y n ω ωs)
        (gaussianReal 0 1) (fun z : ℝ => fun _ : Unit => z) := by
  let Q : Matrix (l ⊕ k) (l ⊕ k) ℝ :=
    popGram μ (twoSLSCombinedRegressors Z X)
  let Vβ : Matrix k k ℝ :=
    twoSLSAsymptoticVariance
      (twoSLSCombinedQXZ Q) (twoSLSCombinedQZZ Q) (scoreCovMat μ Z e)
      (twoSLSCombinedQZX Q)
  have hVβ_pos : Vβ.PosSemidef := by
    have hpos : Vβ.PosDef := by
      dsimp [Vβ, Q]
      exact
        twoSLSAsymptoticVariance_posDef_of_qzz_omega_rank
          (QXZ := twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
          (QZZ := twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
          (Omega := scoreCovMat μ Z e)
          (QZX := twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))
          (twoSLSCombinedQXZ_eq_transpose_QZX_of_popGram_wlln
            (μ := μ) (Z := Z) (X := X)
            (hCombined :=
              h.toTwoSLSAssumption12_1IidConditions.toGramConditions.combined_gram))
          h.qzz_posDef h.omega_posDef h.qzx_rank
    exact hpos.posSemidef
  have hβdist :
      TendstoInBootstrapDistributionIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs => twoSLSBootstrapBetaGapFinSucc Z X Y n ω ωs)
        (multivariateGaussian (0 : EuclideanSpace ℝ k) Vβ)
        (fun z : EuclideanSpace ℝ k => (z : k → ℝ)) := by
    simpa [Vβ, Q] using
      twoSLSBootstrapBetaGapFinSucc_tendstoInBootstrapDistribution_formula_uniform
        (μ := μ) (Z := Z) (X := X) (Y := Y)
        (QXZ := twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
        (QZZ := twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
        (Omega := scoreCovMat μ Z e)
        (QZX := twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))
        hcoef
  have hT :
      TendstoInBootstrapWeakDistributionIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs =>
          twoSLSBootstrapLinearRestrictionStatisticFinSucc R Z X Y n ω ωs)
        (gaussianReal 0 1)
        (fun z : ℝ => linearRestrictionStdError R Vβ * z) := by
    simpa [Vβ, Q] using
      twoSLSBootstrapLinearRestrictionStatisticFinSucc_tendstoInBootstrapWeakDistribution_standardNormal_formula_uniform
        (μ := μ) (Z := Z) (X := X) (Y := Y) (R := R)
        (QXZ := twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
        (QZZ := twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
        (Omega := scoreCovMat μ Z e)
        (QZX := twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))
        hVβ_pos hcoef
  have ht :
      TendstoInBootstrapDistributionIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs (_ : Unit) =>
          twoSLSBootstrapRobustLinearTStatFinSucc R Z X Y n ω ωs)
        (gaussianReal 0 1) (fun z : ℝ => fun _ : Unit => z) := by
    simpa [Vβ, Q] using
      twoSLSBootstrapRobustLinearTStatFinSucc_theorem12_8_of_assumption12_2_weight_wlln
        (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y) (R := R)
        h β hmodel hw hseθ hT hT_meas hse_meas hTail hV_resample_close
  exact ⟨by simpa [Vβ, Q] using hβdist, ht⟩

set_option linter.style.longLine false in
/-- Hansen Theorem 12.8 with finite-resample bootstrap numerator and standard-error
measurability derived automatically.

This is the auto-measurability companion to
`twoSLSBootstrap_theorem12_8_of_assumption12_2_weight_wlln`: the only change is
that the two finite-resample measurability premises for the robust bootstrap
t-ratio are supplied by the deterministic bridges
`twoSLSBootstrapLinearRestrictionStatisticFinSucc_measurable` and
`twoSLSBootstrapRobustLinearRestrictionStdErrorFinSucc_measurable`. -/
theorem
    twoSLSBootstrap_theorem12_8_of_assumption12_2_weight_wlln_autoMeas
    [IsProbabilityMeasure μ]
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {R : Matrix Unit k ℝ}
    (h : TwoSLSAssumption12_2IidFourthConditions μ Z X e)
    (β : k → ℝ)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hw : TwoSLSCovarianceWeightWLLNConditions μ Z X e)
    (hcoef :
      TwoSLSBootstrapFormulaAsymptoticNormalConditions μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω)) Z X Y
        (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
        (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
        (scoreCovMat μ Z e)
        (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X))))
    (hseθ : 0 <
      linearRestrictionStdError R
        (twoSLSAsymptoticVariance
          (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
          (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
          (scoreCovMat μ Z e)
          (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))))
    (hTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set (ℝ × ℝ), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω =>
            (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω) n ω).real
              {ωs |
                (twoSLSBootstrapLinearRestrictionStatisticFinSucc R Z X Y n ω ωs,
                  linearRestrictionStdError R
                    (twoSLSAsymptoticVariance
                      (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
                      (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
                      (scoreCovMat μ Z e)
                      (twoSLSCombinedQZX
                        (popGram μ (twoSLSCombinedRegressors Z X))))) ∉ K})
          atTop (fun _ => 0) ∧
        TendstoInMeasure μ
          (fun n ω =>
            (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω) n ω).real
              {ωs |
                (twoSLSBootstrapLinearRestrictionStatisticFinSucc R Z X Y n ω ωs,
                  twoSLSBootstrapRobustLinearRestrictionStdErrorFinSucc
                    R Z X Y n ω ωs) ∉ K})
          atTop (fun _ => 0))
    (hV_resample_close :
      TendstoInBootstrapProbabilityIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs =>
          twoSLSBootstrapVHatStarFinSucc Z X Y n ω ωs -
            twoSLSVHatStar
              (stackRegressors Z (n + 1) ω) (stackRegressors X (n + 1) ω)
              (stackOutcomes Y (n + 1) ω))
        (fun _ => 0)) :
    TendstoInBootstrapDistributionIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs => twoSLSBootstrapBetaGapFinSucc Z X Y n ω ωs)
        (multivariateGaussian (0 : EuclideanSpace ℝ k)
          (twoSLSAsymptoticVariance
            (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (scoreCovMat μ Z e)
            (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))))
        (fun z : EuclideanSpace ℝ k => (z : k → ℝ)) ∧
      TendstoInBootstrapDistributionIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs (_ : Unit) =>
          twoSLSBootstrapRobustLinearTStatFinSucc R Z X Y n ω ωs)
        (gaussianReal 0 1) (fun z : ℝ => fun _ : Unit => z) :=
  twoSLSBootstrap_theorem12_8_of_assumption12_2_weight_wlln
    (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y) (R := R)
    h β hmodel hw hcoef hseθ
    (fun n ω =>
      twoSLSBootstrapLinearRestrictionStatisticFinSucc_measurable
        (R := R) (Z := Z) (X := X) (Y := Y) n ω)
    (fun n ω =>
      twoSLSBootstrapRobustLinearRestrictionStdErrorFinSucc_measurable
        (R := R) (Z := Z) (X := X) (Y := Y) n ω)
    hTail hV_resample_close

/-- Hansen Theorem 12.8, bundled ordinary-bootstrap endpoint from the
score-level and linearization-level coefficient inputs.

This is the tightened theorem-facing wrapper for the coefficient side: the
coefficient bootstrap condition package is constructed from the score CLT,
population-to-bootstrap-sample linearization closeness, and coefficient
linearization closeness, then reused for the robust t-ratio conclusion. -/
theorem
    twoSLSBootstrap_theorem12_8_of_assumption12_2_weight_wlln_score_clt_inputs
    [IsProbabilityMeasure μ]
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {R : Matrix Unit k ℝ}
    (h : TwoSLSAssumption12_2IidFourthConditions μ Z X e)
    (β : k → ℝ)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hw : TwoSLSCovarianceWeightWLLNConditions μ Z X e)
    (hcoef :
      TwoSLSBootstrapFormulaCoefficientCLTInputs μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω)) Z X Y
        (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
        (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
        (scoreCovMat μ Z e)
        (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X))))
    (hseθ : 0 <
      linearRestrictionStdError R
        (twoSLSAsymptoticVariance
          (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
          (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
          (scoreCovMat μ Z e)
          (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))))
    (hT_meas : ∀ n ω,
      Measurable
        (fun ωs => twoSLSBootstrapLinearRestrictionStatisticFinSucc R Z X Y n ω ωs))
    (hse_meas : ∀ n ω,
      Measurable
        (fun ωs =>
          twoSLSBootstrapRobustLinearRestrictionStdErrorFinSucc R Z X Y n ω ωs))
    (hTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set (ℝ × ℝ), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω =>
            (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω) n ω).real
              {ωs |
                (twoSLSBootstrapLinearRestrictionStatisticFinSucc R Z X Y n ω ωs,
                  linearRestrictionStdError R
                    (twoSLSAsymptoticVariance
                      (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
                      (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
                      (scoreCovMat μ Z e)
                      (twoSLSCombinedQZX
                        (popGram μ (twoSLSCombinedRegressors Z X))))) ∉ K})
          atTop (fun _ => 0) ∧
        TendstoInMeasure μ
          (fun n ω =>
            (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω) n ω).real
              {ωs |
                (twoSLSBootstrapLinearRestrictionStatisticFinSucc R Z X Y n ω ωs,
                  twoSLSBootstrapRobustLinearRestrictionStdErrorFinSucc
                    R Z X Y n ω ωs) ∉ K})
          atTop (fun _ => 0))
    (hV_resample_close :
      TendstoInBootstrapProbabilityIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs =>
          twoSLSBootstrapVHatStarFinSucc Z X Y n ω ωs -
            twoSLSVHatStar
              (stackRegressors Z (n + 1) ω) (stackRegressors X (n + 1) ω)
              (stackOutcomes Y (n + 1) ω))
        (fun _ => 0)) :
    TendstoInBootstrapDistributionIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs => twoSLSBootstrapBetaGapFinSucc Z X Y n ω ωs)
        (multivariateGaussian (0 : EuclideanSpace ℝ k)
          (twoSLSAsymptoticVariance
            (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (scoreCovMat μ Z e)
            (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))))
        (fun z : EuclideanSpace ℝ k => (z : k → ℝ)) ∧
      TendstoInBootstrapDistributionIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs (_ : Unit) =>
          twoSLSBootstrapRobustLinearTStatFinSucc R Z X Y n ω ωs)
        (gaussianReal 0 1) (fun z : ℝ => fun _ : Unit => z) :=
  twoSLSBootstrap_theorem12_8_of_assumption12_2_weight_wlln
    (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y) (R := R)
    h β hmodel hw
    (twoSLSBootstrapFormulaAsymptoticNormalConditions_of_score_clt_inputs
      (μ := μ) (Pstar := twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
      (Z := Z) (X := X) (Y := Y)
      (QXZ := twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
      (QZZ := twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
      (Omega := scoreCovMat μ Z e)
      (QZX := twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))
      hcoef)
    hseθ hT_meas hse_meas hTail hV_resample_close

/-- Hansen Theorem 12.8 with the tightened theorem-facing input surface.

Assumption 12.2 supplies the true-score ordinary-bootstrap CLT, covariance
positivity, and population block identities. The remaining inputs are the
concrete residual-substitution statistic, the coefficient linearization
replacement, and the named robust covariance resampling condition. -/
theorem
    twoSLSBootstrap_theorem12_8_of_assumption12_2_weight_wlln_residualSubstitution_linearization
    [IsProbabilityMeasure μ]
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {R : Matrix Unit k ℝ}
    (h : TwoSLSAssumption12_2IidFourthConditions μ Z X e)
    (β : k → ℝ)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hw : TwoSLSCovarianceWeightWLLNConditions μ Z X e)
    (hresid : TwoSLSBootstrapResidualSubstitutionInputs μ Z X Y e β)
    (hlin : TwoSLSBootstrapCoefficientLinearizationInputs μ
      (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω)) Z X Y
      (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
      (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
      (scoreCovMat μ Z e)
      (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X))))
    (hseθ : 0 <
      linearRestrictionStdError R
        (twoSLSAsymptoticVariance
          (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
          (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
          (scoreCovMat μ Z e)
          (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))))
    (hT_meas : ∀ n ω,
      Measurable
        (fun ωs => twoSLSBootstrapLinearRestrictionStatisticFinSucc R Z X Y n ω ωs))
    (hse_meas : ∀ n ω,
      Measurable
        (fun ωs =>
          twoSLSBootstrapRobustLinearRestrictionStdErrorFinSucc R Z X Y n ω ωs))
    (hTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set (ℝ × ℝ), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω =>
            (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω) n ω).real
              {ωs |
                (twoSLSBootstrapLinearRestrictionStatisticFinSucc R Z X Y n ω ωs,
                  linearRestrictionStdError R
                    (twoSLSAsymptoticVariance
                      (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
                      (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
                      (scoreCovMat μ Z e)
                      (twoSLSCombinedQZX
                        (popGram μ (twoSLSCombinedRegressors Z X))))) ∉ K})
          atTop (fun _ => 0) ∧
        TendstoInMeasure μ
          (fun n ω =>
            (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω) n ω).real
              {ωs |
                (twoSLSBootstrapLinearRestrictionStatisticFinSucc R Z X Y n ω ωs,
                  twoSLSBootstrapRobustLinearRestrictionStdErrorFinSucc
                    R Z X Y n ω ωs) ∉ K})
          atTop (fun _ => 0))
    (hV : TwoSLSBootstrapRobustCovarianceResampleCloseness μ Z X Y) :
    TendstoInBootstrapDistributionIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs => twoSLSBootstrapBetaGapFinSucc Z X Y n ω ωs)
        (multivariateGaussian (0 : EuclideanSpace ℝ k)
          (twoSLSAsymptoticVariance
            (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (scoreCovMat μ Z e)
            (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))))
        (fun z : EuclideanSpace ℝ k => (z : k → ℝ)) ∧
      TendstoInBootstrapDistributionIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs (_ : Unit) =>
          twoSLSBootstrapRobustLinearTStatFinSucc R Z X Y n ω ωs)
        (gaussianReal 0 1) (fun z : ℝ => fun _ : Unit => z) :=
  twoSLSBootstrap_theorem12_8_of_assumption12_2_weight_wlln
    (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y) (R := R)
    h β hmodel hw
    (twoSLSBootstrapFormulaAsymptoticNormalConditions_uniform_of_assumption12_2_residualSubstitution_linearization
      (μ := μ) (Z := Z) (X := X) (Y := Y) (e := e)
      h hmodel hresid hlin)
    hseθ hT_meas hse_meas hTail hV.covariance_closeness

/-- Hansen Theorem 12.8 with only named theorem-facing bootstrap input
packages left on the coefficient and robust t-ratio sides. -/
theorem
    twoSLSBootstrap_theorem12_8_of_assumption12_2_weight_wlln_residualSubstitution_linearization_studentization
    [IsProbabilityMeasure μ]
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {R : Matrix Unit k ℝ}
    (h : TwoSLSAssumption12_2IidFourthConditions μ Z X e)
    (β : k → ℝ)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hw : TwoSLSCovarianceWeightWLLNConditions μ Z X e)
    (hresid : TwoSLSBootstrapResidualSubstitutionInputs μ Z X Y e β)
    (hlin : TwoSLSBootstrapCoefficientLinearizationInputs μ
      (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω)) Z X Y
      (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
      (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
      (scoreCovMat μ Z e)
      (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X))))
    (hstudent :
      TwoSLSBootstrapRobustStudentizationInputs μ Z X Y R
        (twoSLSAsymptoticVariance
          (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
          (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
          (scoreCovMat μ Z e)
          (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))))
    (hV : TwoSLSBootstrapRobustCovarianceResampleCloseness μ Z X Y) :
    TendstoInBootstrapDistributionIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs => twoSLSBootstrapBetaGapFinSucc Z X Y n ω ωs)
        (multivariateGaussian (0 : EuclideanSpace ℝ k)
          (twoSLSAsymptoticVariance
            (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (scoreCovMat μ Z e)
            (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))))
        (fun z : EuclideanSpace ℝ k => (z : k → ℝ)) ∧
      TendstoInBootstrapDistributionIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs (_ : Unit) =>
          twoSLSBootstrapRobustLinearTStatFinSucc R Z X Y n ω ωs)
        (gaussianReal 0 1) (fun z : ℝ => fun _ : Unit => z) :=
  twoSLSBootstrap_theorem12_8_of_assumption12_2_weight_wlln_residualSubstitution_linearization
    (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y) (R := R)
    h β hmodel hw hresid hlin hstudent.limit_se_pos
    (by
      intro n ω
      fun_prop)
    (by
      intro n ω
      fun_prop)
    hstudent.joint_tail hV

set_option linter.style.longLine false in
/-- Hansen Theorem 12.8 with covariance-form restriction nondegeneracy.

This is the theorem-facing wrapper whose robust studentization hypothesis is
the positive definiteness of `R Vβ R'`, where `Vβ` is Hansen's 2SLS asymptotic
variance formula. The remaining named input packages are the residual-score
substitution, coefficient linearization, joint numerator/standard-error tail,
and robust covariance resampling conditions. -/
theorem
    twoSLSBootstrap_theorem12_8_of_assumption12_2_weight_wlln_residualSubstitution_linearization_restrictionCov_resampleCloseness
    [IsProbabilityMeasure μ]
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {R : Matrix Unit k ℝ}
    (h : TwoSLSAssumption12_2IidFourthConditions μ Z X e)
    (β : k → ℝ)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hw : TwoSLSCovarianceWeightWLLNConditions μ Z X e)
    (hresid : TwoSLSBootstrapResidualSubstitutionInputs μ Z X Y e β)
    (hlin : TwoSLSBootstrapCoefficientLinearizationInputs μ
      (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω)) Z X Y
      (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
      (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
      (scoreCovMat μ Z e)
      (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X))))
    (hVθ :
      (R *
          twoSLSAsymptoticVariance
            (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (scoreCovMat μ Z e)
            (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X))) *
        Rᵀ).PosDef)
    (hTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set (ℝ × ℝ), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω =>
            (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω) n ω).real
              {ωs |
                (twoSLSBootstrapLinearRestrictionStatisticFinSucc R Z X Y n ω ωs,
                  linearRestrictionStdError R
                    (twoSLSAsymptoticVariance
                      (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
                      (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
                      (scoreCovMat μ Z e)
                      (twoSLSCombinedQZX
                        (popGram μ (twoSLSCombinedRegressors Z X))))) ∉ K})
          atTop (fun _ => 0) ∧
        TendstoInMeasure μ
          (fun n ω =>
            (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω) n ω).real
              {ωs |
                (twoSLSBootstrapLinearRestrictionStatisticFinSucc R Z X Y n ω ωs,
                  twoSLSBootstrapRobustLinearRestrictionStdErrorFinSucc
                    R Z X Y n ω ωs) ∉ K})
          atTop (fun _ => 0))
    (hV : TwoSLSBootstrapRobustCovarianceResampleCloseness μ Z X Y) :
    TendstoInBootstrapDistributionIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs => twoSLSBootstrapBetaGapFinSucc Z X Y n ω ωs)
        (multivariateGaussian (0 : EuclideanSpace ℝ k)
          (twoSLSAsymptoticVariance
            (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (scoreCovMat μ Z e)
            (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))))
        (fun z : EuclideanSpace ℝ k => (z : k → ℝ)) ∧
      TendstoInBootstrapDistributionIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs (_ : Unit) =>
          twoSLSBootstrapRobustLinearTStatFinSucc R Z X Y n ω ωs)
        (gaussianReal 0 1) (fun z : ℝ => fun _ : Unit => z) :=
  twoSLSBootstrap_theorem12_8_of_assumption12_2_weight_wlln_residualSubstitution_linearization_studentization
    (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y) (R := R)
    h β hmodel hw hresid hlin
    (TwoSLSBootstrapRobustStudentizationInputs.of_restrictionCov_posDef
      (μ := μ) (Z := Z) (X := X) (Y := Y) (R := R)
      (Vβ :=
        twoSLSAsymptoticVariance
          (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
          (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
          (scoreCovMat μ Z e)
          (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X))))
      hVθ hTail)
    hV

set_option linter.style.longLine false in
/-- Hansen Theorem 12.8 with full-rank one-row restriction nondegeneracy.

This is the current tightest iid/weight-WLLN theorem-facing route in this file.
Compared with
`twoSLSBootstrap_theorem12_8_of_assumption12_2_weight_wlln_residualSubstitution_linearization_studentization`,
it does not ask for a separate studentization package. Assumption 12.2 and
full rank of `Rᵀ.mulVec` give restriction nondegeneracy; coefficient
linearization supplies the scalar numerator compact tail; and robust covariance
resampling plus the Chapter 12 covariance WLLN supplies the bootstrap standard
error consistency. -/
theorem
    twoSLSBootstrap_theorem12_8_of_assumption12_2_weight_wlln_residualSubstitution_linearization_fullRank_resampleCloseness
    [IsProbabilityMeasure μ]
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {R : Matrix Unit k ℝ}
    (h : TwoSLSAssumption12_2IidFourthConditions μ Z X e)
    (β : k → ℝ)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hw : TwoSLSCovarianceWeightWLLNConditions μ Z X e)
    (hresid : TwoSLSBootstrapResidualSubstitutionInputs μ Z X Y e β)
    (hlin : TwoSLSBootstrapCoefficientLinearizationInputs μ
      (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω)) Z X Y
      (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
      (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
      (scoreCovMat μ Z e)
      (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X))))
    (hR : Function.Injective Rᵀ.mulVec)
    (hV : TwoSLSBootstrapRobustCovarianceResampleCloseness μ Z X Y) :
    TendstoInBootstrapDistributionIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs => twoSLSBootstrapBetaGapFinSucc Z X Y n ω ωs)
        (multivariateGaussian (0 : EuclideanSpace ℝ k)
          (twoSLSAsymptoticVariance
            (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (scoreCovMat μ Z e)
            (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))))
        (fun z : EuclideanSpace ℝ k => (z : k → ℝ)) ∧
      TendstoInBootstrapDistributionIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs (_ : Unit) =>
          twoSLSBootstrapRobustLinearTStatFinSucc R Z X Y n ω ωs)
        (gaussianReal 0 1) (fun z : ℝ => fun _ : Unit => z) := by
  have hstudent :
      TwoSLSBootstrapRobustStudentizationInputs μ Z X Y R
        (twoSLSAsymptoticVariance
          (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
          (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
          (scoreCovMat μ Z e)
          (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))) :=
    TwoSLSBootstrapRobustStudentizationInputs.of_assumption12_2_weight_wlln_coefficientLinearization_resampleCloseness
      (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y) (R := R)
      h β hmodel hw hlin hR hV
  exact
    twoSLSBootstrap_theorem12_8_of_assumption12_2_weight_wlln_residualSubstitution_linearization_studentization
      (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y) (R := R)
      h β hmodel hw hresid hlin hstudent hV

set_option linter.style.longLine false in
/-- Hansen Theorem 12.8 with the currently narrowest coefficient/bootstrap
empirical-process inputs on the iid weight-WLLN route.

Compared with
`twoSLSBootstrap_theorem12_8_of_assumption12_2_weight_wlln_residualSubstitution_linearization_fullRank_resampleCloseness`,
this theorem does not ask callers to build the full feasible residual-score
package or the full coefficient-linearization package. It derives them from
centered residual-substitution negligibility, true-score compact-tail control,
and the two coefficient-closeness fields. -/
theorem
    twoSLSBootstrap_theorem12_8_of_assumption12_2_weight_wlln_residualSubstitutionNegligibility_trueScoreTail_closeness_fullRank_resampleCloseness
    [IsProbabilityMeasure μ]
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {R : Matrix Unit k ℝ}
    (h : TwoSLSAssumption12_2IidFourthConditions μ Z X e)
    (β : k → ℝ)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hw : TwoSLSCovarianceWeightWLLNConditions μ Z X e)
    (hresid :
      TwoSLSBootstrapResidualSubstitutionNegligibilityInputs μ Z X Y β)
    (hTrueTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set (EuclideanSpace ℝ l), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω =>
            (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω) n ω).real
              {ωs |
                twoSLSBootstrapTrueRecenteredScoreStatisticFinSucc
                  Z e n ω ωs ∉ K})
          atTop (fun _ => 0))
    (hcoef :
      TwoSLSBootstrapCoefficientLinearizationClosenessInputs μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω)) Z X Y
        (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
        (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
        (scoreCovMat μ Z e)
        (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X))))
    (hR : Function.Injective Rᵀ.mulVec)
    (hV : TwoSLSBootstrapRobustCovarianceResampleCloseness μ Z X Y) :
    TendstoInBootstrapDistributionIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs => twoSLSBootstrapBetaGapFinSucc Z X Y n ω ωs)
        (multivariateGaussian (0 : EuclideanSpace ℝ k)
          (twoSLSAsymptoticVariance
            (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (scoreCovMat μ Z e)
            (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))))
        (fun z : EuclideanSpace ℝ k => (z : k → ℝ)) ∧
      TendstoInBootstrapDistributionIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs (_ : Unit) =>
          twoSLSBootstrapRobustLinearTStatFinSucc R Z X Y n ω ωs)
        (gaussianReal 0 1) (fun z : ℝ => fun _ : Unit => z) := by
  let hresidFull :
      TwoSLSBootstrapResidualSubstitutionInputs μ Z X Y e β :=
    hresid.toResidualSubstitutionInputs_of_trueScore_compactTail
      (μ := μ) (Z := Z) (X := X) (Y := Y) (e := e) (β := β)
      hmodel hTrueTail
  let hlinPrimitive :
      TwoSLSBootstrapCoefficientLinearizationPrimitiveInputs μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω)) Z X Y
        (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
        (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
        (scoreCovMat μ Z e)
        (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X))) :=
    hcoef.toPrimitiveInputs_of_residualSubstitution_trueScoreTail
      (μ := μ) (Z := Z) (X := X) (Y := Y) (e := e) (β := β)
      (QXZ := twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
      (QZZ := twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
      (Omega := scoreCovMat μ Z e)
      (QZX := twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))
      hmodel hresid hTrueTail
  let hlin :
      TwoSLSBootstrapCoefficientLinearizationInputs μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω)) Z X Y
        (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
        (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
        (scoreCovMat μ Z e)
        (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X))) :=
    hlinPrimitive.toCoefficientLinearizationInputs
      (μ := μ)
      (Pstar := twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
      (Z := Z) (X := X) (Y := Y)
      (QXZ := twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
      (QZZ := twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
      (Omega := scoreCovMat μ Z e)
      (QZX := twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))
      (fun n ω =>
        twoSLSBootstrapUniformPstarFinSucc_isProbabilityMeasure (Ω := Ω) n ω)
  exact
    twoSLSBootstrap_theorem12_8_of_assumption12_2_weight_wlln_residualSubstitution_linearization_fullRank_resampleCloseness
      (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y) (R := R)
      h β hmodel hw hresidFull hlin hR hV

set_option linter.style.longLine false in
/-- Hansen Theorem 12.8 with the current narrowest iid/weight-WLLN
empirical-process boundary.

Compared with
`twoSLSBootstrap_theorem12_8_of_assumption12_2_weight_wlln_residualSubstitutionNegligibility_trueScoreTail_closeness_fullRank_resampleCloseness`,
this wrapper keeps robust covariance resampling at the primitive norm-tail
level.  The theorem derives the named resample-closeness package internally,
so callers only provide the concrete covariance-resampling empirical-process
tail. -/
theorem
    twoSLSBootstrap_theorem12_8_of_assumption12_2_weight_wlln_residualSubstitutionNegligibility_trueScoreTail_closeness_fullRank_resamplePrimitive
    [IsProbabilityMeasure μ]
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {R : Matrix Unit k ℝ}
    (h : TwoSLSAssumption12_2IidFourthConditions μ Z X e)
    (β : k → ℝ)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hw : TwoSLSCovarianceWeightWLLNConditions μ Z X e)
    (hresid :
      TwoSLSBootstrapResidualSubstitutionNegligibilityInputs μ Z X Y β)
    (hTrueTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set (EuclideanSpace ℝ l), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω =>
            (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω) n ω).real
              {ωs |
                twoSLSBootstrapTrueRecenteredScoreStatisticFinSucc
                  Z e n ω ωs ∉ K})
          atTop (fun _ => 0))
    (hcoef :
      TwoSLSBootstrapCoefficientLinearizationClosenessInputs μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω)) Z X Y
        (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
        (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
        (scoreCovMat μ Z e)
        (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X))))
    (hR : Function.Injective Rᵀ.mulVec)
    (hV : TwoSLSBootstrapRobustCovarianceResamplePrimitiveInputs μ Z X Y) :
    TendstoInBootstrapDistributionIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs => twoSLSBootstrapBetaGapFinSucc Z X Y n ω ωs)
        (multivariateGaussian (0 : EuclideanSpace ℝ k)
          (twoSLSAsymptoticVariance
            (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (scoreCovMat μ Z e)
            (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))))
        (fun z : EuclideanSpace ℝ k => (z : k → ℝ)) ∧
      TendstoInBootstrapDistributionIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs (_ : Unit) =>
          twoSLSBootstrapRobustLinearTStatFinSucc R Z X Y n ω ωs)
        (gaussianReal 0 1) (fun z : ℝ => fun _ : Unit => z) :=
  twoSLSBootstrap_theorem12_8_of_assumption12_2_weight_wlln_residualSubstitutionNegligibility_trueScoreTail_closeness_fullRank_resampleCloseness
    (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y) (R := R)
    h β hmodel hw hresid hTrueTail hcoef hR
    (hV.toResampleCloseness
      (μ := μ) (Z := Z) (X := X) (Y := Y))

set_option linter.style.longLine false in
/-- Primitive bootstrap empirical-process inputs left for Hansen Theorem 12.8.

This package deliberately contains only the bootstrap-specific pieces not
derived from Assumption 12.2 by the wrappers below: residual-score
substitution negligibility, true-score bootstrap tightness, replacement of the
population linearized statistic by the feasible coefficient statistic, and
resampled robust-covariance stability. The feasible residual-score tightness is
derived from the true-score tail and residual-substitution negligibility under
the structural equation. The package does not include covariance weight WLLNs,
standard-error positivity, measurability, scalar numerator tightness,
studentization joint-tail control, or Gaussian frontier-null conditions; those
are derived by existing Chapter 10/12 wrappers. -/
structure TwoSLSBootstrapTheorem12_8EmpiricalProcessInputs
    (μ : Measure Ω)
    (Z : ℕ → Ω → l → ℝ) (X : ℕ → Ω → k → ℝ)
    (Y e : ℕ → Ω → ℝ) (β : k → ℝ)
    (R : Matrix Unit k ℝ) : Prop where
  residual_negligibility :
    TwoSLSBootstrapResidualSubstitutionNegligibilityInputs μ Z X Y β
  true_score_tail : ∀ η : ℝ, 0 < η →
    ∃ K : Set (EuclideanSpace ℝ l), IsCompact K ∧
      TendstoInMeasure μ
        (fun n ω =>
          (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω) n ω).real
            {ωs |
              twoSLSBootstrapTrueRecenteredScoreStatisticFinSucc
                Z e n ω ωs ∉ K})
        atTop (fun _ => 0)
  coefficient_linearization :
    TwoSLSBootstrapCoefficientLinearizationInputs μ
      (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω)) Z X Y
      (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
      (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
      (scoreCovMat μ Z e)
      (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))
  covariance_resample :
    TwoSLSBootstrapRobustCovarianceResampleCloseness μ Z X Y

set_option linter.style.longLine false in
/-- Build the primitive empirical-process package for Hansen Theorem 12.8 from
the stronger residual-substitution package already used by the coefficient
bootstrap route.

This closes a packaging gap only: it does not replace the residual-substitution,
coefficient-linearization, or covariance-resampling stochastic arguments by an
assumed conclusion.  It lets theorem-facing callers provide the established
`TwoSLSBootstrapResidualSubstitutionInputs` package directly, rather than
splitting it back into residual-substitution negligibility and score-tail
fields by hand. -/
theorem
    TwoSLSBootstrapTheorem12_8EmpiricalProcessInputs.of_residualSubstitution_linearization_resampleCloseness
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {Y e : ℕ → Ω → ℝ} {β : k → ℝ} {R : Matrix Unit k ℝ}
    (hresid : TwoSLSBootstrapResidualSubstitutionInputs μ Z X Y e β)
    (hlin : TwoSLSBootstrapCoefficientLinearizationInputs μ
      (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω)) Z X Y
      (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
      (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
      (scoreCovMat μ Z e)
      (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X))))
    (hV : TwoSLSBootstrapRobustCovarianceResampleCloseness μ Z X Y) :
    TwoSLSBootstrapTheorem12_8EmpiricalProcessInputs μ Z X Y e β R where
  residual_negligibility :=
    { residual_substitution_negligible :=
        hresid.residual_substitution_negligible }
  true_score_tail := by
    intro η hη
    rcases hresid.compact_tail η hη with ⟨K, hK, hTrue, _hActual⟩
    exact ⟨K, hK, hTrue⟩
  coefficient_linearization := hlin
  covariance_resample := hV

set_option linter.style.longLine false in
/-- Build the primitive empirical-process package for Hansen Theorem 12.8 from
the now minimal residual-score inputs.

This constructor is the direct theorem-facing surface after the tightness
transfer: callers supply true-score compact-tail control and the centered
residual-substitution negligibility statement, while feasible residual-score
compact-tail control is derived later from the structural equation. -/
theorem
    TwoSLSBootstrapTheorem12_8EmpiricalProcessInputs.of_residualSubstitutionNegligibility_trueScoreTail_linearization_resampleCloseness
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {Y e : ℕ → Ω → ℝ} {β : k → ℝ} {R : Matrix Unit k ℝ}
    (hresid :
      TwoSLSBootstrapResidualSubstitutionNegligibilityInputs μ Z X Y β)
    (hTrueTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set (EuclideanSpace ℝ l), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω =>
            (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω) n ω).real
              {ωs |
                twoSLSBootstrapTrueRecenteredScoreStatisticFinSucc
                  Z e n ω ωs ∉ K})
          atTop (fun _ => 0))
    (hlin : TwoSLSBootstrapCoefficientLinearizationInputs μ
      (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω)) Z X Y
      (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
      (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
      (scoreCovMat μ Z e)
      (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X))))
    (hV : TwoSLSBootstrapRobustCovarianceResampleCloseness μ Z X Y) :
    TwoSLSBootstrapTheorem12_8EmpiricalProcessInputs μ Z X Y e β R where
  residual_negligibility := hresid
  true_score_tail := hTrueTail
  coefficient_linearization := hlin
  covariance_resample := hV

set_option linter.style.longLine false in
/-- Build the Hansen Theorem 12.8 empirical-process package from direct
bootstrap robust-covariance consistency under the named mixed-moment
Assumption 12.2 surface.

The mixed-moment package supplies the original-sample robust covariance limit
through the existing Chapter 12 covariance WLLN route.  The direct bootstrap
premise `hV_boot` is therefore enough to derive the named
`covariance_resample` field, so theorem-facing callers no longer have to
construct `TwoSLSBootstrapRobustCovarianceResampleCloseness` by hand on this
route. -/
theorem
    TwoSLSBootstrapTheorem12_8EmpiricalProcessInputs.of_mixed_moment_conditions_residualSubstitution_linearization_bootstrapCovarianceConsistency
    [IsProbabilityMeasure μ]
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {Y e : ℕ → Ω → ℝ} {β : k → ℝ} {R : Matrix Unit k ℝ}
    (h : TwoSLSAssumption12_2JointIidMixedMomentConditions μ Z X e)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hresid : TwoSLSBootstrapResidualSubstitutionInputs μ Z X Y e β)
    (hlin : TwoSLSBootstrapCoefficientLinearizationInputs μ
      (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω)) Z X Y
      (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
      (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
      (scoreCovMat μ Z e)
      (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X))))
    (hV_boot :
      TendstoInBootstrapProbabilityIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs => twoSLSBootstrapVHatStarFinSucc Z X Y n ω ωs)
        (fun _ =>
          twoSLSAsymptoticVariance
            (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (scoreCovMat μ Z e)
            (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X))))) :
    TwoSLSBootstrapTheorem12_8EmpiricalProcessInputs μ Z X Y e β R :=
  TwoSLSBootstrapTheorem12_8EmpiricalProcessInputs.of_residualSubstitution_linearization_resampleCloseness
    (μ := μ) (Z := Z) (X := X) (Y := Y) (e := e) (β := β)
    (R := R) hresid hlin
    (TwoSLSBootstrapRobustCovarianceResampleCloseness.of_mixed_moment_conditions_bootstrap_consistency
      (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y)
      h β hmodel hV_boot)

set_option linter.style.longLine false in
/-- Literal finite-fourth Assumption 12.2 version of
`TwoSLSBootstrapTheorem12_8EmpiricalProcessInputs.of_mixed_moment_conditions_residualSubstitution_linearization_bootstrapCovarianceConsistency`.

Hansen's textbook fourth-moment package derives the mixed-moment covariance
WLLNs, while the direct bootstrap covariance consistency premise supplies the
remaining bootstrap covariance input. -/
theorem
    TwoSLSBootstrapTheorem12_8EmpiricalProcessInputs.of_textbook_fourth_residualSubstitution_linearization_bootstrapCovarianceConsistency
    [IsProbabilityMeasure μ]
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {Y e : ℕ → Ω → ℝ} {β : k → ℝ} {R : Matrix Unit k ℝ}
    (h : TwoSLSAssumption12_2JointIidTextbookFourthConditions μ Z X e Y β)
    (hresid : TwoSLSBootstrapResidualSubstitutionInputs μ Z X Y e β)
    (hlin : TwoSLSBootstrapCoefficientLinearizationInputs μ
      (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω)) Z X Y
      (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
      (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
      (scoreCovMat μ Z e)
      (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X))))
    (hV_boot :
      TendstoInBootstrapProbabilityIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs => twoSLSBootstrapVHatStarFinSucc Z X Y n ω ωs)
        (fun _ =>
          twoSLSAsymptoticVariance
            (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (scoreCovMat μ Z e)
            (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X))))) :
    TwoSLSBootstrapTheorem12_8EmpiricalProcessInputs μ Z X Y e β R :=
  TwoSLSBootstrapTheorem12_8EmpiricalProcessInputs.of_mixed_moment_conditions_residualSubstitution_linearization_bootstrapCovarianceConsistency
    (μ := μ) (Z := Z) (X := X) (Y := Y) (e := e) (β := β)
    (R := R) h.toJointIidMixedMomentConditions h.model hresid hlin hV_boot

set_option linter.style.longLine false in
/-- Build the minimal Hansen Theorem 12.8 empirical-process package from
direct bootstrap robust-covariance consistency under the named mixed-moment
Assumption 12.2 surface.

Compared with
`TwoSLSBootstrapTheorem12_8EmpiricalProcessInputs.of_mixed_moment_conditions_residualSubstitution_linearization_bootstrapCovarianceConsistency`,
this constructor also keeps coefficient linearization at the closeness layer:
true-score compact-tail control and residual-substitution negligibility derive
the population-linearized compact-tail field internally, while direct
consistency of `twoSLSBootstrapVHatStarFinSucc` supplies the robust covariance
resampling field. -/
theorem
    TwoSLSBootstrapTheorem12_8EmpiricalProcessInputs.of_mixed_moment_conditions_residualSubstitutionNegligibility_trueScoreTail_closeness_bootstrapCovarianceConsistency
    [IsProbabilityMeasure μ]
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {Y e : ℕ → Ω → ℝ} {β : k → ℝ} {R : Matrix Unit k ℝ}
    (h : TwoSLSAssumption12_2JointIidMixedMomentConditions μ Z X e)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hresid :
      TwoSLSBootstrapResidualSubstitutionNegligibilityInputs μ Z X Y β)
    (hTrueTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set (EuclideanSpace ℝ l), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω =>
            (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω) n ω).real
              {ωs |
                twoSLSBootstrapTrueRecenteredScoreStatisticFinSucc
                  Z e n ω ωs ∉ K})
          atTop (fun _ => 0))
    (hcoef :
      TwoSLSBootstrapCoefficientLinearizationClosenessInputs μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω)) Z X Y
        (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
        (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
        (scoreCovMat μ Z e)
        (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X))))
    (hV_boot :
      TendstoInBootstrapProbabilityIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs => twoSLSBootstrapVHatStarFinSucc Z X Y n ω ωs)
        (fun _ =>
          twoSLSAsymptoticVariance
            (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (scoreCovMat μ Z e)
            (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X))))) :
    TwoSLSBootstrapTheorem12_8EmpiricalProcessInputs μ Z X Y e β R where
  residual_negligibility := hresid
  true_score_tail := hTrueTail
  coefficient_linearization := by
    let hcoefPrim :
        TwoSLSBootstrapCoefficientLinearizationPrimitiveInputs μ
          (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω)) Z X Y
          (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
          (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
          (scoreCovMat μ Z e)
          (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X))) :=
      hcoef.toPrimitiveInputs_of_residualSubstitution_trueScoreTail
        (μ := μ) (Z := Z) (X := X) (Y := Y) (e := e) (β := β)
        (QXZ := twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
        (QZZ := twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
        (Omega := scoreCovMat μ Z e)
        (QZX := twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))
        hmodel hresid hTrueTail
    exact
      hcoefPrim.toCoefficientLinearizationInputs
        (μ := μ)
        (Pstar := twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (Z := Z) (X := X) (Y := Y)
        (QXZ := twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
        (QZZ := twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
        (Omega := scoreCovMat μ Z e)
        (QZX := twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))
        (fun n ω =>
          twoSLSBootstrapUniformPstarFinSucc_isProbabilityMeasure (Ω := Ω) n ω)
  covariance_resample :=
    TwoSLSBootstrapRobustCovarianceResampleCloseness.of_mixed_moment_conditions_bootstrap_consistency
      (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y)
      h β hmodel hV_boot

set_option linter.style.longLine false in
/-- Literal finite-fourth Assumption 12.2 version of
`TwoSLSBootstrapTheorem12_8EmpiricalProcessInputs.of_mixed_moment_conditions_residualSubstitutionNegligibility_trueScoreTail_closeness_bootstrapCovarianceConsistency`. -/
theorem
    TwoSLSBootstrapTheorem12_8EmpiricalProcessInputs.of_textbook_fourth_residualSubstitutionNegligibility_trueScoreTail_closeness_bootstrapCovarianceConsistency
    [IsProbabilityMeasure μ]
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {Y e : ℕ → Ω → ℝ} {β : k → ℝ} {R : Matrix Unit k ℝ}
    (h : TwoSLSAssumption12_2JointIidTextbookFourthConditions μ Z X e Y β)
    (hresid :
      TwoSLSBootstrapResidualSubstitutionNegligibilityInputs μ Z X Y β)
    (hTrueTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set (EuclideanSpace ℝ l), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω =>
            (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω) n ω).real
              {ωs |
                twoSLSBootstrapTrueRecenteredScoreStatisticFinSucc
                  Z e n ω ωs ∉ K})
          atTop (fun _ => 0))
    (hcoef :
      TwoSLSBootstrapCoefficientLinearizationClosenessInputs μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω)) Z X Y
        (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
        (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
        (scoreCovMat μ Z e)
        (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X))))
    (hV_boot :
      TendstoInBootstrapProbabilityIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs => twoSLSBootstrapVHatStarFinSucc Z X Y n ω ωs)
        (fun _ =>
          twoSLSAsymptoticVariance
            (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (scoreCovMat μ Z e)
            (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X))))) :
    TwoSLSBootstrapTheorem12_8EmpiricalProcessInputs μ Z X Y e β R :=
  TwoSLSBootstrapTheorem12_8EmpiricalProcessInputs.of_mixed_moment_conditions_residualSubstitutionNegligibility_trueScoreTail_closeness_bootstrapCovarianceConsistency
    (μ := μ) (Z := Z) (X := X) (Y := Y) (e := e) (β := β)
    (R := R) h.toJointIidMixedMomentConditions h.model
    hresid hTrueTail hcoef hV_boot

set_option linter.style.longLine false in
/-- Primitive empirical-process input surface for Hansen Theorem 12.8.

Compared with `TwoSLSBootstrapTheorem12_8EmpiricalProcessInputs`, this package
keeps coefficient linearization and covariance resampling at their primitive
tail/closeness level. The conversion theorem below derives the established
residual-substitution, coefficient-linearization, studentization, and robust
covariance packages used by the public Theorem 12.8 wrappers. -/
structure TwoSLSBootstrapTheorem12_8PrimitiveEmpiricalProcessInputs
    (μ : Measure Ω)
    (Z : ℕ → Ω → l → ℝ) (X : ℕ → Ω → k → ℝ)
    (Y e : ℕ → Ω → ℝ) (β : k → ℝ)
    (R : Matrix Unit k ℝ) : Prop where
  residual_negligibility :
    TwoSLSBootstrapResidualSubstitutionNegligibilityInputs μ Z X Y β
  true_score_tail : ∀ η : ℝ, 0 < η →
    ∃ K : Set (EuclideanSpace ℝ l), IsCompact K ∧
      TendstoInMeasure μ
        (fun n ω =>
          (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω) n ω).real
            {ωs |
              twoSLSBootstrapTrueRecenteredScoreStatisticFinSucc
                Z e n ω ωs ∉ K})
        atTop (fun _ => 0)
  coefficient_linearization :
    TwoSLSBootstrapCoefficientLinearizationPrimitiveInputs μ
      (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω)) Z X Y
      (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
      (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
      (scoreCovMat μ Z e)
      (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))
  covariance_resample :
    TwoSLSBootstrapRobustCovarianceResamplePrimitiveInputs μ Z X Y

namespace TwoSLSBootstrapTheorem12_8PrimitiveEmpiricalProcessInputs

set_option linter.style.longLine false in
/-- Convert the primitive empirical-process package into the established
Theorem 12.8 empirical-process package. -/
theorem toEmpiricalProcessInputs
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {Y e : ℕ → Ω → ℝ} {β : k → ℝ} {R : Matrix Unit k ℝ}
    (h :
      TwoSLSBootstrapTheorem12_8PrimitiveEmpiricalProcessInputs
        μ Z X Y e β R) :
    TwoSLSBootstrapTheorem12_8EmpiricalProcessInputs
      μ Z X Y e β R where
  residual_negligibility := h.residual_negligibility
  true_score_tail := h.true_score_tail
  coefficient_linearization :=
    h.coefficient_linearization.toCoefficientLinearizationInputs
      (μ := μ)
      (Pstar := twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
      (Z := Z) (X := X) (Y := Y)
      (QXZ := twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
      (QZZ := twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
      (Omega := scoreCovMat μ Z e)
      (QZX := twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))
      (fun n ω =>
        twoSLSBootstrapUniformPstarFinSucc_isProbabilityMeasure (Ω := Ω) n ω)
  covariance_resample :=
    h.covariance_resample.toResampleCloseness
      (μ := μ) (Z := Z) (X := X) (Y := Y)

end TwoSLSBootstrapTheorem12_8PrimitiveEmpiricalProcessInputs

set_option linter.style.longLine false in
/-- Score-tail primitive empirical-process input surface for Hansen
Theorem 12.8.

Compared with `TwoSLSBootstrapTheorem12_8PrimitiveEmpiricalProcessInputs`, this
package removes the population-linearized coefficient compact-tail field.
That tail is derived from true-score tightness and residual-substitution
negligibility, then pushed through the fixed population linearization map. -/
structure TwoSLSBootstrapTheorem12_8ScoreTailPrimitiveEmpiricalProcessInputs
    (μ : Measure Ω)
    (Z : ℕ → Ω → l → ℝ) (X : ℕ → Ω → k → ℝ)
    (Y e : ℕ → Ω → ℝ) (β : k → ℝ)
    (R : Matrix Unit k ℝ) : Prop where
  residual_negligibility :
    TwoSLSBootstrapResidualSubstitutionNegligibilityInputs μ Z X Y β
  true_score_tail : ∀ η : ℝ, 0 < η →
    ∃ K : Set (EuclideanSpace ℝ l), IsCompact K ∧
      TendstoInMeasure μ
        (fun n ω =>
          (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω) n ω).real
            {ωs |
              twoSLSBootstrapTrueRecenteredScoreStatisticFinSucc
                Z e n ω ωs ∉ K})
        atTop (fun _ => 0)
  coefficient_closeness :
    TwoSLSBootstrapCoefficientLinearizationClosenessInputs μ
      (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω)) Z X Y
      (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
      (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
      (scoreCovMat μ Z e)
      (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))
  covariance_resample :
    TwoSLSBootstrapRobustCovarianceResamplePrimitiveInputs μ Z X Y

namespace TwoSLSBootstrapTheorem12_8ScoreTailPrimitiveEmpiricalProcessInputs

set_option linter.style.longLine false in
/-- Build the score-tail primitive Hansen 12.8 empirical-process package from
bootstrap empirical-process envelope bounds.

This is the bundled proof boundary after reusing the local deterministic
decompositions. The true-score tail remains a score-tightness input; the
residual substitution, population-to-sample linearization, coefficient
linearization, and robust covariance resampling fields are reduced to scalar
envelopes with bootstrap tails. -/
theorem of_tail_bounds
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {Y e : ℕ → Ω → ℝ} {β : k → ℝ} {R : Matrix Unit k ℝ}
    {Bresid Bpop Bcoef Bcov :
      ∀ n, Ω → (Fin (n + 1) → Fin (n + 1)) → ℝ}
    (hTrueTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set (EuclideanSpace ℝ l), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω =>
            (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω) n ω).real
              {ωs |
                twoSLSBootstrapTrueRecenteredScoreStatisticFinSucc
                  Z e n ω ωs ∉ K})
          atTop (fun _ => 0))
    (hBresidTail : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω) n ω).real
            {ωs | δ ≤ Bresid n ω ωs})
        atTop (fun _ => 0))
    (hBresidBound : ∀ n ω (ωs : Fin (n + 1) → Fin (n + 1)),
      ‖twoSLSBootstrapResidualSubstitutionRecenteredScoreStatisticFinSucc
        Z X Y β n ω ωs‖ ≤ Bresid n ω ωs)
    (hBpopTail : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω) n ω).real
            {ωs | δ ≤ Bpop n ω ωs})
        atTop (fun _ => 0))
    (hBpopBound : ∀ n ω (ωs : Fin (n + 1) → Fin (n + 1)),
      dist (twoSLSBootstrapLinearizedGapFinSucc Z X Y n ω ωs)
        (twoSLSBootstrapPopulationLinearizedGapFinSucc
          (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
          (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
          (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))
          Z X Y n ω ωs) ≤ Bpop n ω ωs)
    (hBcoefTail : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω) n ω).real
            {ωs | δ ≤ Bcoef n ω ωs})
        atTop (fun _ => 0))
    (hBcoefBound : ∀ n ω (ωs : Fin (n + 1) → Fin (n + 1)),
      dist (twoSLSBootstrapBetaGapFinSucc Z X Y n ω ωs)
        (twoSLSBootstrapLinearizedGapFinSucc Z X Y n ω ωs) ≤
          Bcoef n ω ωs)
    (hBcovTail : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω) n ω).real
            {ωs | δ ≤ Bcov n ω ωs})
        atTop (fun _ => 0))
    (hBcovBound : ∀ n ω (ωs : Fin (n + 1) → Fin (n + 1)),
      ‖twoSLSBootstrapVHatStarFinSucc Z X Y n ω ωs -
        twoSLSVHatStar
          (stackRegressors Z (n + 1) ω)
          (stackRegressors X (n + 1) ω)
          (stackOutcomes Y (n + 1) ω)‖ ≤ Bcov n ω ωs) :
    TwoSLSBootstrapTheorem12_8ScoreTailPrimitiveEmpiricalProcessInputs
      μ Z X Y e β R where
  residual_negligibility :=
    TwoSLSBootstrapResidualSubstitutionNegligibilityInputs.of_norm_bound
      (μ := μ) (Z := Z) (X := X) (Y := Y) (β := β)
      hBresidTail hBresidBound
  true_score_tail := hTrueTail
  coefficient_closeness :=
    TwoSLSBootstrapCoefficientLinearizationClosenessInputs.of_dist_bounds
      (μ := μ) (Pstar := twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
      (Z := Z) (X := X) (Y := Y)
      (QXZ := twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
      (QZZ := twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
      (Omega := scoreCovMat μ Z e)
      (QZX := twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))
      (Bpop := Bpop) (Bcoef := Bcoef)
      (fun n ω =>
        twoSLSBootstrapUniformPstarFinSucc_isProbabilityMeasure (Ω := Ω) n ω)
      hBpopTail hBcoefTail hBpopBound hBcoefBound
  covariance_resample :=
    TwoSLSBootstrapRobustCovarianceResamplePrimitiveInputs.of_norm_bound
      (μ := μ) (Z := Z) (X := X) (Y := Y)
      hBcovTail hBcovBound

set_option linter.style.longLine false in
/-- Version of `of_tail_bounds` whose true-score compact tail is supplied by an
eventual deterministic norm bound. -/
theorem of_tail_bounds_trueScore_norm_bound
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {Y e : ℕ → Ω → ℝ} {β : k → ℝ} {R : Matrix Unit k ℝ}
    {Bresid Bpop Bcoef Bcov :
      ∀ n, Ω → (Fin (n + 1) → Fin (n + 1)) → ℝ}
    {C : ℝ}
    (hTrueBound :
      ∀ᶠ n in atTop,
        ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
          ‖twoSLSBootstrapTrueRecenteredScoreStatisticFinSucc
            Z e n ω ωs‖ ≤ C)
    (hBresidTail : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω) n ω).real
            {ωs | δ ≤ Bresid n ω ωs})
        atTop (fun _ => 0))
    (hBresidBound : ∀ n ω (ωs : Fin (n + 1) → Fin (n + 1)),
      ‖twoSLSBootstrapResidualSubstitutionRecenteredScoreStatisticFinSucc
        Z X Y β n ω ωs‖ ≤ Bresid n ω ωs)
    (hBpopTail : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω) n ω).real
            {ωs | δ ≤ Bpop n ω ωs})
        atTop (fun _ => 0))
    (hBpopBound : ∀ n ω (ωs : Fin (n + 1) → Fin (n + 1)),
      dist (twoSLSBootstrapLinearizedGapFinSucc Z X Y n ω ωs)
        (twoSLSBootstrapPopulationLinearizedGapFinSucc
          (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
          (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
          (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))
          Z X Y n ω ωs) ≤ Bpop n ω ωs)
    (hBcoefTail : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω) n ω).real
            {ωs | δ ≤ Bcoef n ω ωs})
        atTop (fun _ => 0))
    (hBcoefBound : ∀ n ω (ωs : Fin (n + 1) → Fin (n + 1)),
      dist (twoSLSBootstrapBetaGapFinSucc Z X Y n ω ωs)
        (twoSLSBootstrapLinearizedGapFinSucc Z X Y n ω ωs) ≤
          Bcoef n ω ωs)
    (hBcovTail : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω) n ω).real
            {ωs | δ ≤ Bcov n ω ωs})
        atTop (fun _ => 0))
    (hBcovBound : ∀ n ω (ωs : Fin (n + 1) → Fin (n + 1)),
      ‖twoSLSBootstrapVHatStarFinSucc Z X Y n ω ωs -
        twoSLSVHatStar
          (stackRegressors Z (n + 1) ω)
          (stackRegressors X (n + 1) ω)
          (stackOutcomes Y (n + 1) ω)‖ ≤ Bcov n ω ωs) :
    TwoSLSBootstrapTheorem12_8ScoreTailPrimitiveEmpiricalProcessInputs
      μ Z X Y e β R :=
  of_tail_bounds
    (μ := μ) (Z := Z) (X := X) (Y := Y) (e := e) (β := β) (R := R)
    (Bresid := Bresid) (Bpop := Bpop) (Bcoef := Bcoef) (Bcov := Bcov)
    (twoSLSBootstrapTrueRecenteredScoreStatisticFinSucc_compactTail_uniform_of_eventually_norm_bound
      (μ := μ) (Z := Z) (e := e) hTrueBound)
    hBresidTail hBresidBound hBpopTail hBpopBound
    hBcoefTail hBcoefBound hBcovTail hBcovBound

set_option linter.style.longLine false in
/-- Score-tail primitive empirical-process package from true-score boundedness
and uniform bootstrap remainder bounds.

This is the smallest deterministic-envelope surface currently exposed for
Hansen Theorem 12.8 in this file.  It removes the scalar envelope random
variables `Bresid`, `Bpop`, `Bcoef`, and `Bcov`: callers only prove that the
actual residual-substitution, population-to-sample linearization,
coefficient-linearization, and robust covariance resampling remainders are
uniformly `o(1)` over the ordinary bootstrap resamples. -/
theorem of_uniform_remainders_trueScore_norm_bound
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {Y e : ℕ → Ω → ℝ} {β : k → ℝ} {R : Matrix Unit k ℝ}
    {C : ℝ}
    (hTrueBound :
      ∀ᶠ n in atTop,
        ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
          ‖twoSLSBootstrapTrueRecenteredScoreStatisticFinSucc
            Z e n ω ωs‖ ≤ C)
    (hResidSmall : ∀ δ : ℝ, 0 < δ →
      ∀ᶠ n in atTop,
        ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
          ‖twoSLSBootstrapResidualSubstitutionRecenteredScoreStatisticFinSucc
            Z X Y β n ω ωs‖ < δ)
    (hPopSmall : ∀ δ : ℝ, 0 < δ →
      ∀ᶠ n in atTop,
        ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
          dist (twoSLSBootstrapLinearizedGapFinSucc Z X Y n ω ωs)
            (twoSLSBootstrapPopulationLinearizedGapFinSucc
              (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
              (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
              (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))
              Z X Y n ω ωs) < δ)
    (hCoefSmall : ∀ δ : ℝ, 0 < δ →
      ∀ᶠ n in atTop,
        ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
          dist (twoSLSBootstrapBetaGapFinSucc Z X Y n ω ωs)
            (twoSLSBootstrapLinearizedGapFinSucc Z X Y n ω ωs) < δ)
    (hCovSmall : ∀ δ : ℝ, 0 < δ →
      ∀ᶠ n in atTop,
        ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
          ‖twoSLSBootstrapVHatStarFinSucc Z X Y n ω ωs -
            twoSLSVHatStar
              (stackRegressors Z (n + 1) ω)
              (stackRegressors X (n + 1) ω)
              (stackOutcomes Y (n + 1) ω)‖ < δ) :
    TwoSLSBootstrapTheorem12_8ScoreTailPrimitiveEmpiricalProcessInputs
      μ Z X Y e β R where
  residual_negligibility :=
    TwoSLSBootstrapResidualSubstitutionNegligibilityInputs.of_uniform_norm_vanish
      (μ := μ) (Z := Z) (X := X) (Y := Y) (β := β)
      hResidSmall
  true_score_tail :=
    twoSLSBootstrapTrueRecenteredScoreStatisticFinSucc_compactTail_uniform_of_eventually_norm_bound
      (μ := μ) (Z := Z) (e := e) hTrueBound
  coefficient_closeness :=
    TwoSLSBootstrapCoefficientLinearizationClosenessInputs.of_uniform_dist_vanish
      (μ := μ) (Pstar := twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
      (Z := Z) (X := X) (Y := Y)
      (QXZ := twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
      (QZZ := twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
      (Omega := scoreCovMat μ Z e)
      (QZX := twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))
      hPopSmall hCoefSmall
  covariance_resample :=
    TwoSLSBootstrapRobustCovarianceResamplePrimitiveInputs.of_uniform_norm_vanish
      (μ := μ) (Z := Z) (X := X) (Y := Y) hCovSmall

set_option linter.style.longLine false in
/-- Score-tail primitive empirical-process package from the established
residual-substitution package, coefficient closeness, and primitive covariance
resampling control.

This is the preferred bridge when a proof has already built
`TwoSLSBootstrapResidualSubstitutionInputs`: the full residual-score compact
tail and residual-substitution negligibility fields are projected out of that
package, while the coefficient and covariance inputs stay at the smallest
currently exposed primitive layers. -/
theorem of_residualSubstitution_closeness_covariancePrimitive
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {Y e : ℕ → Ω → ℝ} {β : k → ℝ} {R : Matrix Unit k ℝ}
    (hresid : TwoSLSBootstrapResidualSubstitutionInputs μ Z X Y e β)
    (hcoef :
      TwoSLSBootstrapCoefficientLinearizationClosenessInputs μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω)) Z X Y
        (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
        (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
        (scoreCovMat μ Z e)
        (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X))))
    (hcov : TwoSLSBootstrapRobustCovarianceResamplePrimitiveInputs μ Z X Y) :
    TwoSLSBootstrapTheorem12_8ScoreTailPrimitiveEmpiricalProcessInputs
      μ Z X Y e β R where
  residual_negligibility :=
    { residual_substitution_negligible :=
        hresid.residual_substitution_negligible }
  true_score_tail := by
    intro η hη
    rcases hresid.compact_tail η hη with ⟨K, hK, hTrue, _hActual⟩
    exact ⟨K, hK, hTrue⟩
  coefficient_closeness := hcoef
  covariance_resample := hcov

set_option linter.style.longLine false in
/-- Convert the score-tail primitive empirical-process package into the
primitive package used by the existing Theorem 12.8 wrappers. -/
theorem toPrimitiveEmpiricalProcessInputs
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {Y e : ℕ → Ω → ℝ} {β : k → ℝ} {R : Matrix Unit k ℝ}
    (h :
      TwoSLSBootstrapTheorem12_8ScoreTailPrimitiveEmpiricalProcessInputs
        μ Z X Y e β R)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω) :
    TwoSLSBootstrapTheorem12_8PrimitiveEmpiricalProcessInputs
      μ Z X Y e β R where
  residual_negligibility := h.residual_negligibility
  true_score_tail := h.true_score_tail
  coefficient_linearization :=
    h.coefficient_closeness.toPrimitiveInputs_of_residualSubstitution_trueScoreTail
      (μ := μ) (Z := Z) (X := X) (Y := Y) (e := e) (β := β)
      (QXZ := twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
      (QZZ := twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
      (Omega := scoreCovMat μ Z e)
      (QZX := twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))
      hmodel h.residual_negligibility h.true_score_tail
  covariance_resample := h.covariance_resample

set_option linter.style.longLine false in
/-- Convert the score-tail primitive empirical-process package directly into
the established Theorem 12.8 empirical-process package. -/
theorem toEmpiricalProcessInputs
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {Y e : ℕ → Ω → ℝ} {β : k → ℝ} {R : Matrix Unit k ℝ}
    (h :
      TwoSLSBootstrapTheorem12_8ScoreTailPrimitiveEmpiricalProcessInputs
        μ Z X Y e β R)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω) :
    TwoSLSBootstrapTheorem12_8EmpiricalProcessInputs
      μ Z X Y e β R :=
  (h.toPrimitiveEmpiricalProcessInputs (μ := μ) (Z := Z) (X := X)
    (Y := Y) (e := e) (β := β) (R := R) hmodel).toEmpiricalProcessInputs

end TwoSLSBootstrapTheorem12_8ScoreTailPrimitiveEmpiricalProcessInputs

set_option linter.style.longLine false in
/-- Hansen Theorem 12.8 from the single-row iid Assumption 12.2 surface plus
the remaining primitive bootstrap empirical-process inputs.

The wrapper derives the covariance weight WLLN package from the joint-iid
Assumption 12.2 rows and the mixed third/fourth moment integrability premises,
derives restriction nondegeneracy from Assumption 12.2 and full rank of the
one-row restriction, and then reuses the existing coefficient and robust
bootstrap t-ratio endpoints. Both Hansen conclusions are returned together. -/
theorem
    twoSLSBootstrap_theorem12_8_of_assumption12_2_joint_iid_mixed_moments_empiricalProcess
    [IsProbabilityMeasure μ]
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {R : Matrix Unit k ℝ}
    (h : TwoSLSAssumption12_2JointIidFourthConditions μ Z X e)
    (β : k → ℝ)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hOmegaCross : ∀ a b : l, ∀ j : k,
      Integrable (fun ω => e 0 ω * X 0 ω j * Z 0 ω a * Z 0 ω b) μ)
    (hOmegaQuadratic : ∀ a b : l, ∀ j m : k,
      Integrable (fun ω => X 0 ω j * X 0 ω m * Z 0 ω a * Z 0 ω b) μ)
    (hSigmaCross : ∀ j : k,
      Integrable (fun ω => e 0 ω * X 0 ω j) μ)
    (hR : Function.Injective Rᵀ.mulVec)
    (hboot :
      TwoSLSBootstrapTheorem12_8EmpiricalProcessInputs μ Z X Y e β R) :
    TendstoInBootstrapDistributionIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs => twoSLSBootstrapBetaGapFinSucc Z X Y n ω ωs)
        (multivariateGaussian (0 : EuclideanSpace ℝ k)
          (twoSLSAsymptoticVariance
            (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (scoreCovMat μ Z e)
            (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))))
        (fun z : EuclideanSpace ℝ k => (z : k → ℝ)) ∧
      TendstoInBootstrapDistributionIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs (_ : Unit) =>
          twoSLSBootstrapRobustLinearTStatFinSucc R Z X Y n ω ωs)
        (gaussianReal 0 1) (fun z : ℝ => fun _ : Unit => z) := by
  let hIid : TwoSLSAssumption12_2IidFourthConditions μ Z X e :=
    h.toIidFourthConditions
  let hw : TwoSLSCovarianceWeightWLLNConditions μ Z X e :=
    TwoSLSCovarianceWeightWLLNConditions.of_joint_iid
      (μ := μ) (Z := Z) (X := X) (e := e)
      h.joint_iIndep h.joint_identDistrib
      hOmegaCross hOmegaQuadratic hSigmaCross
  have hresid : TwoSLSBootstrapResidualSubstitutionInputs μ Z X Y e β :=
    hboot.residual_negligibility.toResidualSubstitutionInputs_of_trueScore_compactTail
      (μ := μ) (Z := Z) (X := X) (Y := Y) (e := e) (β := β)
      hmodel hboot.true_score_tail
  exact
    twoSLSBootstrap_theorem12_8_of_assumption12_2_weight_wlln_residualSubstitution_linearization_fullRank_resampleCloseness
      (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y) (R := R)
      hIid β hmodel hw hresid hboot.coefficient_linearization
      hR hboot.covariance_resample

/-- Hansen Theorem 12.8 from the named mixed-moment Assumption 12.2 package
plus the remaining bootstrap empirical-process inputs.

This wrapper removes the separate scalar mixed-moment arguments from
`twoSLSBootstrap_theorem12_8_of_assumption12_2_joint_iid_mixed_moments_empiricalProcess`;
they are fields of `TwoSLSAssumption12_2JointIidMixedMomentConditions`. -/
theorem twoSLSBootstrap_theorem12_8_of_mixed_moment_conditions_empiricalProcess
    [IsProbabilityMeasure μ]
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {R : Matrix Unit k ℝ}
    (h : TwoSLSAssumption12_2JointIidMixedMomentConditions μ Z X e)
    (β : k → ℝ)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hR : Function.Injective Rᵀ.mulVec)
    (hboot :
      TwoSLSBootstrapTheorem12_8EmpiricalProcessInputs μ Z X Y e β R) :
    TendstoInBootstrapDistributionIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs => twoSLSBootstrapBetaGapFinSucc Z X Y n ω ωs)
        (multivariateGaussian (0 : EuclideanSpace ℝ k)
          (twoSLSAsymptoticVariance
            (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (scoreCovMat μ Z e)
            (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))))
        (fun z : EuclideanSpace ℝ k => (z : k → ℝ)) ∧
      TendstoInBootstrapDistributionIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs (_ : Unit) =>
          twoSLSBootstrapRobustLinearTStatFinSucc R Z X Y n ω ωs)
        (gaussianReal 0 1) (fun z : ℝ => fun _ : Unit => z) :=
  twoSLSBootstrap_theorem12_8_of_assumption12_2_joint_iid_mixed_moments_empiricalProcess
    (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y) (R := R)
    h.toTwoSLSAssumption12_2JointIidFourthConditions β hmodel
    h.omega_cross_integrable h.omega_quadratic_integrable
    h.sigma_cross_integrable hR hboot

/-- Hansen Theorem 12.8 from the literal textbook fourth-moment Assumption
12.2 package plus the remaining bootstrap empirical-process inputs.

The package derives all mixed moments by Hölder and supplies the structural
equation, so the only non-textbook input left here is the explicit bootstrap
empirical-process package. -/
theorem twoSLSBootstrap_theorem12_8_of_textbook_fourth_empiricalProcess
    [IsProbabilityMeasure μ]
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {R : Matrix Unit k ℝ} {β : k → ℝ}
    (h : TwoSLSAssumption12_2JointIidTextbookFourthConditions μ Z X e Y β)
    (hR : Function.Injective Rᵀ.mulVec)
    (hboot :
      TwoSLSBootstrapTheorem12_8EmpiricalProcessInputs μ Z X Y e β R) :
    TendstoInBootstrapDistributionIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs => twoSLSBootstrapBetaGapFinSucc Z X Y n ω ωs)
        (multivariateGaussian (0 : EuclideanSpace ℝ k)
          (twoSLSAsymptoticVariance
            (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (scoreCovMat μ Z e)
            (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))))
        (fun z : EuclideanSpace ℝ k => (z : k → ℝ)) ∧
      TendstoInBootstrapDistributionIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs (_ : Unit) =>
          twoSLSBootstrapRobustLinearTStatFinSucc R Z X Y n ω ωs)
        (gaussianReal 0 1) (fun z : ℝ => fun _ : Unit => z) :=
  twoSLSBootstrap_theorem12_8_of_mixed_moment_conditions_empiricalProcess
    (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y) (R := R)
    (h.toJointIidMixedMomentConditions) β h.model hR hboot

set_option linter.style.longLine false in
/-- Hansen Theorem 12.8 from joint-iid Assumption 12.2 and primitive
bootstrap empirical-process assumptions.

This wrapper is theorem-facing: coefficient compact-tail fields and robust
covariance bootstrap-probability closeness are derived from the primitive
tail/closeness package before applying the established empirical-process
endpoint. -/
theorem
    twoSLSBootstrap_theorem12_8_of_assumption12_2_joint_iid_mixed_moments_primitiveEmpiricalProcess
    [IsProbabilityMeasure μ]
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {R : Matrix Unit k ℝ}
    (h : TwoSLSAssumption12_2JointIidFourthConditions μ Z X e)
    (β : k → ℝ)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hOmegaCross : ∀ a b : l, ∀ j : k,
      Integrable (fun ω => e 0 ω * X 0 ω j * Z 0 ω a * Z 0 ω b) μ)
    (hOmegaQuadratic : ∀ a b : l, ∀ j m : k,
      Integrable (fun ω => X 0 ω j * X 0 ω m * Z 0 ω a * Z 0 ω b) μ)
    (hSigmaCross : ∀ j : k,
      Integrable (fun ω => e 0 ω * X 0 ω j) μ)
    (hR : Function.Injective Rᵀ.mulVec)
    (hboot :
      TwoSLSBootstrapTheorem12_8PrimitiveEmpiricalProcessInputs
        μ Z X Y e β R) :
    TendstoInBootstrapDistributionIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs => twoSLSBootstrapBetaGapFinSucc Z X Y n ω ωs)
        (multivariateGaussian (0 : EuclideanSpace ℝ k)
          (twoSLSAsymptoticVariance
            (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (scoreCovMat μ Z e)
            (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))))
        (fun z : EuclideanSpace ℝ k => (z : k → ℝ)) ∧
      TendstoInBootstrapDistributionIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs (_ : Unit) =>
          twoSLSBootstrapRobustLinearTStatFinSucc R Z X Y n ω ωs)
        (gaussianReal 0 1) (fun z : ℝ => fun _ : Unit => z) :=
  twoSLSBootstrap_theorem12_8_of_assumption12_2_joint_iid_mixed_moments_empiricalProcess
    (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y) (R := R)
    h β hmodel hOmegaCross hOmegaQuadratic hSigmaCross hR
    (hboot.toEmpiricalProcessInputs
      (μ := μ) (Z := Z) (X := X) (Y := Y) (e := e) (β := β) (R := R))

set_option linter.style.longLine false in
/-- Hansen Theorem 12.8 from joint-iid Assumption 12.2 and the score-tail
primitive bootstrap empirical-process package.

This is the smallest bundled 12.8 endpoint in this file: true-score tightness
and residual-substitution negligibility imply feasible score tightness, which
then implies population-linearized coefficient tightness by continuous
mapping. The remaining coefficient inputs are only the two bootstrap closeness
statements. -/
theorem
    twoSLSBootstrap_theorem12_8_of_assumption12_2_joint_iid_mixed_moments_scoreTailPrimitiveEmpiricalProcess
    [IsProbabilityMeasure μ]
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {R : Matrix Unit k ℝ}
    (h : TwoSLSAssumption12_2JointIidFourthConditions μ Z X e)
    (β : k → ℝ)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hOmegaCross : ∀ a b : l, ∀ j : k,
      Integrable (fun ω => e 0 ω * X 0 ω j * Z 0 ω a * Z 0 ω b) μ)
    (hOmegaQuadratic : ∀ a b : l, ∀ j m : k,
      Integrable (fun ω => X 0 ω j * X 0 ω m * Z 0 ω a * Z 0 ω b) μ)
    (hSigmaCross : ∀ j : k,
      Integrable (fun ω => e 0 ω * X 0 ω j) μ)
    (hR : Function.Injective Rᵀ.mulVec)
    (hboot :
      TwoSLSBootstrapTheorem12_8ScoreTailPrimitiveEmpiricalProcessInputs
        μ Z X Y e β R) :
    TendstoInBootstrapDistributionIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs => twoSLSBootstrapBetaGapFinSucc Z X Y n ω ωs)
        (multivariateGaussian (0 : EuclideanSpace ℝ k)
          (twoSLSAsymptoticVariance
            (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (scoreCovMat μ Z e)
            (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))))
        (fun z : EuclideanSpace ℝ k => (z : k → ℝ)) ∧
      TendstoInBootstrapDistributionIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs (_ : Unit) =>
          twoSLSBootstrapRobustLinearTStatFinSucc R Z X Y n ω ωs)
        (gaussianReal 0 1) (fun z : ℝ => fun _ : Unit => z) :=
  twoSLSBootstrap_theorem12_8_of_assumption12_2_joint_iid_mixed_moments_primitiveEmpiricalProcess
    (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y) (R := R)
    h β hmodel hOmegaCross hOmegaQuadratic hSigmaCross hR
    (hboot.toPrimitiveEmpiricalProcessInputs
      (μ := μ) (Z := Z) (X := X) (Y := Y) (e := e) (β := β) (R := R)
      hmodel)

set_option linter.style.longLine false in
/-- Hansen Theorem 12.8 from the literal textbook fourth-moment Assumption
12.2 package plus the score-tail primitive bootstrap empirical-process package.

This is the textbook-fourth companion to
`twoSLSBootstrap_theorem12_8_of_assumption12_2_joint_iid_mixed_moments_scoreTailPrimitiveEmpiricalProcess`:
the mixed fourth moments are derived from Hansen's finite-fourth package, while
the remaining bootstrap empirical-process work is exactly the score-tail
primitive package. -/
theorem
    twoSLSBootstrap_theorem12_8_of_textbook_fourth_scoreTailPrimitiveEmpiricalProcess
    [IsProbabilityMeasure μ]
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {R : Matrix Unit k ℝ} {β : k → ℝ}
    (h : TwoSLSAssumption12_2JointIidTextbookFourthConditions μ Z X e Y β)
    (hR : Function.Injective Rᵀ.mulVec)
    (hboot :
      TwoSLSBootstrapTheorem12_8ScoreTailPrimitiveEmpiricalProcessInputs
        μ Z X Y e β R) :
    TendstoInBootstrapDistributionIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs => twoSLSBootstrapBetaGapFinSucc Z X Y n ω ωs)
        (multivariateGaussian (0 : EuclideanSpace ℝ k)
          (twoSLSAsymptoticVariance
            (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (scoreCovMat μ Z e)
            (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))))
        (fun z : EuclideanSpace ℝ k => (z : k → ℝ)) ∧
      TendstoInBootstrapDistributionIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs (_ : Unit) =>
          twoSLSBootstrapRobustLinearTStatFinSucc R Z X Y n ω ωs)
        (gaussianReal 0 1) (fun z : ℝ => fun _ : Unit => z) := by
  let hm := h.toJointIidMixedMomentConditions
  exact
    twoSLSBootstrap_theorem12_8_of_assumption12_2_joint_iid_mixed_moments_scoreTailPrimitiveEmpiricalProcess
      (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y) (R := R)
      hm.toTwoSLSAssumption12_2JointIidFourthConditions β h.model
      hm.omega_cross_integrable hm.omega_quadratic_integrable
      hm.sigma_cross_integrable hR hboot

set_option linter.style.longLine false in
/-- Hansen Theorem 12.8 from the literal textbook fourth-moment Assumption
12.2 package, with the one-row restriction rank condition stated as a nonzero
restriction row.

This is a theorem-facing bridge over
`twoSLSBootstrap_theorem12_8_of_textbook_fourth_scoreTailPrimitiveEmpiricalProcess`;
it keeps the remaining bootstrap empirical-process work in the score-tail
primitive package. -/
theorem
    twoSLSBootstrap_theorem12_8_of_textbook_fourth_scoreTailPrimitiveEmpiricalProcess_row_ne_zero
    [IsProbabilityMeasure μ]
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {R : Matrix Unit k ℝ} {β : k → ℝ}
    (h : TwoSLSAssumption12_2JointIidTextbookFourthConditions μ Z X e Y β)
    (hR : ∃ j : k, R () j ≠ 0)
    (hboot :
      TwoSLSBootstrapTheorem12_8ScoreTailPrimitiveEmpiricalProcessInputs
        μ Z X Y e β R) :
    TendstoInBootstrapDistributionIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs => twoSLSBootstrapBetaGapFinSucc Z X Y n ω ωs)
        (multivariateGaussian (0 : EuclideanSpace ℝ k)
          (twoSLSAsymptoticVariance
            (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (scoreCovMat μ Z e)
            (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))))
        (fun z : EuclideanSpace ℝ k => (z : k → ℝ)) ∧
      TendstoInBootstrapDistributionIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs (_ : Unit) =>
          twoSLSBootstrapRobustLinearTStatFinSucc R Z X Y n ω ωs)
        (gaussianReal 0 1) (fun z : ℝ => fun _ : Unit => z) :=
  twoSLSBootstrap_theorem12_8_of_textbook_fourth_scoreTailPrimitiveEmpiricalProcess
    (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y)
    (R := R) (β := β) h
    (oneRow_transpose_mulVec_injective_of_exists_ne_zero hR) hboot

set_option linter.style.longLine false in
/-- Observed-row Assumption 12.2 endpoint for Hansen Theorem 12.8 at the
score-tail primitive bootstrap boundary.

This is the observed-row companion to
`twoSLSBootstrap_theorem12_8_of_textbook_fourth_scoreTailPrimitiveEmpiricalProcess`.
It keeps the bootstrap empirical-process work in the same score-tail package and
uses the established observed-to-residual Assumption 12.2 bridge. -/
theorem
    twoSLSBootstrap_theorem12_8_of_observed_textbook_fourth_scoreTailPrimitiveEmpiricalProcess
    [IsProbabilityMeasure μ]
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {R : Matrix Unit k ℝ} {β : k → ℝ}
    (h : TwoSLSAssumption12_2ObservedIidTextbookFourthConditions μ Z X e Y β)
    (hR : Function.Injective Rᵀ.mulVec)
    (hboot :
      TwoSLSBootstrapTheorem12_8ScoreTailPrimitiveEmpiricalProcessInputs
        μ Z X Y e β R) :
    TendstoInBootstrapDistributionIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs => twoSLSBootstrapBetaGapFinSucc Z X Y n ω ωs)
        (multivariateGaussian (0 : EuclideanSpace ℝ k)
          (twoSLSAsymptoticVariance
            (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (scoreCovMat μ Z e)
            (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))))
        (fun z : EuclideanSpace ℝ k => (z : k → ℝ)) ∧
      TendstoInBootstrapDistributionIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs (_ : Unit) =>
          twoSLSBootstrapRobustLinearTStatFinSucc R Z X Y n ω ωs)
        (gaussianReal 0 1) (fun z : ℝ => fun _ : Unit => z) :=
  twoSLSBootstrap_theorem12_8_of_textbook_fourth_scoreTailPrimitiveEmpiricalProcess
    (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y)
    (R := R) (β := β) h.toResidualTextbookFourthConditions hR hboot

set_option linter.style.longLine false in
/-- Observed-row Assumption 12.2 endpoint for Hansen Theorem 12.8 with the
one-row restriction rank condition stated as a nonzero row entry. -/
theorem
    twoSLSBootstrap_theorem12_8_of_observed_textbook_fourth_scoreTailPrimitiveEmpiricalProcess_row_ne_zero
    [IsProbabilityMeasure μ]
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {R : Matrix Unit k ℝ} {β : k → ℝ}
    (h : TwoSLSAssumption12_2ObservedIidTextbookFourthConditions μ Z X e Y β)
    (hR : ∃ j : k, R () j ≠ 0)
    (hboot :
      TwoSLSBootstrapTheorem12_8ScoreTailPrimitiveEmpiricalProcessInputs
        μ Z X Y e β R) :
    TendstoInBootstrapDistributionIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs => twoSLSBootstrapBetaGapFinSucc Z X Y n ω ωs)
        (multivariateGaussian (0 : EuclideanSpace ℝ k)
          (twoSLSAsymptoticVariance
            (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (scoreCovMat μ Z e)
            (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))))
        (fun z : EuclideanSpace ℝ k => (z : k → ℝ)) ∧
      TendstoInBootstrapDistributionIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs (_ : Unit) =>
          twoSLSBootstrapRobustLinearTStatFinSucc R Z X Y n ω ωs)
        (gaussianReal 0 1) (fun z : ℝ => fun _ : Unit => z) :=
  twoSLSBootstrap_theorem12_8_of_observed_textbook_fourth_scoreTailPrimitiveEmpiricalProcess
    (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y)
    (R := R) (β := β) h
    (oneRow_transpose_mulVec_injective_of_exists_ne_zero hR) hboot

set_option linter.style.longLine false in
/-- Hansen Theorem 12.8 from joint-iid Assumption 12.2 and scalar bootstrap
empirical-process envelope bounds.

This is the direct theorem-facing endpoint for the current primitive boundary:
the residual-substitution, population-to-sample linearization,
coefficient-linearization, and robust-covariance resampling inputs are supplied
as scalar envelopes with bootstrap tails.  The theorem then builds the
score-tail primitive package internally and reuses the established Hansen 12.8
endpoint, so callers no longer need to assemble
`TwoSLSBootstrapTheorem12_8ScoreTailPrimitiveEmpiricalProcessInputs` by hand. -/
theorem
    twoSLSBootstrap_theorem12_8_of_assumption12_2_joint_iid_mixed_moments_tail_bounds
    [IsProbabilityMeasure μ]
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {R : Matrix Unit k ℝ} {β : k → ℝ}
    {Bresid Bpop Bcoef Bcov :
      ∀ n, Ω → (Fin (n + 1) → Fin (n + 1)) → ℝ}
    (h : TwoSLSAssumption12_2JointIidFourthConditions μ Z X e)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hOmegaCross : ∀ a b : l, ∀ j : k,
      Integrable (fun ω => e 0 ω * X 0 ω j * Z 0 ω a * Z 0 ω b) μ)
    (hOmegaQuadratic : ∀ a b : l, ∀ j m : k,
      Integrable (fun ω => X 0 ω j * X 0 ω m * Z 0 ω a * Z 0 ω b) μ)
    (hSigmaCross : ∀ j : k,
      Integrable (fun ω => e 0 ω * X 0 ω j) μ)
    (hR : Function.Injective Rᵀ.mulVec)
    (hTrueTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set (EuclideanSpace ℝ l), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω =>
            (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω) n ω).real
              {ωs |
                twoSLSBootstrapTrueRecenteredScoreStatisticFinSucc
                  Z e n ω ωs ∉ K})
          atTop (fun _ => 0))
    (hBresidTail : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω) n ω).real
            {ωs | δ ≤ Bresid n ω ωs})
        atTop (fun _ => 0))
    (hBresidBound : ∀ n ω (ωs : Fin (n + 1) → Fin (n + 1)),
      ‖twoSLSBootstrapResidualSubstitutionRecenteredScoreStatisticFinSucc
        Z X Y β n ω ωs‖ ≤ Bresid n ω ωs)
    (hBpopTail : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω) n ω).real
            {ωs | δ ≤ Bpop n ω ωs})
        atTop (fun _ => 0))
    (hBpopBound : ∀ n ω (ωs : Fin (n + 1) → Fin (n + 1)),
      dist (twoSLSBootstrapLinearizedGapFinSucc Z X Y n ω ωs)
        (twoSLSBootstrapPopulationLinearizedGapFinSucc
          (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
          (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
          (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))
          Z X Y n ω ωs) ≤ Bpop n ω ωs)
    (hBcoefTail : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω) n ω).real
            {ωs | δ ≤ Bcoef n ω ωs})
        atTop (fun _ => 0))
    (hBcoefBound : ∀ n ω (ωs : Fin (n + 1) → Fin (n + 1)),
      dist (twoSLSBootstrapBetaGapFinSucc Z X Y n ω ωs)
        (twoSLSBootstrapLinearizedGapFinSucc Z X Y n ω ωs) ≤
          Bcoef n ω ωs)
    (hBcovTail : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω) n ω).real
            {ωs | δ ≤ Bcov n ω ωs})
        atTop (fun _ => 0))
    (hBcovBound : ∀ n ω (ωs : Fin (n + 1) → Fin (n + 1)),
      ‖twoSLSBootstrapVHatStarFinSucc Z X Y n ω ωs -
        twoSLSVHatStar
          (stackRegressors Z (n + 1) ω)
          (stackRegressors X (n + 1) ω)
          (stackOutcomes Y (n + 1) ω)‖ ≤ Bcov n ω ωs) :
    TendstoInBootstrapDistributionIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs => twoSLSBootstrapBetaGapFinSucc Z X Y n ω ωs)
        (multivariateGaussian (0 : EuclideanSpace ℝ k)
          (twoSLSAsymptoticVariance
            (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (scoreCovMat μ Z e)
            (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))))
        (fun z : EuclideanSpace ℝ k => (z : k → ℝ)) ∧
      TendstoInBootstrapDistributionIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs (_ : Unit) =>
          twoSLSBootstrapRobustLinearTStatFinSucc R Z X Y n ω ωs)
        (gaussianReal 0 1) (fun z : ℝ => fun _ : Unit => z) :=
  twoSLSBootstrap_theorem12_8_of_assumption12_2_joint_iid_mixed_moments_scoreTailPrimitiveEmpiricalProcess
    (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y) (R := R)
    h β hmodel hOmegaCross hOmegaQuadratic hSigmaCross hR
    (TwoSLSBootstrapTheorem12_8ScoreTailPrimitiveEmpiricalProcessInputs.of_tail_bounds
      (μ := μ) (Z := Z) (X := X) (Y := Y) (e := e) (β := β) (R := R)
      (Bresid := Bresid) (Bpop := Bpop) (Bcoef := Bcoef) (Bcov := Bcov)
      hTrueTail hBresidTail hBresidBound hBpopTail hBpopBound
      hBcoefTail hBcoefBound hBcovTail hBcovBound)

set_option linter.style.longLine false in
/-- Hansen Theorem 12.8 from scalar bootstrap envelope bounds, with the
true-score tightness input supplied by an eventual deterministic norm bound.

This is a theorem-facing version of
`TwoSLSBootstrapTheorem12_8ScoreTailPrimitiveEmpiricalProcessInputs.of_tail_bounds_trueScore_norm_bound`:
the deterministic bound is converted to compact-tail control and the rest of
the proof is delegated to
`twoSLSBootstrap_theorem12_8_of_assumption12_2_joint_iid_mixed_moments_tail_bounds`. -/
theorem
    twoSLSBootstrap_theorem12_8_of_assumption12_2_joint_iid_mixed_moments_tail_bounds_trueScore_norm_bound
    [IsProbabilityMeasure μ]
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {R : Matrix Unit k ℝ} {β : k → ℝ} {C : ℝ}
    {Bresid Bpop Bcoef Bcov :
      ∀ n, Ω → (Fin (n + 1) → Fin (n + 1)) → ℝ}
    (h : TwoSLSAssumption12_2JointIidFourthConditions μ Z X e)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hOmegaCross : ∀ a b : l, ∀ j : k,
      Integrable (fun ω => e 0 ω * X 0 ω j * Z 0 ω a * Z 0 ω b) μ)
    (hOmegaQuadratic : ∀ a b : l, ∀ j m : k,
      Integrable (fun ω => X 0 ω j * X 0 ω m * Z 0 ω a * Z 0 ω b) μ)
    (hSigmaCross : ∀ j : k,
      Integrable (fun ω => e 0 ω * X 0 ω j) μ)
    (hR : Function.Injective Rᵀ.mulVec)
    (hTrueBound :
      ∀ᶠ n in atTop,
        ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
          ‖twoSLSBootstrapTrueRecenteredScoreStatisticFinSucc
            Z e n ω ωs‖ ≤ C)
    (hBresidTail : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω) n ω).real
            {ωs | δ ≤ Bresid n ω ωs})
        atTop (fun _ => 0))
    (hBresidBound : ∀ n ω (ωs : Fin (n + 1) → Fin (n + 1)),
      ‖twoSLSBootstrapResidualSubstitutionRecenteredScoreStatisticFinSucc
        Z X Y β n ω ωs‖ ≤ Bresid n ω ωs)
    (hBpopTail : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω) n ω).real
            {ωs | δ ≤ Bpop n ω ωs})
        atTop (fun _ => 0))
    (hBpopBound : ∀ n ω (ωs : Fin (n + 1) → Fin (n + 1)),
      dist (twoSLSBootstrapLinearizedGapFinSucc Z X Y n ω ωs)
        (twoSLSBootstrapPopulationLinearizedGapFinSucc
          (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
          (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
          (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))
          Z X Y n ω ωs) ≤ Bpop n ω ωs)
    (hBcoefTail : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω) n ω).real
            {ωs | δ ≤ Bcoef n ω ωs})
        atTop (fun _ => 0))
    (hBcoefBound : ∀ n ω (ωs : Fin (n + 1) → Fin (n + 1)),
      dist (twoSLSBootstrapBetaGapFinSucc Z X Y n ω ωs)
        (twoSLSBootstrapLinearizedGapFinSucc Z X Y n ω ωs) ≤
          Bcoef n ω ωs)
    (hBcovTail : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω) n ω).real
            {ωs | δ ≤ Bcov n ω ωs})
        atTop (fun _ => 0))
    (hBcovBound : ∀ n ω (ωs : Fin (n + 1) → Fin (n + 1)),
      ‖twoSLSBootstrapVHatStarFinSucc Z X Y n ω ωs -
        twoSLSVHatStar
          (stackRegressors Z (n + 1) ω)
          (stackRegressors X (n + 1) ω)
          (stackOutcomes Y (n + 1) ω)‖ ≤ Bcov n ω ωs) :
    TendstoInBootstrapDistributionIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs => twoSLSBootstrapBetaGapFinSucc Z X Y n ω ωs)
        (multivariateGaussian (0 : EuclideanSpace ℝ k)
          (twoSLSAsymptoticVariance
            (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (scoreCovMat μ Z e)
            (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))))
        (fun z : EuclideanSpace ℝ k => (z : k → ℝ)) ∧
      TendstoInBootstrapDistributionIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs (_ : Unit) =>
          twoSLSBootstrapRobustLinearTStatFinSucc R Z X Y n ω ωs)
        (gaussianReal 0 1) (fun z : ℝ => fun _ : Unit => z) :=
  twoSLSBootstrap_theorem12_8_of_assumption12_2_joint_iid_mixed_moments_tail_bounds
    (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y) (R := R) (β := β)
    (Bresid := Bresid) (Bpop := Bpop) (Bcoef := Bcoef) (Bcov := Bcov)
    h hmodel hOmegaCross hOmegaQuadratic hSigmaCross hR
    (twoSLSBootstrapTrueRecenteredScoreStatisticFinSucc_compactTail_uniform_of_eventually_norm_bound
      (μ := μ) (Z := Z) (e := e) hTrueBound)
    hBresidTail hBresidBound hBpopTail hBpopBound
    hBcoefTail hBcoefBound hBcovTail hBcovBound

set_option linter.style.longLine false in
/-- Hansen Theorem 12.8 from true-score boundedness and uniform bootstrap
remainder bounds.

This is the deterministic-envelope theorem-facing route: it removes the
scalar envelope-tail premises from
`twoSLSBootstrap_theorem12_8_of_assumption12_2_joint_iid_mixed_moments_tail_bounds_trueScore_norm_bound`
and asks directly for uniform `o(1)` control of the four concrete bootstrap
remainders. It still derives both Hansen conclusions through the score-tail
primitive empirical-process package, rather than assuming either conclusion. -/
theorem
    twoSLSBootstrap_theorem12_8_of_assumption12_2_joint_iid_mixed_moments_uniform_remainders_trueScore_norm_bound
    [IsProbabilityMeasure μ]
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {R : Matrix Unit k ℝ} {β : k → ℝ} {C : ℝ}
    (h : TwoSLSAssumption12_2JointIidFourthConditions μ Z X e)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hOmegaCross : ∀ a b : l, ∀ j : k,
      Integrable (fun ω => e 0 ω * X 0 ω j * Z 0 ω a * Z 0 ω b) μ)
    (hOmegaQuadratic : ∀ a b : l, ∀ j m : k,
      Integrable (fun ω => X 0 ω j * X 0 ω m * Z 0 ω a * Z 0 ω b) μ)
    (hSigmaCross : ∀ j : k,
      Integrable (fun ω => e 0 ω * X 0 ω j) μ)
    (hR : Function.Injective Rᵀ.mulVec)
    (hTrueBound :
      ∀ᶠ n in atTop,
        ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
          ‖twoSLSBootstrapTrueRecenteredScoreStatisticFinSucc
            Z e n ω ωs‖ ≤ C)
    (hResidSmall : ∀ δ : ℝ, 0 < δ →
      ∀ᶠ n in atTop,
        ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
          ‖twoSLSBootstrapResidualSubstitutionRecenteredScoreStatisticFinSucc
            Z X Y β n ω ωs‖ < δ)
    (hPopSmall : ∀ δ : ℝ, 0 < δ →
      ∀ᶠ n in atTop,
        ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
          dist (twoSLSBootstrapLinearizedGapFinSucc Z X Y n ω ωs)
            (twoSLSBootstrapPopulationLinearizedGapFinSucc
              (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
              (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
              (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))
              Z X Y n ω ωs) < δ)
    (hCoefSmall : ∀ δ : ℝ, 0 < δ →
      ∀ᶠ n in atTop,
        ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
          dist (twoSLSBootstrapBetaGapFinSucc Z X Y n ω ωs)
            (twoSLSBootstrapLinearizedGapFinSucc Z X Y n ω ωs) < δ)
    (hCovSmall : ∀ δ : ℝ, 0 < δ →
      ∀ᶠ n in atTop,
        ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
          ‖twoSLSBootstrapVHatStarFinSucc Z X Y n ω ωs -
            twoSLSVHatStar
              (stackRegressors Z (n + 1) ω)
              (stackRegressors X (n + 1) ω)
              (stackOutcomes Y (n + 1) ω)‖ < δ) :
    TendstoInBootstrapDistributionIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs => twoSLSBootstrapBetaGapFinSucc Z X Y n ω ωs)
        (multivariateGaussian (0 : EuclideanSpace ℝ k)
          (twoSLSAsymptoticVariance
            (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (scoreCovMat μ Z e)
            (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))))
        (fun z : EuclideanSpace ℝ k => (z : k → ℝ)) ∧
      TendstoInBootstrapDistributionIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs (_ : Unit) =>
          twoSLSBootstrapRobustLinearTStatFinSucc R Z X Y n ω ωs)
        (gaussianReal 0 1) (fun z : ℝ => fun _ : Unit => z) :=
  twoSLSBootstrap_theorem12_8_of_assumption12_2_joint_iid_mixed_moments_scoreTailPrimitiveEmpiricalProcess
    (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y) (R := R)
    h β hmodel hOmegaCross hOmegaQuadratic hSigmaCross hR
    (TwoSLSBootstrapTheorem12_8ScoreTailPrimitiveEmpiricalProcessInputs.of_uniform_remainders_trueScore_norm_bound
      (μ := μ) (Z := Z) (X := X) (Y := Y) (e := e) (β := β)
      (R := R) hTrueBound hResidSmall hPopSmall hCoefSmall hCovSmall)

set_option linter.style.longLine false in
/-- Textbook-fourth companion to
`twoSLSBootstrap_theorem12_8_of_assumption12_2_joint_iid_mixed_moments_tail_bounds_trueScore_norm_bound`.

The mixed fourth-moment fields are derived from the literal Hansen Assumption
12.2 package, leaving only the bootstrap tail/envelope inputs at the theorem
boundary. -/
theorem
    twoSLSBootstrap_theorem12_8_of_textbook_fourth_tail_bounds_trueScore_norm_bound
    [IsProbabilityMeasure μ]
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {R : Matrix Unit k ℝ} {β : k → ℝ} {C : ℝ}
    {Bresid Bpop Bcoef Bcov :
      ∀ n, Ω → (Fin (n + 1) → Fin (n + 1)) → ℝ}
    (h : TwoSLSAssumption12_2JointIidTextbookFourthConditions μ Z X e Y β)
    (hR : Function.Injective Rᵀ.mulVec)
    (hTrueBound :
      ∀ᶠ n in atTop,
        ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
          ‖twoSLSBootstrapTrueRecenteredScoreStatisticFinSucc
            Z e n ω ωs‖ ≤ C)
    (hBresidTail : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω) n ω).real
            {ωs | δ ≤ Bresid n ω ωs})
        atTop (fun _ => 0))
    (hBresidBound : ∀ n ω (ωs : Fin (n + 1) → Fin (n + 1)),
      ‖twoSLSBootstrapResidualSubstitutionRecenteredScoreStatisticFinSucc
        Z X Y β n ω ωs‖ ≤ Bresid n ω ωs)
    (hBpopTail : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω) n ω).real
            {ωs | δ ≤ Bpop n ω ωs})
        atTop (fun _ => 0))
    (hBpopBound : ∀ n ω (ωs : Fin (n + 1) → Fin (n + 1)),
      dist (twoSLSBootstrapLinearizedGapFinSucc Z X Y n ω ωs)
        (twoSLSBootstrapPopulationLinearizedGapFinSucc
          (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
          (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
          (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))
          Z X Y n ω ωs) ≤ Bpop n ω ωs)
    (hBcoefTail : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω) n ω).real
            {ωs | δ ≤ Bcoef n ω ωs})
        atTop (fun _ => 0))
    (hBcoefBound : ∀ n ω (ωs : Fin (n + 1) → Fin (n + 1)),
      dist (twoSLSBootstrapBetaGapFinSucc Z X Y n ω ωs)
        (twoSLSBootstrapLinearizedGapFinSucc Z X Y n ω ωs) ≤
          Bcoef n ω ωs)
    (hBcovTail : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω) n ω).real
            {ωs | δ ≤ Bcov n ω ωs})
        atTop (fun _ => 0))
    (hBcovBound : ∀ n ω (ωs : Fin (n + 1) → Fin (n + 1)),
      ‖twoSLSBootstrapVHatStarFinSucc Z X Y n ω ωs -
        twoSLSVHatStar
          (stackRegressors Z (n + 1) ω)
          (stackRegressors X (n + 1) ω)
          (stackOutcomes Y (n + 1) ω)‖ ≤ Bcov n ω ωs) :
    TendstoInBootstrapDistributionIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs => twoSLSBootstrapBetaGapFinSucc Z X Y n ω ωs)
        (multivariateGaussian (0 : EuclideanSpace ℝ k)
          (twoSLSAsymptoticVariance
            (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (scoreCovMat μ Z e)
            (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))))
        (fun z : EuclideanSpace ℝ k => (z : k → ℝ)) ∧
      TendstoInBootstrapDistributionIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs (_ : Unit) =>
          twoSLSBootstrapRobustLinearTStatFinSucc R Z X Y n ω ωs)
        (gaussianReal 0 1) (fun z : ℝ => fun _ : Unit => z) := by
  let hm := h.toJointIidMixedMomentConditions
  exact
    twoSLSBootstrap_theorem12_8_of_assumption12_2_joint_iid_mixed_moments_tail_bounds_trueScore_norm_bound
      (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y) (R := R)
      (β := β) (C := C) (Bresid := Bresid) (Bpop := Bpop)
      (Bcoef := Bcoef) (Bcov := Bcov)
      hm.toTwoSLSAssumption12_2JointIidFourthConditions h.model
      hm.omega_cross_integrable hm.omega_quadratic_integrable
      hm.sigma_cross_integrable hR hTrueBound
      hBresidTail hBresidBound hBpopTail hBpopBound
      hBcoefTail hBcoefBound hBcovTail hBcovBound

set_option linter.style.longLine false in
/-- Textbook-fourth companion to
`twoSLSBootstrap_theorem12_8_of_assumption12_2_joint_iid_mixed_moments_uniform_remainders_trueScore_norm_bound`.

This is the most compact literal-Assumption-12.2 endpoint for the current
deterministic-envelope bootstrap route: callers prove true-score boundedness
and the four concrete uniform bootstrap remainders. -/
theorem
    twoSLSBootstrap_theorem12_8_of_textbook_fourth_uniform_remainders_trueScore_norm_bound
    [IsProbabilityMeasure μ]
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {R : Matrix Unit k ℝ} {β : k → ℝ} {C : ℝ}
    (h : TwoSLSAssumption12_2JointIidTextbookFourthConditions μ Z X e Y β)
    (hR : Function.Injective Rᵀ.mulVec)
    (hTrueBound :
      ∀ᶠ n in atTop,
        ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
          ‖twoSLSBootstrapTrueRecenteredScoreStatisticFinSucc
            Z e n ω ωs‖ ≤ C)
    (hResidSmall : ∀ δ : ℝ, 0 < δ →
      ∀ᶠ n in atTop,
        ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
          ‖twoSLSBootstrapResidualSubstitutionRecenteredScoreStatisticFinSucc
            Z X Y β n ω ωs‖ < δ)
    (hPopSmall : ∀ δ : ℝ, 0 < δ →
      ∀ᶠ n in atTop,
        ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
          dist (twoSLSBootstrapLinearizedGapFinSucc Z X Y n ω ωs)
            (twoSLSBootstrapPopulationLinearizedGapFinSucc
              (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
              (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
              (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))
              Z X Y n ω ωs) < δ)
    (hCoefSmall : ∀ δ : ℝ, 0 < δ →
      ∀ᶠ n in atTop,
        ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
          dist (twoSLSBootstrapBetaGapFinSucc Z X Y n ω ωs)
            (twoSLSBootstrapLinearizedGapFinSucc Z X Y n ω ωs) < δ)
    (hCovSmall : ∀ δ : ℝ, 0 < δ →
      ∀ᶠ n in atTop,
        ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
          ‖twoSLSBootstrapVHatStarFinSucc Z X Y n ω ωs -
            twoSLSVHatStar
              (stackRegressors Z (n + 1) ω)
              (stackRegressors X (n + 1) ω)
              (stackOutcomes Y (n + 1) ω)‖ < δ) :
    TendstoInBootstrapDistributionIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs => twoSLSBootstrapBetaGapFinSucc Z X Y n ω ωs)
        (multivariateGaussian (0 : EuclideanSpace ℝ k)
          (twoSLSAsymptoticVariance
            (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (scoreCovMat μ Z e)
            (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))))
        (fun z : EuclideanSpace ℝ k => (z : k → ℝ)) ∧
      TendstoInBootstrapDistributionIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs (_ : Unit) =>
          twoSLSBootstrapRobustLinearTStatFinSucc R Z X Y n ω ωs)
        (gaussianReal 0 1) (fun z : ℝ => fun _ : Unit => z) := by
  let hm := h.toJointIidMixedMomentConditions
  exact
    twoSLSBootstrap_theorem12_8_of_assumption12_2_joint_iid_mixed_moments_uniform_remainders_trueScore_norm_bound
      (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y) (R := R)
      (β := β) (C := C)
      hm.toTwoSLSAssumption12_2JointIidFourthConditions h.model
      hm.omega_cross_integrable hm.omega_quadratic_integrable
      hm.sigma_cross_integrable hR hTrueBound hResidSmall hPopSmall
      hCoefSmall hCovSmall

set_option linter.style.longLine false in
/-- Hansen Theorem 12.8 from the established residual-substitution package,
coefficient closeness, and primitive robust-covariance resampling control.

Compared with the full empirical-process wrapper, this reuses the existing
residual-score compact-tail package instead of asking separately for
true-score tail control and residual-substitution negligibility. Compared with
the older residual-substitution/linearization wrapper, it keeps coefficient
linearization and covariance resampling at their smaller primitive layers. -/
theorem
    twoSLSBootstrap_theorem12_8_of_assumption12_2_joint_iid_mixed_moments_residualSubstitution_closeness_covariancePrimitive
    [IsProbabilityMeasure μ]
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {R : Matrix Unit k ℝ}
    (h : TwoSLSAssumption12_2JointIidFourthConditions μ Z X e)
    (β : k → ℝ)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hOmegaCross : ∀ a b : l, ∀ j : k,
      Integrable (fun ω => e 0 ω * X 0 ω j * Z 0 ω a * Z 0 ω b) μ)
    (hOmegaQuadratic : ∀ a b : l, ∀ j m : k,
      Integrable (fun ω => X 0 ω j * X 0 ω m * Z 0 ω a * Z 0 ω b) μ)
    (hSigmaCross : ∀ j : k,
      Integrable (fun ω => e 0 ω * X 0 ω j) μ)
    (hR : Function.Injective Rᵀ.mulVec)
    (hresid : TwoSLSBootstrapResidualSubstitutionInputs μ Z X Y e β)
    (hcoef :
      TwoSLSBootstrapCoefficientLinearizationClosenessInputs μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω)) Z X Y
        (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
        (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
        (scoreCovMat μ Z e)
        (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X))))
    (hcov : TwoSLSBootstrapRobustCovarianceResamplePrimitiveInputs μ Z X Y) :
    TendstoInBootstrapDistributionIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs => twoSLSBootstrapBetaGapFinSucc Z X Y n ω ωs)
        (multivariateGaussian (0 : EuclideanSpace ℝ k)
          (twoSLSAsymptoticVariance
            (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (scoreCovMat μ Z e)
            (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))))
        (fun z : EuclideanSpace ℝ k => (z : k → ℝ)) ∧
      TendstoInBootstrapDistributionIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs (_ : Unit) =>
          twoSLSBootstrapRobustLinearTStatFinSucc R Z X Y n ω ωs)
        (gaussianReal 0 1) (fun z : ℝ => fun _ : Unit => z) :=
  twoSLSBootstrap_theorem12_8_of_assumption12_2_joint_iid_mixed_moments_scoreTailPrimitiveEmpiricalProcess
    (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y) (R := R)
    h β hmodel hOmegaCross hOmegaQuadratic hSigmaCross hR
    (TwoSLSBootstrapTheorem12_8ScoreTailPrimitiveEmpiricalProcessInputs.of_residualSubstitution_closeness_covariancePrimitive
      (μ := μ) (Z := Z) (X := X) (Y := Y) (e := e) (β := β)
      (R := R) hresid hcoef hcov)

set_option linter.style.longLine false in
/-- Hansen Theorem 12.8 from joint-iid Assumption 12.2 with the residual-score
and covariance inputs kept at their narrow primitive levels.

This is the joint-iid companion to the iid/weight-WLLN primitive wrapper:
mixed moment assumptions derive the covariance-weight WLLNs, true-score tail
control plus centered residual-substitution negligibility supplies the
feasible score package, coefficient closeness supplies the linearization
package, and primitive covariance-resampling tails supply robust
studentization. -/
theorem
    twoSLSBootstrap_theorem12_8_of_assumption12_2_joint_iid_mixed_moments_residualSubstitutionNegligibility_trueScoreTail_closeness_covariancePrimitive
    [IsProbabilityMeasure μ]
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {R : Matrix Unit k ℝ}
    (h : TwoSLSAssumption12_2JointIidFourthConditions μ Z X e)
    (β : k → ℝ)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hOmegaCross : ∀ a b : l, ∀ j : k,
      Integrable (fun ω => e 0 ω * X 0 ω j * Z 0 ω a * Z 0 ω b) μ)
    (hOmegaQuadratic : ∀ a b : l, ∀ j m : k,
      Integrable (fun ω => X 0 ω j * X 0 ω m * Z 0 ω a * Z 0 ω b) μ)
    (hSigmaCross : ∀ j : k,
      Integrable (fun ω => e 0 ω * X 0 ω j) μ)
    (hR : Function.Injective Rᵀ.mulVec)
    (hresid :
      TwoSLSBootstrapResidualSubstitutionNegligibilityInputs μ Z X Y β)
    (hTrueTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set (EuclideanSpace ℝ l), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω =>
            (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω) n ω).real
              {ωs |
                twoSLSBootstrapTrueRecenteredScoreStatisticFinSucc
                  Z e n ω ωs ∉ K})
          atTop (fun _ => 0))
    (hcoef :
      TwoSLSBootstrapCoefficientLinearizationClosenessInputs μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω)) Z X Y
        (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
        (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
        (scoreCovMat μ Z e)
        (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X))))
    (hcov : TwoSLSBootstrapRobustCovarianceResamplePrimitiveInputs μ Z X Y) :
    TendstoInBootstrapDistributionIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs => twoSLSBootstrapBetaGapFinSucc Z X Y n ω ωs)
        (multivariateGaussian (0 : EuclideanSpace ℝ k)
          (twoSLSAsymptoticVariance
            (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (scoreCovMat μ Z e)
            (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))))
        (fun z : EuclideanSpace ℝ k => (z : k → ℝ)) ∧
      TendstoInBootstrapDistributionIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs (_ : Unit) =>
          twoSLSBootstrapRobustLinearTStatFinSucc R Z X Y n ω ωs)
        (gaussianReal 0 1) (fun z : ℝ => fun _ : Unit => z) :=
  twoSLSBootstrap_theorem12_8_of_assumption12_2_joint_iid_mixed_moments_residualSubstitution_closeness_covariancePrimitive
    (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y) (R := R)
    h β hmodel hOmegaCross hOmegaQuadratic hSigmaCross hR
    (hresid.toResidualSubstitutionInputs_of_trueScore_compactTail
      (μ := μ) (Z := Z) (X := X) (Y := Y) (e := e) (β := β)
      hmodel hTrueTail)
    hcoef hcov

set_option linter.style.longLine false in
/-- Hansen Theorem 12.8 from joint-iid Assumption 12.2, with the residual-score
input supplied through the established residual-substitution package.

Compared with
`twoSLSBootstrap_theorem12_8_of_assumption12_2_joint_iid_mixed_moments_empiricalProcess`,
this wrapper removes the artificial need to build
`TwoSLSBootstrapTheorem12_8EmpiricalProcessInputs` manually.  The remaining
premises are still the genuine bootstrap empirical-process gaps:
residual-substitution negligibility, true-score tail control, coefficient
linearization, and robust covariance resampling closeness. -/
theorem
    twoSLSBootstrap_theorem12_8_of_assumption12_2_joint_iid_mixed_moments_residualSubstitution_linearization_resampleCloseness
    [IsProbabilityMeasure μ]
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {R : Matrix Unit k ℝ}
    (h : TwoSLSAssumption12_2JointIidFourthConditions μ Z X e)
    (β : k → ℝ)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hOmegaCross : ∀ a b : l, ∀ j : k,
      Integrable (fun ω => e 0 ω * X 0 ω j * Z 0 ω a * Z 0 ω b) μ)
    (hOmegaQuadratic : ∀ a b : l, ∀ j m : k,
      Integrable (fun ω => X 0 ω j * X 0 ω m * Z 0 ω a * Z 0 ω b) μ)
    (hSigmaCross : ∀ j : k,
      Integrable (fun ω => e 0 ω * X 0 ω j) μ)
    (hR : Function.Injective Rᵀ.mulVec)
    (hresid : TwoSLSBootstrapResidualSubstitutionInputs μ Z X Y e β)
    (hlin : TwoSLSBootstrapCoefficientLinearizationInputs μ
      (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω)) Z X Y
      (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
      (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
      (scoreCovMat μ Z e)
      (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X))))
    (hV : TwoSLSBootstrapRobustCovarianceResampleCloseness μ Z X Y) :
    TendstoInBootstrapDistributionIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs => twoSLSBootstrapBetaGapFinSucc Z X Y n ω ωs)
        (multivariateGaussian (0 : EuclideanSpace ℝ k)
          (twoSLSAsymptoticVariance
            (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (scoreCovMat μ Z e)
            (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))))
        (fun z : EuclideanSpace ℝ k => (z : k → ℝ)) ∧
      TendstoInBootstrapDistributionIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs (_ : Unit) =>
          twoSLSBootstrapRobustLinearTStatFinSucc R Z X Y n ω ωs)
        (gaussianReal 0 1) (fun z : ℝ => fun _ : Unit => z) :=
  twoSLSBootstrap_theorem12_8_of_assumption12_2_joint_iid_mixed_moments_empiricalProcess
    (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y) (R := R)
    h β hmodel hOmegaCross hOmegaQuadratic hSigmaCross hR
    (TwoSLSBootstrapTheorem12_8EmpiricalProcessInputs.of_residualSubstitution_linearization_resampleCloseness
      (μ := μ) (Z := Z) (X := X) (Y := Y) (e := e) (β := β)
      (R := R) hresid hlin hV)

set_option linter.style.longLine false in
/-- Hansen Theorem 12.8, percentile-`t` interval coverage from the
Assumption-12.2-facing ordinary-bootstrap endpoint.

This is the interval-validity face of Theorem 12.8.  It composes the existing
coefficient and robust bootstrap t-ratio conclusions with Chapter 10's
percentile-`t` coverage theorem.  The remaining premises are the sample
t-ratio limit and the quantile calibration/measurability inputs for the
bootstrap t-ratio, not the final coverage conclusion. -/
theorem
    twoSLSBootstrapRobustPercentileTCIEventFinSucc_theorem12_8_of_assumption12_2_weight_wlln
    [IsProbabilityMeasure μ]
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {R : Matrix Unit k ℝ} {β : k → ℝ} {q α : ℝ}
    (h : TwoSLSAssumption12_2IidFourthConditions μ Z X e)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hw : TwoSLSCovarianceWeightWLLNConditions μ Z X e)
    (hcoef :
      TwoSLSBootstrapFormulaAsymptoticNormalConditions μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω)) Z X Y
        (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
        (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
        (scoreCovMat μ Z e)
        (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X))))
    (hseθ : 0 <
      linearRestrictionStdError R
        (twoSLSAsymptoticVariance
          (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
          (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
          (scoreCovMat μ Z e)
          (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))))
    (hsampleSe : ∀ n ω,
      0 < twoSLSRobustLinearRestrictionEstimatorStdErrorFinSucc R Z X Y n ω)
    (htstat :
      TendstoInDistribution
        (fun n ω =>
          percentileTStatistic (linearRestrictionEstimate R β)
            (twoSLSLinearRestrictionEstimateFinSucc R Z X Y n ω)
            (twoSLSRobustLinearRestrictionEstimatorStdErrorFinSucc R Z X Y n ω))
        atTop (fun x : ℝ => x) (fun _ => μ) (gaussianReal 0 1))
    (hT_meas : ∀ n ω,
      Measurable
        (fun ωs => twoSLSBootstrapLinearRestrictionStatisticFinSucc R Z X Y n ω ωs))
    (hse_meas : ∀ n ω,
      Measurable
        (fun ωs =>
          twoSLSBootstrapRobustLinearRestrictionStdErrorFinSucc R Z X Y n ω ωs))
    (hTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set (ℝ × ℝ), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω =>
            (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω) n ω).real
              {ωs |
                (twoSLSBootstrapLinearRestrictionStatisticFinSucc R Z X Y n ω ωs,
                  linearRestrictionStdError R
                    (twoSLSAsymptoticVariance
                      (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
                      (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
                      (scoreCovMat μ Z e)
                      (twoSLSCombinedQZX
                        (popGram μ (twoSLSCombinedRegressors Z X))))) ∉ K})
          atTop (fun _ => 0) ∧
        TendstoInMeasure μ
          (fun n ω =>
            (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω) n ω).real
              {ωs |
                (twoSLSBootstrapLinearRestrictionStatisticFinSucc R Z X Y n ω ωs,
                  twoSLSBootstrapRobustLinearRestrictionStdErrorFinSucc
                    R Z X Y n ω ωs) ∉ K})
          atTop (fun _ => 0))
    (hV_resample_close :
      TendstoInBootstrapProbabilityIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs =>
          twoSLSBootstrapVHatStarFinSucc Z X Y n ω ωs -
            twoSLSVHatStar
              (stackRegressors Z (n + 1) ω) (stackRegressors X (n + 1) ω)
              (stackOutcomes Y (n + 1) ω))
        (fun _ => 0))
    (hα_pos : 0 < α) (hα_lt_one : α < 1)
    (hstrict : StrictMono (fun x => cdf (gaussianReal 0 1) x))
    (hlower_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed
            (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
            (fun n ω ωs =>
              twoSLSBootstrapRobustLinearTStatFinSucc R Z X Y n ω ωs)
            (α / 2) n) μ)
    (hupper_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed
            (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
            (fun n ω ωs =>
              twoSLSBootstrapRobustLinearTStatFinSucc R Z X Y n ω ωs)
            (1 - α / 2) n) μ)
    (hq_nonneg : 0 ≤ q)
    (hcdfLower : cdf (gaussianReal 0 1) (-q) = α / 2)
    (hcdfUpper : cdf (gaussianReal 0 1) q = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω |
          twoSLSBootstrapRobustPercentileTCIEventFinSucc
            R Z X Y β α n ω})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) := by
  have hTstar :
      TendstoInBootstrapDistributionIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs (_ : Unit) =>
          twoSLSBootstrapRobustLinearTStatFinSucc R Z X Y n ω ωs)
        (gaussianReal 0 1) (fun z : ℝ => fun _ : Unit => z) :=
    (twoSLSBootstrap_theorem12_8_of_assumption12_2_weight_wlln
      (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y) (R := R)
      h β hmodel hw hcoef hseθ hT_meas hse_meas hTail hV_resample_close).2
  have hTstar_meas : ∀ n ω,
      AEMeasurable
        (fun ωs => twoSLSBootstrapRobustLinearTStatFinSucc R Z X Y n ω ωs)
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω) n ω) := by
    intro n ω
    simpa [twoSLSBootstrapRobustLinearTStatFinSucc,
      twoSLSBootstrapLinearTStatFinSucc] using
      ((hT_meas n ω).div (hse_meas n ω)).aemeasurable
  exact
    twoSLSBootstrapRobustPercentileTCIEventFinSucc_tendsto_one_sub_alpha_uniform
      (μ := μ) (Z := Z) (X := X) (Y := Y) (R := R) (β := β)
      (q := q) (α := α)
      hsampleSe htstat hTstar_meas hTstar hα_pos hα_lt_one hstrict
      hlower_meas hupper_meas hq_nonneg hcdfLower hcdfUpper

set_option linter.style.longLine false in
/-- Percentile-`t` coverage from the tightened iid/weight-WLLN Theorem 12.8
input surface.

The bootstrap robust t-ratio limit is derived from residual substitution,
coefficient linearization, full-rank one-row restriction nondegeneracy, and
robust covariance resampling. The remaining premises are the sample-side
t-ratio limit and the usual quantile calibration/measurability inputs needed
by the Chapter 10 percentile-`t` coverage theorem. -/
theorem
    twoSLSBootstrapRobustPercentileTCIEventFinSucc_theorem12_8_of_assumption12_2_weight_wlln_residualSubstitution_linearization_fullRank_resampleCloseness
    [IsProbabilityMeasure μ]
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {R : Matrix Unit k ℝ} {β : k → ℝ} {q α : ℝ}
    (h : TwoSLSAssumption12_2IidFourthConditions μ Z X e)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hw : TwoSLSCovarianceWeightWLLNConditions μ Z X e)
    (hresid : TwoSLSBootstrapResidualSubstitutionInputs μ Z X Y e β)
    (hlin : TwoSLSBootstrapCoefficientLinearizationInputs μ
      (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω)) Z X Y
      (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
      (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
      (scoreCovMat μ Z e)
      (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X))))
    (hR : Function.Injective Rᵀ.mulVec)
    (hV : TwoSLSBootstrapRobustCovarianceResampleCloseness μ Z X Y)
    (hsampleSe : ∀ n ω,
      0 < twoSLSRobustLinearRestrictionEstimatorStdErrorFinSucc R Z X Y n ω)
    (htstat :
      TendstoInDistribution
        (fun n ω =>
          percentileTStatistic (linearRestrictionEstimate R β)
            (twoSLSLinearRestrictionEstimateFinSucc R Z X Y n ω)
            (twoSLSRobustLinearRestrictionEstimatorStdErrorFinSucc R Z X Y n ω))
        atTop (fun x : ℝ => x) (fun _ => μ) (gaussianReal 0 1))
    (hα_pos : 0 < α) (hα_lt_one : α < 1)
    (hstrict : StrictMono (fun x => cdf (gaussianReal 0 1) x))
    (hlower_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed
            (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
            (fun n ω ωs =>
              twoSLSBootstrapRobustLinearTStatFinSucc R Z X Y n ω ωs)
            (α / 2) n) μ)
    (hupper_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed
            (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
            (fun n ω ωs =>
              twoSLSBootstrapRobustLinearTStatFinSucc R Z X Y n ω ωs)
            (1 - α / 2) n) μ)
    (hq_nonneg : 0 ≤ q)
    (hcdfLower : cdf (gaussianReal 0 1) (-q) = α / 2)
    (hcdfUpper : cdf (gaussianReal 0 1) q = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω |
          twoSLSBootstrapRobustPercentileTCIEventFinSucc
            R Z X Y β α n ω})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) := by
  have hTstar :
      TendstoInBootstrapDistributionIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs (_ : Unit) =>
          twoSLSBootstrapRobustLinearTStatFinSucc R Z X Y n ω ωs)
        (gaussianReal 0 1) (fun z : ℝ => fun _ : Unit => z) :=
    (twoSLSBootstrap_theorem12_8_of_assumption12_2_weight_wlln_residualSubstitution_linearization_fullRank_resampleCloseness
      (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y) (R := R)
      h β hmodel hw hresid hlin hR hV).2
  have hTstar_meas : ∀ n ω,
      AEMeasurable
        (fun ωs => twoSLSBootstrapRobustLinearTStatFinSucc R Z X Y n ω ωs)
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω) n ω) := by
    intro n ω
    have hT_meas :
        Measurable
          (fun ωs =>
            twoSLSBootstrapLinearRestrictionStatisticFinSucc R Z X Y n ω ωs) := by
      fun_prop
    have hse_meas :
        Measurable
          (fun ωs =>
            twoSLSBootstrapRobustLinearRestrictionStdErrorFinSucc
              R Z X Y n ω ωs) := by
      fun_prop
    simpa [twoSLSBootstrapRobustLinearTStatFinSucc,
      twoSLSBootstrapLinearTStatFinSucc] using
      (hT_meas.div hse_meas).aemeasurable
  exact
    twoSLSBootstrapRobustPercentileTCIEventFinSucc_tendsto_one_sub_alpha_uniform
      (μ := μ) (Z := Z) (X := X) (Y := Y) (R := R) (β := β)
      (q := q) (α := α)
      hsampleSe htstat hTstar_meas hTstar hα_pos hα_lt_one hstrict
      hlower_meas hupper_meas hq_nonneg hcdfLower hcdfUpper

set_option linter.style.longLine false in
/-- Percentile-`t` coverage from the single empirical-process package used by
the bundled Hansen Theorem 12.8 endpoint.

This wrapper derives the covariance weight WLLN from the joint iid Assumption
12.2 rows and mixed moment hypotheses, then applies the tightened
iid/weight-WLLN coverage theorem. The empirical-process package still contains
the exact remaining bootstrap stochastic gaps: true-score compact-tail
control, residual-substitution negligibility, coefficient linearization, and
robust covariance resampling closeness. -/
theorem
    twoSLSBootstrapRobustPercentileTCIEventFinSucc_theorem12_8_of_assumption12_2_joint_iid_mixed_moments_empiricalProcess
    [IsProbabilityMeasure μ]
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {R : Matrix Unit k ℝ} {β : k → ℝ} {q α : ℝ}
    (h : TwoSLSAssumption12_2JointIidFourthConditions μ Z X e)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hOmegaCross : ∀ a b : l, ∀ j : k,
      Integrable (fun ω => e 0 ω * X 0 ω j * Z 0 ω a * Z 0 ω b) μ)
    (hOmegaQuadratic : ∀ a b : l, ∀ j m : k,
      Integrable (fun ω => X 0 ω j * X 0 ω m * Z 0 ω a * Z 0 ω b) μ)
    (hSigmaCross : ∀ j : k,
      Integrable (fun ω => e 0 ω * X 0 ω j) μ)
    (hR : Function.Injective Rᵀ.mulVec)
    (hboot :
      TwoSLSBootstrapTheorem12_8EmpiricalProcessInputs μ Z X Y e β R)
    (hsampleSe : ∀ n ω,
      0 < twoSLSRobustLinearRestrictionEstimatorStdErrorFinSucc R Z X Y n ω)
    (htstat :
      TendstoInDistribution
        (fun n ω =>
          percentileTStatistic (linearRestrictionEstimate R β)
            (twoSLSLinearRestrictionEstimateFinSucc R Z X Y n ω)
            (twoSLSRobustLinearRestrictionEstimatorStdErrorFinSucc R Z X Y n ω))
        atTop (fun x : ℝ => x) (fun _ => μ) (gaussianReal 0 1))
    (hα_pos : 0 < α) (hα_lt_one : α < 1)
    (hstrict : StrictMono (fun x => cdf (gaussianReal 0 1) x))
    (hlower_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed
            (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
            (fun n ω ωs =>
              twoSLSBootstrapRobustLinearTStatFinSucc R Z X Y n ω ωs)
            (α / 2) n) μ)
    (hupper_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed
            (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
            (fun n ω ωs =>
              twoSLSBootstrapRobustLinearTStatFinSucc R Z X Y n ω ωs)
            (1 - α / 2) n) μ)
    (hq_nonneg : 0 ≤ q)
    (hcdfLower : cdf (gaussianReal 0 1) (-q) = α / 2)
    (hcdfUpper : cdf (gaussianReal 0 1) q = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω |
          twoSLSBootstrapRobustPercentileTCIEventFinSucc
            R Z X Y β α n ω})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) := by
  let hIid : TwoSLSAssumption12_2IidFourthConditions μ Z X e :=
    h.toIidFourthConditions
  let hw : TwoSLSCovarianceWeightWLLNConditions μ Z X e :=
    TwoSLSCovarianceWeightWLLNConditions.of_joint_iid
      (μ := μ) (Z := Z) (X := X) (e := e)
      h.joint_iIndep h.joint_identDistrib
      hOmegaCross hOmegaQuadratic hSigmaCross
  have hresid : TwoSLSBootstrapResidualSubstitutionInputs μ Z X Y e β :=
    hboot.residual_negligibility.toResidualSubstitutionInputs_of_trueScore_compactTail
      (μ := μ) (Z := Z) (X := X) (Y := Y) (e := e) (β := β)
      hmodel hboot.true_score_tail
  exact
    twoSLSBootstrapRobustPercentileTCIEventFinSucc_theorem12_8_of_assumption12_2_weight_wlln_residualSubstitution_linearization_fullRank_resampleCloseness
      (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y) (R := R)
      hIid hmodel hw hresid hboot.coefficient_linearization hR
      hboot.covariance_resample hsampleSe htstat hα_pos hα_lt_one
      hstrict hlower_meas hupper_meas hq_nonneg hcdfLower hcdfUpper

set_option linter.style.longLine false in
/-- Percentile-`t` coverage for Hansen Theorem 12.8 from joint-iid Assumption
12.2 and the direct residual-substitution/coefficient-linearization bootstrap
input surface.

This is the coverage companion to
`twoSLSBootstrap_theorem12_8_of_assumption12_2_joint_iid_mixed_moments_residualSubstitution_linearization_resampleCloseness`.
It still leaves the sample-side robust t-ratio limit and bootstrap quantile
calibration/measurability as explicit Chapter-10 percentile-`t` inputs. -/
theorem
    twoSLSBootstrapRobustPercentileTCIEventFinSucc_theorem12_8_of_assumption12_2_joint_iid_mixed_moments_residualSubstitution_linearization_resampleCloseness
    [IsProbabilityMeasure μ]
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {R : Matrix Unit k ℝ} {β : k → ℝ} {q α : ℝ}
    (h : TwoSLSAssumption12_2JointIidFourthConditions μ Z X e)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hOmegaCross : ∀ a b : l, ∀ j : k,
      Integrable (fun ω => e 0 ω * X 0 ω j * Z 0 ω a * Z 0 ω b) μ)
    (hOmegaQuadratic : ∀ a b : l, ∀ j m : k,
      Integrable (fun ω => X 0 ω j * X 0 ω m * Z 0 ω a * Z 0 ω b) μ)
    (hSigmaCross : ∀ j : k,
      Integrable (fun ω => e 0 ω * X 0 ω j) μ)
    (hR : Function.Injective Rᵀ.mulVec)
    (hresid : TwoSLSBootstrapResidualSubstitutionInputs μ Z X Y e β)
    (hlin : TwoSLSBootstrapCoefficientLinearizationInputs μ
      (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω)) Z X Y
      (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
      (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
      (scoreCovMat μ Z e)
      (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X))))
    (hV : TwoSLSBootstrapRobustCovarianceResampleCloseness μ Z X Y)
    (hsampleSe : ∀ n ω,
      0 < twoSLSRobustLinearRestrictionEstimatorStdErrorFinSucc R Z X Y n ω)
    (htstat :
      TendstoInDistribution
        (fun n ω =>
          percentileTStatistic (linearRestrictionEstimate R β)
            (twoSLSLinearRestrictionEstimateFinSucc R Z X Y n ω)
            (twoSLSRobustLinearRestrictionEstimatorStdErrorFinSucc R Z X Y n ω))
        atTop (fun x : ℝ => x) (fun _ => μ) (gaussianReal 0 1))
    (hα_pos : 0 < α) (hα_lt_one : α < 1)
    (hstrict : StrictMono (fun x => cdf (gaussianReal 0 1) x))
    (hlower_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed
            (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
            (fun n ω ωs =>
              twoSLSBootstrapRobustLinearTStatFinSucc R Z X Y n ω ωs)
            (α / 2) n) μ)
    (hupper_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed
            (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
            (fun n ω ωs =>
              twoSLSBootstrapRobustLinearTStatFinSucc R Z X Y n ω ωs)
            (1 - α / 2) n) μ)
    (hq_nonneg : 0 ≤ q)
    (hcdfLower : cdf (gaussianReal 0 1) (-q) = α / 2)
    (hcdfUpper : cdf (gaussianReal 0 1) q = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω |
          twoSLSBootstrapRobustPercentileTCIEventFinSucc
            R Z X Y β α n ω})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) :=
  twoSLSBootstrapRobustPercentileTCIEventFinSucc_theorem12_8_of_assumption12_2_joint_iid_mixed_moments_empiricalProcess
    (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y) (R := R)
    h hmodel hOmegaCross hOmegaQuadratic hSigmaCross hR
    (TwoSLSBootstrapTheorem12_8EmpiricalProcessInputs.of_residualSubstitution_linearization_resampleCloseness
      (μ := μ) (Z := Z) (X := X) (Y := Y) (e := e) (β := β)
      (R := R) hresid hlin hV)
    hsampleSe htstat hα_pos hα_lt_one hstrict hlower_meas hupper_meas
    hq_nonneg hcdfLower hcdfUpper

set_option linter.style.longLine false in
/-- Percentile-`t` coverage from the generic Assumption-12.2/weight-WLLN
bootstrap endpoint and named interval-side inputs.

This is the compatibility version of
`twoSLSBootstrapRobustPercentileTCIEventFinSucc_theorem12_8_of_assumption12_2_weight_wlln`
whose sample t-ratio, standard-error positivity, and quantile calibration
premises are packaged rather than passed as unrelated arguments. -/
theorem
    twoSLSBootstrapRobustPercentileTCIEventFinSucc_theorem12_8_of_assumption12_2_weight_wlln_coverageInputs
    [IsProbabilityMeasure μ]
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {R : Matrix Unit k ℝ} {β : k → ℝ} {q α : ℝ}
    (h : TwoSLSAssumption12_2IidFourthConditions μ Z X e)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hw : TwoSLSCovarianceWeightWLLNConditions μ Z X e)
    (hcoef :
      TwoSLSBootstrapFormulaAsymptoticNormalConditions μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω)) Z X Y
        (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
        (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
        (scoreCovMat μ Z e)
        (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X))))
    (hseθ : 0 <
      linearRestrictionStdError R
        (twoSLSAsymptoticVariance
          (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
          (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
          (scoreCovMat μ Z e)
          (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))))
    (hT_meas : ∀ n ω,
      Measurable
        (fun ωs => twoSLSBootstrapLinearRestrictionStatisticFinSucc R Z X Y n ω ωs))
    (hse_meas : ∀ n ω,
      Measurable
        (fun ωs =>
          twoSLSBootstrapRobustLinearRestrictionStdErrorFinSucc R Z X Y n ω ωs))
    (hTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set (ℝ × ℝ), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω =>
            (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω) n ω).real
              {ωs |
                (twoSLSBootstrapLinearRestrictionStatisticFinSucc R Z X Y n ω ωs,
                  linearRestrictionStdError R
                    (twoSLSAsymptoticVariance
                      (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
                      (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
                      (scoreCovMat μ Z e)
                      (twoSLSCombinedQZX
                        (popGram μ (twoSLSCombinedRegressors Z X))))) ∉ K})
          atTop (fun _ => 0) ∧
        TendstoInMeasure μ
          (fun n ω =>
            (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω) n ω).real
              {ωs |
                (twoSLSBootstrapLinearRestrictionStatisticFinSucc R Z X Y n ω ωs,
                  twoSLSBootstrapRobustLinearRestrictionStdErrorFinSucc
                    R Z X Y n ω ωs) ∉ K})
          atTop (fun _ => 0))
    (hV_resample_close :
      TendstoInBootstrapProbabilityIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs =>
          twoSLSBootstrapVHatStarFinSucc Z X Y n ω ωs -
            twoSLSVHatStar
              (stackRegressors Z (n + 1) ω) (stackRegressors X (n + 1) ω)
              (stackOutcomes Y (n + 1) ω))
        (fun _ => 0))
    (hcoverage :
      TwoSLSBootstrapRobustPercentileTCoverageInputs
        μ Z X Y β R q α) :
    Tendsto
      (fun n =>
        μ {ω |
          twoSLSBootstrapRobustPercentileTCIEventFinSucc
            R Z X Y β α n ω})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) := by
  have hTstar :
      TendstoInBootstrapDistributionIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs (_ : Unit) =>
          twoSLSBootstrapRobustLinearTStatFinSucc R Z X Y n ω ωs)
        (gaussianReal 0 1) (fun z : ℝ => fun _ : Unit => z) :=
    (twoSLSBootstrap_theorem12_8_of_assumption12_2_weight_wlln
      (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y) (R := R)
      h β hmodel hw hcoef hseθ hT_meas hse_meas hTail hV_resample_close).2
  exact
    twoSLSBootstrapRobustPercentileTCIEventFinSucc_tendsto_one_sub_alpha_uniform_of_coverageInputs
      (μ := μ) (Z := Z) (X := X) (Y := Y) (R := R) (β := β)
      (q := q) (α := α) hTstar hcoverage

set_option linter.style.longLine false in
/-- Percentile-`t` coverage from the generic Assumption-12.2/weight-WLLN
bootstrap endpoint and named interval-side inputs, with finite-resample
bootstrap t-ratio measurability derived automatically. -/
theorem
    twoSLSBootstrapRobustPercentileTCIEventFinSucc_theorem12_8_of_assumption12_2_weight_wlln_coverageInputs_autoMeas
    [IsProbabilityMeasure μ]
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {R : Matrix Unit k ℝ} {β : k → ℝ} {q α : ℝ}
    (h : TwoSLSAssumption12_2IidFourthConditions μ Z X e)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hw : TwoSLSCovarianceWeightWLLNConditions μ Z X e)
    (hcoef :
      TwoSLSBootstrapFormulaAsymptoticNormalConditions μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω)) Z X Y
        (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
        (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
        (scoreCovMat μ Z e)
        (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X))))
    (hseθ : 0 <
      linearRestrictionStdError R
        (twoSLSAsymptoticVariance
          (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
          (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
          (scoreCovMat μ Z e)
          (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))))
    (hTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set (ℝ × ℝ), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω =>
            (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω) n ω).real
              {ωs |
                (twoSLSBootstrapLinearRestrictionStatisticFinSucc R Z X Y n ω ωs,
                  linearRestrictionStdError R
                    (twoSLSAsymptoticVariance
                      (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
                      (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
                      (scoreCovMat μ Z e)
                      (twoSLSCombinedQZX
                        (popGram μ (twoSLSCombinedRegressors Z X))))) ∉ K})
          atTop (fun _ => 0) ∧
        TendstoInMeasure μ
          (fun n ω =>
            (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω) n ω).real
              {ωs |
                (twoSLSBootstrapLinearRestrictionStatisticFinSucc R Z X Y n ω ωs,
                  twoSLSBootstrapRobustLinearRestrictionStdErrorFinSucc
                    R Z X Y n ω ωs) ∉ K})
          atTop (fun _ => 0))
    (hV_resample_close :
      TendstoInBootstrapProbabilityIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs =>
          twoSLSBootstrapVHatStarFinSucc Z X Y n ω ωs -
            twoSLSVHatStar
              (stackRegressors Z (n + 1) ω) (stackRegressors X (n + 1) ω)
              (stackOutcomes Y (n + 1) ω))
        (fun _ => 0))
    (hcoverage :
      TwoSLSBootstrapRobustPercentileTCoverageInputs
        μ Z X Y β R q α) :
    Tendsto
      (fun n =>
        μ {ω |
          twoSLSBootstrapRobustPercentileTCIEventFinSucc
            R Z X Y β α n ω})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) :=
  twoSLSBootstrapRobustPercentileTCIEventFinSucc_theorem12_8_of_assumption12_2_weight_wlln_coverageInputs
    (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y) (R := R)
    h hmodel hw hcoef hseθ
    (fun n ω =>
      twoSLSBootstrapLinearRestrictionStatisticFinSucc_measurable
        (R := R) (Z := Z) (X := X) (Y := Y) n ω)
    (fun n ω =>
      twoSLSBootstrapRobustLinearRestrictionStdErrorFinSucc_measurable
        (R := R) (Z := Z) (X := X) (Y := Y) n ω)
    hTail hV_resample_close hcoverage

set_option linter.style.longLine false in
/-- Percentile-`t` coverage from the tightened full-rank Theorem 12.8
bootstrap endpoint and named interval-side inputs. -/
theorem
    twoSLSBootstrapRobustPercentileTCIEventFinSucc_theorem12_8_of_assumption12_2_weight_wlln_residualSubstitution_linearization_fullRank_resampleCloseness_coverageInputs
    [IsProbabilityMeasure μ]
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {R : Matrix Unit k ℝ} {β : k → ℝ} {q α : ℝ}
    (h : TwoSLSAssumption12_2IidFourthConditions μ Z X e)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hw : TwoSLSCovarianceWeightWLLNConditions μ Z X e)
    (hresid : TwoSLSBootstrapResidualSubstitutionInputs μ Z X Y e β)
    (hlin : TwoSLSBootstrapCoefficientLinearizationInputs μ
      (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω)) Z X Y
      (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
      (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
      (scoreCovMat μ Z e)
      (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X))))
    (hR : Function.Injective Rᵀ.mulVec)
    (hV : TwoSLSBootstrapRobustCovarianceResampleCloseness μ Z X Y)
    (hcoverage :
      TwoSLSBootstrapRobustPercentileTCoverageInputs
        μ Z X Y β R q α) :
    Tendsto
      (fun n =>
        μ {ω |
          twoSLSBootstrapRobustPercentileTCIEventFinSucc
            R Z X Y β α n ω})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) := by
  have hTstar :
      TendstoInBootstrapDistributionIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs (_ : Unit) =>
          twoSLSBootstrapRobustLinearTStatFinSucc R Z X Y n ω ωs)
        (gaussianReal 0 1) (fun z : ℝ => fun _ : Unit => z) :=
    (twoSLSBootstrap_theorem12_8_of_assumption12_2_weight_wlln_residualSubstitution_linearization_fullRank_resampleCloseness
      (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y) (R := R)
      h β hmodel hw hresid hlin hR hV).2
  exact
    twoSLSBootstrapRobustPercentileTCIEventFinSucc_tendsto_one_sub_alpha_uniform_of_coverageInputs
      (μ := μ) (Z := Z) (X := X) (Y := Y) (R := R) (β := β)
      (q := q) (α := α) hTstar hcoverage

set_option linter.style.longLine false in
/-- Percentile-`t` coverage from the joint-iid empirical-process Theorem 12.8
endpoint and named interval-side inputs. -/
theorem
    twoSLSBootstrapRobustPercentileTCIEventFinSucc_theorem12_8_of_assumption12_2_joint_iid_mixed_moments_empiricalProcess_coverageInputs
    [IsProbabilityMeasure μ]
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {R : Matrix Unit k ℝ} {β : k → ℝ} {q α : ℝ}
    (h : TwoSLSAssumption12_2JointIidFourthConditions μ Z X e)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hOmegaCross : ∀ a b : l, ∀ j : k,
      Integrable (fun ω => e 0 ω * X 0 ω j * Z 0 ω a * Z 0 ω b) μ)
    (hOmegaQuadratic : ∀ a b : l, ∀ j m : k,
      Integrable (fun ω => X 0 ω j * X 0 ω m * Z 0 ω a * Z 0 ω b) μ)
    (hSigmaCross : ∀ j : k,
      Integrable (fun ω => e 0 ω * X 0 ω j) μ)
    (hR : Function.Injective Rᵀ.mulVec)
    (hboot :
      TwoSLSBootstrapTheorem12_8EmpiricalProcessInputs μ Z X Y e β R)
    (hcoverage :
      TwoSLSBootstrapRobustPercentileTCoverageInputs
        μ Z X Y β R q α) :
    Tendsto
      (fun n =>
        μ {ω |
          twoSLSBootstrapRobustPercentileTCIEventFinSucc
            R Z X Y β α n ω})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) := by
  have hTstar :
      TendstoInBootstrapDistributionIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs (_ : Unit) =>
          twoSLSBootstrapRobustLinearTStatFinSucc R Z X Y n ω ωs)
        (gaussianReal 0 1) (fun z : ℝ => fun _ : Unit => z) :=
    (twoSLSBootstrap_theorem12_8_of_assumption12_2_joint_iid_mixed_moments_empiricalProcess
      (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y) (R := R)
      h β hmodel hOmegaCross hOmegaQuadratic hSigmaCross hR hboot).2
  exact
    twoSLSBootstrapRobustPercentileTCIEventFinSucc_tendsto_one_sub_alpha_uniform_of_coverageInputs
      (μ := μ) (Z := Z) (X := X) (Y := Y) (R := R) (β := β)
      (q := q) (α := α) hTstar hcoverage

set_option linter.style.longLine false in
/-- Percentile-`t` coverage from joint-iid Assumption 12.2, primitive
bootstrap empirical-process assumptions, and named interval-side inputs. -/
theorem
    twoSLSBootstrapRobustPercentileTCIEventFinSucc_theorem12_8_of_assumption12_2_joint_iid_mixed_moments_primitiveEmpiricalProcess_coverageInputs
    [IsProbabilityMeasure μ]
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {R : Matrix Unit k ℝ} {β : k → ℝ} {q α : ℝ}
    (h : TwoSLSAssumption12_2JointIidFourthConditions μ Z X e)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hOmegaCross : ∀ a b : l, ∀ j : k,
      Integrable (fun ω => e 0 ω * X 0 ω j * Z 0 ω a * Z 0 ω b) μ)
    (hOmegaQuadratic : ∀ a b : l, ∀ j m : k,
      Integrable (fun ω => X 0 ω j * X 0 ω m * Z 0 ω a * Z 0 ω b) μ)
    (hSigmaCross : ∀ j : k,
      Integrable (fun ω => e 0 ω * X 0 ω j) μ)
    (hR : Function.Injective Rᵀ.mulVec)
    (hboot :
      TwoSLSBootstrapTheorem12_8PrimitiveEmpiricalProcessInputs
        μ Z X Y e β R)
    (hcoverage :
      TwoSLSBootstrapRobustPercentileTCoverageInputs
        μ Z X Y β R q α) :
    Tendsto
      (fun n =>
        μ {ω |
          twoSLSBootstrapRobustPercentileTCIEventFinSucc
            R Z X Y β α n ω})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) := by
  have hTstar :
      TendstoInBootstrapDistributionIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs (_ : Unit) =>
          twoSLSBootstrapRobustLinearTStatFinSucc R Z X Y n ω ωs)
        (gaussianReal 0 1) (fun z : ℝ => fun _ : Unit => z) :=
    (twoSLSBootstrap_theorem12_8_of_assumption12_2_joint_iid_mixed_moments_primitiveEmpiricalProcess
      (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y) (R := R)
      h β hmodel hOmegaCross hOmegaQuadratic hSigmaCross hR hboot).2
  exact
    twoSLSBootstrapRobustPercentileTCIEventFinSucc_tendsto_one_sub_alpha_uniform_of_coverageInputs
      (μ := μ) (Z := Z) (X := X) (Y := Y) (R := R) (β := β)
      (q := q) (α := α) hTstar hcoverage

set_option linter.style.longLine false in
/-- Percentile-`t` coverage from joint-iid Assumption 12.2, the score-tail
primitive bootstrap empirical-process package, and named interval-side inputs.

This is the coverage analogue of
`twoSLSBootstrap_theorem12_8_of_assumption12_2_joint_iid_mixed_moments_scoreTailPrimitiveEmpiricalProcess`:
population-linearized coefficient tightness is derived from feasible
recentered-score tightness rather than supplied as a primitive field. -/
theorem
    twoSLSBootstrapRobustPercentileTCIEventFinSucc_theorem12_8_of_assumption12_2_joint_iid_mixed_moments_scoreTailPrimitiveEmpiricalProcess_coverageInputs
    [IsProbabilityMeasure μ]
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {R : Matrix Unit k ℝ} {β : k → ℝ} {q α : ℝ}
    (h : TwoSLSAssumption12_2JointIidFourthConditions μ Z X e)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hOmegaCross : ∀ a b : l, ∀ j : k,
      Integrable (fun ω => e 0 ω * X 0 ω j * Z 0 ω a * Z 0 ω b) μ)
    (hOmegaQuadratic : ∀ a b : l, ∀ j m : k,
      Integrable (fun ω => X 0 ω j * X 0 ω m * Z 0 ω a * Z 0 ω b) μ)
    (hSigmaCross : ∀ j : k,
      Integrable (fun ω => e 0 ω * X 0 ω j) μ)
    (hR : Function.Injective Rᵀ.mulVec)
    (hboot :
      TwoSLSBootstrapTheorem12_8ScoreTailPrimitiveEmpiricalProcessInputs
        μ Z X Y e β R)
    (hcoverage :
      TwoSLSBootstrapRobustPercentileTCoverageInputs
        μ Z X Y β R q α) :
    Tendsto
      (fun n =>
        μ {ω |
          twoSLSBootstrapRobustPercentileTCIEventFinSucc
            R Z X Y β α n ω})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) := by
  have hTstar :
      TendstoInBootstrapDistributionIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs (_ : Unit) =>
          twoSLSBootstrapRobustLinearTStatFinSucc R Z X Y n ω ωs)
        (gaussianReal 0 1) (fun z : ℝ => fun _ : Unit => z) :=
    (twoSLSBootstrap_theorem12_8_of_assumption12_2_joint_iid_mixed_moments_scoreTailPrimitiveEmpiricalProcess
      (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y) (R := R)
      h β hmodel hOmegaCross hOmegaQuadratic hSigmaCross hR hboot).2
  exact
    twoSLSBootstrapRobustPercentileTCIEventFinSucc_tendsto_one_sub_alpha_uniform_of_coverageInputs
      (μ := μ) (Z := Z) (X := X) (Y := Y) (R := R) (β := β)
      (q := q) (α := α) hTstar hcoverage

set_option linter.style.longLine false in
/-- Percentile-`t` coverage from joint-iid Assumption 12.2, scalar bootstrap
empirical-process envelope bounds, and named interval-side inputs.

This is the interval companion to
`twoSLSBootstrap_theorem12_8_of_assumption12_2_joint_iid_mixed_moments_tail_bounds`.
The bootstrap coefficient and robust t-ratio limits are derived from the scalar
envelope bounds; the remaining sample-side robust t-ratio and quantile
calibration fields stay in `TwoSLSBootstrapRobustPercentileTCoverageInputs`. -/
theorem
    twoSLSBootstrapRobustPercentileTCIEventFinSucc_theorem12_8_of_assumption12_2_joint_iid_mixed_moments_tail_bounds_coverageInputs
    [IsProbabilityMeasure μ]
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {R : Matrix Unit k ℝ} {β : k → ℝ} {q α : ℝ}
    {Bresid Bpop Bcoef Bcov :
      ∀ n, Ω → (Fin (n + 1) → Fin (n + 1)) → ℝ}
    (h : TwoSLSAssumption12_2JointIidFourthConditions μ Z X e)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hOmegaCross : ∀ a b : l, ∀ j : k,
      Integrable (fun ω => e 0 ω * X 0 ω j * Z 0 ω a * Z 0 ω b) μ)
    (hOmegaQuadratic : ∀ a b : l, ∀ j m : k,
      Integrable (fun ω => X 0 ω j * X 0 ω m * Z 0 ω a * Z 0 ω b) μ)
    (hSigmaCross : ∀ j : k,
      Integrable (fun ω => e 0 ω * X 0 ω j) μ)
    (hR : Function.Injective Rᵀ.mulVec)
    (hTrueTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set (EuclideanSpace ℝ l), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω =>
            (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω) n ω).real
              {ωs |
                twoSLSBootstrapTrueRecenteredScoreStatisticFinSucc
                  Z e n ω ωs ∉ K})
          atTop (fun _ => 0))
    (hBresidTail : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω) n ω).real
            {ωs | δ ≤ Bresid n ω ωs})
        atTop (fun _ => 0))
    (hBresidBound : ∀ n ω (ωs : Fin (n + 1) → Fin (n + 1)),
      ‖twoSLSBootstrapResidualSubstitutionRecenteredScoreStatisticFinSucc
        Z X Y β n ω ωs‖ ≤ Bresid n ω ωs)
    (hBpopTail : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω) n ω).real
            {ωs | δ ≤ Bpop n ω ωs})
        atTop (fun _ => 0))
    (hBpopBound : ∀ n ω (ωs : Fin (n + 1) → Fin (n + 1)),
      dist (twoSLSBootstrapLinearizedGapFinSucc Z X Y n ω ωs)
        (twoSLSBootstrapPopulationLinearizedGapFinSucc
          (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
          (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
          (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))
          Z X Y n ω ωs) ≤ Bpop n ω ωs)
    (hBcoefTail : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω) n ω).real
            {ωs | δ ≤ Bcoef n ω ωs})
        atTop (fun _ => 0))
    (hBcoefBound : ∀ n ω (ωs : Fin (n + 1) → Fin (n + 1)),
      dist (twoSLSBootstrapBetaGapFinSucc Z X Y n ω ωs)
        (twoSLSBootstrapLinearizedGapFinSucc Z X Y n ω ωs) ≤
          Bcoef n ω ωs)
    (hBcovTail : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω) n ω).real
            {ωs | δ ≤ Bcov n ω ωs})
        atTop (fun _ => 0))
    (hBcovBound : ∀ n ω (ωs : Fin (n + 1) → Fin (n + 1)),
      ‖twoSLSBootstrapVHatStarFinSucc Z X Y n ω ωs -
        twoSLSVHatStar
          (stackRegressors Z (n + 1) ω)
          (stackRegressors X (n + 1) ω)
          (stackOutcomes Y (n + 1) ω)‖ ≤ Bcov n ω ωs)
    (hcoverage :
      TwoSLSBootstrapRobustPercentileTCoverageInputs
        μ Z X Y β R q α) :
    Tendsto
      (fun n =>
        μ {ω |
          twoSLSBootstrapRobustPercentileTCIEventFinSucc
            R Z X Y β α n ω})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) := by
  have hTstar :
      TendstoInBootstrapDistributionIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs (_ : Unit) =>
          twoSLSBootstrapRobustLinearTStatFinSucc R Z X Y n ω ωs)
        (gaussianReal 0 1) (fun z : ℝ => fun _ : Unit => z) :=
    (twoSLSBootstrap_theorem12_8_of_assumption12_2_joint_iid_mixed_moments_tail_bounds
      (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y) (R := R) (β := β)
      (Bresid := Bresid) (Bpop := Bpop) (Bcoef := Bcoef) (Bcov := Bcov)
      h hmodel hOmegaCross hOmegaQuadratic hSigmaCross hR hTrueTail
      hBresidTail hBresidBound hBpopTail hBpopBound hBcoefTail
      hBcoefBound hBcovTail hBcovBound).2
  exact
    twoSLSBootstrapRobustPercentileTCIEventFinSucc_tendsto_one_sub_alpha_uniform_of_coverageInputs
      (μ := μ) (Z := Z) (X := X) (Y := Y) (R := R) (β := β)
      (q := q) (α := α) hTstar hcoverage

set_option linter.style.longLine false in
/-- Percentile-`t` coverage from scalar bootstrap envelope bounds, with the
true-score compact-tail input supplied by an eventual deterministic norm
bound. -/
theorem
    twoSLSBootstrapRobustPercentileTCIEventFinSucc_theorem12_8_of_assumption12_2_joint_iid_mixed_moments_tail_bounds_trueScore_norm_bound_coverageInputs
    [IsProbabilityMeasure μ]
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {R : Matrix Unit k ℝ} {β : k → ℝ} {q α C : ℝ}
    {Bresid Bpop Bcoef Bcov :
      ∀ n, Ω → (Fin (n + 1) → Fin (n + 1)) → ℝ}
    (h : TwoSLSAssumption12_2JointIidFourthConditions μ Z X e)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hOmegaCross : ∀ a b : l, ∀ j : k,
      Integrable (fun ω => e 0 ω * X 0 ω j * Z 0 ω a * Z 0 ω b) μ)
    (hOmegaQuadratic : ∀ a b : l, ∀ j m : k,
      Integrable (fun ω => X 0 ω j * X 0 ω m * Z 0 ω a * Z 0 ω b) μ)
    (hSigmaCross : ∀ j : k,
      Integrable (fun ω => e 0 ω * X 0 ω j) μ)
    (hR : Function.Injective Rᵀ.mulVec)
    (hTrueBound :
      ∀ᶠ n in atTop,
        ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
          ‖twoSLSBootstrapTrueRecenteredScoreStatisticFinSucc
            Z e n ω ωs‖ ≤ C)
    (hBresidTail : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω) n ω).real
            {ωs | δ ≤ Bresid n ω ωs})
        atTop (fun _ => 0))
    (hBresidBound : ∀ n ω (ωs : Fin (n + 1) → Fin (n + 1)),
      ‖twoSLSBootstrapResidualSubstitutionRecenteredScoreStatisticFinSucc
        Z X Y β n ω ωs‖ ≤ Bresid n ω ωs)
    (hBpopTail : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω) n ω).real
            {ωs | δ ≤ Bpop n ω ωs})
        atTop (fun _ => 0))
    (hBpopBound : ∀ n ω (ωs : Fin (n + 1) → Fin (n + 1)),
      dist (twoSLSBootstrapLinearizedGapFinSucc Z X Y n ω ωs)
        (twoSLSBootstrapPopulationLinearizedGapFinSucc
          (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
          (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
          (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))
          Z X Y n ω ωs) ≤ Bpop n ω ωs)
    (hBcoefTail : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω) n ω).real
            {ωs | δ ≤ Bcoef n ω ωs})
        atTop (fun _ => 0))
    (hBcoefBound : ∀ n ω (ωs : Fin (n + 1) → Fin (n + 1)),
      dist (twoSLSBootstrapBetaGapFinSucc Z X Y n ω ωs)
        (twoSLSBootstrapLinearizedGapFinSucc Z X Y n ω ωs) ≤
          Bcoef n ω ωs)
    (hBcovTail : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω) n ω).real
            {ωs | δ ≤ Bcov n ω ωs})
        atTop (fun _ => 0))
    (hBcovBound : ∀ n ω (ωs : Fin (n + 1) → Fin (n + 1)),
      ‖twoSLSBootstrapVHatStarFinSucc Z X Y n ω ωs -
        twoSLSVHatStar
          (stackRegressors Z (n + 1) ω)
          (stackRegressors X (n + 1) ω)
          (stackOutcomes Y (n + 1) ω)‖ ≤ Bcov n ω ωs)
    (hcoverage :
      TwoSLSBootstrapRobustPercentileTCoverageInputs
        μ Z X Y β R q α) :
    Tendsto
      (fun n =>
        μ {ω |
          twoSLSBootstrapRobustPercentileTCIEventFinSucc
            R Z X Y β α n ω})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) :=
  twoSLSBootstrapRobustPercentileTCIEventFinSucc_theorem12_8_of_assumption12_2_joint_iid_mixed_moments_tail_bounds_coverageInputs
    (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y) (R := R) (β := β)
    (q := q) (α := α)
    (Bresid := Bresid) (Bpop := Bpop) (Bcoef := Bcoef) (Bcov := Bcov)
    h hmodel hOmegaCross hOmegaQuadratic hSigmaCross hR
    (twoSLSBootstrapTrueRecenteredScoreStatisticFinSucc_compactTail_uniform_of_eventually_norm_bound
      (μ := μ) (Z := Z) (e := e) hTrueBound)
    hBresidTail hBresidBound hBpopTail hBpopBound
    hBcoefTail hBcoefBound hBcovTail hBcovBound hcoverage

set_option linter.style.longLine false in
/-- Percentile-`t` coverage from true-score boundedness and uniform bootstrap
remainder bounds.

This is the coverage companion to
`twoSLSBootstrap_theorem12_8_of_assumption12_2_joint_iid_mixed_moments_uniform_remainders_trueScore_norm_bound`.
It keeps the original-sample robust t-statistic and bootstrap quantile
calibration in the named coverage package, while deriving the bootstrap
t-ratio limit from the uniform remainder route. -/
theorem
    twoSLSBootstrapRobustPercentileTCIEventFinSucc_theorem12_8_of_assumption12_2_joint_iid_mixed_moments_uniform_remainders_trueScore_norm_bound_coverageInputs
    [IsProbabilityMeasure μ]
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {R : Matrix Unit k ℝ} {β : k → ℝ} {q α C : ℝ}
    (h : TwoSLSAssumption12_2JointIidFourthConditions μ Z X e)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hOmegaCross : ∀ a b : l, ∀ j : k,
      Integrable (fun ω => e 0 ω * X 0 ω j * Z 0 ω a * Z 0 ω b) μ)
    (hOmegaQuadratic : ∀ a b : l, ∀ j m : k,
      Integrable (fun ω => X 0 ω j * X 0 ω m * Z 0 ω a * Z 0 ω b) μ)
    (hSigmaCross : ∀ j : k,
      Integrable (fun ω => e 0 ω * X 0 ω j) μ)
    (hR : Function.Injective Rᵀ.mulVec)
    (hTrueBound :
      ∀ᶠ n in atTop,
        ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
          ‖twoSLSBootstrapTrueRecenteredScoreStatisticFinSucc
            Z e n ω ωs‖ ≤ C)
    (hResidSmall : ∀ δ : ℝ, 0 < δ →
      ∀ᶠ n in atTop,
        ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
          ‖twoSLSBootstrapResidualSubstitutionRecenteredScoreStatisticFinSucc
            Z X Y β n ω ωs‖ < δ)
    (hPopSmall : ∀ δ : ℝ, 0 < δ →
      ∀ᶠ n in atTop,
        ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
          dist (twoSLSBootstrapLinearizedGapFinSucc Z X Y n ω ωs)
            (twoSLSBootstrapPopulationLinearizedGapFinSucc
              (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
              (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
              (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))
              Z X Y n ω ωs) < δ)
    (hCoefSmall : ∀ δ : ℝ, 0 < δ →
      ∀ᶠ n in atTop,
        ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
          dist (twoSLSBootstrapBetaGapFinSucc Z X Y n ω ωs)
            (twoSLSBootstrapLinearizedGapFinSucc Z X Y n ω ωs) < δ)
    (hCovSmall : ∀ δ : ℝ, 0 < δ →
      ∀ᶠ n in atTop,
        ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
          ‖twoSLSBootstrapVHatStarFinSucc Z X Y n ω ωs -
            twoSLSVHatStar
              (stackRegressors Z (n + 1) ω)
              (stackRegressors X (n + 1) ω)
              (stackOutcomes Y (n + 1) ω)‖ < δ)
    (hcoverage :
      TwoSLSBootstrapRobustPercentileTCoverageInputs
        μ Z X Y β R q α) :
    Tendsto
      (fun n =>
        μ {ω |
          twoSLSBootstrapRobustPercentileTCIEventFinSucc
            R Z X Y β α n ω})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) := by
  have hTstar :
      TendstoInBootstrapDistributionIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs (_ : Unit) =>
          twoSLSBootstrapRobustLinearTStatFinSucc R Z X Y n ω ωs)
        (gaussianReal 0 1) (fun z : ℝ => fun _ : Unit => z) :=
    (twoSLSBootstrap_theorem12_8_of_assumption12_2_joint_iid_mixed_moments_uniform_remainders_trueScore_norm_bound
      (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y) (R := R) (β := β)
      h hmodel hOmegaCross hOmegaQuadratic hSigmaCross hR hTrueBound
      hResidSmall hPopSmall hCoefSmall hCovSmall).2
  exact
    twoSLSBootstrapRobustPercentileTCIEventFinSucc_tendsto_one_sub_alpha_uniform_of_coverageInputs
      (μ := μ) (Z := Z) (X := X) (Y := Y) (R := R) (β := β)
      (q := q) (α := α) hTstar hcoverage

set_option linter.style.longLine false in
/-- Textbook-fourth coverage wrapper for Hansen's Theorem 12.8 using scalar
bootstrap envelope bounds and an eventual deterministic true-score bound.

This bridge discharges the mixed-moment and model side conditions from the
literal finite-fourth Assumption 12.2 package, then reuses the joint-iid
bounded-score coverage endpoint. -/
theorem
    twoSLSBootstrapRobustPercentileTCIEventFinSucc_theorem12_8_of_textbook_fourth_tail_bounds_trueScore_norm_bound_coverageInputs
    [IsProbabilityMeasure μ]
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {R : Matrix Unit k ℝ} {β : k → ℝ} {q α C : ℝ}
    {Bresid Bpop Bcoef Bcov :
      ∀ n, Ω → (Fin (n + 1) → Fin (n + 1)) → ℝ}
    (h : TwoSLSAssumption12_2JointIidTextbookFourthConditions μ Z X e Y β)
    (hR : Function.Injective Rᵀ.mulVec)
    (hTrueBound :
      ∀ᶠ n in atTop,
        ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
          ‖twoSLSBootstrapTrueRecenteredScoreStatisticFinSucc
            Z e n ω ωs‖ ≤ C)
    (hBresidTail : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω) n ω).real
            {ωs | δ ≤ Bresid n ω ωs})
        atTop (fun _ => 0))
    (hBresidBound : ∀ n ω (ωs : Fin (n + 1) → Fin (n + 1)),
      ‖twoSLSBootstrapResidualSubstitutionRecenteredScoreStatisticFinSucc
        Z X Y β n ω ωs‖ ≤ Bresid n ω ωs)
    (hBpopTail : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω) n ω).real
            {ωs | δ ≤ Bpop n ω ωs})
        atTop (fun _ => 0))
    (hBpopBound : ∀ n ω (ωs : Fin (n + 1) → Fin (n + 1)),
      dist (twoSLSBootstrapLinearizedGapFinSucc Z X Y n ω ωs)
        (twoSLSBootstrapPopulationLinearizedGapFinSucc
          (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
          (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
          (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))
          Z X Y n ω ωs) ≤ Bpop n ω ωs)
    (hBcoefTail : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω) n ω).real
            {ωs | δ ≤ Bcoef n ω ωs})
        atTop (fun _ => 0))
    (hBcoefBound : ∀ n ω (ωs : Fin (n + 1) → Fin (n + 1)),
      dist (twoSLSBootstrapBetaGapFinSucc Z X Y n ω ωs)
        (twoSLSBootstrapLinearizedGapFinSucc Z X Y n ω ωs) ≤
          Bcoef n ω ωs)
    (hBcovTail : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω) n ω).real
            {ωs | δ ≤ Bcov n ω ωs})
        atTop (fun _ => 0))
    (hBcovBound : ∀ n ω (ωs : Fin (n + 1) → Fin (n + 1)),
      ‖twoSLSBootstrapVHatStarFinSucc Z X Y n ω ωs -
        twoSLSVHatStar
          (stackRegressors Z (n + 1) ω)
          (stackRegressors X (n + 1) ω)
          (stackOutcomes Y (n + 1) ω)‖ ≤ Bcov n ω ωs)
    (hcoverage :
      TwoSLSBootstrapRobustPercentileTCoverageInputs
        μ Z X Y β R q α) :
    Tendsto
      (fun n =>
        μ {ω |
          twoSLSBootstrapRobustPercentileTCIEventFinSucc
            R Z X Y β α n ω})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) := by
  let hm := h.toJointIidMixedMomentConditions
  exact
    twoSLSBootstrapRobustPercentileTCIEventFinSucc_theorem12_8_of_assumption12_2_joint_iid_mixed_moments_tail_bounds_trueScore_norm_bound_coverageInputs
      (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y) (R := R)
      (β := β) (q := q) (α := α) (C := C)
      (Bresid := Bresid) (Bpop := Bpop) (Bcoef := Bcoef) (Bcov := Bcov)
      hm.toTwoSLSAssumption12_2JointIidFourthConditions
      h.model hm.omega_cross_integrable hm.omega_quadratic_integrable
      hm.sigma_cross_integrable hR hTrueBound
      hBresidTail hBresidBound hBpopTail hBpopBound
      hBcoefTail hBcoefBound hBcovTail hBcovBound hcoverage

set_option linter.style.longLine false in
/-- Textbook-fourth coverage wrapper for Hansen's Theorem 12.8 using direct
uniform remainder bounds and an eventual deterministic true-score bound.

This is the literal finite-fourth companion to the joint-iid
uniform-remainder coverage endpoint; it introduces no new bootstrap empirical
process argument. -/
theorem
    twoSLSBootstrapRobustPercentileTCIEventFinSucc_theorem12_8_of_textbook_fourth_uniform_remainders_trueScore_norm_bound_coverageInputs
    [IsProbabilityMeasure μ]
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {R : Matrix Unit k ℝ} {β : k → ℝ} {q α C : ℝ}
    (h : TwoSLSAssumption12_2JointIidTextbookFourthConditions μ Z X e Y β)
    (hR : Function.Injective Rᵀ.mulVec)
    (hTrueBound :
      ∀ᶠ n in atTop,
        ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
          ‖twoSLSBootstrapTrueRecenteredScoreStatisticFinSucc
            Z e n ω ωs‖ ≤ C)
    (hResidSmall : ∀ δ : ℝ, 0 < δ →
      ∀ᶠ n in atTop,
        ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
          ‖twoSLSBootstrapResidualSubstitutionRecenteredScoreStatisticFinSucc
            Z X Y β n ω ωs‖ < δ)
    (hPopSmall : ∀ δ : ℝ, 0 < δ →
      ∀ᶠ n in atTop,
        ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
          dist (twoSLSBootstrapLinearizedGapFinSucc Z X Y n ω ωs)
            (twoSLSBootstrapPopulationLinearizedGapFinSucc
              (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
              (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
              (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))
              Z X Y n ω ωs) < δ)
    (hCoefSmall : ∀ δ : ℝ, 0 < δ →
      ∀ᶠ n in atTop,
        ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
          dist (twoSLSBootstrapBetaGapFinSucc Z X Y n ω ωs)
            (twoSLSBootstrapLinearizedGapFinSucc Z X Y n ω ωs) < δ)
    (hCovSmall : ∀ δ : ℝ, 0 < δ →
      ∀ᶠ n in atTop,
        ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
          ‖twoSLSBootstrapVHatStarFinSucc Z X Y n ω ωs -
            twoSLSVHatStar
              (stackRegressors Z (n + 1) ω)
              (stackRegressors X (n + 1) ω)
              (stackOutcomes Y (n + 1) ω)‖ < δ)
    (hcoverage :
      TwoSLSBootstrapRobustPercentileTCoverageInputs
        μ Z X Y β R q α) :
    Tendsto
      (fun n =>
        μ {ω |
          twoSLSBootstrapRobustPercentileTCIEventFinSucc
            R Z X Y β α n ω})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) := by
  let hm := h.toJointIidMixedMomentConditions
  exact
    twoSLSBootstrapRobustPercentileTCIEventFinSucc_theorem12_8_of_assumption12_2_joint_iid_mixed_moments_uniform_remainders_trueScore_norm_bound_coverageInputs
      (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y) (R := R)
      (β := β) (q := q) (α := α) (C := C)
      hm.toTwoSLSAssumption12_2JointIidFourthConditions
      h.model hm.omega_cross_integrable hm.omega_quadratic_integrable
      hm.sigma_cross_integrable hR hTrueBound hResidSmall hPopSmall
      hCoefSmall hCovSmall hcoverage

set_option linter.style.longLine false in
/-- Percentile-`t` coverage from the direct residual-substitution and
linearization theorem-facing inputs, with the interval-side sample/quantile
premises bundled. -/
theorem
    twoSLSBootstrapRobustPercentileTCIEventFinSucc_theorem12_8_of_assumption12_2_joint_iid_mixed_moments_residualSubstitution_linearization_resampleCloseness_coverageInputs
    [IsProbabilityMeasure μ]
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {R : Matrix Unit k ℝ} {β : k → ℝ} {q α : ℝ}
    (h : TwoSLSAssumption12_2JointIidFourthConditions μ Z X e)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hOmegaCross : ∀ a b : l, ∀ j : k,
      Integrable (fun ω => e 0 ω * X 0 ω j * Z 0 ω a * Z 0 ω b) μ)
    (hOmegaQuadratic : ∀ a b : l, ∀ j m : k,
      Integrable (fun ω => X 0 ω j * X 0 ω m * Z 0 ω a * Z 0 ω b) μ)
    (hSigmaCross : ∀ j : k,
      Integrable (fun ω => e 0 ω * X 0 ω j) μ)
    (hR : Function.Injective Rᵀ.mulVec)
    (hresid : TwoSLSBootstrapResidualSubstitutionInputs μ Z X Y e β)
    (hlin : TwoSLSBootstrapCoefficientLinearizationInputs μ
      (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω)) Z X Y
      (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
      (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
      (scoreCovMat μ Z e)
      (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X))))
    (hV : TwoSLSBootstrapRobustCovarianceResampleCloseness μ Z X Y)
    (hcoverage :
      TwoSLSBootstrapRobustPercentileTCoverageInputs
        μ Z X Y β R q α) :
    Tendsto
      (fun n =>
        μ {ω |
          twoSLSBootstrapRobustPercentileTCIEventFinSucc
            R Z X Y β α n ω})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) :=
  twoSLSBootstrapRobustPercentileTCIEventFinSucc_theorem12_8_of_assumption12_2_joint_iid_mixed_moments_empiricalProcess_coverageInputs
    (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y) (R := R)
    h hmodel hOmegaCross hOmegaQuadratic hSigmaCross hR
    (TwoSLSBootstrapTheorem12_8EmpiricalProcessInputs.of_residualSubstitution_linearization_resampleCloseness
      (μ := μ) (Z := Z) (X := X) (Y := Y) (e := e) (β := β)
      (R := R) hresid hlin hV)
    hcoverage

set_option linter.style.longLine false in
/-- Percentile-`t` coverage from the residual-substitution package,
coefficient closeness, primitive covariance resampling, and bundled
interval-side inputs. -/
theorem
    twoSLSBootstrapRobustPercentileTCIEventFinSucc_theorem12_8_of_assumption12_2_joint_iid_mixed_moments_residualSubstitution_closeness_covariancePrimitive_coverageInputs
    [IsProbabilityMeasure μ]
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {R : Matrix Unit k ℝ} {β : k → ℝ} {q α : ℝ}
    (h : TwoSLSAssumption12_2JointIidFourthConditions μ Z X e)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hOmegaCross : ∀ a b : l, ∀ j : k,
      Integrable (fun ω => e 0 ω * X 0 ω j * Z 0 ω a * Z 0 ω b) μ)
    (hOmegaQuadratic : ∀ a b : l, ∀ j m : k,
      Integrable (fun ω => X 0 ω j * X 0 ω m * Z 0 ω a * Z 0 ω b) μ)
    (hSigmaCross : ∀ j : k,
      Integrable (fun ω => e 0 ω * X 0 ω j) μ)
    (hR : Function.Injective Rᵀ.mulVec)
    (hresid : TwoSLSBootstrapResidualSubstitutionInputs μ Z X Y e β)
    (hcoef :
      TwoSLSBootstrapCoefficientLinearizationClosenessInputs μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω)) Z X Y
        (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
        (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
        (scoreCovMat μ Z e)
        (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X))))
    (hcov : TwoSLSBootstrapRobustCovarianceResamplePrimitiveInputs μ Z X Y)
    (hcoverage :
      TwoSLSBootstrapRobustPercentileTCoverageInputs
        μ Z X Y β R q α) :
    Tendsto
      (fun n =>
        μ {ω |
          twoSLSBootstrapRobustPercentileTCIEventFinSucc
            R Z X Y β α n ω})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) :=
  twoSLSBootstrapRobustPercentileTCIEventFinSucc_theorem12_8_of_assumption12_2_joint_iid_mixed_moments_scoreTailPrimitiveEmpiricalProcess_coverageInputs
    (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y) (R := R)
    h hmodel hOmegaCross hOmegaQuadratic hSigmaCross hR
    (TwoSLSBootstrapTheorem12_8ScoreTailPrimitiveEmpiricalProcessInputs.of_residualSubstitution_closeness_covariancePrimitive
      (μ := μ) (Z := Z) (X := X) (Y := Y) (e := e) (β := β)
      (R := R) hresid hcoef hcov)
    hcoverage

set_option linter.style.longLine false in
/-- Hansen Theorem 12.8 from the named mixed-moment Assumption 12.2 package
and the score-tail primitive bootstrap empirical-process package.

This is the mixed-moment analogue of
`twoSLSBootstrap_theorem12_8_of_assumption12_2_joint_iid_mixed_moments_scoreTailPrimitiveEmpiricalProcess`:
the Chapter 12 mixed moment package supplies the covariance weight WLLN
premises, while the remaining bootstrap-specific work stays isolated in the
score-tail primitive package. -/
theorem
    twoSLSBootstrap_theorem12_8_of_mixed_moment_conditions_scoreTailPrimitiveEmpiricalProcess
    [IsProbabilityMeasure μ]
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {R : Matrix Unit k ℝ}
    (h : TwoSLSAssumption12_2JointIidMixedMomentConditions μ Z X e)
    (β : k → ℝ)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hR : Function.Injective Rᵀ.mulVec)
    (hboot :
      TwoSLSBootstrapTheorem12_8ScoreTailPrimitiveEmpiricalProcessInputs
        μ Z X Y e β R) :
    TendstoInBootstrapDistributionIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs => twoSLSBootstrapBetaGapFinSucc Z X Y n ω ωs)
        (multivariateGaussian (0 : EuclideanSpace ℝ k)
          (twoSLSAsymptoticVariance
            (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (scoreCovMat μ Z e)
            (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))))
        (fun z : EuclideanSpace ℝ k => (z : k → ℝ)) ∧
      TendstoInBootstrapDistributionIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs (_ : Unit) =>
          twoSLSBootstrapRobustLinearTStatFinSucc R Z X Y n ω ωs)
        (gaussianReal 0 1) (fun z : ℝ => fun _ : Unit => z) :=
  twoSLSBootstrap_theorem12_8_of_assumption12_2_joint_iid_mixed_moments_scoreTailPrimitiveEmpiricalProcess
    (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y) (R := R)
    h.toTwoSLSAssumption12_2JointIidFourthConditions β hmodel
    h.omega_cross_integrable h.omega_quadratic_integrable
    h.sigma_cross_integrable hR hboot

set_option linter.style.longLine false in
/-- Hansen Theorem 12.8 from the named mixed-moment Assumption 12.2 package,
with the residual-score input supplied through the established
residual-substitution package and the coefficient/covariance inputs kept at
their primitive closeness/tail level.

This is the named-condition companion to
`twoSLSBootstrap_theorem12_8_of_assumption12_2_joint_iid_mixed_moments_residualSubstitution_closeness_covariancePrimitive`:
the mixed-moment package supplies the covariance-weight WLLN assumptions, while
the bootstrap-specific work remains exactly residual substitution,
coefficient-linearization closeness, and robust covariance resampling. -/
theorem
    twoSLSBootstrap_theorem12_8_of_mixed_moment_conditions_residualSubstitution_closeness_covariancePrimitive
    [IsProbabilityMeasure μ]
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {R : Matrix Unit k ℝ}
    (h : TwoSLSAssumption12_2JointIidMixedMomentConditions μ Z X e)
    (β : k → ℝ)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hR : Function.Injective Rᵀ.mulVec)
    (hresid : TwoSLSBootstrapResidualSubstitutionInputs μ Z X Y e β)
    (hcoef :
      TwoSLSBootstrapCoefficientLinearizationClosenessInputs μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω)) Z X Y
        (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
        (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
        (scoreCovMat μ Z e)
        (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X))))
    (hcov : TwoSLSBootstrapRobustCovarianceResamplePrimitiveInputs μ Z X Y) :
    TendstoInBootstrapDistributionIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs => twoSLSBootstrapBetaGapFinSucc Z X Y n ω ωs)
        (multivariateGaussian (0 : EuclideanSpace ℝ k)
          (twoSLSAsymptoticVariance
            (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (scoreCovMat μ Z e)
            (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))))
        (fun z : EuclideanSpace ℝ k => (z : k → ℝ)) ∧
      TendstoInBootstrapDistributionIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs (_ : Unit) =>
          twoSLSBootstrapRobustLinearTStatFinSucc R Z X Y n ω ωs)
        (gaussianReal 0 1) (fun z : ℝ => fun _ : Unit => z) :=
  twoSLSBootstrap_theorem12_8_of_mixed_moment_conditions_scoreTailPrimitiveEmpiricalProcess
    (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y) (R := R)
    h β hmodel hR
    (TwoSLSBootstrapTheorem12_8ScoreTailPrimitiveEmpiricalProcessInputs.of_residualSubstitution_closeness_covariancePrimitive
      (μ := μ) (Z := Z) (X := X) (Y := Y) (e := e) (β := β)
      (R := R) hresid hcoef hcov)

set_option linter.style.longLine false in
/-- Hansen Theorem 12.8 from the named mixed-moment Assumption 12.2 package
with all remaining bootstrap inputs at the current primitive boundary.

The residual-score package is derived internally from true-score compact-tail
control and centered residual-substitution negligibility. The coefficient
linearization input is the two-closeness package, and robust covariance
resampling is the primitive norm-tail package. -/
theorem
    twoSLSBootstrap_theorem12_8_of_mixed_moment_conditions_residualSubstitutionNegligibility_trueScoreTail_closeness_covariancePrimitive
    [IsProbabilityMeasure μ]
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {R : Matrix Unit k ℝ}
    (h : TwoSLSAssumption12_2JointIidMixedMomentConditions μ Z X e)
    (β : k → ℝ)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hR : Function.Injective Rᵀ.mulVec)
    (hresid :
      TwoSLSBootstrapResidualSubstitutionNegligibilityInputs μ Z X Y β)
    (hTrueTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set (EuclideanSpace ℝ l), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω =>
            (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω) n ω).real
              {ωs |
                twoSLSBootstrapTrueRecenteredScoreStatisticFinSucc
                  Z e n ω ωs ∉ K})
          atTop (fun _ => 0))
    (hcoef :
      TwoSLSBootstrapCoefficientLinearizationClosenessInputs μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω)) Z X Y
        (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
        (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
        (scoreCovMat μ Z e)
        (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X))))
    (hcov : TwoSLSBootstrapRobustCovarianceResamplePrimitiveInputs μ Z X Y) :
    TendstoInBootstrapDistributionIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs => twoSLSBootstrapBetaGapFinSucc Z X Y n ω ωs)
        (multivariateGaussian (0 : EuclideanSpace ℝ k)
          (twoSLSAsymptoticVariance
            (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (scoreCovMat μ Z e)
            (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))))
        (fun z : EuclideanSpace ℝ k => (z : k → ℝ)) ∧
      TendstoInBootstrapDistributionIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs (_ : Unit) =>
          twoSLSBootstrapRobustLinearTStatFinSucc R Z X Y n ω ωs)
        (gaussianReal 0 1) (fun z : ℝ => fun _ : Unit => z) :=
  twoSLSBootstrap_theorem12_8_of_mixed_moment_conditions_residualSubstitution_closeness_covariancePrimitive
    (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y) (R := R)
    h β hmodel hR
    (hresid.toResidualSubstitutionInputs_of_trueScore_compactTail
      (μ := μ) (Z := Z) (X := X) (Y := Y) (e := e) (β := β)
      hmodel hTrueTail)
    hcoef hcov

set_option linter.style.longLine false in
/-- Textbook-fourth Assumption 12.2 endpoint for Hansen Theorem 12.8 at the
current primitive bootstrap boundary.

The literal textbook fourth-moment package supplies the mixed-moment
Assumption 12.2 fields and the structural equation. The remaining premises are
only true-score compact-tail control, centered residual-substitution
negligibility, coefficient closeness, primitive robust covariance resampling,
and full rank of the one-row restriction. -/
theorem
    twoSLSBootstrap_theorem12_8_of_textbook_fourth_residualSubstitutionNegligibility_trueScoreTail_closeness_covariancePrimitive
    [IsProbabilityMeasure μ]
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {R : Matrix Unit k ℝ} {β : k → ℝ}
    (h : TwoSLSAssumption12_2JointIidTextbookFourthConditions μ Z X e Y β)
    (hR : Function.Injective Rᵀ.mulVec)
    (hresid :
      TwoSLSBootstrapResidualSubstitutionNegligibilityInputs μ Z X Y β)
    (hTrueTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set (EuclideanSpace ℝ l), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω =>
            (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω) n ω).real
              {ωs |
                twoSLSBootstrapTrueRecenteredScoreStatisticFinSucc
                  Z e n ω ωs ∉ K})
          atTop (fun _ => 0))
    (hcoef :
      TwoSLSBootstrapCoefficientLinearizationClosenessInputs μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω)) Z X Y
        (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
        (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
        (scoreCovMat μ Z e)
        (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X))))
    (hcov : TwoSLSBootstrapRobustCovarianceResamplePrimitiveInputs μ Z X Y) :
    TendstoInBootstrapDistributionIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs => twoSLSBootstrapBetaGapFinSucc Z X Y n ω ωs)
        (multivariateGaussian (0 : EuclideanSpace ℝ k)
          (twoSLSAsymptoticVariance
            (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (scoreCovMat μ Z e)
            (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))))
        (fun z : EuclideanSpace ℝ k => (z : k → ℝ)) ∧
      TendstoInBootstrapDistributionIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs (_ : Unit) =>
          twoSLSBootstrapRobustLinearTStatFinSucc R Z X Y n ω ωs)
        (gaussianReal 0 1) (fun z : ℝ => fun _ : Unit => z) :=
  twoSLSBootstrap_theorem12_8_of_mixed_moment_conditions_residualSubstitutionNegligibility_trueScoreTail_closeness_covariancePrimitive
    (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y) (R := R)
    (h.toJointIidMixedMomentConditions) β h.model hR
    hresid hTrueTail hcoef hcov

set_option linter.style.longLine false in
/-- Hansen Theorem 12.8 from the named mixed-moment Assumption 12.2 package,
with robust covariance resampling supplied as direct bootstrap covariance
consistency.

Compared with
`twoSLSBootstrap_theorem12_8_of_mixed_moment_conditions_residualSubstitutionNegligibility_trueScoreTail_closeness_covariancePrimitive`,
this wrapper no longer asks for the norm-tail primitive for the robust
covariance resampling remainder. The mixed-moment package supplies the
original-sample robust covariance limit; the remaining covariance input is the
ordinary-bootstrap consistency of `twoSLSBootstrapVHatStarFinSucc` to Hansen's
formula variance. -/
theorem
    twoSLSBootstrap_theorem12_8_of_mixed_moment_conditions_residualSubstitutionNegligibility_trueScoreTail_closeness_bootstrapCovarianceConsistency
    [IsProbabilityMeasure μ]
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {R : Matrix Unit k ℝ}
    (h : TwoSLSAssumption12_2JointIidMixedMomentConditions μ Z X e)
    (β : k → ℝ)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hR : Function.Injective Rᵀ.mulVec)
    (hresid :
      TwoSLSBootstrapResidualSubstitutionNegligibilityInputs μ Z X Y β)
    (hTrueTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set (EuclideanSpace ℝ l), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω =>
            (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω) n ω).real
              {ωs |
                twoSLSBootstrapTrueRecenteredScoreStatisticFinSucc
                  Z e n ω ωs ∉ K})
          atTop (fun _ => 0))
    (hcoef :
      TwoSLSBootstrapCoefficientLinearizationClosenessInputs μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω)) Z X Y
        (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
        (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
        (scoreCovMat μ Z e)
        (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X))))
    (hV_boot :
      TendstoInBootstrapProbabilityIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs => twoSLSBootstrapVHatStarFinSucc Z X Y n ω ωs)
        (fun _ =>
          twoSLSAsymptoticVariance
            (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (scoreCovMat μ Z e)
            (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X))))) :
    TendstoInBootstrapDistributionIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs => twoSLSBootstrapBetaGapFinSucc Z X Y n ω ωs)
        (multivariateGaussian (0 : EuclideanSpace ℝ k)
          (twoSLSAsymptoticVariance
            (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (scoreCovMat μ Z e)
            (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))))
        (fun z : EuclideanSpace ℝ k => (z : k → ℝ)) ∧
      TendstoInBootstrapDistributionIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs (_ : Unit) =>
          twoSLSBootstrapRobustLinearTStatFinSucc R Z X Y n ω ωs)
        (gaussianReal 0 1) (fun z : ℝ => fun _ : Unit => z) := by
  let hV :
      TwoSLSBootstrapRobustCovarianceResampleCloseness μ Z X Y :=
    TwoSLSBootstrapRobustCovarianceResampleCloseness.of_mixed_moment_conditions_bootstrap_consistency
      (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y)
      h β hmodel hV_boot
  exact
    twoSLSBootstrap_theorem12_8_of_assumption12_2_weight_wlln_residualSubstitutionNegligibility_trueScoreTail_closeness_fullRank_resampleCloseness
      (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y) (R := R)
      h.toTwoSLSAssumption12_2JointIidFourthConditions.toIidFourthConditions
      β hmodel
      (h.toWeightWLLNConditions (μ := μ) (Z := Z) (X := X) (e := e))
      hresid hTrueTail hcoef hR hV

set_option linter.style.longLine false in
/-- Literal textbook-fourth Assumption 12.2 endpoint for Hansen Theorem 12.8
with robust covariance resampling supplied as direct bootstrap covariance
consistency. -/
theorem
    twoSLSBootstrap_theorem12_8_of_textbook_fourth_residualSubstitutionNegligibility_trueScoreTail_closeness_bootstrapCovarianceConsistency
    [IsProbabilityMeasure μ]
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {R : Matrix Unit k ℝ} {β : k → ℝ}
    (h : TwoSLSAssumption12_2JointIidTextbookFourthConditions μ Z X e Y β)
    (hR : Function.Injective Rᵀ.mulVec)
    (hresid :
      TwoSLSBootstrapResidualSubstitutionNegligibilityInputs μ Z X Y β)
    (hTrueTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set (EuclideanSpace ℝ l), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω =>
            (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω) n ω).real
              {ωs |
                twoSLSBootstrapTrueRecenteredScoreStatisticFinSucc
                  Z e n ω ωs ∉ K})
          atTop (fun _ => 0))
    (hcoef :
      TwoSLSBootstrapCoefficientLinearizationClosenessInputs μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω)) Z X Y
        (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
        (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
        (scoreCovMat μ Z e)
        (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X))))
    (hV_boot :
      TendstoInBootstrapProbabilityIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs => twoSLSBootstrapVHatStarFinSucc Z X Y n ω ωs)
        (fun _ =>
          twoSLSAsymptoticVariance
            (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (scoreCovMat μ Z e)
            (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X))))) :
    TendstoInBootstrapDistributionIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs => twoSLSBootstrapBetaGapFinSucc Z X Y n ω ωs)
        (multivariateGaussian (0 : EuclideanSpace ℝ k)
          (twoSLSAsymptoticVariance
            (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (scoreCovMat μ Z e)
            (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))))
        (fun z : EuclideanSpace ℝ k => (z : k → ℝ)) ∧
      TendstoInBootstrapDistributionIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs (_ : Unit) =>
          twoSLSBootstrapRobustLinearTStatFinSucc R Z X Y n ω ωs)
        (gaussianReal 0 1) (fun z : ℝ => fun _ : Unit => z) :=
  twoSLSBootstrap_theorem12_8_of_mixed_moment_conditions_residualSubstitutionNegligibility_trueScoreTail_closeness_bootstrapCovarianceConsistency
    (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y) (R := R)
    h.toJointIidMixedMomentConditions β h.model hR
    hresid hTrueTail hcoef hV_boot

set_option linter.style.longLine false in
/-- Historical fixed-compact-tail compatibility wrapper with residual
substitution derived from textbook-fourth Assumption 12.2.

Its compact-tail premise is incompatible with the nondegenerate Gaussian score
limit, so the public theorem surface uses the later asymptotic-tightness
transfer instead. -/
private theorem
    twoSLSBootstrap_theorem12_8_of_textbook_fourth_trueScoreTail_closeness_bootstrapCovarianceConsistency
    [IsProbabilityMeasure μ]
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {R : Matrix Unit k ℝ} {β : k → ℝ}
    (h : TwoSLSAssumption12_2JointIidTextbookFourthConditions μ Z X e Y β)
    (hR : Function.Injective Rᵀ.mulVec)
    (hTrueTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set (EuclideanSpace ℝ l), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω =>
            (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω) n ω).real
              {ωs |
                twoSLSBootstrapTrueRecenteredScoreStatisticFinSucc
                  Z e n ω ωs ∉ K})
          atTop (fun _ => 0))
    (hcoef :
      TwoSLSBootstrapCoefficientLinearizationClosenessInputs μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω)) Z X Y
        (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
        (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
        (scoreCovMat μ Z e)
        (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X))))
    (hV_boot :
      TendstoInBootstrapProbabilityIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs => twoSLSBootstrapVHatStarFinSucc Z X Y n ω ωs)
        (fun _ =>
          twoSLSAsymptoticVariance
            (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (scoreCovMat μ Z e)
            (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X))))) :
    TendstoInBootstrapDistributionIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs => twoSLSBootstrapBetaGapFinSucc Z X Y n ω ωs)
        (multivariateGaussian (0 : EuclideanSpace ℝ k)
          (twoSLSAsymptoticVariance
            (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (scoreCovMat μ Z e)
            (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))))
        (fun z : EuclideanSpace ℝ k => (z : k → ℝ)) ∧
      TendstoInBootstrapDistributionIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs (_ : Unit) =>
          twoSLSBootstrapRobustLinearTStatFinSucc R Z X Y n ω ωs)
        (gaussianReal 0 1) (fun z : ℝ => fun _ : Unit => z) :=
  twoSLSBootstrap_theorem12_8_of_textbook_fourth_residualSubstitutionNegligibility_trueScoreTail_closeness_bootstrapCovarianceConsistency
    (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y) (R := R) (β := β)
    h hR
    (TwoSLSBootstrapResidualSubstitutionNegligibilityInputs.of_textbook_fourth
      (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y) (β := β) h)
    hTrueTail hcoef hV_boot

set_option linter.style.longLine false in
/-- Hansen Theorem 12.8 from uniform residual/coefficient remainders and
direct ordinary-bootstrap robust covariance consistency.

This bridge keeps the true-score compact-tail and direct bootstrap covariance
consistency premises explicit, but no longer asks callers to assemble the
residual-substitution negligibility or coefficient-closeness packages by hand.
The residual and coefficient packages are derived from uniform `o(1)` bounds
for the concrete remainder statistics. -/
theorem
    twoSLSBootstrap_theorem12_8_of_mixed_moment_conditions_uniform_remainders_trueScoreTail_bootstrapCovarianceConsistency
    [IsProbabilityMeasure μ]
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {R : Matrix Unit k ℝ} {β : k → ℝ}
    (h : TwoSLSAssumption12_2JointIidMixedMomentConditions μ Z X e)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hR : Function.Injective Rᵀ.mulVec)
    (hTrueTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set (EuclideanSpace ℝ l), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω =>
            (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω) n ω).real
              {ωs |
                twoSLSBootstrapTrueRecenteredScoreStatisticFinSucc
                  Z e n ω ωs ∉ K})
          atTop (fun _ => 0))
    (hResidSmall : ∀ δ : ℝ, 0 < δ →
      ∀ᶠ n in atTop,
        ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
          ‖twoSLSBootstrapResidualSubstitutionRecenteredScoreStatisticFinSucc
            Z X Y β n ω ωs‖ < δ)
    (hPopSmall : ∀ δ : ℝ, 0 < δ →
      ∀ᶠ n in atTop,
        ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
          dist (twoSLSBootstrapLinearizedGapFinSucc Z X Y n ω ωs)
            (twoSLSBootstrapPopulationLinearizedGapFinSucc
              (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
              (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
              (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))
              Z X Y n ω ωs) < δ)
    (hCoefSmall : ∀ δ : ℝ, 0 < δ →
      ∀ᶠ n in atTop,
        ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
          dist (twoSLSBootstrapBetaGapFinSucc Z X Y n ω ωs)
            (twoSLSBootstrapLinearizedGapFinSucc Z X Y n ω ωs) < δ)
    (hV_boot :
      TendstoInBootstrapProbabilityIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs => twoSLSBootstrapVHatStarFinSucc Z X Y n ω ωs)
        (fun _ =>
          twoSLSAsymptoticVariance
            (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (scoreCovMat μ Z e)
            (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X))))) :
    TendstoInBootstrapDistributionIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs => twoSLSBootstrapBetaGapFinSucc Z X Y n ω ωs)
        (multivariateGaussian (0 : EuclideanSpace ℝ k)
          (twoSLSAsymptoticVariance
            (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (scoreCovMat μ Z e)
            (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))))
        (fun z : EuclideanSpace ℝ k => (z : k → ℝ)) ∧
      TendstoInBootstrapDistributionIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs (_ : Unit) =>
          twoSLSBootstrapRobustLinearTStatFinSucc R Z X Y n ω ωs)
        (gaussianReal 0 1) (fun z : ℝ => fun _ : Unit => z) := by
  let hresid :
      TwoSLSBootstrapResidualSubstitutionNegligibilityInputs μ Z X Y β :=
    TwoSLSBootstrapResidualSubstitutionNegligibilityInputs.of_uniform_norm_vanish
      (μ := μ) (Z := Z) (X := X) (Y := Y) (β := β) hResidSmall
  let hcoef :
      TwoSLSBootstrapCoefficientLinearizationClosenessInputs μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω)) Z X Y
        (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
        (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
        (scoreCovMat μ Z e)
        (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X))) :=
    TwoSLSBootstrapCoefficientLinearizationClosenessInputs.of_uniform_dist_vanish
      (μ := μ) (Pstar := twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
      (Z := Z) (X := X) (Y := Y)
      (QXZ := twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
      (QZZ := twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
      (Omega := scoreCovMat μ Z e)
      (QZX := twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))
      hPopSmall hCoefSmall
  exact
    twoSLSBootstrap_theorem12_8_of_mixed_moment_conditions_residualSubstitutionNegligibility_trueScoreTail_closeness_bootstrapCovarianceConsistency
      (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y) (R := R)
      h β hmodel hR hresid hTrueTail hcoef hV_boot

set_option linter.style.longLine false in
/-- Hansen Theorem 12.8 from uniform residual/coefficient remainders, a
deterministic true-score bound, and direct ordinary-bootstrap robust covariance
consistency.

This is the direct-covariance counterpart of
`twoSLSBootstrap_theorem12_8_of_assumption12_2_joint_iid_mixed_moments_uniform_remainders_trueScore_norm_bound`:
the eventual bound is converted to true-score compact-tail control, while the
robust covariance input stays as direct consistency of
`twoSLSBootstrapVHatStarFinSucc` to Hansen's formula variance. -/
theorem
    twoSLSBootstrap_theorem12_8_of_mixed_moment_conditions_uniform_remainders_trueScore_norm_bound_bootstrapCovarianceConsistency
    [IsProbabilityMeasure μ]
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {R : Matrix Unit k ℝ} {β : k → ℝ} {C : ℝ}
    (h : TwoSLSAssumption12_2JointIidMixedMomentConditions μ Z X e)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hR : Function.Injective Rᵀ.mulVec)
    (hTrueBound :
      ∀ᶠ n in atTop,
        ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
          ‖twoSLSBootstrapTrueRecenteredScoreStatisticFinSucc
            Z e n ω ωs‖ ≤ C)
    (hResidSmall : ∀ δ : ℝ, 0 < δ →
      ∀ᶠ n in atTop,
        ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
          ‖twoSLSBootstrapResidualSubstitutionRecenteredScoreStatisticFinSucc
            Z X Y β n ω ωs‖ < δ)
    (hPopSmall : ∀ δ : ℝ, 0 < δ →
      ∀ᶠ n in atTop,
        ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
          dist (twoSLSBootstrapLinearizedGapFinSucc Z X Y n ω ωs)
            (twoSLSBootstrapPopulationLinearizedGapFinSucc
              (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
              (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
              (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))
              Z X Y n ω ωs) < δ)
    (hCoefSmall : ∀ δ : ℝ, 0 < δ →
      ∀ᶠ n in atTop,
        ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
          dist (twoSLSBootstrapBetaGapFinSucc Z X Y n ω ωs)
            (twoSLSBootstrapLinearizedGapFinSucc Z X Y n ω ωs) < δ)
    (hV_boot :
      TendstoInBootstrapProbabilityIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs => twoSLSBootstrapVHatStarFinSucc Z X Y n ω ωs)
        (fun _ =>
          twoSLSAsymptoticVariance
            (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (scoreCovMat μ Z e)
            (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X))))) :
    TendstoInBootstrapDistributionIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs => twoSLSBootstrapBetaGapFinSucc Z X Y n ω ωs)
        (multivariateGaussian (0 : EuclideanSpace ℝ k)
          (twoSLSAsymptoticVariance
            (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (scoreCovMat μ Z e)
            (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))))
        (fun z : EuclideanSpace ℝ k => (z : k → ℝ)) ∧
      TendstoInBootstrapDistributionIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs (_ : Unit) =>
          twoSLSBootstrapRobustLinearTStatFinSucc R Z X Y n ω ωs)
        (gaussianReal 0 1) (fun z : ℝ => fun _ : Unit => z) :=
  twoSLSBootstrap_theorem12_8_of_mixed_moment_conditions_uniform_remainders_trueScoreTail_bootstrapCovarianceConsistency
    (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y) (R := R)
    (β := β) h hmodel hR
    (twoSLSBootstrapTrueRecenteredScoreStatisticFinSucc_compactTail_uniform_of_eventually_norm_bound
      (μ := μ) (Z := Z) (e := e) hTrueBound)
    hResidSmall hPopSmall hCoefSmall hV_boot

set_option linter.style.longLine false in
/-- Assumption-12.2 joint-iid finite-fourth endpoint for Hansen Theorem 12.8
from uniform residual/coefficient remainders, a deterministic true-score bound,
and direct ordinary-bootstrap robust covariance consistency.

This is the scalar-mixed-moment facade for
`twoSLSBootstrap_theorem12_8_of_mixed_moment_conditions_uniform_remainders_trueScore_norm_bound_bootstrapCovarianceConsistency`:
the three mixed moment premises are exactly the extra fields needed to build
the named mixed-moment Assumption 12.2 package. -/
theorem
    twoSLSBootstrap_theorem12_8_of_assumption12_2_joint_iid_mixed_moments_uniform_remainders_trueScore_norm_bound_bootstrapCovarianceConsistency
    [IsProbabilityMeasure μ]
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {R : Matrix Unit k ℝ} {β : k → ℝ} {C : ℝ}
    (h : TwoSLSAssumption12_2JointIidFourthConditions μ Z X e)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hOmegaCross : ∀ a b : l, ∀ j : k,
      Integrable (fun ω => e 0 ω * X 0 ω j * Z 0 ω a * Z 0 ω b) μ)
    (hOmegaQuadratic : ∀ a b : l, ∀ j m : k,
      Integrable (fun ω => X 0 ω j * X 0 ω m * Z 0 ω a * Z 0 ω b) μ)
    (hSigmaCross : ∀ j : k,
      Integrable (fun ω => e 0 ω * X 0 ω j) μ)
    (hR : Function.Injective Rᵀ.mulVec)
    (hTrueBound :
      ∀ᶠ n in atTop,
        ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
          ‖twoSLSBootstrapTrueRecenteredScoreStatisticFinSucc
            Z e n ω ωs‖ ≤ C)
    (hResidSmall : ∀ δ : ℝ, 0 < δ →
      ∀ᶠ n in atTop,
        ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
          ‖twoSLSBootstrapResidualSubstitutionRecenteredScoreStatisticFinSucc
            Z X Y β n ω ωs‖ < δ)
    (hPopSmall : ∀ δ : ℝ, 0 < δ →
      ∀ᶠ n in atTop,
        ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
          dist (twoSLSBootstrapLinearizedGapFinSucc Z X Y n ω ωs)
            (twoSLSBootstrapPopulationLinearizedGapFinSucc
              (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
              (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
              (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))
              Z X Y n ω ωs) < δ)
    (hCoefSmall : ∀ δ : ℝ, 0 < δ →
      ∀ᶠ n in atTop,
        ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
          dist (twoSLSBootstrapBetaGapFinSucc Z X Y n ω ωs)
            (twoSLSBootstrapLinearizedGapFinSucc Z X Y n ω ωs) < δ)
    (hV_boot :
      TendstoInBootstrapProbabilityIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs => twoSLSBootstrapVHatStarFinSucc Z X Y n ω ωs)
        (fun _ =>
          twoSLSAsymptoticVariance
            (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (scoreCovMat μ Z e)
            (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X))))) :
    TendstoInBootstrapDistributionIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs => twoSLSBootstrapBetaGapFinSucc Z X Y n ω ωs)
        (multivariateGaussian (0 : EuclideanSpace ℝ k)
          (twoSLSAsymptoticVariance
            (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (scoreCovMat μ Z e)
            (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))))
        (fun z : EuclideanSpace ℝ k => (z : k → ℝ)) ∧
      TendstoInBootstrapDistributionIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs (_ : Unit) =>
          twoSLSBootstrapRobustLinearTStatFinSucc R Z X Y n ω ωs)
        (gaussianReal 0 1) (fun z : ℝ => fun _ : Unit => z) := by
  let hm : TwoSLSAssumption12_2JointIidMixedMomentConditions μ Z X e :=
    { toTwoSLSAssumption12_2JointIidFourthConditions := h
      omega_cross_integrable := hOmegaCross
      omega_quadratic_integrable := hOmegaQuadratic
      sigma_cross_integrable := hSigmaCross }
  exact
    twoSLSBootstrap_theorem12_8_of_mixed_moment_conditions_uniform_remainders_trueScore_norm_bound_bootstrapCovarianceConsistency
      (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y) (R := R)
      (β := β) (C := C) hm hmodel hR hTrueBound
      hResidSmall hPopSmall hCoefSmall hV_boot

set_option linter.style.longLine false in
/-- Literal textbook-fourth Assumption 12.2 endpoint for Hansen Theorem 12.8
from uniform residual/coefficient remainders and direct bootstrap covariance
consistency. -/
theorem
    twoSLSBootstrap_theorem12_8_of_textbook_fourth_uniform_remainders_trueScoreTail_bootstrapCovarianceConsistency
    [IsProbabilityMeasure μ]
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {R : Matrix Unit k ℝ} {β : k → ℝ}
    (h : TwoSLSAssumption12_2JointIidTextbookFourthConditions μ Z X e Y β)
    (hR : Function.Injective Rᵀ.mulVec)
    (hTrueTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set (EuclideanSpace ℝ l), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω =>
            (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω) n ω).real
              {ωs |
                twoSLSBootstrapTrueRecenteredScoreStatisticFinSucc
                  Z e n ω ωs ∉ K})
          atTop (fun _ => 0))
    (hResidSmall : ∀ δ : ℝ, 0 < δ →
      ∀ᶠ n in atTop,
        ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
          ‖twoSLSBootstrapResidualSubstitutionRecenteredScoreStatisticFinSucc
            Z X Y β n ω ωs‖ < δ)
    (hPopSmall : ∀ δ : ℝ, 0 < δ →
      ∀ᶠ n in atTop,
        ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
          dist (twoSLSBootstrapLinearizedGapFinSucc Z X Y n ω ωs)
            (twoSLSBootstrapPopulationLinearizedGapFinSucc
              (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
              (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
              (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))
              Z X Y n ω ωs) < δ)
    (hCoefSmall : ∀ δ : ℝ, 0 < δ →
      ∀ᶠ n in atTop,
        ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
          dist (twoSLSBootstrapBetaGapFinSucc Z X Y n ω ωs)
            (twoSLSBootstrapLinearizedGapFinSucc Z X Y n ω ωs) < δ)
    (hV_boot :
      TendstoInBootstrapProbabilityIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs => twoSLSBootstrapVHatStarFinSucc Z X Y n ω ωs)
        (fun _ =>
          twoSLSAsymptoticVariance
            (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (scoreCovMat μ Z e)
            (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X))))) :
    TendstoInBootstrapDistributionIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs => twoSLSBootstrapBetaGapFinSucc Z X Y n ω ωs)
        (multivariateGaussian (0 : EuclideanSpace ℝ k)
          (twoSLSAsymptoticVariance
            (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (scoreCovMat μ Z e)
            (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))))
        (fun z : EuclideanSpace ℝ k => (z : k → ℝ)) ∧
      TendstoInBootstrapDistributionIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs (_ : Unit) =>
          twoSLSBootstrapRobustLinearTStatFinSucc R Z X Y n ω ωs)
        (gaussianReal 0 1) (fun z : ℝ => fun _ : Unit => z) :=
  twoSLSBootstrap_theorem12_8_of_mixed_moment_conditions_uniform_remainders_trueScoreTail_bootstrapCovarianceConsistency
    (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y) (R := R)
    (β := β) h.toJointIidMixedMomentConditions h.model hR hTrueTail
    hResidSmall hPopSmall hCoefSmall hV_boot

set_option linter.style.longLine false in
/-- Literal finite-fourth Assumption 12.2 endpoint for Hansen Theorem 12.8
from uniform residual/coefficient remainders, a deterministic true-score bound,
and direct bootstrap covariance consistency. -/
theorem
    twoSLSBootstrap_theorem12_8_of_textbook_fourth_uniform_remainders_trueScore_norm_bound_bootstrapCovarianceConsistency
    [IsProbabilityMeasure μ]
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {R : Matrix Unit k ℝ} {β : k → ℝ} {C : ℝ}
    (h : TwoSLSAssumption12_2JointIidTextbookFourthConditions μ Z X e Y β)
    (hR : Function.Injective Rᵀ.mulVec)
    (hTrueBound :
      ∀ᶠ n in atTop,
        ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
          ‖twoSLSBootstrapTrueRecenteredScoreStatisticFinSucc
            Z e n ω ωs‖ ≤ C)
    (hResidSmall : ∀ δ : ℝ, 0 < δ →
      ∀ᶠ n in atTop,
        ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
          ‖twoSLSBootstrapResidualSubstitutionRecenteredScoreStatisticFinSucc
            Z X Y β n ω ωs‖ < δ)
    (hPopSmall : ∀ δ : ℝ, 0 < δ →
      ∀ᶠ n in atTop,
        ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
          dist (twoSLSBootstrapLinearizedGapFinSucc Z X Y n ω ωs)
            (twoSLSBootstrapPopulationLinearizedGapFinSucc
              (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
              (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
              (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))
              Z X Y n ω ωs) < δ)
    (hCoefSmall : ∀ δ : ℝ, 0 < δ →
      ∀ᶠ n in atTop,
        ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
          dist (twoSLSBootstrapBetaGapFinSucc Z X Y n ω ωs)
            (twoSLSBootstrapLinearizedGapFinSucc Z X Y n ω ωs) < δ)
    (hV_boot :
      TendstoInBootstrapProbabilityIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs => twoSLSBootstrapVHatStarFinSucc Z X Y n ω ωs)
        (fun _ =>
          twoSLSAsymptoticVariance
            (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (scoreCovMat μ Z e)
            (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X))))) :
    TendstoInBootstrapDistributionIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs => twoSLSBootstrapBetaGapFinSucc Z X Y n ω ωs)
        (multivariateGaussian (0 : EuclideanSpace ℝ k)
          (twoSLSAsymptoticVariance
            (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (scoreCovMat μ Z e)
            (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))))
        (fun z : EuclideanSpace ℝ k => (z : k → ℝ)) ∧
      TendstoInBootstrapDistributionIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs (_ : Unit) =>
          twoSLSBootstrapRobustLinearTStatFinSucc R Z X Y n ω ωs)
        (gaussianReal 0 1) (fun z : ℝ => fun _ : Unit => z) :=
  twoSLSBootstrap_theorem12_8_of_mixed_moment_conditions_uniform_remainders_trueScore_norm_bound_bootstrapCovarianceConsistency
    (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y) (R := R)
    (β := β) (C := C) h.toJointIidMixedMomentConditions h.model hR
    hTrueBound hResidSmall hPopSmall hCoefSmall hV_boot

set_option linter.style.longLine false in
/-- Observed-row Assumption 12.2 companion to the preferred direct-covariance
Hansen Theorem 12.8 endpoint.

The proof reuses the residual-row endpoint through
`TwoSLSAssumption12_2ObservedIidTextbookFourthConditions.toResidualTextbookFourthConditions`,
so the empirical-process boundary is unchanged while the public assumption
surface matches Hansen's observed data rows. -/
theorem
    twoSLSBootstrap_theorem12_8_of_observed_textbook_fourth_uniform_remainders_trueScore_norm_bound_bootstrapCovarianceConsistency
    [IsProbabilityMeasure μ]
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {R : Matrix Unit k ℝ} {β : k → ℝ} {C : ℝ}
    (h : TwoSLSAssumption12_2ObservedIidTextbookFourthConditions μ Z X e Y β)
    (hR : Function.Injective Rᵀ.mulVec)
    (hTrueBound :
      ∀ᶠ n in atTop,
        ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
          ‖twoSLSBootstrapTrueRecenteredScoreStatisticFinSucc
            Z e n ω ωs‖ ≤ C)
    (hResidSmall : ∀ δ : ℝ, 0 < δ →
      ∀ᶠ n in atTop,
        ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
          ‖twoSLSBootstrapResidualSubstitutionRecenteredScoreStatisticFinSucc
            Z X Y β n ω ωs‖ < δ)
    (hPopSmall : ∀ δ : ℝ, 0 < δ →
      ∀ᶠ n in atTop,
        ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
          dist (twoSLSBootstrapLinearizedGapFinSucc Z X Y n ω ωs)
            (twoSLSBootstrapPopulationLinearizedGapFinSucc
              (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
              (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
              (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))
              Z X Y n ω ωs) < δ)
    (hCoefSmall : ∀ δ : ℝ, 0 < δ →
      ∀ᶠ n in atTop,
        ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
          dist (twoSLSBootstrapBetaGapFinSucc Z X Y n ω ωs)
            (twoSLSBootstrapLinearizedGapFinSucc Z X Y n ω ωs) < δ)
    (hV_boot :
      TendstoInBootstrapProbabilityIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs => twoSLSBootstrapVHatStarFinSucc Z X Y n ω ωs)
        (fun _ =>
          twoSLSAsymptoticVariance
            (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (scoreCovMat μ Z e)
            (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X))))) :
    TendstoInBootstrapDistributionIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs => twoSLSBootstrapBetaGapFinSucc Z X Y n ω ωs)
        (multivariateGaussian (0 : EuclideanSpace ℝ k)
          (twoSLSAsymptoticVariance
            (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (scoreCovMat μ Z e)
            (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))))
        (fun z : EuclideanSpace ℝ k => (z : k → ℝ)) ∧
      TendstoInBootstrapDistributionIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs (_ : Unit) =>
          twoSLSBootstrapRobustLinearTStatFinSucc R Z X Y n ω ωs)
        (gaussianReal 0 1) (fun z : ℝ => fun _ : Unit => z) :=
  twoSLSBootstrap_theorem12_8_of_textbook_fourth_uniform_remainders_trueScore_norm_bound_bootstrapCovarianceConsistency
    (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y) (R := R)
    (β := β) (C := C) h.toResidualTextbookFourthConditions hR
    hTrueBound hResidSmall hPopSmall hCoefSmall hV_boot

set_option linter.style.longLine false in
/-- Observed-row Assumption 12.2 direct-covariance Hansen Theorem 12.8
endpoint with the one-row restriction rank condition stated as a nonzero row
entry. -/
theorem
    twoSLSBootstrap_theorem12_8_of_observed_textbook_fourth_uniform_remainders_trueScore_norm_bound_bootstrapCovarianceConsistency_row_ne_zero
    [IsProbabilityMeasure μ]
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {R : Matrix Unit k ℝ} {β : k → ℝ} {C : ℝ}
    (h : TwoSLSAssumption12_2ObservedIidTextbookFourthConditions μ Z X e Y β)
    (hR : ∃ j : k, R () j ≠ 0)
    (hTrueBound :
      ∀ᶠ n in atTop,
        ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
          ‖twoSLSBootstrapTrueRecenteredScoreStatisticFinSucc
            Z e n ω ωs‖ ≤ C)
    (hResidSmall : ∀ δ : ℝ, 0 < δ →
      ∀ᶠ n in atTop,
        ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
          ‖twoSLSBootstrapResidualSubstitutionRecenteredScoreStatisticFinSucc
            Z X Y β n ω ωs‖ < δ)
    (hPopSmall : ∀ δ : ℝ, 0 < δ →
      ∀ᶠ n in atTop,
        ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
          dist (twoSLSBootstrapLinearizedGapFinSucc Z X Y n ω ωs)
            (twoSLSBootstrapPopulationLinearizedGapFinSucc
              (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
              (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
              (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))
              Z X Y n ω ωs) < δ)
    (hCoefSmall : ∀ δ : ℝ, 0 < δ →
      ∀ᶠ n in atTop,
        ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
          dist (twoSLSBootstrapBetaGapFinSucc Z X Y n ω ωs)
            (twoSLSBootstrapLinearizedGapFinSucc Z X Y n ω ωs) < δ)
    (hV_boot :
      TendstoInBootstrapProbabilityIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs => twoSLSBootstrapVHatStarFinSucc Z X Y n ω ωs)
        (fun _ =>
          twoSLSAsymptoticVariance
            (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (scoreCovMat μ Z e)
            (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X))))) :
    TendstoInBootstrapDistributionIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs => twoSLSBootstrapBetaGapFinSucc Z X Y n ω ωs)
        (multivariateGaussian (0 : EuclideanSpace ℝ k)
          (twoSLSAsymptoticVariance
            (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (scoreCovMat μ Z e)
            (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))))
        (fun z : EuclideanSpace ℝ k => (z : k → ℝ)) ∧
      TendstoInBootstrapDistributionIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs (_ : Unit) =>
          twoSLSBootstrapRobustLinearTStatFinSucc R Z X Y n ω ωs)
        (gaussianReal 0 1) (fun z : ℝ => fun _ : Unit => z) :=
  twoSLSBootstrap_theorem12_8_of_observed_textbook_fourth_uniform_remainders_trueScore_norm_bound_bootstrapCovarianceConsistency
    (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y) (R := R)
    (β := β) (C := C) h
    (oneRow_transpose_mulVec_injective_of_exists_ne_zero hR)
    hTrueBound hResidSmall hPopSmall hCoefSmall hV_boot

set_option linter.style.longLine false in
/-- Preferred direct-covariance Hansen Theorem 12.8 endpoint with the one-row
restriction rank condition stated as a nonzero row entry. -/
theorem
    twoSLSBootstrap_theorem12_8_of_textbook_fourth_uniform_remainders_trueScore_norm_bound_bootstrapCovarianceConsistency_row_ne_zero
    [IsProbabilityMeasure μ]
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {R : Matrix Unit k ℝ} {β : k → ℝ} {C : ℝ}
    (h : TwoSLSAssumption12_2JointIidTextbookFourthConditions μ Z X e Y β)
    (hR : ∃ j : k, R () j ≠ 0)
    (hTrueBound :
      ∀ᶠ n in atTop,
        ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
          ‖twoSLSBootstrapTrueRecenteredScoreStatisticFinSucc
            Z e n ω ωs‖ ≤ C)
    (hResidSmall : ∀ δ : ℝ, 0 < δ →
      ∀ᶠ n in atTop,
        ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
          ‖twoSLSBootstrapResidualSubstitutionRecenteredScoreStatisticFinSucc
            Z X Y β n ω ωs‖ < δ)
    (hPopSmall : ∀ δ : ℝ, 0 < δ →
      ∀ᶠ n in atTop,
        ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
          dist (twoSLSBootstrapLinearizedGapFinSucc Z X Y n ω ωs)
            (twoSLSBootstrapPopulationLinearizedGapFinSucc
              (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
              (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
              (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))
              Z X Y n ω ωs) < δ)
    (hCoefSmall : ∀ δ : ℝ, 0 < δ →
      ∀ᶠ n in atTop,
        ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
          dist (twoSLSBootstrapBetaGapFinSucc Z X Y n ω ωs)
            (twoSLSBootstrapLinearizedGapFinSucc Z X Y n ω ωs) < δ)
    (hV_boot :
      TendstoInBootstrapProbabilityIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs => twoSLSBootstrapVHatStarFinSucc Z X Y n ω ωs)
        (fun _ =>
          twoSLSAsymptoticVariance
            (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (scoreCovMat μ Z e)
            (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X))))) :
    TendstoInBootstrapDistributionIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs => twoSLSBootstrapBetaGapFinSucc Z X Y n ω ωs)
        (multivariateGaussian (0 : EuclideanSpace ℝ k)
          (twoSLSAsymptoticVariance
            (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (scoreCovMat μ Z e)
            (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))))
        (fun z : EuclideanSpace ℝ k => (z : k → ℝ)) ∧
      TendstoInBootstrapDistributionIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs (_ : Unit) =>
          twoSLSBootstrapRobustLinearTStatFinSucc R Z X Y n ω ωs)
        (gaussianReal 0 1) (fun z : ℝ => fun _ : Unit => z) :=
  twoSLSBootstrap_theorem12_8_of_textbook_fourth_uniform_remainders_trueScore_norm_bound_bootstrapCovarianceConsistency
    (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y) (R := R)
    (β := β) (C := C) h
    (oneRow_transpose_mulVec_injective_of_exists_ne_zero hR)
    hTrueBound hResidSmall hPopSmall hCoefSmall hV_boot

set_option linter.style.longLine false in
/-- Percentile-`t` coverage from the named mixed-moment Assumption 12.2
package, the minimal residual/coefficient empirical-process inputs, and direct
ordinary-bootstrap robust covariance consistency.

This is the coverage companion to
`twoSLSBootstrap_theorem12_8_of_mixed_moment_conditions_residualSubstitutionNegligibility_trueScoreTail_closeness_bootstrapCovarianceConsistency`.
It avoids routing interval validity through the covariance norm-tail primitive:
the bootstrap t-ratio limit is derived from direct consistency of
`twoSLSBootstrapVHatStarFinSucc`, then Chapter 10's percentile-`t` coverage
bridge consumes the named interval-side package. -/
theorem
    twoSLSBootstrapRobustPercentileTCIEventFinSucc_theorem12_8_of_mixed_moment_conditions_residualSubstitutionNegligibility_trueScoreTail_closeness_bootstrapCovarianceConsistency_coverageInputs
    [IsProbabilityMeasure μ]
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {R : Matrix Unit k ℝ} {β : k → ℝ} {q α : ℝ}
    (h : TwoSLSAssumption12_2JointIidMixedMomentConditions μ Z X e)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hR : Function.Injective Rᵀ.mulVec)
    (hresid :
      TwoSLSBootstrapResidualSubstitutionNegligibilityInputs μ Z X Y β)
    (hTrueTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set (EuclideanSpace ℝ l), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω =>
            (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω) n ω).real
              {ωs |
                twoSLSBootstrapTrueRecenteredScoreStatisticFinSucc
                  Z e n ω ωs ∉ K})
          atTop (fun _ => 0))
    (hcoef :
      TwoSLSBootstrapCoefficientLinearizationClosenessInputs μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω)) Z X Y
        (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
        (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
        (scoreCovMat μ Z e)
        (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X))))
    (hV_boot :
      TendstoInBootstrapProbabilityIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs => twoSLSBootstrapVHatStarFinSucc Z X Y n ω ωs)
        (fun _ =>
          twoSLSAsymptoticVariance
            (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (scoreCovMat μ Z e)
            (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))))
    (hcoverage :
      TwoSLSBootstrapRobustPercentileTCoverageInputs
        μ Z X Y β R q α) :
    Tendsto
      (fun n =>
        μ {ω |
          twoSLSBootstrapRobustPercentileTCIEventFinSucc
            R Z X Y β α n ω})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) := by
  have hTstar :
      TendstoInBootstrapDistributionIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs (_ : Unit) =>
          twoSLSBootstrapRobustLinearTStatFinSucc R Z X Y n ω ωs)
        (gaussianReal 0 1) (fun z : ℝ => fun _ : Unit => z) :=
    (twoSLSBootstrap_theorem12_8_of_mixed_moment_conditions_residualSubstitutionNegligibility_trueScoreTail_closeness_bootstrapCovarianceConsistency
      (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y) (R := R)
      h β hmodel hR hresid hTrueTail hcoef hV_boot).2
  exact
    twoSLSBootstrapRobustPercentileTCIEventFinSucc_tendsto_one_sub_alpha_uniform_of_coverageInputs
      (μ := μ) (Z := Z) (X := X) (Y := Y) (R := R) (β := β)
      (q := q) (α := α) hTstar hcoverage

set_option linter.style.longLine false in
/-- Literal finite-fourth Assumption 12.2 coverage wrapper for the direct
ordinary-bootstrap robust covariance consistency route. -/
theorem
    twoSLSBootstrapRobustPercentileTCIEventFinSucc_theorem12_8_of_textbook_fourth_residualSubstitutionNegligibility_trueScoreTail_closeness_bootstrapCovarianceConsistency_coverageInputs
    [IsProbabilityMeasure μ]
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {R : Matrix Unit k ℝ} {β : k → ℝ} {q α : ℝ}
    (h : TwoSLSAssumption12_2JointIidTextbookFourthConditions μ Z X e Y β)
    (hR : Function.Injective Rᵀ.mulVec)
    (hresid :
      TwoSLSBootstrapResidualSubstitutionNegligibilityInputs μ Z X Y β)
    (hTrueTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set (EuclideanSpace ℝ l), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω =>
            (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω) n ω).real
              {ωs |
                twoSLSBootstrapTrueRecenteredScoreStatisticFinSucc
                  Z e n ω ωs ∉ K})
          atTop (fun _ => 0))
    (hcoef :
      TwoSLSBootstrapCoefficientLinearizationClosenessInputs μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω)) Z X Y
        (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
        (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
        (scoreCovMat μ Z e)
        (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X))))
    (hV_boot :
      TendstoInBootstrapProbabilityIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs => twoSLSBootstrapVHatStarFinSucc Z X Y n ω ωs)
        (fun _ =>
          twoSLSAsymptoticVariance
            (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (scoreCovMat μ Z e)
            (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))))
    (hcoverage :
      TwoSLSBootstrapRobustPercentileTCoverageInputs
        μ Z X Y β R q α) :
    Tendsto
      (fun n =>
        μ {ω |
          twoSLSBootstrapRobustPercentileTCIEventFinSucc
            R Z X Y β α n ω})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) := by
  have hTstar :
      TendstoInBootstrapDistributionIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs (_ : Unit) =>
          twoSLSBootstrapRobustLinearTStatFinSucc R Z X Y n ω ωs)
        (gaussianReal 0 1) (fun z : ℝ => fun _ : Unit => z) :=
    (twoSLSBootstrap_theorem12_8_of_textbook_fourth_residualSubstitutionNegligibility_trueScoreTail_closeness_bootstrapCovarianceConsistency
      (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y) (R := R)
      (β := β) h hR hresid hTrueTail hcoef hV_boot).2
  exact
    twoSLSBootstrapRobustPercentileTCIEventFinSucc_tendsto_one_sub_alpha_uniform_of_coverageInputs
      (μ := μ) (Z := Z) (X := X) (Y := Y) (R := R) (β := β)
      (q := q) (α := α) hTstar hcoverage

set_option linter.style.longLine false in
/-- Percentile-`t` coverage from the named mixed-moment Assumption 12.2
package, minimal residual/coefficient inputs, direct bootstrap robust
covariance consistency, and explicit interval-side primitives.

This wrapper builds the coverage-input package internally from realized robust
covariance positive definiteness and the Chapter 10 quantile-calibration
package. -/
theorem
    twoSLSBootstrapRobustPercentileTCIEventFinSucc_theorem12_8_of_mixed_moment_conditions_residualSubstitutionNegligibility_trueScoreTail_closeness_bootstrapCovarianceConsistency_cov_posDef_quantileCalibration
    [IsProbabilityMeasure μ]
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {R : Matrix Unit k ℝ} {β : k → ℝ} {q α : ℝ}
    (h : TwoSLSAssumption12_2JointIidMixedMomentConditions μ Z X e)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hR : Function.Injective Rᵀ.mulVec)
    (hresid :
      TwoSLSBootstrapResidualSubstitutionNegligibilityInputs μ Z X Y β)
    (hTrueTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set (EuclideanSpace ℝ l), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω =>
            (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω) n ω).real
              {ωs |
                twoSLSBootstrapTrueRecenteredScoreStatisticFinSucc
                  Z e n ω ωs ∉ K})
          atTop (fun _ => 0))
    (hcoef :
      TwoSLSBootstrapCoefficientLinearizationClosenessInputs μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω)) Z X Y
        (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
        (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
        (scoreCovMat μ Z e)
        (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X))))
    (hV_boot :
      TendstoInBootstrapProbabilityIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs => twoSLSBootstrapVHatStarFinSucc Z X Y n ω ωs)
        (fun _ =>
          twoSLSAsymptoticVariance
            (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (scoreCovMat μ Z e)
            (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))))
    (hVhat_pos : ∀ n ω,
      (twoSLSVHatStar
        (stackRegressors Z (n + 1) ω) (stackRegressors X (n + 1) ω)
        (stackOutcomes Y (n + 1) ω)).PosDef)
    (hquantile :
      TwoSLSBootstrapRobustPercentileTQuantileCalibrationInputs
        μ Z X Y R q α) :
    Tendsto
      (fun n =>
        μ {ω |
          twoSLSBootstrapRobustPercentileTCIEventFinSucc
            R Z X Y β α n ω})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) :=
  twoSLSBootstrapRobustPercentileTCIEventFinSucc_theorem12_8_of_mixed_moment_conditions_residualSubstitutionNegligibility_trueScoreTail_closeness_bootstrapCovarianceConsistency_coverageInputs
    (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y)
    (R := R) (β := β) (q := q) (α := α)
    h hmodel hR hresid hTrueTail hcoef hV_boot
    (TwoSLSBootstrapRobustPercentileTCoverageInputs.of_mixed_moment_conditions_cov_posDef_quantileCalibration
      (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y)
      (β := β) (R := R) (q := q) (α := α)
      h hmodel hR hVhat_pos hquantile)

set_option linter.style.longLine false in
/-- Literal finite-fourth Assumption 12.2 coverage wrapper with direct
ordinary-bootstrap robust covariance consistency and explicit interval-side
primitives. -/
theorem
    twoSLSBootstrapRobustPercentileTCIEventFinSucc_theorem12_8_of_textbook_fourth_residualSubstitutionNegligibility_trueScoreTail_closeness_bootstrapCovarianceConsistency_cov_posDef_quantileCalibration
    [IsProbabilityMeasure μ]
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {R : Matrix Unit k ℝ} {β : k → ℝ} {q α : ℝ}
    (h : TwoSLSAssumption12_2JointIidTextbookFourthConditions μ Z X e Y β)
    (hR : Function.Injective Rᵀ.mulVec)
    (hresid :
      TwoSLSBootstrapResidualSubstitutionNegligibilityInputs μ Z X Y β)
    (hTrueTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set (EuclideanSpace ℝ l), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω =>
            (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω) n ω).real
              {ωs |
                twoSLSBootstrapTrueRecenteredScoreStatisticFinSucc
                  Z e n ω ωs ∉ K})
          atTop (fun _ => 0))
    (hcoef :
      TwoSLSBootstrapCoefficientLinearizationClosenessInputs μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω)) Z X Y
        (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
        (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
        (scoreCovMat μ Z e)
        (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X))))
    (hV_boot :
      TendstoInBootstrapProbabilityIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs => twoSLSBootstrapVHatStarFinSucc Z X Y n ω ωs)
        (fun _ =>
          twoSLSAsymptoticVariance
            (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (scoreCovMat μ Z e)
            (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))))
    (hVhat_pos : ∀ n ω,
      (twoSLSVHatStar
        (stackRegressors Z (n + 1) ω) (stackRegressors X (n + 1) ω)
        (stackOutcomes Y (n + 1) ω)).PosDef)
    (hquantile :
      TwoSLSBootstrapRobustPercentileTQuantileCalibrationInputs
        μ Z X Y R q α) :
    Tendsto
      (fun n =>
        μ {ω |
          twoSLSBootstrapRobustPercentileTCIEventFinSucc
            R Z X Y β α n ω})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) :=
  twoSLSBootstrapRobustPercentileTCIEventFinSucc_theorem12_8_of_textbook_fourth_residualSubstitutionNegligibility_trueScoreTail_closeness_bootstrapCovarianceConsistency_coverageInputs
    (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y)
    (R := R) (β := β) (q := q) (α := α)
    h hR hresid hTrueTail hcoef hV_boot
    (TwoSLSBootstrapRobustPercentileTCoverageInputs.of_textbook_fourth_cov_posDef_quantileCalibration
      (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y)
      (β := β) (R := R) (q := q) (α := α)
      h hR hVhat_pos hquantile)

set_option linter.style.longLine false in
/-- Percentile-`t` coverage from uniform residual/coefficient remainders and
direct ordinary-bootstrap robust covariance consistency.

This is the coverage companion to
`twoSLSBootstrap_theorem12_8_of_mixed_moment_conditions_uniform_remainders_trueScoreTail_bootstrapCovarianceConsistency`.
It keeps the interval-side sample and quantile conditions in the named
coverage-input package. -/
theorem
    twoSLSBootstrapRobustPercentileTCIEventFinSucc_theorem12_8_of_mixed_moment_conditions_uniform_remainders_trueScoreTail_bootstrapCovarianceConsistency_coverageInputs
    [IsProbabilityMeasure μ]
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {R : Matrix Unit k ℝ} {β : k → ℝ} {q α : ℝ}
    (h : TwoSLSAssumption12_2JointIidMixedMomentConditions μ Z X e)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hR : Function.Injective Rᵀ.mulVec)
    (hTrueTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set (EuclideanSpace ℝ l), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω =>
            (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω) n ω).real
              {ωs |
                twoSLSBootstrapTrueRecenteredScoreStatisticFinSucc
                  Z e n ω ωs ∉ K})
          atTop (fun _ => 0))
    (hResidSmall : ∀ δ : ℝ, 0 < δ →
      ∀ᶠ n in atTop,
        ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
          ‖twoSLSBootstrapResidualSubstitutionRecenteredScoreStatisticFinSucc
            Z X Y β n ω ωs‖ < δ)
    (hPopSmall : ∀ δ : ℝ, 0 < δ →
      ∀ᶠ n in atTop,
        ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
          dist (twoSLSBootstrapLinearizedGapFinSucc Z X Y n ω ωs)
            (twoSLSBootstrapPopulationLinearizedGapFinSucc
              (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
              (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
              (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))
              Z X Y n ω ωs) < δ)
    (hCoefSmall : ∀ δ : ℝ, 0 < δ →
      ∀ᶠ n in atTop,
        ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
          dist (twoSLSBootstrapBetaGapFinSucc Z X Y n ω ωs)
            (twoSLSBootstrapLinearizedGapFinSucc Z X Y n ω ωs) < δ)
    (hV_boot :
      TendstoInBootstrapProbabilityIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs => twoSLSBootstrapVHatStarFinSucc Z X Y n ω ωs)
        (fun _ =>
          twoSLSAsymptoticVariance
            (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (scoreCovMat μ Z e)
            (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))))
    (hcoverage :
      TwoSLSBootstrapRobustPercentileTCoverageInputs
        μ Z X Y β R q α) :
    Tendsto
      (fun n =>
        μ {ω |
          twoSLSBootstrapRobustPercentileTCIEventFinSucc
            R Z X Y β α n ω})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) := by
  have hTstar :
      TendstoInBootstrapDistributionIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs (_ : Unit) =>
          twoSLSBootstrapRobustLinearTStatFinSucc R Z X Y n ω ωs)
        (gaussianReal 0 1) (fun z : ℝ => fun _ : Unit => z) :=
    (twoSLSBootstrap_theorem12_8_of_mixed_moment_conditions_uniform_remainders_trueScoreTail_bootstrapCovarianceConsistency
      (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y) (R := R)
      (β := β) h hmodel hR hTrueTail hResidSmall hPopSmall
      hCoefSmall hV_boot).2
  exact
    twoSLSBootstrapRobustPercentileTCIEventFinSucc_tendsto_one_sub_alpha_uniform_of_coverageInputs
      (μ := μ) (Z := Z) (X := X) (Y := Y) (R := R) (β := β)
      (q := q) (α := α) hTstar hcoverage

set_option linter.style.longLine false in
/-- Textbook-fourth coverage endpoint from uniform residual/coefficient
remainders and direct ordinary-bootstrap robust covariance consistency. -/
theorem
    twoSLSBootstrapRobustPercentileTCIEventFinSucc_theorem12_8_of_textbook_fourth_uniform_remainders_trueScoreTail_bootstrapCovarianceConsistency_coverageInputs
    [IsProbabilityMeasure μ]
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {R : Matrix Unit k ℝ} {β : k → ℝ} {q α : ℝ}
    (h : TwoSLSAssumption12_2JointIidTextbookFourthConditions μ Z X e Y β)
    (hR : Function.Injective Rᵀ.mulVec)
    (hTrueTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set (EuclideanSpace ℝ l), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω =>
            (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω) n ω).real
              {ωs |
                twoSLSBootstrapTrueRecenteredScoreStatisticFinSucc
                  Z e n ω ωs ∉ K})
          atTop (fun _ => 0))
    (hResidSmall : ∀ δ : ℝ, 0 < δ →
      ∀ᶠ n in atTop,
        ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
          ‖twoSLSBootstrapResidualSubstitutionRecenteredScoreStatisticFinSucc
            Z X Y β n ω ωs‖ < δ)
    (hPopSmall : ∀ δ : ℝ, 0 < δ →
      ∀ᶠ n in atTop,
        ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
          dist (twoSLSBootstrapLinearizedGapFinSucc Z X Y n ω ωs)
            (twoSLSBootstrapPopulationLinearizedGapFinSucc
              (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
              (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
              (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))
              Z X Y n ω ωs) < δ)
    (hCoefSmall : ∀ δ : ℝ, 0 < δ →
      ∀ᶠ n in atTop,
        ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
          dist (twoSLSBootstrapBetaGapFinSucc Z X Y n ω ωs)
            (twoSLSBootstrapLinearizedGapFinSucc Z X Y n ω ωs) < δ)
    (hV_boot :
      TendstoInBootstrapProbabilityIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs => twoSLSBootstrapVHatStarFinSucc Z X Y n ω ωs)
        (fun _ =>
          twoSLSAsymptoticVariance
            (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (scoreCovMat μ Z e)
            (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))))
    (hcoverage :
      TwoSLSBootstrapRobustPercentileTCoverageInputs
        μ Z X Y β R q α) :
    Tendsto
      (fun n =>
        μ {ω |
          twoSLSBootstrapRobustPercentileTCIEventFinSucc
            R Z X Y β α n ω})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) := by
  have hTstar :
      TendstoInBootstrapDistributionIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs (_ : Unit) =>
          twoSLSBootstrapRobustLinearTStatFinSucc R Z X Y n ω ωs)
        (gaussianReal 0 1) (fun z : ℝ => fun _ : Unit => z) :=
    (twoSLSBootstrap_theorem12_8_of_textbook_fourth_uniform_remainders_trueScoreTail_bootstrapCovarianceConsistency
      (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y) (R := R)
      (β := β) h hR hTrueTail hResidSmall hPopSmall hCoefSmall
      hV_boot).2
  exact
    twoSLSBootstrapRobustPercentileTCIEventFinSucc_tendsto_one_sub_alpha_uniform_of_coverageInputs
      (μ := μ) (Z := Z) (X := X) (Y := Y) (R := R) (β := β)
      (q := q) (α := α) hTstar hcoverage

set_option linter.style.longLine false in
/-- Coverage from uniform residual/coefficient remainders, direct bootstrap
covariance consistency, realized robust covariance positive definiteness, and
quantile calibration. -/
theorem
    twoSLSBootstrapRobustPercentileTCIEventFinSucc_theorem12_8_of_mixed_moment_conditions_uniform_remainders_trueScoreTail_bootstrapCovarianceConsistency_cov_posDef_quantileCalibration
    [IsProbabilityMeasure μ]
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {R : Matrix Unit k ℝ} {β : k → ℝ} {q α : ℝ}
    (h : TwoSLSAssumption12_2JointIidMixedMomentConditions μ Z X e)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hR : Function.Injective Rᵀ.mulVec)
    (hTrueTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set (EuclideanSpace ℝ l), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω =>
            (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω) n ω).real
              {ωs |
                twoSLSBootstrapTrueRecenteredScoreStatisticFinSucc
                  Z e n ω ωs ∉ K})
          atTop (fun _ => 0))
    (hResidSmall : ∀ δ : ℝ, 0 < δ →
      ∀ᶠ n in atTop,
        ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
          ‖twoSLSBootstrapResidualSubstitutionRecenteredScoreStatisticFinSucc
            Z X Y β n ω ωs‖ < δ)
    (hPopSmall : ∀ δ : ℝ, 0 < δ →
      ∀ᶠ n in atTop,
        ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
          dist (twoSLSBootstrapLinearizedGapFinSucc Z X Y n ω ωs)
            (twoSLSBootstrapPopulationLinearizedGapFinSucc
              (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
              (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
              (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))
              Z X Y n ω ωs) < δ)
    (hCoefSmall : ∀ δ : ℝ, 0 < δ →
      ∀ᶠ n in atTop,
        ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
          dist (twoSLSBootstrapBetaGapFinSucc Z X Y n ω ωs)
            (twoSLSBootstrapLinearizedGapFinSucc Z X Y n ω ωs) < δ)
    (hV_boot :
      TendstoInBootstrapProbabilityIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs => twoSLSBootstrapVHatStarFinSucc Z X Y n ω ωs)
        (fun _ =>
          twoSLSAsymptoticVariance
            (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (scoreCovMat μ Z e)
            (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))))
    (hVhat_pos : ∀ n ω,
      (twoSLSVHatStar
        (stackRegressors Z (n + 1) ω) (stackRegressors X (n + 1) ω)
        (stackOutcomes Y (n + 1) ω)).PosDef)
    (hquantile :
      TwoSLSBootstrapRobustPercentileTQuantileCalibrationInputs
        μ Z X Y R q α) :
    Tendsto
      (fun n =>
        μ {ω |
          twoSLSBootstrapRobustPercentileTCIEventFinSucc
            R Z X Y β α n ω})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) :=
  twoSLSBootstrapRobustPercentileTCIEventFinSucc_theorem12_8_of_mixed_moment_conditions_uniform_remainders_trueScoreTail_bootstrapCovarianceConsistency_coverageInputs
    (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y)
    (R := R) (β := β) (q := q) (α := α)
    h hmodel hR hTrueTail hResidSmall hPopSmall hCoefSmall hV_boot
    (TwoSLSBootstrapRobustPercentileTCoverageInputs.of_mixed_moment_conditions_cov_posDef_quantileCalibration
      (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y)
      (β := β) (R := R) (q := q) (α := α)
      h hmodel hR hVhat_pos hquantile)

set_option linter.style.longLine false in
/-- Textbook-fourth coverage endpoint from uniform residual/coefficient
remainders, direct bootstrap covariance consistency, realized robust
covariance positive definiteness, and quantile calibration. -/
theorem
    twoSLSBootstrapRobustPercentileTCIEventFinSucc_theorem12_8_of_textbook_fourth_uniform_remainders_trueScoreTail_bootstrapCovarianceConsistency_cov_posDef_quantileCalibration
    [IsProbabilityMeasure μ]
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {R : Matrix Unit k ℝ} {β : k → ℝ} {q α : ℝ}
    (h : TwoSLSAssumption12_2JointIidTextbookFourthConditions μ Z X e Y β)
    (hR : Function.Injective Rᵀ.mulVec)
    (hTrueTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set (EuclideanSpace ℝ l), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω =>
            (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω) n ω).real
              {ωs |
                twoSLSBootstrapTrueRecenteredScoreStatisticFinSucc
                  Z e n ω ωs ∉ K})
          atTop (fun _ => 0))
    (hResidSmall : ∀ δ : ℝ, 0 < δ →
      ∀ᶠ n in atTop,
        ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
          ‖twoSLSBootstrapResidualSubstitutionRecenteredScoreStatisticFinSucc
            Z X Y β n ω ωs‖ < δ)
    (hPopSmall : ∀ δ : ℝ, 0 < δ →
      ∀ᶠ n in atTop,
        ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
          dist (twoSLSBootstrapLinearizedGapFinSucc Z X Y n ω ωs)
            (twoSLSBootstrapPopulationLinearizedGapFinSucc
              (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
              (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
              (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))
              Z X Y n ω ωs) < δ)
    (hCoefSmall : ∀ δ : ℝ, 0 < δ →
      ∀ᶠ n in atTop,
        ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
          dist (twoSLSBootstrapBetaGapFinSucc Z X Y n ω ωs)
            (twoSLSBootstrapLinearizedGapFinSucc Z X Y n ω ωs) < δ)
    (hV_boot :
      TendstoInBootstrapProbabilityIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs => twoSLSBootstrapVHatStarFinSucc Z X Y n ω ωs)
        (fun _ =>
          twoSLSAsymptoticVariance
            (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (scoreCovMat μ Z e)
            (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))))
    (hVhat_pos : ∀ n ω,
      (twoSLSVHatStar
        (stackRegressors Z (n + 1) ω) (stackRegressors X (n + 1) ω)
        (stackOutcomes Y (n + 1) ω)).PosDef)
    (hquantile :
      TwoSLSBootstrapRobustPercentileTQuantileCalibrationInputs
        μ Z X Y R q α) :
    Tendsto
      (fun n =>
        μ {ω |
          twoSLSBootstrapRobustPercentileTCIEventFinSucc
            R Z X Y β α n ω})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) :=
  twoSLSBootstrapRobustPercentileTCIEventFinSucc_theorem12_8_of_textbook_fourth_uniform_remainders_trueScoreTail_bootstrapCovarianceConsistency_coverageInputs
    (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y)
    (R := R) (β := β) (q := q) (α := α)
    h hR hTrueTail hResidSmall hPopSmall hCoefSmall hV_boot
    (TwoSLSBootstrapRobustPercentileTCoverageInputs.of_textbook_fourth_cov_posDef_quantileCalibration
      (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y)
      (β := β) (R := R) (q := q) (α := α)
      h hR hVhat_pos hquantile)

set_option linter.style.longLine false in
/-- Percentile-`t` coverage from uniform residual/coefficient remainders, a
deterministic true-score bound, direct bootstrap covariance consistency, and a
named coverage package. -/
theorem
    twoSLSBootstrapRobustPercentileTCIEventFinSucc_theorem12_8_of_mixed_moment_conditions_uniform_remainders_trueScore_norm_bound_bootstrapCovarianceConsistency_coverageInputs
    [IsProbabilityMeasure μ]
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {R : Matrix Unit k ℝ} {β : k → ℝ} {q α C : ℝ}
    (h : TwoSLSAssumption12_2JointIidMixedMomentConditions μ Z X e)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hR : Function.Injective Rᵀ.mulVec)
    (hTrueBound :
      ∀ᶠ n in atTop,
        ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
          ‖twoSLSBootstrapTrueRecenteredScoreStatisticFinSucc
            Z e n ω ωs‖ ≤ C)
    (hResidSmall : ∀ δ : ℝ, 0 < δ →
      ∀ᶠ n in atTop,
        ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
          ‖twoSLSBootstrapResidualSubstitutionRecenteredScoreStatisticFinSucc
            Z X Y β n ω ωs‖ < δ)
    (hPopSmall : ∀ δ : ℝ, 0 < δ →
      ∀ᶠ n in atTop,
        ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
          dist (twoSLSBootstrapLinearizedGapFinSucc Z X Y n ω ωs)
            (twoSLSBootstrapPopulationLinearizedGapFinSucc
              (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
              (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
              (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))
              Z X Y n ω ωs) < δ)
    (hCoefSmall : ∀ δ : ℝ, 0 < δ →
      ∀ᶠ n in atTop,
        ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
          dist (twoSLSBootstrapBetaGapFinSucc Z X Y n ω ωs)
            (twoSLSBootstrapLinearizedGapFinSucc Z X Y n ω ωs) < δ)
    (hV_boot :
      TendstoInBootstrapProbabilityIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs => twoSLSBootstrapVHatStarFinSucc Z X Y n ω ωs)
        (fun _ =>
          twoSLSAsymptoticVariance
            (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (scoreCovMat μ Z e)
            (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))))
    (hcoverage :
      TwoSLSBootstrapRobustPercentileTCoverageInputs
        μ Z X Y β R q α) :
    Tendsto
      (fun n =>
        μ {ω |
          twoSLSBootstrapRobustPercentileTCIEventFinSucc
            R Z X Y β α n ω})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) :=
  twoSLSBootstrapRobustPercentileTCIEventFinSucc_theorem12_8_of_mixed_moment_conditions_uniform_remainders_trueScoreTail_bootstrapCovarianceConsistency_coverageInputs
    (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y)
    (R := R) (β := β) (q := q) (α := α)
    h hmodel hR
    (twoSLSBootstrapTrueRecenteredScoreStatisticFinSucc_compactTail_uniform_of_eventually_norm_bound
      (μ := μ) (Z := Z) (e := e) hTrueBound)
    hResidSmall hPopSmall hCoefSmall hV_boot hcoverage

set_option linter.style.longLine false in
/-- Textbook-fourth coverage endpoint from uniform residual/coefficient
remainders, a deterministic true-score bound, direct bootstrap covariance
consistency, and a named coverage package. -/
theorem
    twoSLSBootstrapRobustPercentileTCIEventFinSucc_theorem12_8_of_textbook_fourth_uniform_remainders_trueScore_norm_bound_bootstrapCovarianceConsistency_coverageInputs
    [IsProbabilityMeasure μ]
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {R : Matrix Unit k ℝ} {β : k → ℝ} {q α C : ℝ}
    (h : TwoSLSAssumption12_2JointIidTextbookFourthConditions μ Z X e Y β)
    (hR : Function.Injective Rᵀ.mulVec)
    (hTrueBound :
      ∀ᶠ n in atTop,
        ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
          ‖twoSLSBootstrapTrueRecenteredScoreStatisticFinSucc
            Z e n ω ωs‖ ≤ C)
    (hResidSmall : ∀ δ : ℝ, 0 < δ →
      ∀ᶠ n in atTop,
        ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
          ‖twoSLSBootstrapResidualSubstitutionRecenteredScoreStatisticFinSucc
            Z X Y β n ω ωs‖ < δ)
    (hPopSmall : ∀ δ : ℝ, 0 < δ →
      ∀ᶠ n in atTop,
        ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
          dist (twoSLSBootstrapLinearizedGapFinSucc Z X Y n ω ωs)
            (twoSLSBootstrapPopulationLinearizedGapFinSucc
              (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
              (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
              (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))
              Z X Y n ω ωs) < δ)
    (hCoefSmall : ∀ δ : ℝ, 0 < δ →
      ∀ᶠ n in atTop,
        ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
          dist (twoSLSBootstrapBetaGapFinSucc Z X Y n ω ωs)
            (twoSLSBootstrapLinearizedGapFinSucc Z X Y n ω ωs) < δ)
    (hV_boot :
      TendstoInBootstrapProbabilityIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs => twoSLSBootstrapVHatStarFinSucc Z X Y n ω ωs)
        (fun _ =>
          twoSLSAsymptoticVariance
            (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (scoreCovMat μ Z e)
            (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))))
    (hcoverage :
      TwoSLSBootstrapRobustPercentileTCoverageInputs
        μ Z X Y β R q α) :
    Tendsto
      (fun n =>
        μ {ω |
          twoSLSBootstrapRobustPercentileTCIEventFinSucc
            R Z X Y β α n ω})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) :=
  twoSLSBootstrapRobustPercentileTCIEventFinSucc_theorem12_8_of_textbook_fourth_uniform_remainders_trueScoreTail_bootstrapCovarianceConsistency_coverageInputs
    (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y)
    (R := R) (β := β) (q := q) (α := α)
    h hR
    (twoSLSBootstrapTrueRecenteredScoreStatisticFinSucc_compactTail_uniform_of_eventually_norm_bound
      (μ := μ) (Z := Z) (e := e) hTrueBound)
    hResidSmall hPopSmall hCoefSmall hV_boot hcoverage

set_option linter.style.longLine false in
/-- Coverage from uniform residual/coefficient remainders, a deterministic
true-score bound, direct bootstrap covariance consistency, realized robust
covariance positive definiteness, and quantile calibration. -/
theorem
    twoSLSBootstrapRobustPercentileTCIEventFinSucc_theorem12_8_of_mixed_moment_conditions_uniform_remainders_trueScore_norm_bound_bootstrapCovarianceConsistency_cov_posDef_quantileCalibration
    [IsProbabilityMeasure μ]
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {R : Matrix Unit k ℝ} {β : k → ℝ} {q α C : ℝ}
    (h : TwoSLSAssumption12_2JointIidMixedMomentConditions μ Z X e)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hR : Function.Injective Rᵀ.mulVec)
    (hTrueBound :
      ∀ᶠ n in atTop,
        ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
          ‖twoSLSBootstrapTrueRecenteredScoreStatisticFinSucc
            Z e n ω ωs‖ ≤ C)
    (hResidSmall : ∀ δ : ℝ, 0 < δ →
      ∀ᶠ n in atTop,
        ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
          ‖twoSLSBootstrapResidualSubstitutionRecenteredScoreStatisticFinSucc
            Z X Y β n ω ωs‖ < δ)
    (hPopSmall : ∀ δ : ℝ, 0 < δ →
      ∀ᶠ n in atTop,
        ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
          dist (twoSLSBootstrapLinearizedGapFinSucc Z X Y n ω ωs)
            (twoSLSBootstrapPopulationLinearizedGapFinSucc
              (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
              (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
              (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))
              Z X Y n ω ωs) < δ)
    (hCoefSmall : ∀ δ : ℝ, 0 < δ →
      ∀ᶠ n in atTop,
        ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
          dist (twoSLSBootstrapBetaGapFinSucc Z X Y n ω ωs)
            (twoSLSBootstrapLinearizedGapFinSucc Z X Y n ω ωs) < δ)
    (hV_boot :
      TendstoInBootstrapProbabilityIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs => twoSLSBootstrapVHatStarFinSucc Z X Y n ω ωs)
        (fun _ =>
          twoSLSAsymptoticVariance
            (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (scoreCovMat μ Z e)
            (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))))
    (hVhat_pos : ∀ n ω,
      (twoSLSVHatStar
        (stackRegressors Z (n + 1) ω) (stackRegressors X (n + 1) ω)
        (stackOutcomes Y (n + 1) ω)).PosDef)
    (hquantile :
      TwoSLSBootstrapRobustPercentileTQuantileCalibrationInputs
        μ Z X Y R q α) :
    Tendsto
      (fun n =>
        μ {ω |
          twoSLSBootstrapRobustPercentileTCIEventFinSucc
            R Z X Y β α n ω})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) :=
  twoSLSBootstrapRobustPercentileTCIEventFinSucc_theorem12_8_of_mixed_moment_conditions_uniform_remainders_trueScoreTail_bootstrapCovarianceConsistency_cov_posDef_quantileCalibration
    (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y)
    (R := R) (β := β) (q := q) (α := α)
    h hmodel hR
    (twoSLSBootstrapTrueRecenteredScoreStatisticFinSucc_compactTail_uniform_of_eventually_norm_bound
      (μ := μ) (Z := Z) (e := e) hTrueBound)
    hResidSmall hPopSmall hCoefSmall hV_boot hVhat_pos hquantile

set_option linter.style.longLine false in
/-- Textbook-fourth coverage endpoint from uniform residual/coefficient
remainders, a deterministic true-score bound, direct bootstrap covariance
consistency, realized robust covariance positive definiteness, and quantile
calibration. -/
theorem
    twoSLSBootstrapRobustPercentileTCIEventFinSucc_theorem12_8_of_textbook_fourth_uniform_remainders_trueScore_norm_bound_bootstrapCovarianceConsistency_cov_posDef_quantileCalibration
    [IsProbabilityMeasure μ]
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {R : Matrix Unit k ℝ} {β : k → ℝ} {q α C : ℝ}
    (h : TwoSLSAssumption12_2JointIidTextbookFourthConditions μ Z X e Y β)
    (hR : Function.Injective Rᵀ.mulVec)
    (hTrueBound :
      ∀ᶠ n in atTop,
        ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
          ‖twoSLSBootstrapTrueRecenteredScoreStatisticFinSucc
            Z e n ω ωs‖ ≤ C)
    (hResidSmall : ∀ δ : ℝ, 0 < δ →
      ∀ᶠ n in atTop,
        ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
          ‖twoSLSBootstrapResidualSubstitutionRecenteredScoreStatisticFinSucc
            Z X Y β n ω ωs‖ < δ)
    (hPopSmall : ∀ δ : ℝ, 0 < δ →
      ∀ᶠ n in atTop,
        ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
          dist (twoSLSBootstrapLinearizedGapFinSucc Z X Y n ω ωs)
            (twoSLSBootstrapPopulationLinearizedGapFinSucc
              (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
              (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
              (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))
              Z X Y n ω ωs) < δ)
    (hCoefSmall : ∀ δ : ℝ, 0 < δ →
      ∀ᶠ n in atTop,
        ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
          dist (twoSLSBootstrapBetaGapFinSucc Z X Y n ω ωs)
            (twoSLSBootstrapLinearizedGapFinSucc Z X Y n ω ωs) < δ)
    (hV_boot :
      TendstoInBootstrapProbabilityIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs => twoSLSBootstrapVHatStarFinSucc Z X Y n ω ωs)
        (fun _ =>
          twoSLSAsymptoticVariance
            (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (scoreCovMat μ Z e)
            (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))))
    (hVhat_pos : ∀ n ω,
      (twoSLSVHatStar
        (stackRegressors Z (n + 1) ω) (stackRegressors X (n + 1) ω)
        (stackOutcomes Y (n + 1) ω)).PosDef)
    (hquantile :
      TwoSLSBootstrapRobustPercentileTQuantileCalibrationInputs
        μ Z X Y R q α) :
    Tendsto
      (fun n =>
        μ {ω |
          twoSLSBootstrapRobustPercentileTCIEventFinSucc
            R Z X Y β α n ω})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) :=
  twoSLSBootstrapRobustPercentileTCIEventFinSucc_theorem12_8_of_textbook_fourth_uniform_remainders_trueScoreTail_bootstrapCovarianceConsistency_cov_posDef_quantileCalibration
    (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y)
    (R := R) (β := β) (q := q) (α := α)
    h hR
    (twoSLSBootstrapTrueRecenteredScoreStatisticFinSucc_compactTail_uniform_of_eventually_norm_bound
      (μ := μ) (Z := Z) (e := e) hTrueBound)
    hResidSmall hPopSmall hCoefSmall hV_boot hVhat_pos hquantile

set_option linter.style.longLine false in
/-- Observed-row Assumption 12.2 percentile-`t` coverage endpoint from uniform
residual/coefficient remainders, a deterministic true-score bound, direct
bootstrap covariance consistency, realized robust covariance positive
definiteness, and quantile calibration.

This is the observed-row companion to the residual-row textbook-fourth coverage
wrapper; it changes only the public assumption surface by applying
`TwoSLSAssumption12_2ObservedIidTextbookFourthConditions.toResidualTextbookFourthConditions`. -/
theorem
    twoSLSBootstrapRobustPercentileTCIEventFinSucc_theorem12_8_of_observed_textbook_fourth_uniform_remainders_trueScore_norm_bound_bootstrapCovarianceConsistency_cov_posDef_quantileCalibration
    [IsProbabilityMeasure μ]
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {R : Matrix Unit k ℝ} {β : k → ℝ} {q α C : ℝ}
    (h : TwoSLSAssumption12_2ObservedIidTextbookFourthConditions μ Z X e Y β)
    (hR : Function.Injective Rᵀ.mulVec)
    (hTrueBound :
      ∀ᶠ n in atTop,
        ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
          ‖twoSLSBootstrapTrueRecenteredScoreStatisticFinSucc
            Z e n ω ωs‖ ≤ C)
    (hResidSmall : ∀ δ : ℝ, 0 < δ →
      ∀ᶠ n in atTop,
        ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
          ‖twoSLSBootstrapResidualSubstitutionRecenteredScoreStatisticFinSucc
            Z X Y β n ω ωs‖ < δ)
    (hPopSmall : ∀ δ : ℝ, 0 < δ →
      ∀ᶠ n in atTop,
        ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
          dist (twoSLSBootstrapLinearizedGapFinSucc Z X Y n ω ωs)
            (twoSLSBootstrapPopulationLinearizedGapFinSucc
              (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
              (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
              (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))
              Z X Y n ω ωs) < δ)
    (hCoefSmall : ∀ δ : ℝ, 0 < δ →
      ∀ᶠ n in atTop,
        ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
          dist (twoSLSBootstrapBetaGapFinSucc Z X Y n ω ωs)
            (twoSLSBootstrapLinearizedGapFinSucc Z X Y n ω ωs) < δ)
    (hV_boot :
      TendstoInBootstrapProbabilityIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs => twoSLSBootstrapVHatStarFinSucc Z X Y n ω ωs)
        (fun _ =>
          twoSLSAsymptoticVariance
            (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (scoreCovMat μ Z e)
            (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))))
    (hVhat_pos : ∀ n ω,
      (twoSLSVHatStar
        (stackRegressors Z (n + 1) ω) (stackRegressors X (n + 1) ω)
        (stackOutcomes Y (n + 1) ω)).PosDef)
    (hquantile :
      TwoSLSBootstrapRobustPercentileTQuantileCalibrationInputs
        μ Z X Y R q α) :
    Tendsto
      (fun n =>
        μ {ω |
          twoSLSBootstrapRobustPercentileTCIEventFinSucc
            R Z X Y β α n ω})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) :=
  twoSLSBootstrapRobustPercentileTCIEventFinSucc_theorem12_8_of_textbook_fourth_uniform_remainders_trueScore_norm_bound_bootstrapCovarianceConsistency_cov_posDef_quantileCalibration
    (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y)
    (R := R) (β := β) (q := q) (α := α) (C := C)
    h.toResidualTextbookFourthConditions hR
    hTrueBound hResidSmall hPopSmall hCoefSmall hV_boot hVhat_pos hquantile

set_option linter.style.longLine false in
/-- Observed-row Assumption 12.2 percentile-`t` coverage with the one-row
restriction rank condition stated as a nonzero row entry. -/
theorem
    twoSLSBootstrapRobustPercentileTCIEventFinSucc_theorem12_8_of_observed_textbook_fourth_uniform_remainders_trueScore_norm_bound_bootstrapCovarianceConsistency_cov_posDef_quantileCalibration_row_ne_zero
    [IsProbabilityMeasure μ]
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {R : Matrix Unit k ℝ} {β : k → ℝ} {q α C : ℝ}
    (h : TwoSLSAssumption12_2ObservedIidTextbookFourthConditions μ Z X e Y β)
    (hR : ∃ j : k, R () j ≠ 0)
    (hTrueBound :
      ∀ᶠ n in atTop,
        ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
          ‖twoSLSBootstrapTrueRecenteredScoreStatisticFinSucc
            Z e n ω ωs‖ ≤ C)
    (hResidSmall : ∀ δ : ℝ, 0 < δ →
      ∀ᶠ n in atTop,
        ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
          ‖twoSLSBootstrapResidualSubstitutionRecenteredScoreStatisticFinSucc
            Z X Y β n ω ωs‖ < δ)
    (hPopSmall : ∀ δ : ℝ, 0 < δ →
      ∀ᶠ n in atTop,
        ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
          dist (twoSLSBootstrapLinearizedGapFinSucc Z X Y n ω ωs)
            (twoSLSBootstrapPopulationLinearizedGapFinSucc
              (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
              (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
              (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))
              Z X Y n ω ωs) < δ)
    (hCoefSmall : ∀ δ : ℝ, 0 < δ →
      ∀ᶠ n in atTop,
        ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
          dist (twoSLSBootstrapBetaGapFinSucc Z X Y n ω ωs)
            (twoSLSBootstrapLinearizedGapFinSucc Z X Y n ω ωs) < δ)
    (hV_boot :
      TendstoInBootstrapProbabilityIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs => twoSLSBootstrapVHatStarFinSucc Z X Y n ω ωs)
        (fun _ =>
          twoSLSAsymptoticVariance
            (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (scoreCovMat μ Z e)
            (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))))
    (hVhat_pos : ∀ n ω,
      (twoSLSVHatStar
        (stackRegressors Z (n + 1) ω) (stackRegressors X (n + 1) ω)
        (stackOutcomes Y (n + 1) ω)).PosDef)
    (hquantile :
      TwoSLSBootstrapRobustPercentileTQuantileCalibrationInputs
        μ Z X Y R q α) :
    Tendsto
      (fun n =>
        μ {ω |
          twoSLSBootstrapRobustPercentileTCIEventFinSucc
            R Z X Y β α n ω})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) :=
  twoSLSBootstrapRobustPercentileTCIEventFinSucc_theorem12_8_of_observed_textbook_fourth_uniform_remainders_trueScore_norm_bound_bootstrapCovarianceConsistency_cov_posDef_quantileCalibration
    (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y)
    (R := R) (β := β) (q := q) (α := α) (C := C)
    h (oneRow_transpose_mulVec_injective_of_exists_ne_zero hR)
    hTrueBound hResidSmall hPopSmall hCoefSmall hV_boot hVhat_pos hquantile

set_option linter.style.longLine false in
/-- Textbook-fourth percentile-`t` quantile convergence and coverage from the
preferred direct-covariance Theorem 12.8 route, with the one-row restriction
rank condition stated as a nonzero row entry.

This is the residual-row companion to the observed-row theorem below.  It
returns Hansen's two bootstrap percentile-`t` critical-value limits and the
resulting interval coverage in one theorem-facing endpoint. -/
theorem
    twoSLSBootstrapRobustPercentileTCIEventFinSucc_quantiles_tendsto_and_coverage_theorem12_8_of_textbook_fourth_uniform_remainders_trueScore_norm_bound_bootstrapCovarianceConsistency_cov_posDef_quantileCalibration_row_ne_zero
    [IsProbabilityMeasure μ]
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {R : Matrix Unit k ℝ} {β : k → ℝ} {q α C : ℝ}
    (h : TwoSLSAssumption12_2JointIidTextbookFourthConditions μ Z X e Y β)
    (hR : ∃ j : k, R () j ≠ 0)
    (hTrueBound :
      ∀ᶠ n in atTop,
        ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
          ‖twoSLSBootstrapTrueRecenteredScoreStatisticFinSucc
            Z e n ω ωs‖ ≤ C)
    (hResidSmall : ∀ δ : ℝ, 0 < δ →
      ∀ᶠ n in atTop,
        ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
          ‖twoSLSBootstrapResidualSubstitutionRecenteredScoreStatisticFinSucc
            Z X Y β n ω ωs‖ < δ)
    (hPopSmall : ∀ δ : ℝ, 0 < δ →
      ∀ᶠ n in atTop,
        ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
          dist (twoSLSBootstrapLinearizedGapFinSucc Z X Y n ω ωs)
            (twoSLSBootstrapPopulationLinearizedGapFinSucc
              (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
              (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
              (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))
              Z X Y n ω ωs) < δ)
    (hCoefSmall : ∀ δ : ℝ, 0 < δ →
      ∀ᶠ n in atTop,
        ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
          dist (twoSLSBootstrapBetaGapFinSucc Z X Y n ω ωs)
            (twoSLSBootstrapLinearizedGapFinSucc Z X Y n ω ωs) < δ)
    (hV_boot :
      TendstoInBootstrapProbabilityIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs => twoSLSBootstrapVHatStarFinSucc Z X Y n ω ωs)
        (fun _ =>
          twoSLSAsymptoticVariance
            (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (scoreCovMat μ Z e)
            (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))))
    (hVhat_pos : ∀ n ω,
      (twoSLSVHatStar
        (stackRegressors Z (n + 1) ω) (stackRegressors X (n + 1) ω)
        (stackOutcomes Y (n + 1) ω)).PosDef)
    (hquantile :
      TwoSLSBootstrapRobustPercentileTQuantileCalibrationInputs
        μ Z X Y R q α) :
    (TendstoInMeasure μ
        (bootstrapScalarLowerQuantileIndexed
          (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
          (fun n ω ωs =>
            twoSLSBootstrapRobustLinearTStatFinSucc R Z X Y n ω ωs)
          (α / 2))
        atTop (fun _ => -q) ∧
      TendstoInMeasure μ
        (bootstrapScalarLowerQuantileIndexed
          (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
          (fun n ω ωs =>
            twoSLSBootstrapRobustLinearTStatFinSucc R Z X Y n ω ωs)
          (1 - α / 2))
        atTop (fun _ => q)) ∧
      Tendsto
        (fun n =>
          μ {ω |
            twoSLSBootstrapRobustPercentileTCIEventFinSucc
              R Z X Y β α n ω})
        atTop (𝓝 (ENNReal.ofReal (1 - α))) := by
  let hRinj : Function.Injective Rᵀ.mulVec :=
    oneRow_transpose_mulVec_injective_of_exists_ne_zero hR
  let hcoverage :
      TwoSLSBootstrapRobustPercentileTCoverageInputs
        μ Z X Y β R q α :=
    TwoSLSBootstrapRobustPercentileTCoverageInputs.of_textbook_fourth_cov_posDef_quantileCalibration
      (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y)
      (β := β) (R := R) (q := q) (α := α)
      h hRinj hVhat_pos hquantile
  exact
    twoSLSBootstrapRobustPercentileTCIEventFinSucc_quantiles_tendsto_and_coverage_of_sample_quantile
      (μ := μ) (Z := Z) (X := X) (Y := Y) (R := R)
      (β := β) (q := q) (α := α)
      (twoSLSBootstrap_theorem12_8_of_textbook_fourth_uniform_remainders_trueScore_norm_bound_bootstrapCovarianceConsistency
        (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y)
        (R := R) (β := β) (C := C) h hRinj hTrueBound
        hResidSmall hPopSmall hCoefSmall hV_boot).2
      hcoverage.sample hquantile

set_option linter.style.longLine false in
/-- Observed-row Assumption 12.2 percentile-`t` quantile convergence and
coverage from the preferred direct-covariance Theorem 12.8 route, with the
one-row restriction rank condition stated as a nonzero row entry.

This exposes the Chapter 10 quantile step as part of the theorem-facing
interval conclusion: the two bootstrap percentile-`t` critical values converge
to `-q` and `q`, and the resulting interval has limiting coverage `1 - α`. -/
theorem
    twoSLSBootstrapRobustPercentileTCIEventFinSucc_quantiles_tendsto_and_coverage_theorem12_8_of_observed_textbook_fourth_uniform_remainders_trueScore_norm_bound_bootstrapCovarianceConsistency_cov_posDef_quantileCalibration_row_ne_zero
    [IsProbabilityMeasure μ]
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {R : Matrix Unit k ℝ} {β : k → ℝ} {q α C : ℝ}
    (h : TwoSLSAssumption12_2ObservedIidTextbookFourthConditions μ Z X e Y β)
    (hR : ∃ j : k, R () j ≠ 0)
    (hTrueBound :
      ∀ᶠ n in atTop,
        ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
          ‖twoSLSBootstrapTrueRecenteredScoreStatisticFinSucc
            Z e n ω ωs‖ ≤ C)
    (hResidSmall : ∀ δ : ℝ, 0 < δ →
      ∀ᶠ n in atTop,
        ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
          ‖twoSLSBootstrapResidualSubstitutionRecenteredScoreStatisticFinSucc
            Z X Y β n ω ωs‖ < δ)
    (hPopSmall : ∀ δ : ℝ, 0 < δ →
      ∀ᶠ n in atTop,
        ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
          dist (twoSLSBootstrapLinearizedGapFinSucc Z X Y n ω ωs)
            (twoSLSBootstrapPopulationLinearizedGapFinSucc
              (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
              (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
              (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))
              Z X Y n ω ωs) < δ)
    (hCoefSmall : ∀ δ : ℝ, 0 < δ →
      ∀ᶠ n in atTop,
        ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
          dist (twoSLSBootstrapBetaGapFinSucc Z X Y n ω ωs)
            (twoSLSBootstrapLinearizedGapFinSucc Z X Y n ω ωs) < δ)
    (hV_boot :
      TendstoInBootstrapProbabilityIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs => twoSLSBootstrapVHatStarFinSucc Z X Y n ω ωs)
        (fun _ =>
          twoSLSAsymptoticVariance
            (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (scoreCovMat μ Z e)
            (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))))
    (hVhat_pos : ∀ n ω,
      (twoSLSVHatStar
        (stackRegressors Z (n + 1) ω) (stackRegressors X (n + 1) ω)
        (stackOutcomes Y (n + 1) ω)).PosDef)
    (hquantile :
      TwoSLSBootstrapRobustPercentileTQuantileCalibrationInputs
        μ Z X Y R q α) :
    (TendstoInMeasure μ
        (bootstrapScalarLowerQuantileIndexed
          (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
          (fun n ω ωs =>
            twoSLSBootstrapRobustLinearTStatFinSucc R Z X Y n ω ωs)
          (α / 2))
        atTop (fun _ => -q) ∧
      TendstoInMeasure μ
        (bootstrapScalarLowerQuantileIndexed
          (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
          (fun n ω ωs =>
            twoSLSBootstrapRobustLinearTStatFinSucc R Z X Y n ω ωs)
          (1 - α / 2))
        atTop (fun _ => q)) ∧
      Tendsto
        (fun n =>
          μ {ω |
            twoSLSBootstrapRobustPercentileTCIEventFinSucc
              R Z X Y β α n ω})
        atTop (𝓝 (ENNReal.ofReal (1 - α))) := by
  let hRinj : Function.Injective Rᵀ.mulVec :=
    oneRow_transpose_mulVec_injective_of_exists_ne_zero hR
  let hcoverage :
      TwoSLSBootstrapRobustPercentileTCoverageInputs
        μ Z X Y β R q α :=
    TwoSLSBootstrapRobustPercentileTCoverageInputs.of_textbook_fourth_cov_posDef_quantileCalibration
      (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y)
      (β := β) (R := R) (q := q) (α := α)
      h.toResidualTextbookFourthConditions hRinj hVhat_pos hquantile
  exact
    twoSLSBootstrapRobustPercentileTCIEventFinSucc_quantiles_tendsto_and_coverage_of_sample_quantile
      (μ := μ) (Z := Z) (X := X) (Y := Y) (R := R)
      (β := β) (q := q) (α := α)
      (twoSLSBootstrap_theorem12_8_of_observed_textbook_fourth_uniform_remainders_trueScore_norm_bound_bootstrapCovarianceConsistency
        (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y)
        (R := R) (β := β) (C := C) h hRinj hTrueBound
        hResidSmall hPopSmall hCoefSmall hV_boot).2
      hcoverage.sample hquantile

set_option linter.style.longLine false in
/-- Historical bounded-score compatibility assembly for the direct-covariance
route; this is not a Hansen-facing endpoint.

This bundles the coefficient bootstrap Gaussian limit, robust one-row
studentized bootstrap limit, and the percentile-`t` quantile/coverage
conclusion. Its pathwise bounded-score premise is incompatible with the
nondegenerate Gaussian score limit in Assumption 12.2, so it is retained only
as private same-file proof scaffolding. -/
private theorem boundedScoreCompatibilityFull
    [IsProbabilityMeasure μ]
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {R : Matrix Unit k ℝ} {β : k → ℝ} {q α C : ℝ}
    (h : TwoSLSAssumption12_2ObservedIidTextbookFourthConditions μ Z X e Y β)
    (hR : ∃ j : k, R () j ≠ 0)
    (hTrueBound :
      ∀ᶠ n in atTop,
        ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
          ‖twoSLSBootstrapTrueRecenteredScoreStatisticFinSucc
            Z e n ω ωs‖ ≤ C)
    (hResidSmall : ∀ δ : ℝ, 0 < δ →
      ∀ᶠ n in atTop,
        ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
          ‖twoSLSBootstrapResidualSubstitutionRecenteredScoreStatisticFinSucc
            Z X Y β n ω ωs‖ < δ)
    (hPopSmall : ∀ δ : ℝ, 0 < δ →
      ∀ᶠ n in atTop,
        ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
          dist (twoSLSBootstrapLinearizedGapFinSucc Z X Y n ω ωs)
            (twoSLSBootstrapPopulationLinearizedGapFinSucc
              (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
              (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
              (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))
              Z X Y n ω ωs) < δ)
    (hCoefSmall : ∀ δ : ℝ, 0 < δ →
      ∀ᶠ n in atTop,
        ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
          dist (twoSLSBootstrapBetaGapFinSucc Z X Y n ω ωs)
            (twoSLSBootstrapLinearizedGapFinSucc Z X Y n ω ωs) < δ)
    (hV_boot :
      TendstoInBootstrapProbabilityIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs => twoSLSBootstrapVHatStarFinSucc Z X Y n ω ωs)
        (fun _ =>
          twoSLSAsymptoticVariance
            (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (scoreCovMat μ Z e)
            (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))))
    (hVhat_pos : ∀ n ω,
      (twoSLSVHatStar
        (stackRegressors Z (n + 1) ω) (stackRegressors X (n + 1) ω)
        (stackOutcomes Y (n + 1) ω)).PosDef)
    (hquantile :
      TwoSLSBootstrapRobustPercentileTQuantileCalibrationInputs
        μ Z X Y R q α) :
    TendstoInBootstrapDistributionIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs => twoSLSBootstrapBetaGapFinSucc Z X Y n ω ωs)
        (multivariateGaussian (0 : EuclideanSpace ℝ k)
          (twoSLSAsymptoticVariance
            (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (scoreCovMat μ Z e)
            (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))))
        (fun z : EuclideanSpace ℝ k => (z : k → ℝ)) ∧
      TendstoInBootstrapDistributionIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs (_ : Unit) =>
          twoSLSBootstrapRobustLinearTStatFinSucc R Z X Y n ω ωs)
        (gaussianReal 0 1) (fun z : ℝ => fun _ : Unit => z) ∧
      (TendstoInMeasure μ
          (bootstrapScalarLowerQuantileIndexed
            (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
            (fun n ω ωs =>
              twoSLSBootstrapRobustLinearTStatFinSucc R Z X Y n ω ωs)
            (α / 2))
          atTop (fun _ => -q) ∧
        TendstoInMeasure μ
          (bootstrapScalarLowerQuantileIndexed
            (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
            (fun n ω ωs =>
              twoSLSBootstrapRobustLinearTStatFinSucc R Z X Y n ω ωs)
            (1 - α / 2))
          atTop (fun _ => q)) ∧
        Tendsto
          (fun n =>
            μ {ω |
              twoSLSBootstrapRobustPercentileTCIEventFinSucc
                R Z X Y β α n ω})
          atTop (𝓝 (ENNReal.ofReal (1 - α))) := by
  have hdist :=
    twoSLSBootstrap_theorem12_8_of_observed_textbook_fourth_uniform_remainders_trueScore_norm_bound_bootstrapCovarianceConsistency_row_ne_zero
      (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y)
      (R := R) (β := β) (C := C) h hR hTrueBound
      hResidSmall hPopSmall hCoefSmall hV_boot
  have hci :=
    twoSLSBootstrapRobustPercentileTCIEventFinSucc_quantiles_tendsto_and_coverage_theorem12_8_of_observed_textbook_fourth_uniform_remainders_trueScore_norm_bound_bootstrapCovarianceConsistency_cov_posDef_quantileCalibration_row_ne_zero
      (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y)
      (R := R) (β := β) (q := q) (α := α) (C := C)
      h hR hTrueBound hResidSmall hPopSmall hCoefSmall hV_boot
      hVhat_pos hquantile
  exact ⟨hdist.1, hdist.2, hci⟩

set_option linter.style.longLine false in
/-- Textbook-fourth percentile-`t` coverage with the one-row restriction rank
condition stated as a nonzero row entry. -/
theorem
    twoSLSBootstrapRobustPercentileTCIEventFinSucc_theorem12_8_of_textbook_fourth_uniform_remainders_trueScore_norm_bound_bootstrapCovarianceConsistency_cov_posDef_quantileCalibration_row_ne_zero
    [IsProbabilityMeasure μ]
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {R : Matrix Unit k ℝ} {β : k → ℝ} {q α C : ℝ}
    (h : TwoSLSAssumption12_2JointIidTextbookFourthConditions μ Z X e Y β)
    (hR : ∃ j : k, R () j ≠ 0)
    (hTrueBound :
      ∀ᶠ n in atTop,
        ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
          ‖twoSLSBootstrapTrueRecenteredScoreStatisticFinSucc
            Z e n ω ωs‖ ≤ C)
    (hResidSmall : ∀ δ : ℝ, 0 < δ →
      ∀ᶠ n in atTop,
        ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
          ‖twoSLSBootstrapResidualSubstitutionRecenteredScoreStatisticFinSucc
            Z X Y β n ω ωs‖ < δ)
    (hPopSmall : ∀ δ : ℝ, 0 < δ →
      ∀ᶠ n in atTop,
        ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
          dist (twoSLSBootstrapLinearizedGapFinSucc Z X Y n ω ωs)
            (twoSLSBootstrapPopulationLinearizedGapFinSucc
              (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
              (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
              (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))
              Z X Y n ω ωs) < δ)
    (hCoefSmall : ∀ δ : ℝ, 0 < δ →
      ∀ᶠ n in atTop,
        ∀ ω (ωs : Fin (n + 1) → Fin (n + 1)),
          dist (twoSLSBootstrapBetaGapFinSucc Z X Y n ω ωs)
            (twoSLSBootstrapLinearizedGapFinSucc Z X Y n ω ωs) < δ)
    (hV_boot :
      TendstoInBootstrapProbabilityIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs => twoSLSBootstrapVHatStarFinSucc Z X Y n ω ωs)
        (fun _ =>
          twoSLSAsymptoticVariance
            (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (scoreCovMat μ Z e)
            (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))))
    (hVhat_pos : ∀ n ω,
      (twoSLSVHatStar
        (stackRegressors Z (n + 1) ω) (stackRegressors X (n + 1) ω)
        (stackOutcomes Y (n + 1) ω)).PosDef)
    (hquantile :
      TwoSLSBootstrapRobustPercentileTQuantileCalibrationInputs
        μ Z X Y R q α) :
    Tendsto
      (fun n =>
        μ {ω |
          twoSLSBootstrapRobustPercentileTCIEventFinSucc
            R Z X Y β α n ω})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) :=
  twoSLSBootstrapRobustPercentileTCIEventFinSucc_theorem12_8_of_textbook_fourth_uniform_remainders_trueScore_norm_bound_bootstrapCovarianceConsistency_cov_posDef_quantileCalibration
    (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y)
    (R := R) (β := β) (q := q) (α := α) (C := C)
    h (oneRow_transpose_mulVec_injective_of_exists_ne_zero hR)
    hTrueBound hResidSmall hPopSmall hCoefSmall hV_boot hVhat_pos hquantile

set_option linter.style.longLine false in
/-- Percentile-`t` coverage from the named mixed-moment Assumption 12.2
package, residual-substitution package, coefficient closeness, and primitive
robust-covariance resampling.

This is the coverage companion to
`twoSLSBootstrap_theorem12_8_of_mixed_moment_conditions_residualSubstitution_closeness_covariancePrimitive`;
it derives the bootstrap t-ratio limit from that wrapper and then applies the
generic percentile-`t` coverage bridge. -/
theorem
    twoSLSBootstrapRobustPercentileTCIEventFinSucc_theorem12_8_of_mixed_moment_conditions_residualSubstitution_closeness_covariancePrimitive_coverageInputs
    [IsProbabilityMeasure μ]
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {R : Matrix Unit k ℝ} {β : k → ℝ} {q α : ℝ}
    (h : TwoSLSAssumption12_2JointIidMixedMomentConditions μ Z X e)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hR : Function.Injective Rᵀ.mulVec)
    (hresid : TwoSLSBootstrapResidualSubstitutionInputs μ Z X Y e β)
    (hcoef :
      TwoSLSBootstrapCoefficientLinearizationClosenessInputs μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω)) Z X Y
        (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
        (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
        (scoreCovMat μ Z e)
        (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X))))
    (hcov : TwoSLSBootstrapRobustCovarianceResamplePrimitiveInputs μ Z X Y)
    (hcoverage :
      TwoSLSBootstrapRobustPercentileTCoverageInputs
        μ Z X Y β R q α) :
    Tendsto
      (fun n =>
        μ {ω |
          twoSLSBootstrapRobustPercentileTCIEventFinSucc
            R Z X Y β α n ω})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) := by
  have hTstar :
      TendstoInBootstrapDistributionIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs (_ : Unit) =>
          twoSLSBootstrapRobustLinearTStatFinSucc R Z X Y n ω ωs)
        (gaussianReal 0 1) (fun z : ℝ => fun _ : Unit => z) :=
    (twoSLSBootstrap_theorem12_8_of_mixed_moment_conditions_residualSubstitution_closeness_covariancePrimitive
      (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y) (R := R)
      h β hmodel hR hresid hcoef hcov).2
  exact
    twoSLSBootstrapRobustPercentileTCIEventFinSucc_tendsto_one_sub_alpha_uniform_of_coverageInputs
      (μ := μ) (Z := Z) (X := X) (Y := Y) (R := R) (β := β)
      (q := q) (α := α) hTstar hcoverage

set_option linter.style.longLine false in
/-- Percentile-`t` coverage from the named mixed-moment Assumption 12.2
package and the score-tail primitive bootstrap empirical-process package.

The bootstrap t-ratio limit is derived by the previous mixed-moment wrapper;
the interval-side sample t-ratio and quantile calibration remain bundled in
`TwoSLSBootstrapRobustPercentileTCoverageInputs`. -/
theorem
    twoSLSBootstrapRobustPercentileTCIEventFinSucc_theorem12_8_of_mixed_moment_conditions_scoreTailPrimitiveEmpiricalProcess_coverageInputs
    [IsProbabilityMeasure μ]
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {R : Matrix Unit k ℝ} {β : k → ℝ} {q α : ℝ}
    (h : TwoSLSAssumption12_2JointIidMixedMomentConditions μ Z X e)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hR : Function.Injective Rᵀ.mulVec)
    (hboot :
      TwoSLSBootstrapTheorem12_8ScoreTailPrimitiveEmpiricalProcessInputs
        μ Z X Y e β R)
    (hcoverage :
      TwoSLSBootstrapRobustPercentileTCoverageInputs
        μ Z X Y β R q α) :
    Tendsto
      (fun n =>
        μ {ω |
          twoSLSBootstrapRobustPercentileTCIEventFinSucc
            R Z X Y β α n ω})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) := by
  have hTstar :
      TendstoInBootstrapDistributionIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs (_ : Unit) =>
          twoSLSBootstrapRobustLinearTStatFinSucc R Z X Y n ω ωs)
        (gaussianReal 0 1) (fun z : ℝ => fun _ : Unit => z) :=
    (twoSLSBootstrap_theorem12_8_of_mixed_moment_conditions_scoreTailPrimitiveEmpiricalProcess
      (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y) (R := R)
      h β hmodel hR hboot).2
  exact
    twoSLSBootstrapRobustPercentileTCIEventFinSucc_tendsto_one_sub_alpha_uniform_of_coverageInputs
      (μ := μ) (Z := Z) (X := X) (Y := Y) (R := R) (β := β)
      (q := q) (α := α) hTstar hcoverage

set_option linter.style.longLine false in
/-- Percentile-`t` coverage from the literal textbook Assumption 12.2 package
and the score-tail primitive bootstrap empirical-process package.

The theorem reuses the textbook-facing coefficient/t-ratio endpoint and the
Chapter 10 percentile-`t` coverage bridge. It does not assume coverage or a
bootstrap t-ratio conclusion as a primitive premise. -/
theorem
    twoSLSBootstrapRobustPercentileTCIEventFinSucc_theorem12_8_of_textbook_fourth_scoreTailPrimitiveEmpiricalProcess_coverageInputs
    [IsProbabilityMeasure μ]
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {R : Matrix Unit k ℝ} {β : k → ℝ} {q α : ℝ}
    (h : TwoSLSAssumption12_2JointIidTextbookFourthConditions μ Z X e Y β)
    (hR : Function.Injective Rᵀ.mulVec)
    (hboot :
      TwoSLSBootstrapTheorem12_8ScoreTailPrimitiveEmpiricalProcessInputs
        μ Z X Y e β R)
    (hcoverage :
      TwoSLSBootstrapRobustPercentileTCoverageInputs
        μ Z X Y β R q α) :
    Tendsto
      (fun n =>
        μ {ω |
          twoSLSBootstrapRobustPercentileTCIEventFinSucc
            R Z X Y β α n ω})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) := by
  have hTstar :
      TendstoInBootstrapDistributionIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs (_ : Unit) =>
          twoSLSBootstrapRobustLinearTStatFinSucc R Z X Y n ω ωs)
        (gaussianReal 0 1) (fun z : ℝ => fun _ : Unit => z) :=
    (twoSLSBootstrap_theorem12_8_of_textbook_fourth_scoreTailPrimitiveEmpiricalProcess
      (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y) (R := R)
      (β := β) h hR hboot).2
  exact
    twoSLSBootstrapRobustPercentileTCIEventFinSucc_tendsto_one_sub_alpha_uniform_of_coverageInputs
      (μ := μ) (Z := Z) (X := X) (Y := Y) (R := R) (β := β)
      (q := q) (α := α) hTstar hcoverage

set_option linter.style.longLine false in
/-- Percentile-`t` coverage from the named mixed-moment Assumption 12.2
package, the score-tail primitive bootstrap empirical-process package, and
the remaining interval-side primitives.

Compared with
`twoSLSBootstrapRobustPercentileTCIEventFinSucc_theorem12_8_of_mixed_moment_conditions_scoreTailPrimitiveEmpiricalProcess_coverageInputs`,
this theorem builds the named coverage-input package internally.  The sample
robust `t`-ratio limit is derived from Assumption 12.2 and the covariance
weight WLLNs; callers only provide realized robust covariance positive
definiteness and the Chapter 10 percentile-`t` quantile calibration package. -/
theorem
    twoSLSBootstrapRobustPercentileTCIEventFinSucc_theorem12_8_of_mixed_moment_conditions_scoreTailPrimitiveEmpiricalProcess_cov_posDef_quantileCalibration
    [IsProbabilityMeasure μ]
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {R : Matrix Unit k ℝ} {β : k → ℝ} {q α : ℝ}
    (h : TwoSLSAssumption12_2JointIidMixedMomentConditions μ Z X e)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hR : Function.Injective Rᵀ.mulVec)
    (hboot :
      TwoSLSBootstrapTheorem12_8ScoreTailPrimitiveEmpiricalProcessInputs
        μ Z X Y e β R)
    (hVhat_pos : ∀ n ω,
      (twoSLSVHatStar
        (stackRegressors Z (n + 1) ω) (stackRegressors X (n + 1) ω)
        (stackOutcomes Y (n + 1) ω)).PosDef)
    (hquantile :
      TwoSLSBootstrapRobustPercentileTQuantileCalibrationInputs
        μ Z X Y R q α) :
    Tendsto
      (fun n =>
        μ {ω |
          twoSLSBootstrapRobustPercentileTCIEventFinSucc
            R Z X Y β α n ω})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) :=
  twoSLSBootstrapRobustPercentileTCIEventFinSucc_theorem12_8_of_mixed_moment_conditions_scoreTailPrimitiveEmpiricalProcess_coverageInputs
    (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y)
    (R := R) (β := β) (q := q) (α := α) h hmodel hR hboot
    (TwoSLSBootstrapRobustPercentileTCoverageInputs.of_mixed_moment_conditions_cov_posDef_quantileCalibration
      (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y)
      (β := β) (R := R) (q := q) (α := α)
      h hmodel hR hVhat_pos hquantile)

set_option linter.style.longLine false in
/-- Textbook-fourth Assumption 12.2 coverage wrapper with the score-tail
primitive bootstrap empirical-process package and the remaining interval-side
primitives.

This is the literal textbook-facing companion to
`twoSLSBootstrapRobustPercentileTCIEventFinSucc_theorem12_8_of_mixed_moment_conditions_scoreTailPrimitiveEmpiricalProcess_cov_posDef_quantileCalibration`.
The textbook fourth-moment package supplies the mixed-moment and covariance
weight-WLLN inputs; the theorem still keeps realized robust covariance positive
definiteness and bootstrap quantile calibration explicit. -/
theorem
    twoSLSBootstrapRobustPercentileTCIEventFinSucc_theorem12_8_of_textbook_fourth_scoreTailPrimitiveEmpiricalProcess_cov_posDef_quantileCalibration
    [IsProbabilityMeasure μ]
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {R : Matrix Unit k ℝ} {β : k → ℝ} {q α : ℝ}
    (h : TwoSLSAssumption12_2JointIidTextbookFourthConditions μ Z X e Y β)
    (hR : Function.Injective Rᵀ.mulVec)
    (hboot :
      TwoSLSBootstrapTheorem12_8ScoreTailPrimitiveEmpiricalProcessInputs
        μ Z X Y e β R)
    (hVhat_pos : ∀ n ω,
      (twoSLSVHatStar
        (stackRegressors Z (n + 1) ω) (stackRegressors X (n + 1) ω)
        (stackOutcomes Y (n + 1) ω)).PosDef)
    (hquantile :
      TwoSLSBootstrapRobustPercentileTQuantileCalibrationInputs
        μ Z X Y R q α) :
    Tendsto
      (fun n =>
        μ {ω |
          twoSLSBootstrapRobustPercentileTCIEventFinSucc
            R Z X Y β α n ω})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) :=
  twoSLSBootstrapRobustPercentileTCIEventFinSucc_theorem12_8_of_textbook_fourth_scoreTailPrimitiveEmpiricalProcess_coverageInputs
    (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y)
    (R := R) (β := β) (q := q) (α := α) h hR hboot
    (TwoSLSBootstrapRobustPercentileTCoverageInputs.of_textbook_fourth_cov_posDef_quantileCalibration
      (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y)
      (β := β) (R := R) (q := q) (α := α)
      h hR hVhat_pos hquantile)

set_option linter.style.longLine false in
/-- Observed-row Assumption 12.2 percentile-`t` coverage wrapper with the
score-tail primitive bootstrap empirical-process package.

This is the observed-row companion to
`twoSLSBootstrapRobustPercentileTCIEventFinSucc_theorem12_8_of_textbook_fourth_scoreTailPrimitiveEmpiricalProcess_coverageInputs`.
The coverage-input package is unchanged; only the Assumption 12.2 package is
converted to the residual-row proof engine at the theorem boundary. -/
theorem
    twoSLSBootstrapRobustPercentileTCIEventFinSucc_theorem12_8_of_observed_textbook_fourth_scoreTailPrimitiveEmpiricalProcess_coverageInputs
    [IsProbabilityMeasure μ]
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {R : Matrix Unit k ℝ} {β : k → ℝ} {q α : ℝ}
    (h : TwoSLSAssumption12_2ObservedIidTextbookFourthConditions μ Z X e Y β)
    (hR : Function.Injective Rᵀ.mulVec)
    (hboot :
      TwoSLSBootstrapTheorem12_8ScoreTailPrimitiveEmpiricalProcessInputs
        μ Z X Y e β R)
    (hcoverage :
      TwoSLSBootstrapRobustPercentileTCoverageInputs
        μ Z X Y β R q α) :
    Tendsto
      (fun n =>
        μ {ω |
          twoSLSBootstrapRobustPercentileTCIEventFinSucc
            R Z X Y β α n ω})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) :=
  twoSLSBootstrapRobustPercentileTCIEventFinSucc_theorem12_8_of_textbook_fourth_scoreTailPrimitiveEmpiricalProcess_coverageInputs
    (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y)
    (R := R) (β := β) (q := q) (α := α)
    h.toResidualTextbookFourthConditions hR hboot hcoverage

set_option linter.style.longLine false in
/-- Observed-row Assumption 12.2 coverage wrapper with the score-tail primitive
bootstrap empirical-process package and the interval-side positive-definiteness
and quantile-calibration primitives. -/
theorem
    twoSLSBootstrapRobustPercentileTCIEventFinSucc_theorem12_8_of_observed_textbook_fourth_scoreTailPrimitiveEmpiricalProcess_cov_posDef_quantileCalibration
    [IsProbabilityMeasure μ]
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {R : Matrix Unit k ℝ} {β : k → ℝ} {q α : ℝ}
    (h : TwoSLSAssumption12_2ObservedIidTextbookFourthConditions μ Z X e Y β)
    (hR : Function.Injective Rᵀ.mulVec)
    (hboot :
      TwoSLSBootstrapTheorem12_8ScoreTailPrimitiveEmpiricalProcessInputs
        μ Z X Y e β R)
    (hVhat_pos : ∀ n ω,
      (twoSLSVHatStar
        (stackRegressors Z (n + 1) ω) (stackRegressors X (n + 1) ω)
        (stackOutcomes Y (n + 1) ω)).PosDef)
    (hquantile :
      TwoSLSBootstrapRobustPercentileTQuantileCalibrationInputs
        μ Z X Y R q α) :
    Tendsto
      (fun n =>
        μ {ω |
          twoSLSBootstrapRobustPercentileTCIEventFinSucc
            R Z X Y β α n ω})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) :=
  twoSLSBootstrapRobustPercentileTCIEventFinSucc_theorem12_8_of_observed_textbook_fourth_scoreTailPrimitiveEmpiricalProcess_coverageInputs
    (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y)
    (R := R) (β := β) (q := q) (α := α) h hR hboot
    (TwoSLSBootstrapRobustPercentileTCoverageInputs.of_textbook_fourth_cov_posDef_quantileCalibration
      (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y)
      (β := β) (R := R) (q := q) (α := α)
      h.toResidualTextbookFourthConditions hR hVhat_pos hquantile)

set_option linter.style.longLine false in
/-- Observed-row Assumption 12.2 coverage wrapper with the one-row restriction
rank condition stated as a nonzero row entry. -/
theorem
    twoSLSBootstrapRobustPercentileTCIEventFinSucc_theorem12_8_of_observed_textbook_fourth_scoreTailPrimitiveEmpiricalProcess_cov_posDef_quantileCalibration_row_ne_zero
    [IsProbabilityMeasure μ]
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {R : Matrix Unit k ℝ} {β : k → ℝ} {q α : ℝ}
    (h : TwoSLSAssumption12_2ObservedIidTextbookFourthConditions μ Z X e Y β)
    (hR : ∃ j : k, R () j ≠ 0)
    (hboot :
      TwoSLSBootstrapTheorem12_8ScoreTailPrimitiveEmpiricalProcessInputs
        μ Z X Y e β R)
    (hVhat_pos : ∀ n ω,
      (twoSLSVHatStar
        (stackRegressors Z (n + 1) ω) (stackRegressors X (n + 1) ω)
        (stackOutcomes Y (n + 1) ω)).PosDef)
    (hquantile :
      TwoSLSBootstrapRobustPercentileTQuantileCalibrationInputs
        μ Z X Y R q α) :
    Tendsto
      (fun n =>
        μ {ω |
          twoSLSBootstrapRobustPercentileTCIEventFinSucc
            R Z X Y β α n ω})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) :=
  twoSLSBootstrapRobustPercentileTCIEventFinSucc_theorem12_8_of_observed_textbook_fourth_scoreTailPrimitiveEmpiricalProcess_cov_posDef_quantileCalibration
    (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y)
    (R := R) (β := β) (q := q) (α := α) h
    (oneRow_transpose_mulVec_injective_of_exists_ne_zero hR)
    hboot hVhat_pos hquantile

set_option linter.style.longLine false in
/-- Observed-row Assumption 12.2 score-tail primitive route, returning both
percentile-`t` critical-value convergence and interval coverage.

This is the score-tail analogue of the direct-covariance uniform-remainder
quantile/coverage endpoint: it reuses the existing score-tail bootstrap
distribution theorem and the generic Chapter 10 percentile-`t` quantile bridge,
while keeping realized covariance positive definiteness and quantile calibration
as explicit interval-side inputs. -/
theorem
    twoSLSBootstrapRobustPercentileTCIEventFinSucc_quantiles_tendsto_and_coverage_theorem12_8_of_observed_textbook_fourth_scoreTailPrimitiveEmpiricalProcess_cov_posDef_quantileCalibration_row_ne_zero
    [IsProbabilityMeasure μ]
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {R : Matrix Unit k ℝ} {β : k → ℝ} {q α : ℝ}
    (h : TwoSLSAssumption12_2ObservedIidTextbookFourthConditions μ Z X e Y β)
    (hR : ∃ j : k, R () j ≠ 0)
    (hboot :
      TwoSLSBootstrapTheorem12_8ScoreTailPrimitiveEmpiricalProcessInputs
        μ Z X Y e β R)
    (hVhat_pos : ∀ n ω,
      (twoSLSVHatStar
        (stackRegressors Z (n + 1) ω) (stackRegressors X (n + 1) ω)
        (stackOutcomes Y (n + 1) ω)).PosDef)
    (hquantile :
      TwoSLSBootstrapRobustPercentileTQuantileCalibrationInputs
        μ Z X Y R q α) :
    (TendstoInMeasure μ
        (bootstrapScalarLowerQuantileIndexed
          (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
          (fun n ω ωs =>
            twoSLSBootstrapRobustLinearTStatFinSucc R Z X Y n ω ωs)
          (α / 2))
        atTop (fun _ => -q) ∧
      TendstoInMeasure μ
        (bootstrapScalarLowerQuantileIndexed
          (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
          (fun n ω ωs =>
            twoSLSBootstrapRobustLinearTStatFinSucc R Z X Y n ω ωs)
          (1 - α / 2))
        atTop (fun _ => q)) ∧
      Tendsto
        (fun n =>
          μ {ω |
            twoSLSBootstrapRobustPercentileTCIEventFinSucc
              R Z X Y β α n ω})
        atTop (𝓝 (ENNReal.ofReal (1 - α))) := by
  let hRinj : Function.Injective Rᵀ.mulVec :=
    oneRow_transpose_mulVec_injective_of_exists_ne_zero hR
  let hcoverage :
      TwoSLSBootstrapRobustPercentileTCoverageInputs
        μ Z X Y β R q α :=
    TwoSLSBootstrapRobustPercentileTCoverageInputs.of_textbook_fourth_cov_posDef_quantileCalibration
      (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y)
      (β := β) (R := R) (q := q) (α := α)
      h.toResidualTextbookFourthConditions hRinj hVhat_pos hquantile
  exact
    twoSLSBootstrapRobustPercentileTCIEventFinSucc_quantiles_tendsto_and_coverage_of_sample_quantile
      (μ := μ) (Z := Z) (X := X) (Y := Y) (R := R)
      (β := β) (q := q) (α := α)
      (twoSLSBootstrap_theorem12_8_of_observed_textbook_fourth_scoreTailPrimitiveEmpiricalProcess
        (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y)
        (R := R) (β := β) h hRinj hboot).2
      hcoverage.sample hquantile

set_option linter.style.longLine false in
/-- Historical score-tail compatibility assembly; this is not a Hansen-facing
endpoint.

This bundles the coefficient bootstrap Gaussian limit, robust one-row
studentized bootstrap limit, percentile-`t` critical-value convergence, and
coverage conclusion. Its fixed-compact true-score tail premise is incompatible
with the nondegenerate Gaussian score limit in Assumption 12.2, so it remains
private same-file scaffolding. -/
private theorem scoreTailCompatibilityFull
    [IsProbabilityMeasure μ]
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {R : Matrix Unit k ℝ} {β : k → ℝ} {q α : ℝ}
    (h : TwoSLSAssumption12_2ObservedIidTextbookFourthConditions μ Z X e Y β)
    (hR : ∃ j : k, R () j ≠ 0)
    (hboot :
      TwoSLSBootstrapTheorem12_8ScoreTailPrimitiveEmpiricalProcessInputs
        μ Z X Y e β R)
    (hVhat_pos : ∀ n ω,
      (twoSLSVHatStar
        (stackRegressors Z (n + 1) ω) (stackRegressors X (n + 1) ω)
        (stackOutcomes Y (n + 1) ω)).PosDef)
    (hquantile :
      TwoSLSBootstrapRobustPercentileTQuantileCalibrationInputs
        μ Z X Y R q α) :
    TendstoInBootstrapDistributionIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs => twoSLSBootstrapBetaGapFinSucc Z X Y n ω ωs)
        (multivariateGaussian (0 : EuclideanSpace ℝ k)
          (twoSLSAsymptoticVariance
            (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (scoreCovMat μ Z e)
            (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))))
        (fun z : EuclideanSpace ℝ k => (z : k → ℝ)) ∧
      TendstoInBootstrapDistributionIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs (_ : Unit) =>
          twoSLSBootstrapRobustLinearTStatFinSucc R Z X Y n ω ωs)
        (gaussianReal 0 1) (fun z : ℝ => fun _ : Unit => z) ∧
      (TendstoInMeasure μ
          (bootstrapScalarLowerQuantileIndexed
            (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
            (fun n ω ωs =>
              twoSLSBootstrapRobustLinearTStatFinSucc R Z X Y n ω ωs)
            (α / 2))
          atTop (fun _ => -q) ∧
        TendstoInMeasure μ
          (bootstrapScalarLowerQuantileIndexed
            (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
            (fun n ω ωs =>
              twoSLSBootstrapRobustLinearTStatFinSucc R Z X Y n ω ωs)
            (1 - α / 2))
          atTop (fun _ => q)) ∧
        Tendsto
          (fun n =>
            μ {ω |
              twoSLSBootstrapRobustPercentileTCIEventFinSucc
                R Z X Y β α n ω})
          atTop (𝓝 (ENNReal.ofReal (1 - α))) := by
  have hdist :=
    twoSLSBootstrap_theorem12_8_of_observed_textbook_fourth_scoreTailPrimitiveEmpiricalProcess_row_ne_zero
      (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y)
      (R := R) (β := β) h hR hboot
  have hci :=
    twoSLSBootstrapRobustPercentileTCIEventFinSucc_quantiles_tendsto_and_coverage_theorem12_8_of_observed_textbook_fourth_scoreTailPrimitiveEmpiricalProcess_cov_posDef_quantileCalibration_row_ne_zero
      (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y)
      (R := R) (β := β) (q := q) (α := α)
      h hR hboot hVhat_pos hquantile
  exact ⟨hdist.1, hdist.2, hci⟩

private noncomputable def bootstrapNormTailCutoff
    (E : Type*) [NormedAddCommGroup E] (M : ℝ) :
    BoundedContinuousFunction E ℝ :=
  BoundedContinuousFunction.mkOfBound
    ⟨fun x : E => min 1 (max 0 (‖x‖ - M)),
      continuous_const.min (continuous_const.max (continuous_norm.sub continuous_const))⟩
    1 fun x y => by
      rw [Real.dist_eq]
      change |min 1 (max 0 (‖x‖ - M)) - min 1 (max 0 (‖y‖ - M))| ≤ 1
      have hx0 : 0 ≤ min 1 (max 0 (‖x‖ - M)) :=
        le_min zero_le_one (le_max_left _ _)
      have hy0 : 0 ≤ min 1 (max 0 (‖y‖ - M)) :=
        le_min zero_le_one (le_max_left _ _)
      have hx1 : min 1 (max 0 (‖x‖ - M)) ≤ 1 := min_le_left _ _
      have hy1 : min 1 (max 0 (‖y‖ - M)) ≤ 1 := min_le_left _ _
      exact abs_le.mpr ⟨by linarith, by linarith⟩

@[simp]
private theorem bootstrapNormTailCutoff_apply
    {E : Type*} [NormedAddCommGroup E] (M : ℝ) (x : E) :
    bootstrapNormTailCutoff E M x = min 1 (max 0 (‖x‖ - M)) :=
  rfl

private theorem
    tendstoInBootstrapWeakDistributionIndexed_asymptoticallyTight
    {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E]
    [BorelSpace E] [SecondCountableTopology E] [CompleteSpace E]
    [ProperSpace E]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → E}
    {ν : Measure E} [IsProbabilityMeasure ν]
    (hZ : TendstoInBootstrapWeakDistributionIndexed μ Pstar Zstar ν id)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZstar : ∀ n ω, Measurable (Zstar n ω)) :
    ∀ η : ℝ, 0 < η →
      ∃ K : Set E, IsCompact K ∧
        Tendsto
          (fun n =>
            μ {ω |
              η ≤ (Pstar n ω).real {ωs | Zstar n ω ωs ∉ K}})
          atTop (nhds 0) := by
  intro η hη
  have htight : IsTightMeasureSet {ν} := isTightMeasureSet_singleton
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le] at htight
  have hη4 : 0 < η / 4 := by positivity
  obtain ⟨C, hC, hνC⟩ := htight (ENNReal.ofReal (η / 4)) (ENNReal.ofReal_pos.mpr hη4)
  have hνC' : ν (Cᶜ) ≤ ENNReal.ofReal (η / 4) := hνC ν (by simp)
  obtain ⟨M, hMpos, hCball⟩ := hC.isBounded.subset_ball_lt 0 (0 : E)
  let K : Set E := Metric.closedBall (0 : E) (M + 1)
  let f : BoundedContinuousFunction E ℝ := bootstrapNormTailCutoff E M
  have hK : IsCompact K := isCompact_closedBall (0 : E) (M + 1)
  have hf_nonneg : ∀ x, 0 ≤ f x := by
    intro x
    dsimp [f]
    exact le_min zero_le_one (le_max_left _ _)
  have hf_one_outside : ∀ x, x ∉ K → 1 ≤ f x := by
    intro x hx
    have hxnorm : M + 1 < ‖x‖ := by
      have hx' : ¬‖x‖ ≤ M + 1 := by
        simpa [K, Metric.mem_closedBall, dist_zero_right] using hx
      exact not_le.mp hx'
    have hdiff_nonneg : 0 ≤ ‖x‖ - M := by linarith
    have hone : 1 ≤ ‖x‖ - M := by linarith
    dsimp [f]
    rw [max_eq_right hdiff_nonneg]
    exact le_min le_rfl hone
  have hCmeas : MeasurableSet C := hC.isClosed.measurableSet
  have hf_integrable : Integrable (fun x => f x) ν :=
    BoundedContinuousFunction.integrable ν f
  have hind_integrable :
      Integrable (Cᶜ.indicator (fun _ : E => (1 : ℝ))) ν :=
    (integrable_const (1 : ℝ)).indicator hCmeas.compl
  have hf_le_indicator :
      ∀ x, f x ≤ Cᶜ.indicator (fun _ : E => (1 : ℝ)) x := by
    intro x
    by_cases hx : x ∈ C
    · have hxnorm : ‖x‖ < M := by
        simpa [Metric.mem_ball, dist_zero_right] using hCball hx
      have hdiff : ‖x‖ - M ≤ 0 := by linarith
      change min 1 (max 0 (‖x‖ - M)) ≤
        Cᶜ.indicator (fun _ : E => (1 : ℝ)) x
      simp [Set.indicator, hx, max_eq_left hdiff]
    · change min 1 (max 0 (‖x‖ - M)) ≤
        Cᶜ.indicator (fun _ : E => (1 : ℝ)) x
      simp [Set.indicator, hx]
  have hint_le_tail : ∫ x, f x ∂ν ≤ ν.real (Cᶜ) := by
    have hmono := integral_mono hf_integrable hind_integrable hf_le_indicator
    simpa using hmono.trans_eq (integral_indicator_one (μ := ν) (s := Cᶜ) hCmeas.compl)
  have htail_real : ν.real (Cᶜ) ≤ η / 4 := by
    calc
      ν.real (Cᶜ) = (ν (Cᶜ)).toReal := rfl
      _ ≤ (ENNReal.ofReal (η / 4)).toReal :=
        ENNReal.toReal_mono (by simp) hνC'
      _ = η / 4 := ENNReal.toReal_ofReal hη4.le
  have hint_nonneg : 0 ≤ ∫ x, f x ∂ν := integral_nonneg hf_nonneg
  have hint_small : ∫ x, f x ∂ν ≤ η / 4 := hint_le_tail.trans htail_real
  have htail_le_integral : ∀ n ω,
      (Pstar n ω).real {ωs | Zstar n ω ωs ∉ K} ≤
        bootstrapBoundedContinuousIntegralIndexed Pstar Zstar f n ω := by
    have hPfinite : ∀ n ω, IsFiniteMeasure (Pstar n ω) := by
      intro n ω
      letI : IsProbabilityMeasure (Pstar n ω) := hPstar n ω
      infer_instance
    have hsandwich :=
      bootstrapEventProbabilityIndexed_sandwich_of_boundedContinuous_event_sandwich
        (Pstar := Pstar) (Zstar := Zstar) (A := Kᶜ)
        (lower := 0) (upper := f) hPfinite hZstar hK.isClosed.measurableSet.compl
        (by simp) (by simp) (by simpa using hf_one_outside) hf_nonneg
    intro n ω
    simpa [bootstrapEventProbabilityIndexed] using hsandwich.2 n ω
  have hconv := hZ f
  rw [tendstoInMeasure_iff_dist] at hconv
  have hη2 : 0 < η / 2 := by positivity
  have hdev := hconv (η / 2) hη2
  refine ⟨K, hK, ?_⟩
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hdev
    (fun _ => zero_le _) ?_
  intro n
  refine measure_mono ?_
  intro ω hω
  have hboot_ge :
      η ≤ bootstrapBoundedContinuousIntegralIndexed Pstar Zstar f n ω :=
    hω.trans (htail_le_integral n ω)
  have hdiff_nonneg :
      0 ≤ bootstrapBoundedContinuousIntegralIndexed Pstar Zstar f n ω -
        ∫ x, f x ∂ν := by
    linarith
  change η / 2 ≤
    dist (bootstrapBoundedContinuousIntegralIndexed Pstar Zstar f n ω)
      (∫ x, f x ∂ν)
  rw [Real.dist_eq, abs_of_nonneg hdiff_nonneg]
  linarith

omit [DecidableEq k] [DecidableEq l] in
private theorem norm_mulVec_euclidean_le_card_mul_matrix_norm_mul_norm
    (A : Matrix k l ℝ) (x : EuclideanSpace ℝ l) :
    ‖A *ᵥ (x : l → ℝ)‖ ≤ (Fintype.card l : ℝ) * ‖A‖ * ‖x‖ := by
  have hnonneg : 0 ≤ (Fintype.card l : ℝ) * ‖A‖ * ‖x‖ := by
    positivity
  refine (pi_norm_le_iff_of_nonneg hnonneg).2 ?_
  intro i
  calc
    ‖(A *ᵥ (x : l → ℝ)) i‖
        = |∑ j : l, A i j * x j| := by
            simp [Matrix.mulVec, dotProduct, Real.norm_eq_abs]
    _ ≤ ∑ j : l, |A i j * x j| := by
          simpa using
            (Finset.abs_sum_le_sum_abs (fun j : l => A i j * x j) Finset.univ)
    _ ≤ ∑ _j : l, ‖A‖ * ‖x‖ := by
          refine Finset.sum_le_sum ?_
          intro j _
          rw [abs_mul]
          have hAij : |A i j| ≤ ‖A‖ := by
            simpa [Real.norm_eq_abs] using
              Matrix.norm_entry_le_entrywise_sup_norm (A := A) (i := i) (j := j)
          have hxj : |x j| ≤ ‖x‖ := by
            simpa [Real.norm_eq_abs] using PiLp.norm_apply_le x j
          exact mul_le_mul hAij hxj (abs_nonneg _) (norm_nonneg _)
    _ = (Fintype.card l : ℝ) * ‖A‖ * ‖x‖ := by
          simp [Finset.sum_const, nsmul_eq_mul, mul_assoc]

omit [DecidableEq k] [DecidableEq l] in
private theorem indexed_bootstrap_matrix_mulVec_closeness_of_probability_tight
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Astar : ∀ n, Ω → Ωboot n → Matrix k l ℝ}
    {A : Matrix k l ℝ}
    {Sstar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ l}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hA : TendstoInBootstrapProbabilityIndexed μ Pstar Astar (fun _ => A))
    (hStight : ∀ η : ℝ, 0 < η →
      ∃ K : Set (EuclideanSpace ℝ l), IsCompact K ∧
        Tendsto
          (fun n =>
            μ {ω | η ≤ (Pstar n ω).real {ωs | Sstar n ω ωs ∉ K}})
          atTop (𝓝 0)) :
    ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          (Pstar n ω).real
            {ωs | δ ≤ dist
              (Astar n ω ωs *ᵥ (Sstar n ω ωs : l → ℝ))
              (A *ᵥ (Sstar n ω ωs : l → ℝ))})
        atTop (fun _ => 0) := by
  intro δ hδ
  rw [tendstoInMeasure_iff_dist]
  intro η hη
  have hη2 : 0 < η / 2 := by positivity
  obtain ⟨K, hK, hscoreOuter⟩ := hStight (η / 2) hη2
  obtain ⟨M, _hMpos, hKball⟩ := hK.isBounded.subset_ball_lt 0
    (0 : EuclideanSpace ℝ l)
  let C : ℝ := max 1 ((Fintype.card l : ℝ) * M)
  have hC : 0 < C := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hcardM : (Fintype.card l : ℝ) * M ≤ C := le_max_right _ _
  have hδC : 0 < δ / C := div_pos hδ hC
  let matrixProb : ℕ → Ω → ℝ := fun n ω =>
    (Pstar n ω).real {ωs | δ / C ≤ dist (Astar n ω ωs) A}
  have hmatrixOuter :
      Tendsto (fun n => μ {ω | η / 2 ≤ matrixProb n ω}) atTop (𝓝 0) := by
    have hm := hA (δ / C) hδC
    rw [tendstoInMeasure_iff_dist] at hm
    simpa [matrixProb, bootstrapTailProbIndexed, Real.dist_eq,
      abs_of_nonneg measureReal_nonneg] using hm (η / 2) hη2
  have hsum :
      Tendsto
        (fun n =>
          μ {ω | η / 2 ≤ matrixProb n ω} +
            μ {ω |
              η / 2 ≤ (Pstar n ω).real {ωs | Sstar n ω ωs ∉ K}})
        atTop (𝓝 0) := by
    simpa using hmatrixOuter.add hscoreOuter
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun _ => zero_le _) ?_
  intro n
  calc
    μ {ω |
        η ≤ dist
          ((Pstar n ω).real
            {ωs | δ ≤ dist
              (Astar n ω ωs *ᵥ (Sstar n ω ωs : l → ℝ))
              (A *ᵥ (Sstar n ω ωs : l → ℝ))})
          0}
        ≤ μ ({ω | η / 2 ≤ matrixProb n ω} ∪
          {ω | η / 2 ≤
            (Pstar n ω).real {ωs | Sstar n ω ωs ∉ K}}) := by
      refine measure_mono ?_
      intro ω hω
      let B : Set (Ωboot n) :=
        {ωs | δ / C ≤ dist (Astar n ω ωs) A}
      let T : Set (Ωboot n) := {ωs | Sstar n ω ωs ∉ K}
      let D : Set (Ωboot n) :=
        {ωs | δ ≤ dist
          (Astar n ω ωs *ᵥ (Sstar n ω ωs : l → ℝ))
          (A *ᵥ (Sstar n ω ωs : l → ℝ))}
      have hDBT : D ⊆ B ∪ T := by
        intro ωs hωs
        by_cases hs : Sstar n ω ωs ∈ K
        · left
          by_contra hmat
          have hmat' : dist (Astar n ω ωs) A < δ / C := not_le.mp hmat
          have hsNorm : ‖Sstar n ω ωs‖ ≤ M := by
            have hsNorm' : ‖Sstar n ω ωs‖ < M := by
              simpa [Metric.mem_ball, dist_zero_right] using hKball hs
            exact hsNorm'.le
          have hdistBound :
              dist
                  (Astar n ω ωs *ᵥ (Sstar n ω ωs : l → ℝ))
                  (A *ᵥ (Sstar n ω ωs : l → ℝ)) < δ := by
            calc
              dist
                    (Astar n ω ωs *ᵥ (Sstar n ω ωs : l → ℝ))
                    (A *ᵥ (Sstar n ω ωs : l → ℝ))
                  = ‖(Astar n ω ωs - A) *ᵥ
                      (Sstar n ω ωs : l → ℝ)‖ := by
                      rw [dist_eq_norm, Matrix.sub_mulVec]
              _ ≤ (Fintype.card l : ℝ) * ‖Astar n ω ωs - A‖ *
                    ‖Sstar n ω ωs‖ :=
                  norm_mulVec_euclidean_le_card_mul_matrix_norm_mul_norm
                    (Astar n ω ωs - A) (Sstar n ω ωs)
              _ ≤ (Fintype.card l : ℝ) * ‖Astar n ω ωs - A‖ * M := by
                  exact mul_le_mul_of_nonneg_left hsNorm (by positivity)
              _ = ((Fintype.card l : ℝ) * M) * dist (Astar n ω ωs) A := by
                  rw [dist_eq_norm]
                  ring
              _ ≤ C * dist (Astar n ω ωs) A := by
                  exact mul_le_mul_of_nonneg_right hcardM dist_nonneg
              _ < C * (δ / C) := mul_lt_mul_of_pos_left hmat' hC
              _ = δ := by field_simp
          exact (not_lt_of_ge hωs) hdistBound
        · exact Or.inr hs
      have htailBound :
          (Pstar n ω).real D ≤ (Pstar n ω).real B + (Pstar n ω).real T := by
        letI : IsProbabilityMeasure (Pstar n ω) := hPstar n ω
        calc
          (Pstar n ω).real D ≤ (Pstar n ω).real (B ∪ T) :=
            ENNReal.toReal_mono (measure_ne_top (Pstar n ω) (B ∪ T))
              (measure_mono hDBT)
          _ ≤ ((Pstar n ω) B + (Pstar n ω) T).toReal :=
            ENNReal.toReal_mono
              (ENNReal.add_ne_top.mpr
                ⟨measure_ne_top (Pstar n ω) B, measure_ne_top (Pstar n ω) T⟩)
              (measure_union_le B T)
          _ = (Pstar n ω).real B + (Pstar n ω).real T := by
            rw [ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
            rfl
      have hsumGe : η ≤ (Pstar n ω).real B + (Pstar n ω).real T := by
        have hprobNonneg : 0 ≤ (Pstar n ω).real D := measureReal_nonneg
        have hω' : η ≤ (Pstar n ω).real D := by
          simpa [D, Real.dist_eq, abs_of_nonneg hprobNonneg] using hω
        exact hω'.trans htailBound
      by_cases hB : η / 2 ≤ (Pstar n ω).real B
      · exact Or.inl (by simpa [B, matrixProb] using hB)
      · exact Or.inr (by
          have hT : η / 2 ≤ (Pstar n ω).real T := by linarith
          simpa [T] using hT)
    _ ≤ μ {ω | η / 2 ≤ matrixProb n ω} +
          μ {ω | η / 2 ≤
            (Pstar n ω).real {ωs | Sstar n ω ωs ∉ K}} :=
      measure_union_le _ _

private theorem
    indexed_bootstrap_pair_asymptoticallyTight_of_closeness
    {E : Type*} [NormedAddCommGroup E] [ProperSpace E]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Xstar Ystar : ∀ n, Ω → Ωboot n → E}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hXtight : ∀ η : ℝ, 0 < η →
      ∃ K : Set E, IsCompact K ∧
        Tendsto
          (fun n =>
            μ {ω | η ≤ (Pstar n ω).real {ωs | Xstar n ω ωs ∉ K}})
          atTop (𝓝 0))
    (hclose : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          (Pstar n ω).real
            {ωs | δ ≤ dist (Ystar n ω ωs) (Xstar n ω ωs)})
        atTop (fun _ => 0)) :
    ∀ η : ℝ, 0 < η →
      ∃ K : Set E, IsCompact K ∧
        Tendsto
          (fun n =>
            μ {ω | η ≤ (Pstar n ω).real {ωs | Xstar n ω ωs ∉ K}})
          atTop (𝓝 0) ∧
        Tendsto
          (fun n =>
            μ {ω | η ≤ (Pstar n ω).real {ωs | Ystar n ω ωs ∉ K}})
          atTop (𝓝 0) := by
  intro η hη
  have hη2 : 0 < η / 2 := by positivity
  obtain ⟨Kx, hKx, hXouter⟩ := hXtight (η / 2) hη2
  obtain ⟨M, _hMpos, hKxball⟩ := hKx.isBounded.subset_ball_lt 0 (0 : E)
  let K : Set E := Metric.closedBall (0 : E) (M + 1)
  have hKcompact : IsCompact K := isCompact_closedBall (0 : E) (M + 1)
  have hKxK : Kx ⊆ K := by
    intro x hx
    have hxnorm : ‖x‖ < M := by
      simpa [Metric.mem_ball, dist_zero_right] using hKxball hx
    dsimp [K]
    simpa [Metric.mem_closedBall, dist_zero_right] using (show ‖x‖ ≤ M + 1 by linarith)
  have hXouterK :
      Tendsto
        (fun n =>
          μ {ω | η ≤ (Pstar n ω).real {ωs | Xstar n ω ωs ∉ K}})
        atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hXouter
      (fun _ => zero_le _) ?_
    intro n
    refine measure_mono ?_
    intro ω hω
    have htail_mono :
        (Pstar n ω).real {ωs | Xstar n ω ωs ∉ K} ≤
          (Pstar n ω).real {ωs | Xstar n ω ωs ∉ Kx} := by
      letI : IsProbabilityMeasure (Pstar n ω) := hPstar n ω
      exact ENNReal.toReal_mono
        (measure_ne_top (Pstar n ω) {ωs | Xstar n ω ωs ∉ Kx})
        (measure_mono fun ωs hωs hx => hωs (hKxK hx))
    change η / 2 ≤ (Pstar n ω).real {ωs | Xstar n ω ωs ∉ Kx}
    have hω' : η ≤ (Pstar n ω).real {ωs | Xstar n ω ωs ∉ K} := hω
    linarith
  let closeProb : ℕ → Ω → ℝ := fun n ω =>
    (Pstar n ω).real {ωs | (1 : ℝ) ≤ dist (Ystar n ω ωs) (Xstar n ω ωs)}
  have hcloseOuter :
      Tendsto (fun n => μ {ω | η / 2 ≤ closeProb n ω}) atTop (𝓝 0) := by
    have hc := hclose 1 zero_lt_one
    rw [tendstoInMeasure_iff_dist] at hc
    simpa [closeProb, Real.dist_eq, abs_of_nonneg measureReal_nonneg] using
      hc (η / 2) hη2
  have hsum :
      Tendsto
        (fun n =>
          μ {ω |
              η / 2 ≤ (Pstar n ω).real {ωs | Xstar n ω ωs ∉ Kx}} +
            μ {ω | η / 2 ≤ closeProb n ω})
        atTop (𝓝 0) := by
    simpa using hXouter.add hcloseOuter
  refine ⟨K, hKcompact, hXouterK, ?_⟩
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun _ => zero_le _) ?_
  intro n
  calc
    μ {ω | η ≤ (Pstar n ω).real {ωs | Ystar n ω ωs ∉ K}}
        ≤ μ ({ω |
              η / 2 ≤ (Pstar n ω).real {ωs | Xstar n ω ωs ∉ Kx}} ∪
            {ω | η / 2 ≤ closeProb n ω}) := by
          refine measure_mono ?_
          intro ω hω
          let A : Set (Ωboot n) := {ωs | Xstar n ω ωs ∉ Kx}
          let B : Set (Ωboot n) :=
            {ωs | (1 : ℝ) ≤ dist (Ystar n ω ωs) (Xstar n ω ωs)}
          let D : Set (Ωboot n) := {ωs | Ystar n ω ωs ∉ K}
          have hDAB : D ⊆ A ∪ B := by
            intro ωs hωs
            by_cases hx : Xstar n ω ωs ∈ Kx
            · right
              by_contra hdist_not
              have hdist : dist (Ystar n ω ωs) (Xstar n ω ωs) < 1 :=
                not_le.mp hdist_not
              have hxnorm : ‖Xstar n ω ωs‖ < M := by
                simpa [Metric.mem_ball, dist_zero_right] using hKxball hx
              have hynorm : ‖Ystar n ω ωs‖ < M + 1 := by
                have htri := dist_triangle (Ystar n ω ωs) (Xstar n ω ωs) 0
                rw [dist_zero_right, dist_zero_right] at htri
                linarith
              exact hωs (by
                dsimp [K]
                simpa [Metric.mem_closedBall, dist_zero_right] using hynorm.le)
            · exact Or.inl hx
          have htail_bound :
              (Pstar n ω).real D ≤ (Pstar n ω).real A + (Pstar n ω).real B := by
            letI : IsProbabilityMeasure (Pstar n ω) := hPstar n ω
            calc
              (Pstar n ω).real D ≤ (Pstar n ω).real (A ∪ B) :=
                ENNReal.toReal_mono (measure_ne_top (Pstar n ω) (A ∪ B))
                  (measure_mono hDAB)
              _ ≤ ((Pstar n ω) A + (Pstar n ω) B).toReal :=
                ENNReal.toReal_mono
                  (ENNReal.add_ne_top.mpr
                    ⟨measure_ne_top (Pstar n ω) A, measure_ne_top (Pstar n ω) B⟩)
                  (measure_union_le A B)
              _ = (Pstar n ω).real A + (Pstar n ω).real B := by
                rw [ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
                rfl
          have hsum_ge :
              η ≤ (Pstar n ω).real A + (Pstar n ω).real B := by
            exact hω.trans htail_bound
          by_cases hA : η / 2 ≤ (Pstar n ω).real A
          · exact Or.inl (by simpa [A] using hA)
          · exact Or.inr (by
              have hB : η / 2 ≤ (Pstar n ω).real B := by
                linarith
              simpa [B, closeProb] using hB)
    _ ≤ μ {ω |
              η / 2 ≤ (Pstar n ω).real {ωs | Xstar n ω ωs ∉ Kx}} +
            μ {ω | η / 2 ≤ closeProb n ω} := measure_union_le _ _

private theorem
    tendstoInBootstrapWeakDistributionIndexed_of_closeness_asymptoticallyTight
    {E : Type*} [PseudoMetricSpace E] [MeasurableSpace E]
    [OpensMeasurableSpace E] [SecondCountableTopology E] [T2Space E]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar Zstar' : ∀ n, Ω → Ωboot n → E}
    {ν : Measure Ωlim} {Zlim : Ωlim → E}
    (hZ : TendstoInBootstrapWeakDistributionIndexed μ Pstar Zstar ν Zlim)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZstar : ∀ n ω, Measurable (Zstar n ω))
    (hZstar' : ∀ n ω, Measurable (Zstar' n ω))
    (hTight : ∀ η : ℝ, 0 < η →
      ∃ K : Set E, IsCompact K ∧
        Tendsto
          (fun n =>
            μ {ω |
              η ≤ (Pstar n ω).real {ωs | Zstar n ω ωs ∉ K}})
          atTop (𝓝 0) ∧
        Tendsto
          (fun n =>
            μ {ω |
              η ≤ (Pstar n ω).real {ωs | Zstar' n ω ωs ∉ K}})
          atTop (𝓝 0))
    (hclose : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          (Pstar n ω).real
            {ωs | δ ≤ dist (Zstar' n ω ωs) (Zstar n ω ωs)})
        atTop (fun _ => 0)) :
    TendstoInBootstrapWeakDistributionIndexed μ Pstar Zstar' ν Zlim := by
  refine hZ.of_integral_difference_zero ?_
  intro f
  rw [tendstoInMeasure_iff_dist]
  intro ε hε
  let C : ℝ := 2 * ‖f‖
  let η : ℝ := ε / (8 * (C + 1))
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    positivity
  have hC1_pos : 0 < C + 1 := by linarith
  have hη : 0 < η := by
    dsimp [η]
    positivity
  obtain ⟨K, hK, hTightZ, hTightZ'⟩ := hTight η hη
  have hε2 : 0 < ε / 2 := by positivity
  have hf_uc : UniformContinuousOn (fun x => f x) K :=
    hK.uniformContinuousOn_of_continuous f.continuous.continuousOn
  obtain ⟨δ, hδ_pos, hδ⟩ :=
    Metric.uniformContinuousOn_iff.mp hf_uc (ε / 2) hε2
  let closeProb : ℕ → Ω → ℝ := fun n ω =>
    (Pstar n ω).real
      {ωs | δ ≤ dist (Zstar' n ω ωs) (Zstar n ω ωs)}
  let tailProb : ℕ → Ω → ℝ := fun n ω =>
    (Pstar n ω).real {ωs | Zstar n ω ωs ∉ K}
  let tailProb' : ℕ → Ω → ℝ := fun n ω =>
    (Pstar n ω).real {ωs | Zstar' n ω ωs ∉ K}
  have hcloseOuter :
      Tendsto (fun n => μ {ω | η ≤ closeProb n ω}) atTop (𝓝 0) := by
    have hclose' := hclose δ hδ_pos
    rw [tendstoInMeasure_iff_dist] at hclose'
    simpa [closeProb, Real.dist_eq, abs_of_nonneg measureReal_nonneg] using
      hclose' η hη
  have houterSum :
      Tendsto
        (fun n =>
          (μ {ω | η ≤ closeProb n ω} + μ {ω | η ≤ tailProb n ω}) +
            μ {ω | η ≤ tailProb' n ω})
        atTop (𝓝 0) := by
    simpa [tailProb, tailProb'] using (hcloseOuter.add hTightZ).add hTightZ'
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds houterSum
    (fun _ => zero_le _) ?_
  intro n
  let OA : Set Ω := {ω | η ≤ closeProb n ω}
  let OB : Set Ω := {ω | η ≤ tailProb n ω}
  let OD : Set Ω := {ω | η ≤ tailProb' n ω}
  have hsubset :
      {ω |
        ε ≤ dist
          (bootstrapBoundedContinuousIntegralIndexed Pstar Zstar' f n ω -
            bootstrapBoundedContinuousIntegralIndexed Pstar Zstar f n ω)
          0} ⊆ OA ∪ OB ∪ OD := by
    intro ω hω
    let A : Set (Ωboot n) :=
      {ωs | δ ≤ dist (Zstar' n ω ωs) (Zstar n ω ωs)}
    let B : Set (Ωboot n) := {ωs | Zstar n ω ωs ∉ K}
    let D : Set (Ωboot n) := {ωs | Zstar' n ω ωs ∉ K}
    let pclose : ℝ := closeProb n ω
    let ptail : ℝ := tailProb n ω
    let ptail' : ℝ := tailProb' n ω
    have hpclose_nonneg : 0 ≤ pclose := measureReal_nonneg
    have hptail_nonneg : 0 ≤ ptail := measureReal_nonneg
    have hptail'_nonneg : 0 ≤ ptail' := measureReal_nonneg
    have hKmeas : MeasurableSet K := hK.isClosed.measurableSet
    have hA : MeasurableSet A := by
      dsimp [A]
      exact measurableSet_le measurable_const ((hZstar' n ω).dist (hZstar n ω))
    have hB : MeasurableSet B := by
      dsimp [B]
      simpa only [Set.mem_setOf_eq, Set.mem_compl_iff] using
        hKmeas.compl.preimage (hZstar n ω)
    have hD : MeasurableSet D := by
      dsimp [D]
      simpa only [Set.mem_setOf_eq, Set.mem_compl_iff] using
        hKmeas.compl.preimage (hZstar' n ω)
    have hbad_real_le :
        (Pstar n ω).real (A ∪ B ∪ D) ≤ pclose + ptail + ptail' := by
      have hAB : (Pstar n ω).real (A ∪ B) ≤ pclose + ptail := by
        have hμ : (Pstar n ω) (A ∪ B) ≤ (Pstar n ω) A + (Pstar n ω) B :=
          measure_union_le A B
        have hμreal :
            (Pstar n ω).real (A ∪ B) ≤
              ((Pstar n ω) A + (Pstar n ω) B).toReal :=
          ENNReal.toReal_mono
            (ENNReal.add_ne_top.mpr ⟨measure_ne_top _ _, measure_ne_top _ _⟩) hμ
        have hsum_real :
            ((Pstar n ω) A + (Pstar n ω) B).toReal = pclose + ptail := by
          rw [ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
          simp [Measure.real_def, pclose, ptail, closeProb, tailProb, A, B]
        exact hμreal.trans_eq hsum_real
      have hABD :
          (Pstar n ω).real ((A ∪ B) ∪ D) ≤
            (Pstar n ω).real (A ∪ B) + ptail' := by
        have hμ :
            (Pstar n ω) ((A ∪ B) ∪ D) ≤
              (Pstar n ω) (A ∪ B) + (Pstar n ω) D :=
          measure_union_le (A ∪ B) D
        have hμreal :
            (Pstar n ω).real ((A ∪ B) ∪ D) ≤
              ((Pstar n ω) (A ∪ B) + (Pstar n ω) D).toReal :=
          ENNReal.toReal_mono
            (ENNReal.add_ne_top.mpr ⟨measure_ne_top _ _, measure_ne_top _ _⟩) hμ
        have hsum_real :
            ((Pstar n ω) (A ∪ B) + (Pstar n ω) D).toReal =
              (Pstar n ω).real (A ∪ B) + ptail' := by
          rw [ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
          simp [Measure.real_def, ptail', tailProb', D]
        exact hμreal.trans_eq hsum_real
      rw [show A ∪ B ∪ D = (A ∪ B) ∪ D by rfl]
      linarith
    have hdist_integral :
        |bootstrapBoundedContinuousIntegralIndexed Pstar Zstar' f n ω -
            bootstrapBoundedContinuousIntegralIndexed Pstar Zstar f n ω| ≤
          ε / 2 + C * (pclose + ptail + ptail') := by
      letI : IsProbabilityMeasure (Pstar n ω) := hPstar n ω
      dsimp [bootstrapBoundedContinuousIntegralIndexed, pclose, ptail, ptail',
        closeProb, tailProb, tailProb', A, B, D]
      have hbound :=
        abs_integral_boundedContinuous_comp_sub_le_of_dist_event_compact_tails
          (P := Pstar n ω) (Z := Zstar n ω) (Z' := Zstar' n ω)
          (hZstar n ω) (hZstar' n ω) f hK (le_of_lt hε2)
          (fun x hx y hy hxy =>
            le_of_lt (by simpa [Real.dist_eq] using hδ y hy x hx hxy))
      have hbound' :
          |∫ ωs, f (Zstar' n ω ωs) ∂Pstar n ω -
              ∫ ωs, f (Zstar n ω ωs) ∂Pstar n ω| ≤
            ε / 2 + (2 * ‖f‖) * (Pstar n ω).real (A ∪ B ∪ D) := by
        simpa [A, B, D] using hbound
      have hmul_bad :
          (2 * ‖f‖) * (Pstar n ω).real (A ∪ B ∪ D) ≤
            (2 * ‖f‖) * (pclose + ptail + ptail') :=
        mul_le_mul_of_nonneg_left hbad_real_le (by positivity)
      exact hbound'.trans (by
        dsimp [C]
        linarith)
    have habs_ge :
        ε ≤ |bootstrapBoundedContinuousIntegralIndexed Pstar Zstar' f n ω -
            bootstrapBoundedContinuousIntegralIndexed Pstar Zstar f n ω| := by
      simpa [Real.dist_eq] using hω
    by_contra hout
    have hnotOA : ω ∉ OA := by
      intro hmem
      exact hout (Or.inl (Or.inl hmem))
    have hnotOB : ω ∉ OB := by
      intro hmem
      exact hout (Or.inl (Or.inr hmem))
    have hnotOD : ω ∉ OD := by
      intro hmem
      exact hout (Or.inr hmem)
    have hpclose_lt : pclose < η := by
      exact not_le.mp (by simpa [OA, pclose] using hnotOA)
    have hptail_lt : ptail < η := by
      exact not_le.mp (by simpa [OB, ptail] using hnotOB)
    have hptail'_lt : ptail' < η := by
      exact not_le.mp (by simpa [OD, ptail'] using hnotOD)
    have hpsum : pclose + ptail + ptail' < 3 * η := by linarith
    have hη_nonneg : 0 ≤ 3 * η := by positivity
    have hscale : (C + 1) * (3 * η) = 3 * ε / 8 := by
      dsimp [η]
      field_simp [ne_of_gt hC1_pos]
    have hCsum_lt : C * (pclose + ptail + ptail') < ε / 2 := by
      calc
        C * (pclose + ptail + ptail') ≤ C * (3 * η) :=
          mul_le_mul_of_nonneg_left hpsum.le hC_nonneg
        _ ≤ (C + 1) * (3 * η) :=
          mul_le_mul_of_nonneg_right (by linarith) hη_nonneg
        _ = 3 * ε / 8 := hscale
        _ < ε / 2 := by linarith
    linarith
  calc
    μ {ω |
        ε ≤ dist
          (bootstrapBoundedContinuousIntegralIndexed Pstar Zstar' f n ω -
            bootstrapBoundedContinuousIntegralIndexed Pstar Zstar f n ω)
          0}
        ≤ μ (OA ∪ OB ∪ OD) := measure_mono hsubset
    _ ≤ μ (OA ∪ OB) + μ OD := measure_union_le _ _
    _ ≤ (μ OA + μ OB) + μ OD :=
      add_le_add (measure_union_le _ _) le_rfl
    _ =
        (μ {ω | η ≤ closeProb n ω} + μ {ω | η ≤ tailProb n ω}) +
          μ {ω | η ≤ tailProb' n ω} := rfl

private theorem
    tendstoInBootstrapWeakDistributionIndexed_of_closeness
    {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E]
    [BorelSpace E] [SecondCountableTopology E] [CompleteSpace E]
    [ProperSpace E]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar Zstar' : ∀ n, Ω → Ωboot n → E}
    {ν : Measure E} [IsProbabilityMeasure ν]
    (hZ : TendstoInBootstrapWeakDistributionIndexed μ Pstar Zstar ν id)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZstar : ∀ n ω, Measurable (Zstar n ω))
    (hZstar' : ∀ n ω, Measurable (Zstar' n ω))
    (hclose : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          (Pstar n ω).real
            {ωs | δ ≤ dist (Zstar' n ω ωs) (Zstar n ω ωs)})
        atTop (fun _ => 0)) :
    TendstoInBootstrapWeakDistributionIndexed μ Pstar Zstar' ν id :=
  tendstoInBootstrapWeakDistributionIndexed_of_closeness_asymptoticallyTight
    (μ := μ) (Pstar := Pstar) (Zstar := Zstar) (Zstar' := Zstar')
    (ν := ν) (Zlim := id) hZ hPstar hZstar hZstar'
    (indexed_bootstrap_pair_asymptoticallyTight_of_closeness
      (μ := μ) (Pstar := Pstar) (Xstar := Zstar) (Ystar := Zstar')
      hPstar
      (tendstoInBootstrapWeakDistributionIndexed_asymptoticallyTight
        (μ := μ) (Pstar := Pstar) (Zstar := Zstar) (ν := ν)
        hZ hPstar hZstar)
      hclose)
    hclose

private theorem
    tendstoInBootstrapWeakDistributionIndexed_of_closeness_law
    {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E]
    [BorelSpace E] [SecondCountableTopology E] [CompleteSpace E]
    [ProperSpace E]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Ωlimit : Type*} [MeasurableSpace Ωlimit]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar Zstar' : ∀ n, Ω → Ωboot n → E}
    {νlimit : Measure Ωlimit} [IsProbabilityMeasure νlimit]
    {Zlimit : Ωlimit → E}
    (hZ :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar Zstar νlimit Zlimit)
    (hZlimit : AEMeasurable Zlimit νlimit)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZstar : ∀ n ω, Measurable (Zstar n ω))
    (hZstar' : ∀ n ω, Measurable (Zstar' n ω))
    (hclose : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          (Pstar n ω).real
            {ωs | δ ≤ dist (Zstar' n ω ωs) (Zstar n ω ωs)})
        atTop (fun _ => 0)) :
    TendstoInBootstrapWeakDistributionIndexed μ Pstar Zstar' νlimit Zlimit := by
  let law : Measure E := νlimit.map Zlimit
  letI : IsProbabilityMeasure law := Measure.isProbabilityMeasure_map hZlimit
  have hZlaw : HasLaw Zlimit law νlimit := ⟨hZlimit, rfl⟩
  have hidlaw : HasLaw id law law := by
    refine ⟨measurable_id.aemeasurable, ?_⟩
    simp
  have hbase : TendstoInBootstrapWeakDistributionIndexed μ Pstar Zstar law id :=
    hZ.congr_limit_law hZlaw hidlaw
  have htarget : TendstoInBootstrapWeakDistributionIndexed μ Pstar Zstar' law id :=
    tendstoInBootstrapWeakDistributionIndexed_of_closeness
      (μ := μ) (Pstar := Pstar) (Zstar := Zstar) (Zstar' := Zstar')
      (ν := law) hbase hPstar hZstar hZstar' hclose
  exact htarget.congr_limit_law hidlaw hZlaw

set_option linter.style.longLine false in
private theorem
    twoSLSBootstrapRecenteredScoreStatisticFinSucc_tendstoInBootstrapWeakDistribution_of_observed_textbook_fourth
    [IsProbabilityMeasure μ]
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {e Y : ℕ → Ω → ℝ} {β : k → ℝ}
    (h : TwoSLSAssumption12_2ObservedIidTextbookFourthConditions
      μ Z X e Y β) :
    TendstoInBootstrapWeakDistributionIndexed μ
      (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
      (fun n ω ωs =>
        twoSLSBootstrapRecenteredScoreStatisticFinSucc Z X Y n ω ωs)
      (multivariateGaussian (0 : EuclideanSpace ℝ l) (scoreCovMat μ Z e))
      (fun z : EuclideanSpace ℝ l => z) := by
  let hmixed := h.toJointIidMixedMomentConditions
  let hiid :=
    hmixed.toTwoSLSAssumption12_2JointIidFourthConditions.toIidFourthConditions
  have htrue :=
    twoSLSBootstrapTrueRecenteredScoreStatisticFinSucc_tendstoInBootstrapWeakDistribution_uniform_of_assumption12_2
      (μ := μ) (Z := Z) (X := X) (e := e) hiid
  have hresid :
      TwoSLSBootstrapResidualSubstitutionNegligibilityInputs μ Z X Y β :=
    TwoSLSBootstrapResidualSubstitutionNegligibilityInputs.of_textbook_fourth
      (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y) (β := β)
      h.toResidualTextbookFourthConditions
  have hscoreClose : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω) n ω).real
            {ωs |
              δ ≤ dist
                (twoSLSBootstrapRecenteredScoreStatisticFinSucc Z X Y n ω ωs)
                (twoSLSBootstrapTrueRecenteredScoreStatisticFinSucc
                  Z e n ω ωs)})
        atTop (fun _ => 0) := by
    intro δ hδ
    have hdist : ∀ n ω ωs,
        dist (twoSLSBootstrapRecenteredScoreStatisticFinSucc Z X Y n ω ωs)
          (twoSLSBootstrapTrueRecenteredScoreStatisticFinSucc Z e n ω ωs) =
          ‖twoSLSBootstrapResidualSubstitutionRecenteredScoreStatisticFinSucc
            Z X Y β n ω ωs‖ := by
      intro n ω ωs
      rw [twoSLSBootstrapRecenteredScoreStatisticFinSucc_eq_true_sub_residualSubstitution
        Z X Y e β h.model]
      simp
    simpa [hdist] using hresid.residual_substitution_negligible δ hδ
  exact
    tendstoInBootstrapWeakDistributionIndexed_of_closeness_law
      (μ := μ)
      (Pstar := twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
      (Zstar := fun n ω ωs =>
        twoSLSBootstrapTrueRecenteredScoreStatisticFinSucc Z e n ω ωs)
      (Zstar' := fun n ω ωs =>
        twoSLSBootstrapRecenteredScoreStatisticFinSucc Z X Y n ω ωs)
      htrue continuous_id.aemeasurable
      (fun n ω =>
        twoSLSBootstrapUniformPstarFinSucc_isProbabilityMeasure (Ω := Ω) n ω)
      (by intro n ω; fun_prop) (by intro n ω; fun_prop) hscoreClose

namespace TwoSLSBootstrapCoefficientLinearizationClosenessInputs

set_option linter.style.longLine false in
/-- Honest Chapter 12.8 coefficient-linearization constructor under observed
textbook Assumption 12.2.

The indexed bootstrap WLLN and the 2SLS continuous-mapping theorem give
convergence of the bootstrap linearization matrix. The feasible score CLT gives
conditional asymptotic tightness, so their product proves the
population-to-sample linearization closeness field. Only the genuine nonlinear
coefficient remainder remains as an input. -/
theorem of_observed_textbook_fourth_linearized_closeness
    [IsProbabilityMeasure μ]
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {e Y : ℕ → Ω → ℝ} {β : k → ℝ}
    (h : TwoSLSAssumption12_2ObservedIidTextbookFourthConditions
      μ Z X e Y β)
    (hlinearized_closeness : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω) n ω).real
            {ωs |
              δ ≤ dist (twoSLSBootstrapBetaGapFinSucc Z X Y n ω ωs)
                (twoSLSBootstrapLinearizedGapFinSucc Z X Y n ω ωs)})
        atTop (fun _ => 0)) :
    TwoSLSBootstrapCoefficientLinearizationClosenessInputs μ
      (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω)) Z X Y
      (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
      (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
      (scoreCovMat μ Z e)
      (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X))) where
  population_to_sample_closeness := by
    have hmatrix :=
      twoSLSBootstrapLinearizationMatrixFinSucc_tendstoInBootstrapProbability_uniform_of_observed_textbook_fourth
        (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y) (β := β) h
    have hscore :=
      twoSLSBootstrapRecenteredScoreStatisticFinSucc_tendstoInBootstrapWeakDistribution_of_observed_textbook_fourth
        (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y) (β := β) h
    have hscoreTight :=
      tendstoInBootstrapWeakDistributionIndexed_asymptoticallyTight
        (μ := μ)
        (Pstar := twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (Zstar := fun n ω ωs =>
          twoSLSBootstrapRecenteredScoreStatisticFinSucc Z X Y n ω ωs)
        hscore
        (fun n ω =>
          twoSLSBootstrapUniformPstarFinSucc_isProbabilityMeasure (Ω := Ω) n ω)
        (by intro n ω; fun_prop)
    have hclose :=
      indexed_bootstrap_matrix_mulVec_closeness_of_probability_tight
        (μ := μ)
        (Pstar := twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (Astar := fun n ω ωs =>
          twoSLSBootstrapLinearizationMatrixFinSucc Z X n ω ωs)
        (A := twoSLSPopulationLinearizationMatrix
          (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
          (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
          (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X))))
        (Sstar := fun n ω ωs =>
          twoSLSBootstrapRecenteredScoreStatisticFinSucc Z X Y n ω ωs)
        (fun n ω =>
          twoSLSBootstrapUniformPstarFinSucc_isProbabilityMeasure (Ω := Ω) n ω)
        hmatrix hscoreTight
    intro δ hδ
    simpa [twoSLSBootstrapLinearizedGapFinSucc,
      twoSLSBootstrapLinearizedStatisticFinSucc,
      twoSLSBootstrapPopulationLinearizedGapFinSucc,
      twoSLSBootstrapPopulationLinearizedStatisticFinSucc,
      twoSLSBootstrapRecenteredScoreStatisticFinSucc,
      matrixContinuousLinearMap_apply] using hclose δ hδ
  linearized_closeness := hlinearized_closeness

end TwoSLSBootstrapCoefficientLinearizationClosenessInputs

/-- Honest remaining empirical-process inputs for Hansen Theorem 12.8.

The true-score CLT implies conditional asymptotic tightness, and bootstrap-
probability closeness transfers tightness to the feasible score, the two
coefficient linearizations, and the studentized pair. Consequently none of
those tail statements is a package field. The generic package retains both
coefficient-closeness fields, while the observed-textbook constructor above
derives the population-to-sample field and leaves only the nonlinear coefficient
remainder. Robust covariance resampling stability remains separate. -/
structure TwoSLSBootstrapTheorem12_8TightEmpiricalProcessInputs
    (μ : Measure Ω)
    (Z : ℕ → Ω → l → ℝ) (X : ℕ → Ω → k → ℝ)
    (Y e : ℕ → Ω → ℝ) (β : k → ℝ)
    (R : Matrix Unit k ℝ) : Prop where
  coefficient_closeness :
    TwoSLSBootstrapCoefficientLinearizationClosenessInputs μ
      (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω)) Z X Y
      (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
      (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
      (scoreCovMat μ Z e)
      (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))
  covariance_resample :
    TwoSLSBootstrapRobustCovarianceResamplePrimitiveInputs μ Z X Y

/-- Hansen Theorem 12.8 observed-row distribution inputs.

Assumption 12.2 supplies the population Gaussian and covariance
nondegeneracy facts, the true-score tightness, and residual substitution. The
remaining raw gap is coefficient linearization and covariance resampling. -/
structure TwoSLSBootstrapTheorem12_8ObservedDistributionInputs
    (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (Z : ℕ → Ω → l → ℝ) (X : ℕ → Ω → k → ℝ)
    (e Y : ℕ → Ω → ℝ) (R : Matrix Unit k ℝ)
    (β : k → ℝ) : Prop where
  assumption12_2 :
    TwoSLSAssumption12_2ObservedIidTextbookFourthConditions μ Z X e Y β
  restriction_row_ne_zero : ∃ j : k, R () j ≠ 0
  empirical_process :
    TwoSLSBootstrapTheorem12_8TightEmpiricalProcessInputs
      μ Z X Y e β R

/-- Full observed-row Hansen Theorem 12.8 inputs.

No pathwise score bound or all-sample covariance positive-definiteness field
appears. Sample standard-error nondegeneracy is derived in probability from
Assumption 12.2 covariance consistency. -/
structure TwoSLSBootstrapTheorem12_8ObservedFullInputs
    (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (Z : ℕ → Ω → l → ℝ) (X : ℕ → Ω → k → ℝ)
    (e Y : ℕ → Ω → ℝ) (R : Matrix Unit k ℝ)
    (β : k → ℝ) (q α : ℝ) : Prop where
  distribution :
    TwoSLSBootstrapTheorem12_8ObservedDistributionInputs
      μ Z X e Y R β
  quantile_calibration :
    TwoSLSBootstrapRobustPercentileTQuantileCalibrationInputs
      μ Z X Y R q α

set_option linter.style.longLine false in
private theorem
    twoSLSBootstrapBetaGapFinSucc_tendstoInBootstrapWeakDistribution_of_observed_tightInputs
    [IsProbabilityMeasure μ]
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {R : Matrix Unit k ℝ} {β : k → ℝ}
    (h : TwoSLSBootstrapTheorem12_8ObservedDistributionInputs
      μ Z X e Y R β) :
    TendstoInBootstrapWeakDistributionIndexed μ
      (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
      (fun n ω ωs => twoSLSBootstrapBetaGapFinSucc Z X Y n ω ωs)
      (multivariateGaussian (0 : EuclideanSpace ℝ k)
        (twoSLSAsymptoticVariance
          (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
          (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
          (scoreCovMat μ Z e)
          (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))))
      (fun z : EuclideanSpace ℝ k => (z : k → ℝ)) := by
  let hmixed := h.assumption12_2.toJointIidMixedMomentConditions
  let hiid :=
    hmixed.toTwoSLSAssumption12_2JointIidFourthConditions.toIidFourthConditions
  have hscore :=
    twoSLSBootstrapRecenteredScoreStatisticFinSucc_tendstoInBootstrapWeakDistribution_of_observed_textbook_fourth
      (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y) (β := β)
      h.assumption12_2
  let hGram := hiid.toGramConditions
  have hpop :
      TendstoInBootstrapWeakDistributionIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs =>
          twoSLSBootstrapPopulationLinearizedGapFinSucc
            (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))
            Z X Y n ω ωs)
        (multivariateGaussian (0 : EuclideanSpace ℝ k)
          (twoSLSAsymptoticVariance
            (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (scoreCovMat μ Z e)
            (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))))
        (fun z : EuclideanSpace ℝ k => (z : k → ℝ)) :=
    twoSLSBootstrapPopulationLinearizedGapFinSucc_tendstoInBootstrapWeakDistribution_formula
      (μ := μ) (Pstar := twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
      (Z := Z) (X := X) (Y := Y)
      (QXZ := twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
      (QZZ := twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
      (Omega := scoreCovMat μ Z e)
      (QZX := twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))
      hiid.omega_posDef.posSemidef
      (by simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using hiid.qzz_posDef.1.eq)
      (twoSLSCombinedQZX_eq_transpose_QXZ_of_popGram_wlln
        (μ := μ) (Z := Z) (X := X)
        hGram.toTwoSLSAssumption12_1GramConditions.combined_gram)
      hscore
  have hlinearized :
      TendstoInBootstrapWeakDistributionIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs => twoSLSBootstrapLinearizedGapFinSucc Z X Y n ω ωs)
        (multivariateGaussian (0 : EuclideanSpace ℝ k)
          (twoSLSAsymptoticVariance
            (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (scoreCovMat μ Z e)
            (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))))
        (fun z : EuclideanSpace ℝ k => (z : k → ℝ)) :=
    tendstoInBootstrapWeakDistributionIndexed_of_closeness_law
      (μ := μ)
      (Pstar := twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
      (Zstar := fun n ω ωs =>
        twoSLSBootstrapPopulationLinearizedGapFinSucc
          (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
          (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
          (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))
          Z X Y n ω ωs)
      (Zstar' := fun n ω ωs =>
        twoSLSBootstrapLinearizedGapFinSucc Z X Y n ω ωs)
      hpop (PiLp.continuous_ofLp 2 (fun _ : k => ℝ)).aemeasurable
      (fun n ω =>
        twoSLSBootstrapUniformPstarFinSucc_isProbabilityMeasure (Ω := Ω) n ω)
      (by intro n ω; fun_prop) (by intro n ω; fun_prop)
      h.empirical_process.coefficient_closeness.population_to_sample_closeness
  exact
    tendstoInBootstrapWeakDistributionIndexed_of_closeness_law
      (μ := μ)
      (Pstar := twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
      (Zstar := fun n ω ωs =>
        twoSLSBootstrapLinearizedGapFinSucc Z X Y n ω ωs)
      (Zstar' := fun n ω ωs =>
        twoSLSBootstrapBetaGapFinSucc Z X Y n ω ωs)
      hlinearized (PiLp.continuous_ofLp 2 (fun _ : k => ℝ)).aemeasurable
      (fun n ω =>
        twoSLSBootstrapUniformPstarFinSucc_isProbabilityMeasure (Ω := Ω) n ω)
      (by intro n ω; fun_prop) (by intro n ω; fun_prop)
      h.empirical_process.coefficient_closeness.linearized_closeness

namespace TwoSLSBootstrapTheorem12_8

/-- Corrected observed-row Hansen Theorem 12.8 distribution endpoint.

Assumption 12.2 derives the true-score CLT, its asymptotic tightness, residual
substitution, covariance nondegeneracy, and sample-side covariance WLLNs. The
only remaining bootstrap inputs are coefficient-linearization closeness and
robust covariance resampling stability. -/
theorem distribution
    [IsProbabilityMeasure μ]
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {R : Matrix Unit k ℝ} {β : k → ℝ}
    (h : TwoSLSBootstrapTheorem12_8ObservedDistributionInputs
      μ Z X e Y R β) :
    TendstoInBootstrapDistributionIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs => twoSLSBootstrapBetaGapFinSucc Z X Y n ω ωs)
        (multivariateGaussian (0 : EuclideanSpace ℝ k)
          (twoSLSAsymptoticVariance
            (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (scoreCovMat μ Z e)
            (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))))
        (fun z : EuclideanSpace ℝ k => (z : k → ℝ)) ∧
      TendstoInBootstrapDistributionIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs (_ : Unit) =>
          twoSLSBootstrapRobustLinearTStatFinSucc R Z X Y n ω ωs)
        (gaussianReal 0 1) (fun z : ℝ => fun _ : Unit => z) := by
  let hmixed := h.assumption12_2.toJointIidMixedMomentConditions
  let hiid :=
    hmixed.toTwoSLSAssumption12_2JointIidFourthConditions.toIidFourthConditions
  let Vβ : Matrix k k ℝ :=
    twoSLSAsymptoticVariance
      (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
      (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
      (scoreCovMat μ Z e)
      (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))
  let hGram := hiid.toGramConditions
  have hVβ : Vβ.PosDef := by
    dsimp [Vβ]
    exact
      twoSLSAsymptoticVariance_posDef_of_qzz_omega_rank
        (QXZ := twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
        (QZZ := twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
        (Omega := scoreCovMat μ Z e)
        (QZX := twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))
        (twoSLSCombinedQXZ_eq_transpose_QZX_of_popGram_wlln
          (μ := μ) (Z := Z) (X := X)
          hGram.toTwoSLSAssumption12_1GramConditions.combined_gram)
        hiid.qzz_posDef hiid.omega_posDef hiid.qzx_rank
  have hβweak :=
    twoSLSBootstrapBetaGapFinSucc_tendstoInBootstrapWeakDistribution_of_observed_tightInputs
      (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y)
      (R := R) (β := β) h
  have hβdist :
      TendstoInBootstrapDistributionIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs => twoSLSBootstrapBetaGapFinSucc Z X Y n ω ωs)
        (multivariateGaussian (0 : EuclideanSpace ℝ k) Vβ)
        (fun z : EuclideanSpace ℝ k => (z : k → ℝ)) :=
    chapter10_indexed_bootstrap_clt_gaussian_of_weakDistribution_posDef
      (μ := μ)
      (Pstar := twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
      (Zstar := fun n ω ωs => twoSLSBootstrapBetaGapFinSucc Z X Y n ω ωs)
      hVβ (by simpa [Vβ] using hβweak)
      (fun n ω => by
        letI := twoSLSBootstrapUniformPstarFinSucc_isProbabilityMeasure
          (Ω := Ω) n ω
        infer_instance)
      (by intro n ω; fun_prop)
  have hse_pos : 0 < linearRestrictionStdError R Vβ := by
    dsimp [Vβ]
    exact twoSLSBootstrapLinearRestrictionStdError_pos_of_assumption12_2
      (μ := μ) (Z := Z) (X := X) (e := e) (R := R)
      hiid (oneRow_transpose_mulVec_injective_of_exists_ne_zero
        h.restriction_row_ne_zero)
  have hnum :
      TendstoInBootstrapWeakDistributionIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs =>
          twoSLSBootstrapLinearRestrictionStatisticFinSucc R Z X Y n ω ωs)
        (gaussianReal 0 1)
        (fun z : ℝ => linearRestrictionStdError R Vβ * z) :=
    twoSLSBootstrapLinearRestrictionStatisticFinSucc_tendstoInBootstrapWeakDistribution_standardNormal_of_coefficient
      (μ := μ)
      (Pstar := twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
      hVβ.posSemidef (by simpa [Vβ] using hβweak)
  have hVconv :
      TendstoInBootstrapProbabilityIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs => twoSLSBootstrapVHatStarFinSucc Z X Y n ω ωs)
        (fun _ => Vβ) :=
    twoSLSBootstrapVHatStarFinSucc_tendstoInBootstrapProbability_formula_uniform_of_assumption12_2_iid_weight_wlln_resamplePrimitive
      (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y)
      hiid β h.assumption12_2.model
      (hmixed.toWeightWLLNConditions
        (μ := μ) (Z := Z) (X := X) (e := e))
      h.empirical_process.covariance_resample
  have hse :
      TendstoInBootstrapProbabilityIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs =>
          twoSLSBootstrapRobustLinearRestrictionStdErrorFinSucc
            R Z X Y n ω ωs)
        (fun _ => linearRestrictionStdError R Vβ) := by
    simpa [Vβ] using
      twoSLSBootstrapRobustLinearRestrictionStdErrorFinSucc_tendstoInBootstrapProbability_formula_uniform
        (μ := μ) (R := R) (Z := Z) (X := X) (Y := Y)
        (QXZ := twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
        (QZZ := twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
        (Omega := scoreCovMat μ Z e)
        (QZX := twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))
        hVconv
  have hbase :
      TendstoInBootstrapWeakDistributionIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs =>
          (twoSLSBootstrapLinearRestrictionStatisticFinSucc R Z X Y n ω ωs,
            linearRestrictionStdError R Vβ))
        (gaussianReal 0 1)
        (fun z : ℝ =>
          (linearRestrictionStdError R Vβ * z,
            linearRestrictionStdError R Vβ)) := by
    simpa using
      chapter10_indexed_bootstrap_continuous_mapping_distribution
        (μ := μ)
        (Pstar := twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (Zstar := fun n ω ωs =>
          twoSLSBootstrapLinearRestrictionStatisticFinSucc R Z X Y n ω ωs)
        (ν := gaussianReal 0 1)
        (Z := fun z : ℝ => linearRestrictionStdError R Vβ * z)
        (g := fun x : ℝ => (x, linearRestrictionStdError R Vβ))
        hnum (by fun_prop)
  have hpairClose : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω) n ω).real
            {ωs |
              δ ≤ dist
                (twoSLSBootstrapLinearRestrictionStatisticFinSucc R Z X Y n ω ωs,
                  twoSLSBootstrapRobustLinearRestrictionStdErrorFinSucc
                    R Z X Y n ω ωs)
                (twoSLSBootstrapLinearRestrictionStatisticFinSucc R Z X Y n ω ωs,
                  linearRestrictionStdError R Vβ)})
        atTop (fun _ => 0) := by
    intro δ hδ
    simpa [TendstoInBootstrapProbabilityIndexed, bootstrapTailProbIndexed,
      Prod.dist_eq] using hse δ hδ
  have hjoint :
      TendstoInBootstrapWeakDistributionIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs =>
          (twoSLSBootstrapLinearRestrictionStatisticFinSucc R Z X Y n ω ωs,
            twoSLSBootstrapRobustLinearRestrictionStdErrorFinSucc
              R Z X Y n ω ωs))
        (gaussianReal 0 1)
        (fun z : ℝ =>
          (linearRestrictionStdError R Vβ * z,
            linearRestrictionStdError R Vβ)) :=
    tendstoInBootstrapWeakDistributionIndexed_of_closeness_law
      (μ := μ)
      (Pstar := twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
      (Zstar := fun n ω ωs =>
        (twoSLSBootstrapLinearRestrictionStatisticFinSucc R Z X Y n ω ωs,
          linearRestrictionStdError R Vβ))
      (Zstar' := fun n ω ωs =>
        (twoSLSBootstrapLinearRestrictionStatisticFinSucc R Z X Y n ω ωs,
          twoSLSBootstrapRobustLinearRestrictionStdErrorFinSucc
            R Z X Y n ω ωs))
      hbase (by fun_prop)
      (fun n ω =>
        twoSLSBootstrapUniformPstarFinSucc_isProbabilityMeasure (Ω := Ω) n ω)
      (by intro n ω; fun_prop) (by intro n ω; fun_prop) hpairClose
  refine ⟨by simpa [Vβ] using hβdist, ?_⟩
  simpa [twoSLSBootstrapRobustLinearTStatFinSucc,
    twoSLSBootstrapRobustLinearRestrictionStdErrorFinSucc_eq_generic] using
    twoSLSBootstrapLinearTStatFinSucc_tendstoInBootstrapDistribution_standardNormal
      (μ := μ)
      (Pstar := twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
      (Z := Z) (X := X) (Y := Y) (R := R)
      (Vβ := Vβ)
      (Vstar := fun n ω ωs => twoSLSBootstrapVHatStarFinSucc Z X Y n ω ωs)
      hse_pos hjoint
      (fun n ω =>
        twoSLSBootstrapUniformPstarFinSucc_isProbabilityMeasure (Ω := Ω) n ω)
      (by intro n ω; fun_prop) (by intro n ω; fun_prop) hse

/-- Corrected full observed-row Hansen Theorem 12.8 endpoint.

This adds percentile-`t` critical-value convergence and coverage to
`distribution`. Quantile calibration remains explicit; sample studentization
and high-probability standard-error positivity are reused from the existing
Assumption-12.2 sample-side transfer. -/
theorem quantiles_and_coverage
    [IsProbabilityMeasure μ]
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {R : Matrix Unit k ℝ} {β : k → ℝ} {q α : ℝ}
    (h : TwoSLSBootstrapTheorem12_8ObservedFullInputs
      μ Z X e Y R β q α) :
    TendstoInBootstrapDistributionIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs => twoSLSBootstrapBetaGapFinSucc Z X Y n ω ωs)
        (multivariateGaussian (0 : EuclideanSpace ℝ k)
          (twoSLSAsymptoticVariance
            (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (scoreCovMat μ Z e)
            (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))))
        (fun z : EuclideanSpace ℝ k => (z : k → ℝ)) ∧
      TendstoInBootstrapDistributionIndexed μ
        (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
        (fun n ω ωs (_ : Unit) =>
          twoSLSBootstrapRobustLinearTStatFinSucc R Z X Y n ω ωs)
        (gaussianReal 0 1) (fun z : ℝ => fun _ : Unit => z) ∧
      (TendstoInMeasure μ
          (bootstrapScalarLowerQuantileIndexed
            (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
            (fun n ω ωs =>
              twoSLSBootstrapRobustLinearTStatFinSucc R Z X Y n ω ωs)
            (α / 2))
          atTop (fun _ => -q) ∧
        TendstoInMeasure μ
          (bootstrapScalarLowerQuantileIndexed
            (twoSLSBootstrapUniformPstarFinSucc (Ω := Ω))
            (fun n ω ωs =>
              twoSLSBootstrapRobustLinearTStatFinSucc R Z X Y n ω ωs)
            (1 - α / 2))
          atTop (fun _ => q)) ∧
        Tendsto
          (fun n =>
            μ {ω |
              twoSLSBootstrapRobustPercentileTCIEventFinSucc
                R Z X Y β α n ω})
          atTop (𝓝 (ENNReal.ofReal (1 - α))) := by
  have hdist := distribution
    (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y)
    (R := R) (β := β) h.distribution
  have hsample :
      TwoSLSBootstrapRobustPercentileTAsymptoticSampleInputs
        μ Z X Y β R :=
    TwoSLSBootstrapRobustPercentileTAsymptoticSampleInputs.of_observed_textbook_fourth
      (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y)
      (β := β) (R := R) h.distribution.assumption12_2
      (oneRow_transpose_mulVec_injective_of_exists_ne_zero
        h.distribution.restriction_row_ne_zero)
  have hci :=
    twoSLSBootstrapRobustPercentileTCIEventFinSucc_quantiles_tendsto_and_coverage_of_asymptotic_sample_quantile
      (μ := μ) (Z := Z) (X := X) (Y := Y) (R := R)
      (β := β) (q := q) (α := α) hdist.2 hsample h.quantile_calibration
  exact ⟨hdist.1, hdist.2, hci⟩

end TwoSLSBootstrapTheorem12_8

end DistributionInterfaces

end HansenEconometrics
