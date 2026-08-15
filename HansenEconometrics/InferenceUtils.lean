import HansenEconometrics.AsymptoticInterfaces
import HansenEconometrics.AsymptoticUtils

/-!
# Reusable covariance and studentization tools

This module provides the estimator-independent inference layer that used to
live in the Chapter 8 development. It turns covariance-matrix consistency into
standard-error consistency and transfers scalar distributional limits through
studentization.

The definitions and theorem names are unchanged, so existing chapter imports
remain source compatible. New developments can import this module directly
without importing restricted estimation.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped Matrix Matrix.Norms.Elementwise Topology MeasureTheory ProbabilityTheory

namespace HansenEconometrics

open Matrix

variable {k : Type*} [Fintype k] [DecidableEq k]

/-- Standard-error scale for a fixed linear combination `h'β`, based on an
asymptotic covariance matrix. -/
noncomputable def covarianceStdErrorScale
    (h : k → ℝ) (V : Matrix k k ℝ) : ℝ :=
  Real.sqrt (h ⬝ᵥ V *ᵥ h)

/-- Finite-sample standard error obtained by dividing the asymptotic scale by
the deterministic normalization. -/
noncomputable def covarianceStdError
    (root : ℝ) (h : k → ℝ) (V : Matrix k k ℝ) : ℝ :=
  covarianceStdErrorScale h V / root

/-- Studentized statistic formed with `covarianceStdError`. -/
noncomputable def covarianceTStatistic
    (root : ℝ) (θhat θ : ℝ) (h : k → ℝ) (V : Matrix k k ℝ) : ℝ :=
  (θhat - θ) / covarianceStdError root h V

omit [DecidableEq k] in
/-- The finite-sample standard error is the inverse normalization times the
asymptotic standard-error scale. -/
theorem covarianceStdError_eq_inv_mul_scale
    (root : ℝ) (h : k → ℝ) (V : Matrix k k ℝ) :
    covarianceStdError root h V = root⁻¹ * covarianceStdErrorScale h V := by
  rw [covarianceStdError]
  ring

omit [DecidableEq k] in
/-- Rewrites a t-statistic as the scaled numerator divided by its asymptotic
standard-error scale. -/
theorem covarianceTStatistic_eq_scaled_div_scale
    (root θhat θ : ℝ) (h : k → ℝ) (V : Matrix k k ℝ)
    (hroot : root ≠ 0) (hscale : covarianceStdErrorScale h V ≠ 0) :
    covarianceTStatistic root θhat θ h V =
      (root * (θhat - θ)) / covarianceStdErrorScale h V := by
  unfold covarianceTStatistic covarianceStdError
  field_simp [hroot, hscale]

omit [DecidableEq k] in
/-- A fixed-linear-combination standard-error scale is a.e. measurable whenever
the covariance estimator is. -/
theorem covarianceStdErrorScale_aemeasurable
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (h : k → ℝ) {Vhat : Ω → Matrix k k ℝ}
    (hVhat : AEStronglyMeasurable Vhat μ) :
    AEMeasurable (fun ω => covarianceStdErrorScale h (Vhat ω)) μ := by
  have hcont : Continuous (fun V : Matrix k k ℝ => covarianceStdErrorScale h V) := by
    unfold covarianceStdErrorScale
    exact Real.continuous_sqrt.comp
      ((continuous_const.dotProduct
        (Continuous.matrix_mulVec continuous_id continuous_const)))
  exact (hcont.comp_aestronglyMeasurable hVhat).aemeasurable

omit [DecidableEq k] in
/-- Standard-error scale consistency from covariance-estimator consistency. -/
theorem covarianceStdErrorScale_tendstoInMeasure_of_consistency
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {Vhat : ℕ → Ω → Matrix k k ℝ} {V : Matrix k k ℝ}
    (h : k → ℝ) (hV : CovarianceEstimatorConsistent μ Vhat V) :
    TendstoInMeasure μ (fun n ω => covarianceStdErrorScale h (Vhat n ω))
      atTop (fun _ => covarianceStdErrorScale h V) := by
  have hcont : Continuous (fun V : Matrix k k ℝ => covarianceStdErrorScale h V) := by
    unfold covarianceStdErrorScale
    exact Real.continuous_sqrt.comp
      ((continuous_const.dotProduct
        (Continuous.matrix_mulVec continuous_id continuous_const)))
  exact tendstoInMeasure_continuous_comp hV.covariance_measurable hV.consistent hcont

omit [DecidableEq k] in
/-- A consistent covariance estimator constructs a feasible standard-error
interface for each fixed linear combination. -/
theorem feasibleStandardErrorConsistent_of_covarianceConsistency
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {Vhat : ℕ → Ω → Matrix k k ℝ} {V : Matrix k k ℝ}
    (h : k → ℝ) (hV : CovarianceEstimatorConsistent μ Vhat V) :
    FeasibleStandardErrorConsistent μ
      (fun n ω => covarianceStdErrorScale h (Vhat n ω))
      (covarianceStdErrorScale h V) where
  standardError_measurable := fun n =>
    covarianceStdErrorScale_aemeasurable h (hV.covariance_measurable n)
  consistent := covarianceStdErrorScale_tendstoInMeasure_of_consistency h hV

/-- Scalar Slutsky division with a positive denominator limit.

If `Xₙ ⇒ Z` and `Yₙ →ₚ c` for `c > 0`, then `Xₙ / Yₙ ⇒ Z / c`.
The proof clips the denominator at `c / 2` and removes the clip on an event
whose probability tends to zero. -/
theorem tendstoInDistribution_div_of_tendstoInMeasure_const_pos
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ν : Measure Ω'} [IsProbabilityMeasure ν]
    {X Y : ℕ → Ω → ℝ} {Z : Ω' → ℝ} {c : ℝ}
    (hc : 0 < c)
    (hX : TendstoInDistribution X atTop Z (fun _ => μ) ν)
    (hY : TendstoInMeasure μ Y atTop (fun _ => c))
    (hY_meas : ∀ n, AEMeasurable (Y n) μ)
    (hdiv_meas : ∀ n, AEMeasurable (fun ω => X n ω / Y n ω) μ) :
    TendstoInDistribution
      (fun n ω => X n ω / Y n ω)
      atTop (fun ω => Z ω / c) (fun _ => μ) ν := by
  let c₂ : ℝ := c / 2
  have hc₂ : 0 < c₂ := by positivity
  have hmax_c : max c c₂ = c := by
    have hc₂_le_c : c₂ ≤ c := by
      dsimp [c₂]
      linarith
    exact max_eq_left hc₂_le_c
  have hg : Continuous (fun p : ℝ × ℝ => p.1 / max p.2 c₂) := by
    refine continuous_fst.div (continuous_snd.max continuous_const) ?_
    intro p
    exact ne_of_gt (lt_of_lt_of_le hc₂ (le_max_right p.2 c₂))
  have hclip : TendstoInDistribution
      (fun n ω => X n ω / max (Y n ω) c₂)
      atTop (fun ω => Z ω / c) (fun _ => μ) ν := by
    have hraw := hX.continuous_comp_prodMk_of_tendstoInMeasure_const
      (g := fun p : ℝ × ℝ => p.1 / max p.2 c₂) hg hY hY_meas
    simpa [Function.comp_def, c₂, hmax_c] using hraw
  have hdiff : TendstoInMeasure μ
      (fun n ω => X n ω / Y n ω - X n ω / max (Y n ω) c₂)
      atTop (fun _ => 0) := by
    rw [tendstoInMeasure_iff_dist]
    intro ε hε
    have hYdist := hY
    rw [tendstoInMeasure_iff_dist] at hYdist
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (hYdist c₂ hc₂) (fun _ => zero_le _) (fun n => ?_)
    refine measure_mono (fun ω hω => ?_)
    by_contra hnot
    have hdist_lt : dist (Y n ω) c < c₂ := not_le.mp hnot
    have hY_gt : c₂ < Y n ω := by
      rw [Real.dist_eq] at hdist_lt
      have hbounds := abs_lt.mp hdist_lt
      have hc_sub : c - c₂ = c₂ := by
        dsimp [c₂]
        ring
      linarith [hbounds.1, hc_sub]
    have hmax : max (Y n ω) c₂ = Y n ω := max_eq_left hY_gt.le
    have hdiff_zero : X n ω / Y n ω - X n ω / max (Y n ω) c₂ = 0 := by
      simp [hmax]
    have hε_le_zero : ε ≤ 0 := by
      simpa [Real.dist_eq, hdiff_zero] using hω
    exact (not_le_of_gt hε) hε_le_zero
  exact tendstoInDistribution_of_tendstoInMeasure_sub
    (X := fun n ω => X n ω / max (Y n ω) c₂)
    (Y := fun n ω => X n ω / Y n ω)
    (Z := fun ω => Z ω / c)
    hclip hdiff hdiv_meas

/-- Studentized scalar inference from a stable feasible-standard-error
interface. -/
theorem feasibleStandardErrorConsistent_studentized_tendstoInDistribution
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {μ : Measure Ω} {ν : Measure Ω'} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (num se : ℕ → Ω → ℝ) (Z : Ω' → ℝ) (c : ℝ)
    (hc : 0 < c)
    (hse : FeasibleStandardErrorConsistent μ se c)
    (hnum : TendstoInDistribution num atTop Z (fun _ => μ) ν) :
    TendstoInDistribution (fun n ω => num n ω / se n ω) atTop
      (fun ω => Z ω / c) (fun _ => μ) ν := by
  have hdiv_meas : ∀ n, AEMeasurable (fun ω => num n ω / se n ω) μ :=
    fun n => (hnum.forall_aemeasurable n).div (hse.standardError_measurable n)
  exact tendstoInDistribution_div_of_tendstoInMeasure_const_pos
    (μ := μ) (ν := ν) (X := num) (Y := se) (Z := Z) (c := c)
    hc hnum hse.consistent hse.standardError_measurable hdiv_meas

omit [DecidableEq k] in
/-- Studentized scalar inference for a fixed linear combination using a
consistent covariance estimator. -/
theorem covarianceStdErrorScale_studentized_tendstoInDistribution
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {μ : Measure Ω} {ν : Measure Ω'} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {Vhat : ℕ → Ω → Matrix k k ℝ} {V : Matrix k k ℝ}
    (h : k → ℝ) (num : ℕ → Ω → ℝ) (Z : Ω' → ℝ)
    (hV : CovarianceEstimatorConsistent μ Vhat V)
    (hpos : 0 < covarianceStdErrorScale h V)
    (hnum : TendstoInDistribution num atTop Z (fun _ => μ) ν) :
    TendstoInDistribution
      (fun n ω => num n ω / covarianceStdErrorScale h (Vhat n ω)) atTop
      (fun ω => Z ω / covarianceStdErrorScale h V) (fun _ => μ) ν :=
  feasibleStandardErrorConsistent_studentized_tendstoInDistribution
    num (fun n ω => covarianceStdErrorScale h (Vhat n ω)) Z
    (covarianceStdErrorScale h V) hpos
    (feasibleStandardErrorConsistent_of_covarianceConsistency h hV) hnum

end HansenEconometrics
