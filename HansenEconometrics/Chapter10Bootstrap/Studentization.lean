import HansenEconometrics.Chapter7Asymptotics.Inference
import HansenEconometrics.Chapter10Bootstrap.WeakDistribution

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology MeasureTheory ProbabilityTheory Matrix
open scoped Matrix.Norms.Elementwise Function

namespace HansenEconometrics

variable {Ω Ωs Ωlim E F k : Type*}
variable {mΩ : MeasurableSpace Ω} {mΩs : MeasurableSpace Ωs}
variable {mΩlim : MeasurableSpace Ωlim}
variable {μ : Measure Ω} {ν : Measure Ωlim}

section BootstrapStudentization

private theorem abs_integral_boundedContinuous_ratio_sub_clipped_le
    {P : Measure Ωs} [IsProbabilityMeasure P] {X Y : Ωs → ℝ}
    (hX : Measurable X) (hY : Measurable Y)
    (f : BoundedContinuousFunction ℝ ℝ) (c₂ : ℝ) :
    |(∫ ωs, f (X ωs / Y ωs) ∂P) -
        (∫ ωs, f (X ωs / max (Y ωs) c₂) ∂P)| ≤
      (2 * ‖f‖) * P.real {ωs | Y ωs < c₂} := by
  classical
  let bad : Set Ωs := {ωs | Y ωs < c₂}
  let C : ℝ := 2 * ‖f‖
  have hbad : MeasurableSet bad := by
    dsimp [bad]
    exact measurableSet_lt hY measurable_const
  have hactual_meas : Measurable (fun ωs => f (X ωs / Y ωs)) :=
    f.continuous.measurable.comp (hX.div hY)
  have hclipped_meas : Measurable (fun ωs => f (X ωs / max (Y ωs) c₂)) :=
    f.continuous.measurable.comp (hX.div (hY.max measurable_const))
  have hactual_int : Integrable (fun ωs => f (X ωs / Y ωs)) P := by
    refine Integrable.of_bound hactual_meas.aestronglyMeasurable ‖f‖ ?_
    exact ae_of_all P fun ωs => f.norm_coe_le_norm (X ωs / Y ωs)
  have hclipped_int : Integrable (fun ωs => f (X ωs / max (Y ωs) c₂)) P := by
    refine Integrable.of_bound hclipped_meas.aestronglyMeasurable ‖f‖ ?_
    exact ae_of_all P fun ωs => f.norm_coe_le_norm (X ωs / max (Y ωs) c₂)
  have hdiff_int :
      Integrable
        (fun ωs => f (X ωs / Y ωs) - f (X ωs / max (Y ωs) c₂)) P :=
    hactual_int.sub hclipped_int
  have hbad_ind_int :
      Integrable (fun ωs => if ωs ∈ bad then (1 : ℝ) else 0) P := by
    have hindicator_eq :
        (fun ωs => if ωs ∈ bad then (1 : ℝ) else 0) =
          bad.indicator (fun _ : Ωs => (1 : ℝ)) := by
      funext ωs
      by_cases hω : ωs ∈ bad <;> simp [Set.indicator, hω]
    rw [hindicator_eq]
    exact
      (integrable_indicator_iff hbad).mpr
        (integrable_const (1 : ℝ)).integrableOn
  have hbound_int :
      Integrable (fun ωs => C * (if ωs ∈ bad then (1 : ℝ) else 0)) P :=
    hbad_ind_int.const_mul C
  have hpoint :
      (fun ωs => |f (X ωs / Y ωs) - f (X ωs / max (Y ωs) c₂)|) ≤
        fun ωs => C * (if ωs ∈ bad then (1 : ℝ) else 0) := by
    intro ωs
    by_cases hω : ωs ∈ bad
    · have hfx : |f (X ωs / Y ωs)| ≤ ‖f‖ := by
        simpa [Real.norm_eq_abs] using f.norm_coe_le_norm (X ωs / Y ωs)
      have hfy : |f (X ωs / max (Y ωs) c₂)| ≤ ‖f‖ := by
        simpa [Real.norm_eq_abs] using
          f.norm_coe_le_norm (X ωs / max (Y ωs) c₂)
      have hdiff_le :
          |f (X ωs / Y ωs) - f (X ωs / max (Y ωs) c₂)| ≤ C := by
        dsimp [C]
        calc
          |f (X ωs / Y ωs) - f (X ωs / max (Y ωs) c₂)|
              = |f (X ωs / Y ωs) + -f (X ωs / max (Y ωs) c₂)| := by
                ring_nf
          _ ≤ |f (X ωs / Y ωs)| + |-f (X ωs / max (Y ωs) c₂)| := abs_add_le _ _
          _ = |f (X ωs / Y ωs)| + |f (X ωs / max (Y ωs) c₂)| := by
                rw [abs_neg]
          _ ≤ ‖f‖ + ‖f‖ := add_le_add hfx hfy
          _ = 2 * ‖f‖ := by ring
      simpa [bad, C, hω] using hdiff_le
    · have hY_ge : c₂ ≤ Y ωs := le_of_not_gt hω
      have hmax : max (Y ωs) c₂ = Y ωs := max_eq_left hY_ge
      simp [hmax, bad, hω]
  have hbad_integral :
      ∫ ωs, (if ωs ∈ bad then (1 : ℝ) else 0) ∂P = P.real bad := by
    have hindicator_eq :
        (fun ωs => if ωs ∈ bad then (1 : ℝ) else 0) =
          bad.indicator (fun _ : Ωs => (1 : ℝ)) := by
      funext ωs
      by_cases hω : ωs ∈ bad <;> simp [Set.indicator, hω]
    rw [hindicator_eq]
    simpa using (integral_indicator_one (μ := P) (s := bad) hbad)
  calc
    |(∫ ωs, f (X ωs / Y ωs) ∂P) -
        (∫ ωs, f (X ωs / max (Y ωs) c₂) ∂P)|
        = |∫ ωs, f (X ωs / Y ωs) -
            f (X ωs / max (Y ωs) c₂) ∂P| := by
          rw [integral_sub hactual_int hclipped_int]
    _ ≤ ∫ ωs, |f (X ωs / Y ωs) -
          f (X ωs / max (Y ωs) c₂)| ∂P := abs_integral_le_integral_abs
    _ ≤ ∫ ωs, C * (if ωs ∈ bad then (1 : ℝ) else 0) ∂P :=
          integral_mono hdiff_int.norm hbound_int hpoint
    _ = C * P.real bad := by
          rw [integral_const_mul, hbad_integral]
    _ = (2 * ‖f‖) * P.real {ωs | Y ωs < c₂} := by
          rfl

/-- Bootstrap studentization bridge for a scalar statistic.

If the numerator and standard-error scale have a joint bootstrap weak limit
`(X,c)`, the scale itself converges to the positive constant `c` in bootstrap
probability, and the conditional bootstrap laws are probability laws, then the
unclipped ratio has weak bootstrap limit `X / c`.  The proof clips the
denominator at `c / 2` for the continuous-mapping step and removes the clip by
the scale convergence premise. -/
theorem chapter10_bootstrap_studentized_ratio_weakDistribution
    {Pstar : ℕ → Ω → Measure Ωs}
    {Xstar Ystar : ℕ → Ω → Ωs → ℝ}
    {ν : Measure Ωlim} {X : Ωlim → ℝ} {c : ℝ}
    (hc : 0 < c)
    (hpair :
      TendstoInBootstrapWeakDistribution μ Pstar
        (fun n ω ωs => (Xstar n ω ωs, Ystar n ω ωs)) ν
        (fun ωlim => (X ωlim, c)))
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hXstar : ∀ n ω, Measurable (Xstar n ω))
    (hYstar : ∀ n ω, Measurable (Ystar n ω))
    (hY :
      TendstoInBootstrapProbability μ Pstar Ystar (fun _ => c)) :
    TendstoInBootstrapWeakDistribution μ Pstar
      (fun n ω ωs => Xstar n ω ωs / Ystar n ω ωs) ν
      (fun ωlim => X ωlim / c) := by
  let c₂ : ℝ := c / 2
  have hc₂ : 0 < c₂ := by
    dsimp [c₂]
    positivity
  have hc₂_le_c : c₂ ≤ c := by
    dsimp [c₂]
    linarith
  have hmax_c : max c c₂ = c := max_eq_left hc₂_le_c
  let clipped : ℝ × ℝ → ℝ := fun p => p.1 / max p.2 c₂
  have hclip_cont : Continuous clipped := by
    refine continuous_fst.div (continuous_snd.max continuous_const) ?_
    intro p
    exact ne_of_gt (lt_of_lt_of_le hc₂ (le_max_right p.2 c₂))
  have hclip :
      TendstoInBootstrapWeakDistribution μ Pstar
        (fun n ω ωs => clipped (Xstar n ω ωs, Ystar n ω ωs)) ν
        (fun ωlim => clipped (X ωlim, c)) :=
    chapter10_bootstrap_continuous_mapping_distribution
      (μ := μ) (Pstar := Pstar)
      (Zstar := fun n ω ωs => (Xstar n ω ωs, Ystar n ω ωs))
      (ν := ν) (Z := fun ωlim => (X ωlim, c)) (g := clipped)
      hpair hclip_cont
  have hclip_ratio :
      TendstoInBootstrapWeakDistribution μ Pstar
        (fun n ω ωs => Xstar n ω ωs / max (Ystar n ω ωs) c₂) ν
        (fun ωlim => X ωlim / c) := by
    simpa [clipped, hmax_c] using hclip
  refine hclip_ratio.of_integral_difference_zero ?_
  intro f
  let C : ℝ := 2 * ‖f‖
  have htail :
      TendstoInMeasure μ
        (fun n ω => C * bootstrapTailProb Pstar Ystar (fun _ => c) c₂ n ω)
        atTop (fun _ => 0) :=
    TendstoInMeasure.const_mul_zero_real (μ := μ) C (hY c₂ hc₂)
  refine TendstoInMeasure.of_abs_le_zero_real htail ?_
  intro n ω
  let tail : ℝ := bootstrapTailProb Pstar Ystar (fun _ => c) c₂ n ω
  have hbad_le_tail :
      (Pstar n ω).real {ωs | Ystar n ω ωs < c₂} ≤ tail := by
    refine ENNReal.toReal_mono ?_ (measure_mono ?_)
    · letI : IsProbabilityMeasure (Pstar n ω) := hPstar n ω
      exact measure_ne_top (Pstar n ω)
        {ωs | c₂ ≤ dist (Ystar n ω ωs) c}
    · intro ωs hlt
      have hlt_c : Ystar n ω ωs < c := lt_of_lt_of_le hlt hc₂_le_c
      have habs : |Ystar n ω ωs - c| = c - Ystar n ω ωs := by
        rw [abs_of_neg (sub_neg.mpr hlt_c)]
        ring
      change c₂ ≤ dist (Ystar n ω ωs) c
      rw [Real.dist_eq, habs]
      dsimp [c₂] at hlt ⊢
      linarith
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    positivity
  have hdiff_le_bad :
      |bootstrapBoundedContinuousIntegral Pstar
          (fun n ω ωs => Xstar n ω ωs / Ystar n ω ωs) f n ω -
        bootstrapBoundedContinuousIntegral Pstar
          (fun n ω ωs => Xstar n ω ωs / max (Ystar n ω ωs) c₂) f n ω| ≤
        C * (Pstar n ω).real {ωs | Ystar n ω ωs < c₂} := by
    simpa [bootstrapBoundedContinuousIntegral, C] using
      abs_integral_boundedContinuous_ratio_sub_clipped_le
        (P := Pstar n ω) (X := Xstar n ω) (Y := Ystar n ω)
        (hXstar n ω) (hYstar n ω) f c₂
  have hdiff_le_tail :
      |bootstrapBoundedContinuousIntegral Pstar
          (fun n ω ωs => Xstar n ω ωs / Ystar n ω ωs) f n ω -
        bootstrapBoundedContinuousIntegral Pstar
          (fun n ω ωs => Xstar n ω ωs / max (Ystar n ω ωs) c₂) f n ω| ≤
        C * tail :=
    hdiff_le_bad.trans (mul_le_mul_of_nonneg_left hbad_le_tail hC_nonneg)
  have htail_nonneg : 0 ≤ tail := ENNReal.toReal_nonneg
  have hCtail_nonneg : 0 ≤ C * tail := mul_nonneg hC_nonneg htail_nonneg
  simpa [tail, C, abs_of_nonneg hCtail_nonneg] using hdiff_le_tail

/-- Indexed bootstrap studentization bridge for sample-size-dependent
bootstrap spaces. -/
theorem chapter10_indexed_bootstrap_studentized_ratio_weakDistribution
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Xstar Ystar : ∀ n, Ω → Ωboot n → ℝ}
    {ν : Measure Ωlim} {X : Ωlim → ℝ} {c : ℝ}
    (hc : 0 < c)
    (hpair :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar
        (fun n ω ωs => (Xstar n ω ωs, Ystar n ω ωs)) ν
        (fun ωlim => (X ωlim, c)))
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hXstar : ∀ n ω, Measurable (Xstar n ω))
    (hYstar : ∀ n ω, Measurable (Ystar n ω))
    (hY :
      TendstoInBootstrapProbabilityIndexed μ Pstar Ystar (fun _ => c)) :
    TendstoInBootstrapWeakDistributionIndexed μ Pstar
      (fun n ω ωs => Xstar n ω ωs / Ystar n ω ωs) ν
      (fun ωlim => X ωlim / c) := by
  let c₂ : ℝ := c / 2
  have hc₂ : 0 < c₂ := by
    dsimp [c₂]
    positivity
  have hc₂_le_c : c₂ ≤ c := by
    dsimp [c₂]
    linarith
  have hmax_c : max c c₂ = c := max_eq_left hc₂_le_c
  let clipped : ℝ × ℝ → ℝ := fun p => p.1 / max p.2 c₂
  have hclip_cont : Continuous clipped := by
    refine continuous_fst.div (continuous_snd.max continuous_const) ?_
    intro p
    exact ne_of_gt (lt_of_lt_of_le hc₂ (le_max_right p.2 c₂))
  have hclip :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar
        (fun n ω ωs => clipped (Xstar n ω ωs, Ystar n ω ωs)) ν
        (fun ωlim => clipped (X ωlim, c)) :=
    chapter10_indexed_bootstrap_continuous_mapping_distribution
      (μ := μ) (Pstar := Pstar)
      (Zstar := fun n ω ωs => (Xstar n ω ωs, Ystar n ω ωs))
      (ν := ν) (Z := fun ωlim => (X ωlim, c)) (g := clipped)
      hpair hclip_cont
  have hclip_ratio :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar
        (fun n ω ωs => Xstar n ω ωs / max (Ystar n ω ωs) c₂) ν
        (fun ωlim => X ωlim / c) := by
    simpa [clipped, hmax_c] using hclip
  refine hclip_ratio.of_integral_difference_zero ?_
  intro f
  let C : ℝ := 2 * ‖f‖
  have htail :
      TendstoInMeasure μ
        (fun n ω =>
          C * bootstrapTailProbIndexed Pstar Ystar (fun _ => c) c₂ n ω)
        atTop (fun _ => 0) :=
    TendstoInMeasure.const_mul_zero_real (μ := μ) C (hY c₂ hc₂)
  refine TendstoInMeasure.of_abs_le_zero_real htail ?_
  intro n ω
  let tail : ℝ := bootstrapTailProbIndexed Pstar Ystar (fun _ => c) c₂ n ω
  have hbad_le_tail :
      (Pstar n ω).real {ωs | Ystar n ω ωs < c₂} ≤ tail := by
    refine ENNReal.toReal_mono ?_ (measure_mono ?_)
    · letI : IsProbabilityMeasure (Pstar n ω) := hPstar n ω
      exact measure_ne_top (Pstar n ω)
        {ωs | c₂ ≤ dist (Ystar n ω ωs) c}
    · intro ωs hlt
      have hlt_c : Ystar n ω ωs < c := lt_of_lt_of_le hlt hc₂_le_c
      have habs : |Ystar n ω ωs - c| = c - Ystar n ω ωs := by
        rw [abs_of_neg (sub_neg.mpr hlt_c)]
        ring
      change c₂ ≤ dist (Ystar n ω ωs) c
      rw [Real.dist_eq, habs]
      dsimp [c₂] at hlt ⊢
      linarith
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    positivity
  have hdiff_le_bad :
      |bootstrapBoundedContinuousIntegralIndexed Pstar
          (fun n ω ωs => Xstar n ω ωs / Ystar n ω ωs) f n ω -
        bootstrapBoundedContinuousIntegralIndexed Pstar
          (fun n ω ωs => Xstar n ω ωs / max (Ystar n ω ωs) c₂) f n ω| ≤
        C * (Pstar n ω).real {ωs | Ystar n ω ωs < c₂} := by
    simpa [bootstrapBoundedContinuousIntegralIndexed, C] using
      abs_integral_boundedContinuous_ratio_sub_clipped_le
        (P := Pstar n ω) (X := Xstar n ω) (Y := Ystar n ω)
        (hXstar n ω) (hYstar n ω) f c₂
  have hdiff_le_tail :
      |bootstrapBoundedContinuousIntegralIndexed Pstar
          (fun n ω ωs => Xstar n ω ωs / Ystar n ω ωs) f n ω -
        bootstrapBoundedContinuousIntegralIndexed Pstar
          (fun n ω ωs => Xstar n ω ωs / max (Ystar n ω ωs) c₂) f n ω| ≤
        C * tail :=
    hdiff_le_bad.trans (mul_le_mul_of_nonneg_left hbad_le_tail hC_nonneg)
  have htail_nonneg : 0 ≤ tail := ENNReal.toReal_nonneg
  have hCtail_nonneg : 0 ≤ C * tail := mul_nonneg hC_nonneg htail_nonneg
  simpa [tail, C, abs_of_nonneg hCtail_nonneg] using hdiff_le_tail

/-- Standard-normal face of the bootstrap studentization bridge. -/
theorem chapter10_bootstrap_studentized_ratio_standardNormal
    {Pstar : ℕ → Ω → Measure Ωs}
    {Xstar Ystar : ℕ → Ω → Ωs → ℝ} {c : ℝ}
    (hc : 0 < c)
    (hpair :
      TendstoInBootstrapWeakDistribution μ Pstar
        (fun n ω ωs => (Xstar n ω ωs, Ystar n ω ωs))
        (gaussianReal 0 1) (fun z : ℝ => (c * z, c)))
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hXstar : ∀ n ω, Measurable (Xstar n ω))
    (hYstar : ∀ n ω, Measurable (Ystar n ω))
    (hY :
      TendstoInBootstrapProbability μ Pstar Ystar (fun _ => c)) :
    TendstoInBootstrapWeakDistribution μ Pstar
      (fun n ω ωs => Xstar n ω ωs / Ystar n ω ωs)
      (gaussianReal 0 1) (fun z : ℝ => z) := by
  have hratio :=
    chapter10_bootstrap_studentized_ratio_weakDistribution
      (μ := μ) (Pstar := Pstar) (Xstar := Xstar) (Ystar := Ystar)
      (ν := gaussianReal 0 1) (X := fun z : ℝ => c * z) (c := c)
      hc hpair hPstar hXstar hYstar hY
  refine hratio.congr_limit ?_
  intro z
  field_simp [ne_of_gt hc]

/-- Indexed standard-normal face of the bootstrap studentization bridge. -/
theorem chapter10_indexed_bootstrap_studentized_ratio_standardNormal
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Xstar Ystar : ∀ n, Ω → Ωboot n → ℝ} {c : ℝ}
    (hc : 0 < c)
    (hpair :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar
        (fun n ω ωs => (Xstar n ω ωs, Ystar n ω ωs))
        (gaussianReal 0 1) (fun z : ℝ => (c * z, c)))
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hXstar : ∀ n ω, Measurable (Xstar n ω))
    (hYstar : ∀ n ω, Measurable (Ystar n ω))
    (hY :
      TendstoInBootstrapProbabilityIndexed μ Pstar Ystar (fun _ => c)) :
    TendstoInBootstrapWeakDistributionIndexed μ Pstar
      (fun n ω ωs => Xstar n ω ωs / Ystar n ω ωs)
      (gaussianReal 0 1) (fun z : ℝ => z) := by
  have hratio :=
    chapter10_indexed_bootstrap_studentized_ratio_weakDistribution
      (μ := μ) (Pstar := Pstar) (Xstar := Xstar) (Ystar := Ystar)
      (ν := gaussianReal 0 1) (X := fun z : ℝ => c * z) (c := c)
      hc hpair hPstar hXstar hYstar hY
  refine hratio.congr_limit ?_
  intro z
  field_simp [ne_of_gt hc]

private theorem standardNormal_unit_coordinateLE_frontier_null
    (x : Unit → ℝ) :
    ((gaussianReal 0 1).map (fun z : ℝ => fun _ : Unit => z))
      (frontier {z : Unit → ℝ | coordinateLE z x}) = 0 := by
  have hZ : AEMeasurable (fun z : ℝ => fun _ : Unit => z) (gaussianReal 0 1) := by
    refine aemeasurable_pi_lambda _ ?_
    intro _
    exact measurable_id.aemeasurable
  refine map_measure_frontier_coordinateLE_eq_zero_of_coord_singletons
    (ν := gaussianReal 0 1) (Z := fun z : ℝ => fun _ : Unit => z)
    hZ x ?_
  intro i
  haveI : NoAtoms (gaussianReal 0 1) :=
    noAtoms_gaussianReal (μ := 0) (v := 1) (by norm_num)
  change (gaussianReal 0 1) {z : ℝ | z = x i} = 0
  exact measure_singleton (x i)

private theorem standardNormalAbs_unit_coordinateLE_frontier_null
    (x : Unit → ℝ) :
    (((gaussianReal 0 1).map (fun z : ℝ => |z|)).map
        (fun z : ℝ => fun _ : Unit => z))
      (frontier {z : Unit → ℝ | coordinateLE z x}) = 0 := by
  have hZ :
      AEMeasurable (fun z : ℝ => fun _ : Unit => z)
        ((gaussianReal 0 1).map (fun z : ℝ => |z|)) := by
    refine aemeasurable_pi_lambda _ ?_
    intro _
    exact measurable_id.aemeasurable
  refine map_measure_frontier_coordinateLE_eq_zero_of_coord_singletons
    (ν := (gaussianReal 0 1).map (fun z : ℝ => |z|))
    (Z := fun z : ℝ => fun _ : Unit => z)
    hZ x ?_
  intro i
  change ((gaussianReal 0 1).map (fun z : ℝ => |z|)) {z : ℝ | z = x i} = 0
  simpa [frontier_Iic] using standardNormalAbs_frontier_Iic_null (x i)

/-- Hansen Definition 10.2 face of the standard-normal bootstrap
studentization bridge. -/
theorem chapter10_bootstrap_studentized_ratio_distribution_standardNormal
    {Pstar : ℕ → Ω → Measure Ωs}
    {Xstar Ystar : ℕ → Ω → Ωs → ℝ} {c : ℝ}
    (hc : 0 < c)
    (hpair :
      TendstoInBootstrapWeakDistribution μ Pstar
        (fun n ω ωs => (Xstar n ω ωs, Ystar n ω ωs))
        (gaussianReal 0 1) (fun z : ℝ => (c * z, c)))
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hXstar : ∀ n ω, Measurable (Xstar n ω))
    (hYstar : ∀ n ω, Measurable (Ystar n ω))
    (hY :
      TendstoInBootstrapProbability μ Pstar Ystar (fun _ => c)) :
    TendstoInBootstrapDistribution μ Pstar
      (fun n ω ωs (_ : Unit) => Xstar n ω ωs / Ystar n ω ωs)
      (gaussianReal 0 1) (fun z : ℝ => fun _ : Unit => z) := by
  have hweakScalar :=
    chapter10_bootstrap_studentized_ratio_standardNormal
      (μ := μ) (Pstar := Pstar) (Xstar := Xstar) (Ystar := Ystar)
      (c := c) hc hpair hPstar hXstar hYstar hY
  have hmap_cont : Continuous (fun z : ℝ => fun _ : Unit => z) := by
    refine continuous_pi ?_
    intro _
    exact continuous_id
  have hweakUnit :
      TendstoInBootstrapWeakDistribution μ Pstar
        (fun n ω ωs => fun _ : Unit => Xstar n ω ωs / Ystar n ω ωs)
        (gaussianReal 0 1) (fun z : ℝ => fun _ : Unit => z) :=
    chapter10_bootstrap_continuous_mapping_distribution
      (μ := μ) (Pstar := Pstar)
      (Zstar := fun n ω ωs => Xstar n ω ωs / Ystar n ω ωs)
      (ν := gaussianReal 0 1) (Z := fun z : ℝ => z)
      (g := fun z : ℝ => fun _ : Unit => z) hweakScalar hmap_cont
  have hPfinite : ∀ n ω, IsFiniteMeasure (Pstar n ω) := by
    intro n ω
    letI : IsProbabilityMeasure (Pstar n ω) := hPstar n ω
    infer_instance
  have hZstar :
      ∀ n ω,
        Measurable (fun ωs => fun _ : Unit => Xstar n ω ωs / Ystar n ω ωs) := by
    intro n ω
    refine measurable_pi_lambda _ ?_
    intro _
    exact (hXstar n ω).div (hYstar n ω)
  have hZlim :
      AEMeasurable (fun z : ℝ => fun _ : Unit => z) (gaussianReal 0 1) := by
    refine aemeasurable_pi_lambda _ ?_
    intro _
    exact measurable_id.aemeasurable
  exact
    TendstoInBootstrapDistribution.of_weakDistribution_null_frontiers
      (μ := μ) (Pstar := Pstar)
      (Zstar := fun n ω ωs => fun _ : Unit => Xstar n ω ωs / Ystar n ω ωs)
      (ν := gaussianReal 0 1) (Z := fun z : ℝ => fun _ : Unit => z)
      hweakUnit hPfinite hZstar hZlim
      (fun x _hx => standardNormal_unit_coordinateLE_frontier_null x)

/-- Absolute-value face of the standard-normal bootstrap studentization bridge.

This rewrites the continuous-mapping limit as the push-forward
`N(0,1).map abs`, which is the absolute-statistic law used by the
two-sided bootstrap-test critical-value route. -/
theorem chapter10_bootstrap_studentized_ratio_abs_standardNormalAbs
    {Pstar : ℕ → Ω → Measure Ωs}
    {Xstar Ystar : ℕ → Ω → Ωs → ℝ} {c : ℝ}
    (hc : 0 < c)
    (hpair :
      TendstoInBootstrapWeakDistribution μ Pstar
        (fun n ω ωs => (Xstar n ω ωs, Ystar n ω ωs))
        (gaussianReal 0 1) (fun z : ℝ => (c * z, c)))
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hXstar : ∀ n ω, Measurable (Xstar n ω))
    (hYstar : ∀ n ω, Measurable (Ystar n ω))
    (hY :
      TendstoInBootstrapProbability μ Pstar Ystar (fun _ => c)) :
    TendstoInBootstrapWeakDistribution μ Pstar
      (fun n ω ωs => |Xstar n ω ωs / Ystar n ω ωs|)
      ((gaussianReal 0 1).map (fun z : ℝ => |z|)) (fun z : ℝ => z) := by
  intro f
  have hweakAbs :
      TendstoInBootstrapWeakDistribution μ Pstar
        (fun n ω ωs => |Xstar n ω ωs / Ystar n ω ωs|)
        (gaussianReal 0 1) (fun z : ℝ => |z|) := by
    exact
      chapter10_bootstrap_continuous_mapping_distribution
        (μ := μ) (Pstar := Pstar)
        (Zstar := fun n ω ωs => Xstar n ω ωs / Ystar n ω ωs)
        (ν := gaussianReal 0 1) (Z := fun z : ℝ => z)
        (g := fun z : ℝ => |z|)
        (chapter10_bootstrap_studentized_ratio_standardNormal
          (μ := μ) (Pstar := Pstar) (Xstar := Xstar)
          (Ystar := Ystar) (c := c) hc hpair hPstar hXstar hYstar hY)
        continuous_abs
  have htarget :
      ∫ z, f z ∂((gaussianReal 0 1).map (fun z : ℝ => |z|)) =
        ∫ z, f (|z|) ∂(gaussianReal 0 1) := by
    exact integral_map continuous_abs.aemeasurable f.continuous.aestronglyMeasurable
  simpa [htarget] using hweakAbs.tendsto_integral f

/-- Hansen Definition 10.2 face of the absolute studentized-ratio bootstrap
law. -/
theorem chapter10_bootstrap_studentized_ratio_abs_distribution_standardNormalAbs
    {Pstar : ℕ → Ω → Measure Ωs}
    {Xstar Ystar : ℕ → Ω → Ωs → ℝ} {c : ℝ}
    (hc : 0 < c)
    (hpair :
      TendstoInBootstrapWeakDistribution μ Pstar
        (fun n ω ωs => (Xstar n ω ωs, Ystar n ω ωs))
        (gaussianReal 0 1) (fun z : ℝ => (c * z, c)))
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hXstar : ∀ n ω, Measurable (Xstar n ω))
    (hYstar : ∀ n ω, Measurable (Ystar n ω))
    (hY :
      TendstoInBootstrapProbability μ Pstar Ystar (fun _ => c)) :
    TendstoInBootstrapDistribution μ Pstar
      (fun n ω ωs (_ : Unit) => |Xstar n ω ωs / Ystar n ω ωs|)
      ((gaussianReal 0 1).map (fun z : ℝ => |z|))
      (fun z : ℝ => fun _ : Unit => z) := by
  letI :
      IsProbabilityMeasure ((gaussianReal 0 1).map (fun z : ℝ => |z|)) :=
    Measure.isProbabilityMeasure_map continuous_abs.aemeasurable
  have hweakScalar :=
    chapter10_bootstrap_studentized_ratio_abs_standardNormalAbs
      (μ := μ) (Pstar := Pstar) (Xstar := Xstar) (Ystar := Ystar)
      (c := c) hc hpair hPstar hXstar hYstar hY
  have hmap_cont : Continuous (fun z : ℝ => fun _ : Unit => z) := by
    refine continuous_pi ?_
    intro _
    exact continuous_id
  have hweakUnit :
      TendstoInBootstrapWeakDistribution μ Pstar
        (fun n ω ωs => fun _ : Unit => |Xstar n ω ωs / Ystar n ω ωs|)
        ((gaussianReal 0 1).map (fun z : ℝ => |z|))
        (fun z : ℝ => fun _ : Unit => z) :=
    chapter10_bootstrap_continuous_mapping_distribution
      (μ := μ) (Pstar := Pstar)
      (Zstar := fun n ω ωs => |Xstar n ω ωs / Ystar n ω ωs|)
      (ν := (gaussianReal 0 1).map (fun z : ℝ => |z|))
      (Z := fun z : ℝ => z) (g := fun z : ℝ => fun _ : Unit => z)
      hweakScalar hmap_cont
  have hPfinite : ∀ n ω, IsFiniteMeasure (Pstar n ω) := by
    intro n ω
    letI : IsProbabilityMeasure (Pstar n ω) := hPstar n ω
    infer_instance
  have hZstar :
      ∀ n ω,
        Measurable
          (fun ωs => fun _ : Unit => |Xstar n ω ωs / Ystar n ω ωs|) := by
    intro n ω
    refine measurable_pi_lambda _ ?_
    intro _
    exact continuous_abs.measurable.comp ((hXstar n ω).div (hYstar n ω))
  have hZlim :
      AEMeasurable (fun z : ℝ => fun _ : Unit => z)
        ((gaussianReal 0 1).map (fun z : ℝ => |z|)) := by
    refine aemeasurable_pi_lambda _ ?_
    intro _
    exact measurable_id.aemeasurable
  exact
    TendstoInBootstrapDistribution.of_weakDistribution_null_frontiers
      (μ := μ) (Pstar := Pstar)
      (Zstar := fun n ω ωs => fun _ : Unit => |Xstar n ω ωs / Ystar n ω ωs|)
      (ν := (gaussianReal 0 1).map (fun z : ℝ => |z|))
      (Z := fun z : ℝ => fun _ : Unit => z)
      hweakUnit hPfinite hZstar hZlim
      (fun x _hx => standardNormalAbs_unit_coordinateLE_frontier_null x)

/-- Indexed Hansen Definition 10.2 face of the standard-normal bootstrap
studentization bridge. -/
theorem chapter10_indexed_bootstrap_studentized_ratio_distribution_standardNormal
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Xstar Ystar : ∀ n, Ω → Ωboot n → ℝ} {c : ℝ}
    (hc : 0 < c)
    (hpair :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar
        (fun n ω ωs => (Xstar n ω ωs, Ystar n ω ωs))
        (gaussianReal 0 1) (fun z : ℝ => (c * z, c)))
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hXstar : ∀ n ω, Measurable (Xstar n ω))
    (hYstar : ∀ n ω, Measurable (Ystar n ω))
    (hY :
      TendstoInBootstrapProbabilityIndexed μ Pstar Ystar (fun _ => c)) :
    TendstoInBootstrapDistributionIndexed μ Pstar
      (fun n ω ωs (_ : Unit) => Xstar n ω ωs / Ystar n ω ωs)
      (gaussianReal 0 1) (fun z : ℝ => fun _ : Unit => z) := by
  have hweakScalar :=
    chapter10_indexed_bootstrap_studentized_ratio_standardNormal
      (μ := μ) (Pstar := Pstar) (Xstar := Xstar) (Ystar := Ystar)
      (c := c) hc hpair hPstar hXstar hYstar hY
  have hmap_cont : Continuous (fun z : ℝ => fun _ : Unit => z) := by
    refine continuous_pi ?_
    intro _
    exact continuous_id
  have hweakUnit :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar
        (fun n ω ωs => fun _ : Unit => Xstar n ω ωs / Ystar n ω ωs)
        (gaussianReal 0 1) (fun z : ℝ => fun _ : Unit => z) :=
    chapter10_indexed_bootstrap_continuous_mapping_distribution
      (μ := μ) (Pstar := Pstar)
      (Zstar := fun n ω ωs => Xstar n ω ωs / Ystar n ω ωs)
      (ν := gaussianReal 0 1) (Z := fun z : ℝ => z)
      (g := fun z : ℝ => fun _ : Unit => z) hweakScalar hmap_cont
  have hPfinite : ∀ n ω, IsFiniteMeasure (Pstar n ω) := by
    intro n ω
    letI : IsProbabilityMeasure (Pstar n ω) := hPstar n ω
    infer_instance
  have hZstar :
      ∀ n ω,
        Measurable (fun ωs => fun _ : Unit => Xstar n ω ωs / Ystar n ω ωs) := by
    intro n ω
    refine measurable_pi_lambda _ ?_
    intro _
    exact (hXstar n ω).div (hYstar n ω)
  have hZlim :
      AEMeasurable (fun z : ℝ => fun _ : Unit => z) (gaussianReal 0 1) := by
    refine aemeasurable_pi_lambda _ ?_
    intro _
    exact measurable_id.aemeasurable
  exact
    TendstoInBootstrapDistributionIndexed.of_weakDistribution_null_frontiers
      (μ := μ) (Pstar := Pstar)
      (Zstar := fun n ω ωs => fun _ : Unit => Xstar n ω ωs / Ystar n ω ωs)
      (ν := gaussianReal 0 1) (Z := fun z : ℝ => fun _ : Unit => z)
      hweakUnit hPfinite hZstar hZlim
      (fun x _hx => standardNormal_unit_coordinateLE_frontier_null x)

/-- Indexed absolute-value face of the standard-normal bootstrap
studentization bridge. -/
theorem chapter10_indexed_bootstrap_studentized_ratio_abs_standardNormalAbs
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Xstar Ystar : ∀ n, Ω → Ωboot n → ℝ} {c : ℝ}
    (hc : 0 < c)
    (hpair :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar
        (fun n ω ωs => (Xstar n ω ωs, Ystar n ω ωs))
        (gaussianReal 0 1) (fun z : ℝ => (c * z, c)))
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hXstar : ∀ n ω, Measurable (Xstar n ω))
    (hYstar : ∀ n ω, Measurable (Ystar n ω))
    (hY :
      TendstoInBootstrapProbabilityIndexed μ Pstar Ystar (fun _ => c)) :
    TendstoInBootstrapWeakDistributionIndexed μ Pstar
      (fun n ω ωs => |Xstar n ω ωs / Ystar n ω ωs|)
      ((gaussianReal 0 1).map (fun z : ℝ => |z|)) (fun z : ℝ => z) := by
  intro f
  have hweakAbs :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar
        (fun n ω ωs => |Xstar n ω ωs / Ystar n ω ωs|)
        (gaussianReal 0 1) (fun z : ℝ => |z|) := by
    exact
      chapter10_indexed_bootstrap_continuous_mapping_distribution
        (μ := μ) (Pstar := Pstar)
        (Zstar := fun n ω ωs => Xstar n ω ωs / Ystar n ω ωs)
        (ν := gaussianReal 0 1) (Z := fun z : ℝ => z)
        (g := fun z : ℝ => |z|)
        (chapter10_indexed_bootstrap_studentized_ratio_standardNormal
          (μ := μ) (Pstar := Pstar) (Xstar := Xstar)
          (Ystar := Ystar) (c := c) hc hpair hPstar hXstar hYstar hY)
        continuous_abs
  have htarget :
      ∫ z, f z ∂((gaussianReal 0 1).map (fun z : ℝ => |z|)) =
        ∫ z, f (|z|) ∂(gaussianReal 0 1) := by
    exact integral_map continuous_abs.aemeasurable f.continuous.aestronglyMeasurable
  simpa [htarget] using hweakAbs.tendsto_integral f

/-- Indexed Hansen Definition 10.2 face of the absolute studentized-ratio
bootstrap law. -/
theorem chapter10_indexed_bootstrap_studentized_ratio_abs_distribution_standardNormalAbs
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Xstar Ystar : ∀ n, Ω → Ωboot n → ℝ} {c : ℝ}
    (hc : 0 < c)
    (hpair :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar
        (fun n ω ωs => (Xstar n ω ωs, Ystar n ω ωs))
        (gaussianReal 0 1) (fun z : ℝ => (c * z, c)))
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hXstar : ∀ n ω, Measurable (Xstar n ω))
    (hYstar : ∀ n ω, Measurable (Ystar n ω))
    (hY :
      TendstoInBootstrapProbabilityIndexed μ Pstar Ystar (fun _ => c)) :
    TendstoInBootstrapDistributionIndexed μ Pstar
      (fun n ω ωs (_ : Unit) => |Xstar n ω ωs / Ystar n ω ωs|)
      ((gaussianReal 0 1).map (fun z : ℝ => |z|))
      (fun z : ℝ => fun _ : Unit => z) := by
  letI :
      IsProbabilityMeasure ((gaussianReal 0 1).map (fun z : ℝ => |z|)) :=
    Measure.isProbabilityMeasure_map continuous_abs.aemeasurable
  have hweakScalar :=
    chapter10_indexed_bootstrap_studentized_ratio_abs_standardNormalAbs
      (μ := μ) (Pstar := Pstar) (Xstar := Xstar) (Ystar := Ystar)
      (c := c) hc hpair hPstar hXstar hYstar hY
  have hmap_cont : Continuous (fun z : ℝ => fun _ : Unit => z) := by
    refine continuous_pi ?_
    intro _
    exact continuous_id
  have hweakUnit :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar
        (fun n ω ωs => fun _ : Unit => |Xstar n ω ωs / Ystar n ω ωs|)
        ((gaussianReal 0 1).map (fun z : ℝ => |z|))
        (fun z : ℝ => fun _ : Unit => z) :=
    chapter10_indexed_bootstrap_continuous_mapping_distribution
      (μ := μ) (Pstar := Pstar)
      (Zstar := fun n ω ωs => |Xstar n ω ωs / Ystar n ω ωs|)
      (ν := (gaussianReal 0 1).map (fun z : ℝ => |z|))
      (Z := fun z : ℝ => z) (g := fun z : ℝ => fun _ : Unit => z)
      hweakScalar hmap_cont
  have hPfinite : ∀ n ω, IsFiniteMeasure (Pstar n ω) := by
    intro n ω
    letI : IsProbabilityMeasure (Pstar n ω) := hPstar n ω
    infer_instance
  have hZstar :
      ∀ n ω,
        Measurable
          (fun ωs => fun _ : Unit => |Xstar n ω ωs / Ystar n ω ωs|) := by
    intro n ω
    refine measurable_pi_lambda _ ?_
    intro _
    exact continuous_abs.measurable.comp ((hXstar n ω).div (hYstar n ω))
  have hZlim :
      AEMeasurable (fun z : ℝ => fun _ : Unit => z)
        ((gaussianReal 0 1).map (fun z : ℝ => |z|)) := by
    refine aemeasurable_pi_lambda _ ?_
    intro _
    exact measurable_id.aemeasurable
  exact
    TendstoInBootstrapDistributionIndexed.of_weakDistribution_null_frontiers
      (μ := μ) (Pstar := Pstar)
      (Zstar := fun n ω ωs => fun _ : Unit => |Xstar n ω ωs / Ystar n ω ωs|)
      (ν := (gaussianReal 0 1).map (fun z : ℝ => |z|))
      (Z := fun z : ℝ => fun _ : Unit => z)
      hweakUnit hPfinite hZstar hZlim
      (fun x _hx => standardNormalAbs_unit_coordinateLE_frontier_null x)

/-- Weak-plus-bootstrap-probability Slutsky product constructor.

If `Xₙ*` has bootstrap weak limit `X` and `Yₙ*` converges to the constant `c`
in bootstrap probability, then the joint statistic `(Xₙ*, Yₙ*)` has weak
bootstrap limit `(X, c)` once the caller supplies the noncompact pair tightness
needed by the global closeness transfer.  This is the reusable bridge for
studentized statistics where the numerator CLT and feasible scale consistency
are proved separately. -/
theorem chapter10_bootstrap_weakDistribution_prod_const_of_probability_tight
    {Pstar : ℕ → Ω → Measure Ωs}
    {Xstar Ystar : ℕ → Ω → Ωs → ℝ}
    {ν : Measure Ωlim} {X : Ωlim → ℝ} {c : ℝ}
    (hX : TendstoInBootstrapWeakDistribution μ Pstar Xstar ν X)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hXstar : ∀ n ω, Measurable (Xstar n ω))
    (hYstar : ∀ n ω, Measurable (Ystar n ω))
    (hTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set (ℝ × ℝ), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω => (Pstar n ω).real {ωs | (Xstar n ω ωs, c) ∉ K})
          atTop (fun _ => 0) ∧
        TendstoInMeasure μ
          (fun n ω =>
            (Pstar n ω).real {ωs | (Xstar n ω ωs, Ystar n ω ωs) ∉ K})
          atTop (fun _ => 0))
    (hY : TendstoInBootstrapProbability μ Pstar Ystar (fun _ => c)) :
    TendstoInBootstrapWeakDistribution μ Pstar
      (fun n ω ωs => (Xstar n ω ωs, Ystar n ω ωs)) ν
      (fun ωlim => (X ωlim, c)) := by
  have hconst :
      TendstoInBootstrapWeakDistribution μ Pstar
        (fun n ω ωs => (Xstar n ω ωs, c)) ν
        (fun ωlim => (X ωlim, c)) := by
    have hcont : Continuous (fun x : ℝ => (x, c)) :=
      continuous_id.prodMk continuous_const
    exact
      chapter10_bootstrap_continuous_mapping_distribution
        (μ := μ) (Pstar := Pstar) (Zstar := Xstar)
        (ν := ν) (Z := X) (g := fun x : ℝ => (x, c)) hX hcont
  refine
    TendstoInBootstrapWeakDistribution.of_bootstrap_dist_tendsto_zero_tight
      (μ := μ) (Pstar := Pstar)
      (Zstar := fun n ω ωs => (Xstar n ω ωs, c))
      (Zstar' := fun n ω ωs => (Xstar n ω ωs, Ystar n ω ωs))
      (ν := ν) (Z := fun ωlim => (X ωlim, c))
      hconst hPstar ?_ ?_ hTail ?_
  · intro n ω
    exact (hXstar n ω).prodMk measurable_const
  · intro n ω
    exact (hXstar n ω).prodMk (hYstar n ω)
  · intro δ hδ
    simpa [bootstrapTailProb, Prod.dist_eq] using hY δ hδ

/-- Indexed weak-plus-bootstrap-probability Slutsky product constructor for
sample-size-dependent bootstrap spaces. -/
theorem
chapter10_indexed_bootstrap_weakDistribution_prod_const_of_probability_tight
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Xstar Ystar : ∀ n, Ω → Ωboot n → ℝ}
    {ν : Measure Ωlim} {X : Ωlim → ℝ} {c : ℝ}
    (hX : TendstoInBootstrapWeakDistributionIndexed μ Pstar Xstar ν X)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hXstar : ∀ n ω, Measurable (Xstar n ω))
    (hYstar : ∀ n ω, Measurable (Ystar n ω))
    (hTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set (ℝ × ℝ), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω => (Pstar n ω).real {ωs | (Xstar n ω ωs, c) ∉ K})
          atTop (fun _ => 0) ∧
        TendstoInMeasure μ
          (fun n ω =>
            (Pstar n ω).real {ωs | (Xstar n ω ωs, Ystar n ω ωs) ∉ K})
          atTop (fun _ => 0))
    (hY : TendstoInBootstrapProbabilityIndexed μ Pstar Ystar (fun _ => c)) :
    TendstoInBootstrapWeakDistributionIndexed μ Pstar
      (fun n ω ωs => (Xstar n ω ωs, Ystar n ω ωs)) ν
      (fun ωlim => (X ωlim, c)) := by
  have hconst :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar
        (fun n ω ωs => (Xstar n ω ωs, c)) ν
        (fun ωlim => (X ωlim, c)) := by
    have hcont : Continuous (fun x : ℝ => (x, c)) :=
      continuous_id.prodMk continuous_const
    exact
      chapter10_indexed_bootstrap_continuous_mapping_distribution
        (μ := μ) (Pstar := Pstar) (Zstar := Xstar)
        (ν := ν) (Z := X) (g := fun x : ℝ => (x, c)) hX hcont
  refine
    TendstoInBootstrapWeakDistributionIndexed.of_bootstrap_dist_tendsto_zero_tight
      (μ := μ) (Pstar := Pstar)
      (Zstar := fun n ω ωs => (Xstar n ω ωs, c))
      (Zstar' := fun n ω ωs => (Xstar n ω ωs, Ystar n ω ωs))
      (ν := ν) (Z := fun ωlim => (X ωlim, c))
      hconst hPstar ?_ ?_ hTail ?_
  · intro n ω
    exact (hXstar n ω).prodMk measurable_const
  · intro n ω
    exact (hXstar n ω).prodMk (hYstar n ω)
  · intro δ hδ
    simpa [bootstrapTailProbIndexed, Prod.dist_eq] using hY δ hδ

/-- Scalar compact-tail constructor for eventually bounded bootstrap statistics.

If `|Xₙ*|` is eventually bounded by a deterministic constant, then the
conditional bootstrap mass outside that fixed compact interval is eventually
identically zero.  This is a true compact-range route for bounded or trimmed
statistics; it is stronger than ordinary tightness. -/
theorem chapter10_bootstrap_scalar_compactTail_of_eventually_bound
    {Pstar : ℕ → Ω → Measure Ωs} {Xstar : ℕ → Ω → Ωs → ℝ} {C : ℝ}
    (hbound : ∀ᶠ n in atTop, ∀ ω ωs, |Xstar n ω ωs| ≤ C) :
    ∀ η : ℝ, 0 < η →
      ∃ Kx : Set ℝ, IsCompact Kx ∧
        TendstoInMeasure μ
          (fun n ω => (Pstar n ω).real {ωs | Xstar n ω ωs ∉ Kx})
          atTop (fun _ => 0) := by
  intro η hη
  let Kx : Set ℝ := Set.Icc (-C) C
  refine ⟨Kx, isCompact_Icc, ?_⟩
  have hzero :
      TendstoInMeasure μ (fun _ (_ : Ω) => (0 : ℝ)) atTop (fun _ => 0) :=
    tendstoInMeasure_const_real (μ := μ) tendsto_const_nhds
  refine TendstoInMeasure.congr'
    (f := fun _ (_ : Ω) => (0 : ℝ))
    (f' := fun n ω => (Pstar n ω).real {ωs | Xstar n ω ωs ∉ Kx})
    (g := fun _ : Ω => (0 : ℝ)) (g' := fun _ : Ω => 0)
    ?_ EventuallyEq.rfl hzero
  filter_upwards [hbound] with n hn
  exact ae_of_all μ fun ω => by
    have hset : {ωs | Xstar n ω ωs ∉ Kx} = ∅ := by
      ext ωs
      have hxmem : Xstar n ω ωs ∈ Kx := by
        dsimp [Kx]
        exact abs_le.mp (hn ω ωs)
      simp [hxmem]
    simp [hset]

/-- Indexed scalar compact-tail constructor for eventually bounded bootstrap
statistics on sample-size-dependent bootstrap spaces. -/
theorem chapter10_indexed_bootstrap_scalar_compactTail_of_eventually_bound
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Xstar : ∀ n, Ω → Ωboot n → ℝ} {C : ℝ}
    (hbound : ∀ᶠ n in atTop, ∀ ω ωs, |Xstar n ω ωs| ≤ C) :
    ∀ η : ℝ, 0 < η →
      ∃ Kx : Set ℝ, IsCompact Kx ∧
        TendstoInMeasure μ
          (fun n ω => (Pstar n ω).real {ωs | Xstar n ω ωs ∉ Kx})
          atTop (fun _ => 0) := by
  intro η hη
  let Kx : Set ℝ := Set.Icc (-C) C
  refine ⟨Kx, isCompact_Icc, ?_⟩
  have hzero :
      TendstoInMeasure μ (fun _ (_ : Ω) => (0 : ℝ)) atTop (fun _ => 0) :=
    tendstoInMeasure_const_real (μ := μ) tendsto_const_nhds
  refine TendstoInMeasure.congr'
    (f := fun _ (_ : Ω) => (0 : ℝ))
    (f' := fun n ω => (Pstar n ω).real {ωs | Xstar n ω ωs ∉ Kx})
    (g := fun _ : Ω => (0 : ℝ)) (g' := fun _ : Ω => 0)
    ?_ EventuallyEq.rfl hzero
  filter_upwards [hbound] with n hn
  exact ae_of_all μ fun ω => by
    have hset : {ωs | Xstar n ω ωs ∉ Kx} = ∅ := by
      ext ωs
      have hxmem : Xstar n ω ωs ∈ Kx := by
        dsimp [Kx]
        exact abs_le.mp (hn ω ωs)
      simp [hxmem]
    simp [hset]

/-- Euclidean compact-tail constructor for eventually deterministically
norm-bounded bootstrap statistics.

If `‖Zₙ*‖` is eventually bounded by a deterministic constant, then the
conditional bootstrap mass outside a fixed compact ball is eventually
identically zero. -/
theorem chapter10_bootstrap_euclidean_compactTail_of_eventually_norm_bound
    {k : Type*} [Fintype k]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Zstar : ℕ → Ω → Ωs → EuclideanSpace ℝ k} {C : ℝ}
    (hbound : ∀ᶠ n in atTop, ∀ ω ωs, ‖Zstar n ω ωs‖ ≤ C) :
    ∀ η : ℝ, 0 < η →
      ∃ K : Set (EuclideanSpace ℝ k), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω => (Pstar n ω).real {ωs | Zstar n ω ωs ∉ K})
          atTop (fun _ => 0) := by
  intro η hη
  let K : Set (EuclideanSpace ℝ k) :=
    Metric.closedBall (0 : EuclideanSpace ℝ k) C
  refine ⟨K, isCompact_closedBall (0 : EuclideanSpace ℝ k) C, ?_⟩
  have hzero :
      TendstoInMeasure μ (fun _ (_ : Ω) => (0 : ℝ)) atTop (fun _ => 0) :=
    tendstoInMeasure_const_real (μ := μ) tendsto_const_nhds
  refine TendstoInMeasure.congr'
    (f := fun _ (_ : Ω) => (0 : ℝ))
    (f' := fun n ω => (Pstar n ω).real {ωs | Zstar n ω ωs ∉ K})
    (g := fun _ : Ω => (0 : ℝ)) (g' := fun _ : Ω => 0)
    ?_ EventuallyEq.rfl hzero
  filter_upwards [hbound] with n hn
  exact ae_of_all μ fun ω => by
    have hset : {ωs | Zstar n ω ωs ∉ K} = ∅ := by
      ext ωs
      have hzmem : Zstar n ω ωs ∈ K := by
        dsimp [K]
        simpa [Metric.mem_closedBall, dist_zero_right] using hn ω ωs
      simp [hzmem]
    simp [hset]

/-- Indexed Euclidean compact-tail constructor for eventually
deterministically norm-bounded bootstrap statistics. -/
theorem chapter10_indexed_bootstrap_euclidean_compactTail_of_eventually_norm_bound
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {k : Type*} [Fintype k]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ k} {C : ℝ}
    (hbound : ∀ᶠ n in atTop, ∀ ω ωs, ‖Zstar n ω ωs‖ ≤ C) :
    ∀ η : ℝ, 0 < η →
      ∃ K : Set (EuclideanSpace ℝ k), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω => (Pstar n ω).real {ωs | Zstar n ω ωs ∉ K})
          atTop (fun _ => 0) := by
  intro η hη
  let K : Set (EuclideanSpace ℝ k) :=
    Metric.closedBall (0 : EuclideanSpace ℝ k) C
  refine ⟨K, isCompact_closedBall (0 : EuclideanSpace ℝ k) C, ?_⟩
  have hzero :
      TendstoInMeasure μ (fun _ (_ : Ω) => (0 : ℝ)) atTop (fun _ => 0) :=
    tendstoInMeasure_const_real (μ := μ) tendsto_const_nhds
  refine TendstoInMeasure.congr'
    (f := fun _ (_ : Ω) => (0 : ℝ))
    (f' := fun n ω => (Pstar n ω).real {ωs | Zstar n ω ωs ∉ K})
    (g := fun _ : Ω => (0 : ℝ)) (g' := fun _ : Ω => 0)
    ?_ EventuallyEq.rfl hzero
  filter_upwards [hbound] with n hn
  exact ae_of_all μ fun ω => by
    have hset : {ωs | Zstar n ω ωs ∉ K} = ∅ := by
      ext ωs
      have hzmem : Zstar n ω ωs ∈ K := by
        dsimp [K]
        simpa [Metric.mem_closedBall, dist_zero_right] using hn ω ωs
      simp [hzmem]
    simp [hset]

/-- Euclidean compact-tail constructor for a pair of eventually
deterministically norm-bounded bootstrap statistics.

The two statistics share the same compact ball, so this discharges the exact
pair compact-tail premise used by noncompact weak-transfer bridges. -/
theorem chapter10_bootstrap_euclidean_pair_compactTail_of_eventually_norm_bound
    {k : Type*} [Fintype k]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Zstar Zstar' : ℕ → Ω → Ωs → EuclideanSpace ℝ k}
    {C C' : ℝ}
    (hZ : ∀ᶠ n in atTop, ∀ ω ωs, ‖Zstar n ω ωs‖ ≤ C)
    (hZ' : ∀ᶠ n in atTop, ∀ ω ωs, ‖Zstar' n ω ωs‖ ≤ C') :
    ∀ η : ℝ, 0 < η →
      ∃ K : Set (EuclideanSpace ℝ k), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω => (Pstar n ω).real {ωs | Zstar n ω ωs ∉ K})
          atTop (fun _ => 0) ∧
        TendstoInMeasure μ
          (fun n ω => (Pstar n ω).real {ωs | Zstar' n ω ωs ∉ K})
          atTop (fun _ => 0) := by
  intro η hη
  let M : ℝ := max C C'
  let K : Set (EuclideanSpace ℝ k) :=
    Metric.closedBall (0 : EuclideanSpace ℝ k) M
  refine ⟨K, isCompact_closedBall (0 : EuclideanSpace ℝ k) M, ?_, ?_⟩
  · have hzero :
        TendstoInMeasure μ (fun _ (_ : Ω) => (0 : ℝ)) atTop (fun _ => 0) :=
      tendstoInMeasure_const_real (μ := μ) tendsto_const_nhds
    refine TendstoInMeasure.congr'
      (f := fun _ (_ : Ω) => (0 : ℝ))
      (f' := fun n ω => (Pstar n ω).real {ωs | Zstar n ω ωs ∉ K})
      (g := fun _ : Ω => (0 : ℝ)) (g' := fun _ : Ω => 0)
      ?_ EventuallyEq.rfl hzero
    filter_upwards [hZ] with n hn
    exact ae_of_all μ fun ω => by
      have hset : {ωs | Zstar n ω ωs ∉ K} = ∅ := by
        ext ωs
        have hzmem : Zstar n ω ωs ∈ K := by
          dsimp [K, M]
          simpa [Metric.mem_closedBall, dist_zero_right] using
            (hn ω ωs).trans (le_max_left C C')
        simp [hzmem]
      simp [hset]
  · have hzero :
        TendstoInMeasure μ (fun _ (_ : Ω) => (0 : ℝ)) atTop (fun _ => 0) :=
      tendstoInMeasure_const_real (μ := μ) tendsto_const_nhds
    refine TendstoInMeasure.congr'
      (f := fun _ (_ : Ω) => (0 : ℝ))
      (f' := fun n ω => (Pstar n ω).real {ωs | Zstar' n ω ωs ∉ K})
      (g := fun _ : Ω => (0 : ℝ)) (g' := fun _ : Ω => 0)
      ?_ EventuallyEq.rfl hzero
    filter_upwards [hZ'] with n hn
    exact ae_of_all μ fun ω => by
      have hset : {ωs | Zstar' n ω ωs ∉ K} = ∅ := by
        ext ωs
        have hzmem : Zstar' n ω ωs ∈ K := by
          dsimp [K, M]
          simpa [Metric.mem_closedBall, dist_zero_right] using
            (hn ω ωs).trans (le_max_right C C')
        simp [hzmem]
      simp [hset]

/-- Indexed Euclidean compact-tail constructor for a pair of eventually
deterministically norm-bounded bootstrap statistics.

The two statistics share the same compact ball, so this discharges the exact
pair compact-tail premise used by noncompact weak-transfer bridges. -/
theorem chapter10_indexed_bootstrap_euclidean_pair_compactTail_of_eventually_norm_bound
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {k : Type*} [Fintype k]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar Zstar' : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ k}
    {C C' : ℝ}
    (hZ : ∀ᶠ n in atTop, ∀ ω ωs, ‖Zstar n ω ωs‖ ≤ C)
    (hZ' : ∀ᶠ n in atTop, ∀ ω ωs, ‖Zstar' n ω ωs‖ ≤ C') :
    ∀ η : ℝ, 0 < η →
      ∃ K : Set (EuclideanSpace ℝ k), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω => (Pstar n ω).real {ωs | Zstar n ω ωs ∉ K})
          atTop (fun _ => 0) ∧
        TendstoInMeasure μ
          (fun n ω => (Pstar n ω).real {ωs | Zstar' n ω ωs ∉ K})
          atTop (fun _ => 0) := by
  intro η hη
  let M : ℝ := max C C'
  let K : Set (EuclideanSpace ℝ k) :=
    Metric.closedBall (0 : EuclideanSpace ℝ k) M
  refine ⟨K, isCompact_closedBall (0 : EuclideanSpace ℝ k) M, ?_, ?_⟩
  · have hzero :
        TendstoInMeasure μ (fun _ (_ : Ω) => (0 : ℝ)) atTop (fun _ => 0) :=
      tendstoInMeasure_const_real (μ := μ) tendsto_const_nhds
    refine TendstoInMeasure.congr'
      (f := fun _ (_ : Ω) => (0 : ℝ))
      (f' := fun n ω => (Pstar n ω).real {ωs | Zstar n ω ωs ∉ K})
      (g := fun _ : Ω => (0 : ℝ)) (g' := fun _ : Ω => 0)
      ?_ EventuallyEq.rfl hzero
    filter_upwards [hZ] with n hn
    exact ae_of_all μ fun ω => by
      have hset : {ωs | Zstar n ω ωs ∉ K} = ∅ := by
        ext ωs
        have hzmem : Zstar n ω ωs ∈ K := by
          dsimp [K, M]
          simpa [Metric.mem_closedBall, dist_zero_right] using
            (hn ω ωs).trans (le_max_left C C')
        simp [hzmem]
      simp [hset]
  · have hzero :
        TendstoInMeasure μ (fun _ (_ : Ω) => (0 : ℝ)) atTop (fun _ => 0) :=
      tendstoInMeasure_const_real (μ := μ) tendsto_const_nhds
    refine TendstoInMeasure.congr'
      (f := fun _ (_ : Ω) => (0 : ℝ))
      (f' := fun n ω => (Pstar n ω).real {ωs | Zstar' n ω ωs ∉ K})
      (g := fun _ : Ω => (0 : ℝ)) (g' := fun _ : Ω => 0)
      ?_ EventuallyEq.rfl hzero
    filter_upwards [hZ'] with n hn
    exact ae_of_all μ fun ω => by
      have hset : {ωs | Zstar' n ω ωs ∉ K} = ∅ := by
        ext ωs
        have hzmem : Zstar' n ω ωs ∈ K := by
          dsimp [K, M]
          simpa [Metric.mem_closedBall, dist_zero_right] using
            (hn ω ωs).trans (le_max_right C C')
        simp [hzmem]
      simp [hset]

private theorem one_le_dist_of_not_mem_Icc_one {c y : ℝ}
    (hy : y ∉ Set.Icc (c - 1) (c + 1)) :
    (1 : ℝ) ≤ dist y c := by
  by_cases hleft : c - 1 ≤ y
  · have hright : ¬ y ≤ c + 1 := by
      intro hle
      exact hy ⟨hleft, hle⟩
    have hgt : c + 1 < y := not_le.mp hright
    rw [Real.dist_eq]
    have hnonneg : 0 ≤ y - c := by linarith
    rw [abs_of_nonneg hnonneg]
    linarith
  · have hlt : y < c - 1 := not_le.mp hleft
    rw [Real.dist_eq]
    have hnonpos : y - c ≤ 0 := by linarith
    rw [abs_of_nonpos hnonpos]
    linarith

/-- Construct the product compact-tail premise used by the marginal
studentization Slutsky bridge from scalar numerator compact-tail control and
bootstrap-probability scale consistency.

For each compact set `Kx` controlling the numerator, the proof uses the compact
rectangle `Kx × [c - 1, c + 1]`.  The constant-scale pair can leave this
rectangle only when the numerator leaves `Kx`; the random-scale pair can leave
only when either the numerator leaves `Kx` or the feasible scale is at least
distance `1` from `c`. -/
theorem chapter10_bootstrap_pair_compactTail_of_scalar_compactTail
    {Pstar : ℕ → Ω → Measure Ωs}
    {Xstar Ystar : ℕ → Ω → Ωs → ℝ} {c : ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hXtail : ∀ η : ℝ, 0 < η →
      ∃ Kx : Set ℝ, IsCompact Kx ∧
        TendstoInMeasure μ
          (fun n ω => (Pstar n ω).real {ωs | Xstar n ω ωs ∉ Kx})
          atTop (fun _ => 0))
    (hY : TendstoInBootstrapProbability μ Pstar Ystar (fun _ => c)) :
    ∀ η : ℝ, 0 < η →
      ∃ K : Set (ℝ × ℝ), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω => (Pstar n ω).real {ωs | (Xstar n ω ωs, c) ∉ K})
          atTop (fun _ => 0) ∧
        TendstoInMeasure μ
          (fun n ω =>
            (Pstar n ω).real {ωs | (Xstar n ω ωs, Ystar n ω ωs) ∉ K})
          atTop (fun _ => 0) := by
  intro η hη
  rcases hXtail η hη with ⟨Kx, hKx, hXK⟩
  let Ky : Set ℝ := Set.Icc (c - 1) (c + 1)
  let K : Set (ℝ × ℝ) := Kx ×ˢ Ky
  have hcKy : c ∈ Ky := by
    dsimp [Ky]
    constructor <;> linarith
  refine ⟨K, hKx.prod isCompact_Icc, ?_, ?_⟩
  · refine tendstoInMeasure_zero_of_nonneg_le
      (μ := μ)
      (f := fun n ω => (Pstar n ω).real {ωs | (Xstar n ω ωs, c) ∉ K})
      (g := fun n ω => (Pstar n ω).real {ωs | Xstar n ω ωs ∉ Kx})
      ?_ ?_ hXK
    · intro n ω
      exact measureReal_nonneg
    · intro n ω
      haveI : IsProbabilityMeasure (Pstar n ω) := hPstar n ω
      refine ENNReal.toReal_mono ?_ (measure_mono ?_)
      · exact measure_ne_top (Pstar n ω) {ωs | Xstar n ω ωs ∉ Kx}
      · intro ωs hωs
        by_contra hx
        have hxmem : Xstar n ω ωs ∈ Kx := by
          by_contra hxmem
          exact hx hxmem
        exact hωs (by exact ⟨hxmem, hcKy⟩)
  · have hYtail :
        TendstoInMeasure μ
          (fun n ω => bootstrapTailProb Pstar Ystar (fun _ => c) 1 n ω)
          atTop (fun _ => 0) :=
      hY 1 zero_lt_one
    have hsum :
        TendstoInMeasure μ
          (fun n ω =>
            (Pstar n ω).real {ωs | Xstar n ω ωs ∉ Kx} +
              bootstrapTailProb Pstar Ystar (fun _ => c) 1 n ω)
          atTop (fun _ => 0) :=
      tendstoInMeasure_add_nonneg_zero
        (μ := μ)
        (f := fun n ω => (Pstar n ω).real {ωs | Xstar n ω ωs ∉ Kx})
        (g := fun n ω => bootstrapTailProb Pstar Ystar (fun _ => c) 1 n ω)
        (fun _ _ => measureReal_nonneg)
        (fun _ _ => ENNReal.toReal_nonneg)
        hXK hYtail
    refine tendstoInMeasure_zero_of_nonneg_le
      (μ := μ)
      (f := fun n ω =>
        (Pstar n ω).real {ωs | (Xstar n ω ωs, Ystar n ω ωs) ∉ K})
      (g := fun n ω =>
        (Pstar n ω).real {ωs | Xstar n ω ωs ∉ Kx} +
          bootstrapTailProb Pstar Ystar (fun _ => c) 1 n ω)
      ?_ ?_ hsum
    · intro n ω
      exact measureReal_nonneg
    · intro n ω
      let C : Set Ωs := {ωs | (Xstar n ω ωs, Ystar n ω ωs) ∉ K}
      let A : Set Ωs := {ωs | Xstar n ω ωs ∉ Kx}
      let B : Set Ωs := {ωs | (1 : ℝ) ≤ dist (Ystar n ω ωs) c}
      have hsubset : C ⊆ A ∪ B := by
        intro ωs hωs
        by_cases hx : Xstar n ω ωs ∈ Kx
        · right
          have hyKy : Ystar n ω ωs ∉ Ky := by
            intro hy
            exact hωs ⟨hx, hy⟩
          exact one_le_dist_of_not_mem_Icc_one hyKy
        · exact Or.inl hx
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
              bootstrapTailProb Pstar Ystar (fun _ => c) 1 n ω := rfl

/-- Indexed product compact-tail constructor from scalar numerator compact
tails and bootstrap-probability scale consistency. -/
theorem chapter10_indexed_bootstrap_pair_compactTail_of_scalar_compactTail
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Xstar Ystar : ∀ n, Ω → Ωboot n → ℝ} {c : ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hXtail : ∀ η : ℝ, 0 < η →
      ∃ Kx : Set ℝ, IsCompact Kx ∧
        TendstoInMeasure μ
          (fun n ω => (Pstar n ω).real {ωs | Xstar n ω ωs ∉ Kx})
          atTop (fun _ => 0))
    (hY : TendstoInBootstrapProbabilityIndexed μ Pstar Ystar (fun _ => c)) :
    ∀ η : ℝ, 0 < η →
      ∃ K : Set (ℝ × ℝ), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω => (Pstar n ω).real {ωs | (Xstar n ω ωs, c) ∉ K})
          atTop (fun _ => 0) ∧
        TendstoInMeasure μ
          (fun n ω =>
            (Pstar n ω).real {ωs | (Xstar n ω ωs, Ystar n ω ωs) ∉ K})
          atTop (fun _ => 0) := by
  intro η hη
  rcases hXtail η hη with ⟨Kx, hKx, hXK⟩
  let Ky : Set ℝ := Set.Icc (c - 1) (c + 1)
  let K : Set (ℝ × ℝ) := Kx ×ˢ Ky
  have hcKy : c ∈ Ky := by
    dsimp [Ky]
    constructor <;> linarith
  refine ⟨K, hKx.prod isCompact_Icc, ?_, ?_⟩
  · refine tendstoInMeasure_zero_of_nonneg_le
      (μ := μ)
      (f := fun n ω => (Pstar n ω).real {ωs | (Xstar n ω ωs, c) ∉ K})
      (g := fun n ω => (Pstar n ω).real {ωs | Xstar n ω ωs ∉ Kx})
      ?_ ?_ hXK
    · intro n ω
      exact measureReal_nonneg
    · intro n ω
      haveI : IsProbabilityMeasure (Pstar n ω) := hPstar n ω
      refine ENNReal.toReal_mono ?_ (measure_mono ?_)
      · exact measure_ne_top (Pstar n ω) {ωs | Xstar n ω ωs ∉ Kx}
      · intro ωs hωs
        by_contra hx
        have hxmem : Xstar n ω ωs ∈ Kx := by
          by_contra hxmem
          exact hx hxmem
        exact hωs (by exact ⟨hxmem, hcKy⟩)
  · have hYtail :
        TendstoInMeasure μ
          (fun n ω =>
            bootstrapTailProbIndexed Pstar Ystar (fun _ => c) 1 n ω)
          atTop (fun _ => 0) :=
      hY 1 zero_lt_one
    have hsum :
        TendstoInMeasure μ
          (fun n ω =>
            (Pstar n ω).real {ωs | Xstar n ω ωs ∉ Kx} +
              bootstrapTailProbIndexed Pstar Ystar (fun _ => c) 1 n ω)
          atTop (fun _ => 0) :=
      tendstoInMeasure_add_nonneg_zero
        (μ := μ)
        (f := fun n ω => (Pstar n ω).real {ωs | Xstar n ω ωs ∉ Kx})
        (g := fun n ω =>
          bootstrapTailProbIndexed Pstar Ystar (fun _ => c) 1 n ω)
        (fun _ _ => measureReal_nonneg)
        (fun _ _ => ENNReal.toReal_nonneg)
        hXK hYtail
    refine tendstoInMeasure_zero_of_nonneg_le
      (μ := μ)
      (f := fun n ω =>
        (Pstar n ω).real {ωs | (Xstar n ω ωs, Ystar n ω ωs) ∉ K})
      (g := fun n ω =>
        (Pstar n ω).real {ωs | Xstar n ω ωs ∉ Kx} +
          bootstrapTailProbIndexed Pstar Ystar (fun _ => c) 1 n ω)
      ?_ ?_ hsum
    · intro n ω
      exact measureReal_nonneg
    · intro n ω
      let C : Set (Ωboot n) := {ωs | (Xstar n ω ωs, Ystar n ω ωs) ∉ K}
      let A : Set (Ωboot n) := {ωs | Xstar n ω ωs ∉ Kx}
      let B : Set (Ωboot n) := {ωs | (1 : ℝ) ≤ dist (Ystar n ω ωs) c}
      have hsubset : C ⊆ A ∪ B := by
        intro ωs hωs
        by_cases hx : Xstar n ω ωs ∈ Kx
        · right
          have hyKy : Ystar n ω ωs ∉ Ky := by
            intro hy
            exact hωs ⟨hx, hy⟩
          exact one_le_dist_of_not_mem_Icc_one hyKy
        · exact Or.inl hx
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
              bootstrapTailProbIndexed Pstar Ystar (fun _ => c) 1 n ω := rfl

/-- Product compact-tail constructor from an eventual deterministic numerator
bound and bootstrap-probability scale consistency. -/
theorem chapter10_bootstrap_pair_compactTail_of_eventually_bound
    {Pstar : ℕ → Ω → Measure Ωs}
    {Xstar Ystar : ℕ → Ω → Ωs → ℝ} {c C : ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hbound : ∀ᶠ n in atTop, ∀ ω ωs, |Xstar n ω ωs| ≤ C)
    (hY : TendstoInBootstrapProbability μ Pstar Ystar (fun _ => c)) :
    ∀ η : ℝ, 0 < η →
      ∃ K : Set (ℝ × ℝ), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω => (Pstar n ω).real {ωs | (Xstar n ω ωs, c) ∉ K})
          atTop (fun _ => 0) ∧
        TendstoInMeasure μ
          (fun n ω =>
            (Pstar n ω).real {ωs | (Xstar n ω ωs, Ystar n ω ωs) ∉ K})
          atTop (fun _ => 0) :=
  chapter10_bootstrap_pair_compactTail_of_scalar_compactTail
    (μ := μ) (Pstar := Pstar) (Xstar := Xstar) (Ystar := Ystar)
    (c := c) hPstar
    (chapter10_bootstrap_scalar_compactTail_of_eventually_bound
      (μ := μ) (Pstar := Pstar) (Xstar := Xstar) hbound)
    hY

/-- Indexed product compact-tail constructor from an eventual deterministic
numerator bound and bootstrap-probability scale consistency. -/
theorem chapter10_indexed_bootstrap_pair_compactTail_of_eventually_bound
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Xstar Ystar : ∀ n, Ω → Ωboot n → ℝ} {c C : ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hbound : ∀ᶠ n in atTop, ∀ ω ωs, |Xstar n ω ωs| ≤ C)
    (hY : TendstoInBootstrapProbabilityIndexed μ Pstar Ystar (fun _ => c)) :
    ∀ η : ℝ, 0 < η →
      ∃ K : Set (ℝ × ℝ), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω => (Pstar n ω).real {ωs | (Xstar n ω ωs, c) ∉ K})
          atTop (fun _ => 0) ∧
        TendstoInMeasure μ
          (fun n ω =>
            (Pstar n ω).real {ωs | (Xstar n ω ωs, Ystar n ω ωs) ∉ K})
          atTop (fun _ => 0) :=
  chapter10_indexed_bootstrap_pair_compactTail_of_scalar_compactTail
    (μ := μ) (Pstar := Pstar) (Xstar := Xstar) (Ystar := Ystar)
    (c := c) hPstar
    (chapter10_indexed_bootstrap_scalar_compactTail_of_eventually_bound
      (μ := μ) (Pstar := Pstar) (Xstar := Xstar) hbound)
    hY

/-- Standard-normal studentization from a marginal numerator bootstrap CLT,
bootstrap-probability scale consistency, and explicit pair compact-tail
control. -/
theorem chapter10_bootstrap_studentized_ratio_standardNormal_of_numerator_tight
    {Pstar : ℕ → Ω → Measure Ωs}
    {Xstar Ystar : ℕ → Ω → Ωs → ℝ} {c : ℝ}
    (hc : 0 < c)
    (hX :
      TendstoInBootstrapWeakDistribution μ Pstar Xstar
        (gaussianReal 0 1) (fun z : ℝ => c * z))
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hXstar : ∀ n ω, Measurable (Xstar n ω))
    (hYstar : ∀ n ω, Measurable (Ystar n ω))
    (hTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set (ℝ × ℝ), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω => (Pstar n ω).real {ωs | (Xstar n ω ωs, c) ∉ K})
          atTop (fun _ => 0) ∧
        TendstoInMeasure μ
          (fun n ω =>
            (Pstar n ω).real {ωs | (Xstar n ω ωs, Ystar n ω ωs) ∉ K})
          atTop (fun _ => 0))
    (hY :
      TendstoInBootstrapProbability μ Pstar Ystar (fun _ => c)) :
    TendstoInBootstrapWeakDistribution μ Pstar
      (fun n ω ωs => Xstar n ω ωs / Ystar n ω ωs)
      (gaussianReal 0 1) (fun z : ℝ => z) := by
  have hpair :
      TendstoInBootstrapWeakDistribution μ Pstar
        (fun n ω ωs => (Xstar n ω ωs, Ystar n ω ωs))
        (gaussianReal 0 1) (fun z : ℝ => (c * z, c)) :=
    chapter10_bootstrap_weakDistribution_prod_const_of_probability_tight
      (μ := μ) (Pstar := Pstar) (Xstar := Xstar) (Ystar := Ystar)
      (ν := gaussianReal 0 1) (X := fun z : ℝ => c * z) (c := c)
      hX hPstar hXstar hYstar hTail hY
  exact
    chapter10_bootstrap_studentized_ratio_standardNormal
      (μ := μ) (Pstar := Pstar) (Xstar := Xstar) (Ystar := Ystar)
      (c := c) hc hpair hPstar hXstar hYstar hY

/-- Indexed standard-normal studentization from a marginal numerator bootstrap
CLT, bootstrap-probability scale consistency, and explicit pair compact-tail
control. -/
theorem
chapter10_indexed_bootstrap_studentized_ratio_standardNormal_of_numerator_tight
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Xstar Ystar : ∀ n, Ω → Ωboot n → ℝ} {c : ℝ}
    (hc : 0 < c)
    (hX :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar Xstar
        (gaussianReal 0 1) (fun z : ℝ => c * z))
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hXstar : ∀ n ω, Measurable (Xstar n ω))
    (hYstar : ∀ n ω, Measurable (Ystar n ω))
    (hTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set (ℝ × ℝ), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω => (Pstar n ω).real {ωs | (Xstar n ω ωs, c) ∉ K})
          atTop (fun _ => 0) ∧
        TendstoInMeasure μ
          (fun n ω =>
            (Pstar n ω).real {ωs | (Xstar n ω ωs, Ystar n ω ωs) ∉ K})
          atTop (fun _ => 0))
    (hY :
      TendstoInBootstrapProbabilityIndexed μ Pstar Ystar (fun _ => c)) :
    TendstoInBootstrapWeakDistributionIndexed μ Pstar
      (fun n ω ωs => Xstar n ω ωs / Ystar n ω ωs)
      (gaussianReal 0 1) (fun z : ℝ => z) := by
  have hpair :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar
        (fun n ω ωs => (Xstar n ω ωs, Ystar n ω ωs))
        (gaussianReal 0 1) (fun z : ℝ => (c * z, c)) :=
    chapter10_indexed_bootstrap_weakDistribution_prod_const_of_probability_tight
      (μ := μ) (Pstar := Pstar) (Xstar := Xstar) (Ystar := Ystar)
      (ν := gaussianReal 0 1) (X := fun z : ℝ => c * z) (c := c)
      hX hPstar hXstar hYstar hTail hY
  exact
    chapter10_indexed_bootstrap_studentized_ratio_standardNormal
      (μ := μ) (Pstar := Pstar) (Xstar := Xstar) (Ystar := Ystar)
      (c := c) hc hpair hPstar hXstar hYstar hY

/-- Hansen Definition 10.2 face of the marginal-CLT studentization bridge. -/
theorem chapter10_bootstrap_studentized_ratio_distribution_standardNormal_of_numerator_tight
    {Pstar : ℕ → Ω → Measure Ωs}
    {Xstar Ystar : ℕ → Ω → Ωs → ℝ} {c : ℝ}
    (hc : 0 < c)
    (hX :
      TendstoInBootstrapWeakDistribution μ Pstar Xstar
        (gaussianReal 0 1) (fun z : ℝ => c * z))
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hXstar : ∀ n ω, Measurable (Xstar n ω))
    (hYstar : ∀ n ω, Measurable (Ystar n ω))
    (hTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set (ℝ × ℝ), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω => (Pstar n ω).real {ωs | (Xstar n ω ωs, c) ∉ K})
          atTop (fun _ => 0) ∧
        TendstoInMeasure μ
          (fun n ω =>
            (Pstar n ω).real {ωs | (Xstar n ω ωs, Ystar n ω ωs) ∉ K})
          atTop (fun _ => 0))
    (hY :
      TendstoInBootstrapProbability μ Pstar Ystar (fun _ => c)) :
    TendstoInBootstrapDistribution μ Pstar
      (fun n ω ωs (_ : Unit) => Xstar n ω ωs / Ystar n ω ωs)
      (gaussianReal 0 1) (fun z : ℝ => fun _ : Unit => z) := by
  have hpair :
      TendstoInBootstrapWeakDistribution μ Pstar
        (fun n ω ωs => (Xstar n ω ωs, Ystar n ω ωs))
        (gaussianReal 0 1) (fun z : ℝ => (c * z, c)) :=
    chapter10_bootstrap_weakDistribution_prod_const_of_probability_tight
      (μ := μ) (Pstar := Pstar) (Xstar := Xstar) (Ystar := Ystar)
      (ν := gaussianReal 0 1) (X := fun z : ℝ => c * z) (c := c)
      hX hPstar hXstar hYstar hTail hY
  exact
    chapter10_bootstrap_studentized_ratio_distribution_standardNormal
      (μ := μ) (Pstar := Pstar) (Xstar := Xstar) (Ystar := Ystar)
      (c := c) hc hpair hPstar hXstar hYstar hY

/-- Indexed Hansen Definition 10.2 face of the marginal-CLT
studentization bridge. -/
theorem
chapter10_indexed_bootstrap_studentized_ratio_distribution_standardNormal_of_numerator_tight
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Xstar Ystar : ∀ n, Ω → Ωboot n → ℝ} {c : ℝ}
    (hc : 0 < c)
    (hX :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar Xstar
        (gaussianReal 0 1) (fun z : ℝ => c * z))
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hXstar : ∀ n ω, Measurable (Xstar n ω))
    (hYstar : ∀ n ω, Measurable (Ystar n ω))
    (hTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set (ℝ × ℝ), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω => (Pstar n ω).real {ωs | (Xstar n ω ωs, c) ∉ K})
          atTop (fun _ => 0) ∧
        TendstoInMeasure μ
          (fun n ω =>
            (Pstar n ω).real {ωs | (Xstar n ω ωs, Ystar n ω ωs) ∉ K})
          atTop (fun _ => 0))
    (hY :
      TendstoInBootstrapProbabilityIndexed μ Pstar Ystar (fun _ => c)) :
    TendstoInBootstrapDistributionIndexed μ Pstar
      (fun n ω ωs (_ : Unit) => Xstar n ω ωs / Ystar n ω ωs)
      (gaussianReal 0 1) (fun z : ℝ => fun _ : Unit => z) := by
  have hpair :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar
        (fun n ω ωs => (Xstar n ω ωs, Ystar n ω ωs))
        (gaussianReal 0 1) (fun z : ℝ => (c * z, c)) :=
    chapter10_indexed_bootstrap_weakDistribution_prod_const_of_probability_tight
      (μ := μ) (Pstar := Pstar) (Xstar := Xstar) (Ystar := Ystar)
      (ν := gaussianReal 0 1) (X := fun z : ℝ => c * z) (c := c)
      hX hPstar hXstar hYstar hTail hY
  exact
    chapter10_indexed_bootstrap_studentized_ratio_distribution_standardNormal
      (μ := μ) (Pstar := Pstar) (Xstar := Xstar) (Ystar := Ystar)
      (c := c) hc hpair hPstar hXstar hYstar hY

/-- Absolute-value face of the marginal-CLT studentization bridge. -/
theorem chapter10_bootstrap_studentized_ratio_abs_standardNormalAbs_of_numerator_tight
    {Pstar : ℕ → Ω → Measure Ωs}
    {Xstar Ystar : ℕ → Ω → Ωs → ℝ} {c : ℝ}
    (hc : 0 < c)
    (hX :
      TendstoInBootstrapWeakDistribution μ Pstar Xstar
        (gaussianReal 0 1) (fun z : ℝ => c * z))
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hXstar : ∀ n ω, Measurable (Xstar n ω))
    (hYstar : ∀ n ω, Measurable (Ystar n ω))
    (hTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set (ℝ × ℝ), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω => (Pstar n ω).real {ωs | (Xstar n ω ωs, c) ∉ K})
          atTop (fun _ => 0) ∧
        TendstoInMeasure μ
          (fun n ω =>
            (Pstar n ω).real {ωs | (Xstar n ω ωs, Ystar n ω ωs) ∉ K})
          atTop (fun _ => 0))
    (hY :
      TendstoInBootstrapProbability μ Pstar Ystar (fun _ => c)) :
    TendstoInBootstrapWeakDistribution μ Pstar
      (fun n ω ωs => |Xstar n ω ωs / Ystar n ω ωs|)
      ((gaussianReal 0 1).map (fun z : ℝ => |z|)) (fun z : ℝ => z) := by
  have hpair :
      TendstoInBootstrapWeakDistribution μ Pstar
        (fun n ω ωs => (Xstar n ω ωs, Ystar n ω ωs))
        (gaussianReal 0 1) (fun z : ℝ => (c * z, c)) :=
    chapter10_bootstrap_weakDistribution_prod_const_of_probability_tight
      (μ := μ) (Pstar := Pstar) (Xstar := Xstar) (Ystar := Ystar)
      (ν := gaussianReal 0 1) (X := fun z : ℝ => c * z) (c := c)
      hX hPstar hXstar hYstar hTail hY
  exact
    chapter10_bootstrap_studentized_ratio_abs_standardNormalAbs
      (μ := μ) (Pstar := Pstar) (Xstar := Xstar) (Ystar := Ystar)
      (c := c) hc hpair hPstar hXstar hYstar hY

/-- Indexed absolute-value face of the marginal-CLT studentization bridge. -/
theorem
chapter10_indexed_bootstrap_studentized_ratio_abs_standardNormalAbs_of_numerator_tight
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Xstar Ystar : ∀ n, Ω → Ωboot n → ℝ} {c : ℝ}
    (hc : 0 < c)
    (hX :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar Xstar
        (gaussianReal 0 1) (fun z : ℝ => c * z))
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hXstar : ∀ n ω, Measurable (Xstar n ω))
    (hYstar : ∀ n ω, Measurable (Ystar n ω))
    (hTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set (ℝ × ℝ), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω => (Pstar n ω).real {ωs | (Xstar n ω ωs, c) ∉ K})
          atTop (fun _ => 0) ∧
        TendstoInMeasure μ
          (fun n ω =>
            (Pstar n ω).real {ωs | (Xstar n ω ωs, Ystar n ω ωs) ∉ K})
          atTop (fun _ => 0))
    (hY :
      TendstoInBootstrapProbabilityIndexed μ Pstar Ystar (fun _ => c)) :
    TendstoInBootstrapWeakDistributionIndexed μ Pstar
      (fun n ω ωs => |Xstar n ω ωs / Ystar n ω ωs|)
      ((gaussianReal 0 1).map (fun z : ℝ => |z|)) (fun z : ℝ => z) := by
  have hpair :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar
        (fun n ω ωs => (Xstar n ω ωs, Ystar n ω ωs))
        (gaussianReal 0 1) (fun z : ℝ => (c * z, c)) :=
    chapter10_indexed_bootstrap_weakDistribution_prod_const_of_probability_tight
      (μ := μ) (Pstar := Pstar) (Xstar := Xstar) (Ystar := Ystar)
      (ν := gaussianReal 0 1) (X := fun z : ℝ => c * z) (c := c)
      hX hPstar hXstar hYstar hTail hY
  exact
    chapter10_indexed_bootstrap_studentized_ratio_abs_standardNormalAbs
      (μ := μ) (Pstar := Pstar) (Xstar := Xstar) (Ystar := Ystar)
      (c := c) hc hpair hPstar hXstar hYstar hY

/-- Hansen Definition 10.2 face of the absolute marginal-CLT studentization
bridge. -/
theorem
chapter10_bootstrap_studentized_abs_distribution_of_numerator_tight
    {Pstar : ℕ → Ω → Measure Ωs}
    {Xstar Ystar : ℕ → Ω → Ωs → ℝ} {c : ℝ}
    (hc : 0 < c)
    (hX :
      TendstoInBootstrapWeakDistribution μ Pstar Xstar
        (gaussianReal 0 1) (fun z : ℝ => c * z))
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hXstar : ∀ n ω, Measurable (Xstar n ω))
    (hYstar : ∀ n ω, Measurable (Ystar n ω))
    (hTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set (ℝ × ℝ), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω => (Pstar n ω).real {ωs | (Xstar n ω ωs, c) ∉ K})
          atTop (fun _ => 0) ∧
        TendstoInMeasure μ
          (fun n ω =>
            (Pstar n ω).real {ωs | (Xstar n ω ωs, Ystar n ω ωs) ∉ K})
          atTop (fun _ => 0))
    (hY :
      TendstoInBootstrapProbability μ Pstar Ystar (fun _ => c)) :
    TendstoInBootstrapDistribution μ Pstar
      (fun n ω ωs (_ : Unit) => |Xstar n ω ωs / Ystar n ω ωs|)
      ((gaussianReal 0 1).map (fun z : ℝ => |z|))
      (fun z : ℝ => fun _ : Unit => z) := by
  have hpair :
      TendstoInBootstrapWeakDistribution μ Pstar
        (fun n ω ωs => (Xstar n ω ωs, Ystar n ω ωs))
        (gaussianReal 0 1) (fun z : ℝ => (c * z, c)) :=
    chapter10_bootstrap_weakDistribution_prod_const_of_probability_tight
      (μ := μ) (Pstar := Pstar) (Xstar := Xstar) (Ystar := Ystar)
      (ν := gaussianReal 0 1) (X := fun z : ℝ => c * z) (c := c)
      hX hPstar hXstar hYstar hTail hY
  exact
    chapter10_bootstrap_studentized_ratio_abs_distribution_standardNormalAbs
      (μ := μ) (Pstar := Pstar) (Xstar := Xstar) (Ystar := Ystar)
      (c := c) hc hpair hPstar hXstar hYstar hY

/-- Indexed Hansen Definition 10.2 face of the absolute marginal-CLT
studentization bridge. -/
theorem
chapter10_indexed_bootstrap_studentized_abs_distribution_of_numerator_tight
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Xstar Ystar : ∀ n, Ω → Ωboot n → ℝ} {c : ℝ}
    (hc : 0 < c)
    (hX :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar Xstar
        (gaussianReal 0 1) (fun z : ℝ => c * z))
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hXstar : ∀ n ω, Measurable (Xstar n ω))
    (hYstar : ∀ n ω, Measurable (Ystar n ω))
    (hTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set (ℝ × ℝ), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω => (Pstar n ω).real {ωs | (Xstar n ω ωs, c) ∉ K})
          atTop (fun _ => 0) ∧
        TendstoInMeasure μ
          (fun n ω =>
            (Pstar n ω).real {ωs | (Xstar n ω ωs, Ystar n ω ωs) ∉ K})
          atTop (fun _ => 0))
    (hY :
      TendstoInBootstrapProbabilityIndexed μ Pstar Ystar (fun _ => c)) :
    TendstoInBootstrapDistributionIndexed μ Pstar
      (fun n ω ωs (_ : Unit) => |Xstar n ω ωs / Ystar n ω ωs|)
      ((gaussianReal 0 1).map (fun z : ℝ => |z|))
      (fun z : ℝ => fun _ : Unit => z) := by
  have hpair :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar
        (fun n ω ωs => (Xstar n ω ωs, Ystar n ω ωs))
        (gaussianReal 0 1) (fun z : ℝ => (c * z, c)) :=
    chapter10_indexed_bootstrap_weakDistribution_prod_const_of_probability_tight
      (μ := μ) (Pstar := Pstar) (Xstar := Xstar) (Ystar := Ystar)
      (ν := gaussianReal 0 1) (X := fun z : ℝ => c * z) (c := c)
      hX hPstar hXstar hYstar hTail hY
  exact
    chapter10_indexed_bootstrap_studentized_ratio_abs_distribution_standardNormalAbs
      (μ := μ) (Pstar := Pstar) (Xstar := Xstar) (Ystar := Ystar)
      (c := c) hc hpair hPstar hXstar hYstar hY

/-- Standard-normal studentization from marginal numerator weak convergence,
scalar numerator compact-tail control, and feasible-scale consistency. -/
theorem chapter10_bootstrap_studentized_ratio_standardNormal_of_scalarTail
    {Pstar : ℕ → Ω → Measure Ωs}
    {Xstar Ystar : ℕ → Ω → Ωs → ℝ} {c : ℝ}
    (hc : 0 < c)
    (hX :
      TendstoInBootstrapWeakDistribution μ Pstar Xstar
        (gaussianReal 0 1) (fun z : ℝ => c * z))
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hXstar : ∀ n ω, Measurable (Xstar n ω))
    (hYstar : ∀ n ω, Measurable (Ystar n ω))
    (hXtail : ∀ η : ℝ, 0 < η →
      ∃ Kx : Set ℝ, IsCompact Kx ∧
        TendstoInMeasure μ
          (fun n ω => (Pstar n ω).real {ωs | Xstar n ω ωs ∉ Kx})
          atTop (fun _ => 0))
    (hY :
      TendstoInBootstrapProbability μ Pstar Ystar (fun _ => c)) :
    TendstoInBootstrapWeakDistribution μ Pstar
      (fun n ω ωs => Xstar n ω ωs / Ystar n ω ωs)
      (gaussianReal 0 1) (fun z : ℝ => z) := by
  have hTail :=
    chapter10_bootstrap_pair_compactTail_of_scalar_compactTail
      (μ := μ) (Pstar := Pstar) (Xstar := Xstar) (Ystar := Ystar)
      (c := c) hPstar hXtail hY
  exact
    chapter10_bootstrap_studentized_ratio_standardNormal_of_numerator_tight
      (μ := μ) (Pstar := Pstar) (Xstar := Xstar) (Ystar := Ystar)
      (c := c) hc hX hPstar hXstar hYstar hTail hY

/-- Indexed standard-normal studentization from marginal numerator weak
convergence, scalar numerator compact-tail control, and feasible-scale
consistency. -/
theorem
chapter10_indexed_bootstrap_studentized_ratio_standardNormal_of_scalarTail
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Xstar Ystar : ∀ n, Ω → Ωboot n → ℝ} {c : ℝ}
    (hc : 0 < c)
    (hX :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar Xstar
        (gaussianReal 0 1) (fun z : ℝ => c * z))
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hXstar : ∀ n ω, Measurable (Xstar n ω))
    (hYstar : ∀ n ω, Measurable (Ystar n ω))
    (hXtail : ∀ η : ℝ, 0 < η →
      ∃ Kx : Set ℝ, IsCompact Kx ∧
        TendstoInMeasure μ
          (fun n ω => (Pstar n ω).real {ωs | Xstar n ω ωs ∉ Kx})
          atTop (fun _ => 0))
    (hY :
      TendstoInBootstrapProbabilityIndexed μ Pstar Ystar (fun _ => c)) :
    TendstoInBootstrapWeakDistributionIndexed μ Pstar
      (fun n ω ωs => Xstar n ω ωs / Ystar n ω ωs)
      (gaussianReal 0 1) (fun z : ℝ => z) := by
  have hTail :=
    chapter10_indexed_bootstrap_pair_compactTail_of_scalar_compactTail
      (μ := μ) (Pstar := Pstar) (Xstar := Xstar) (Ystar := Ystar)
      (c := c) hPstar hXtail hY
  exact
    chapter10_indexed_bootstrap_studentized_ratio_standardNormal_of_numerator_tight
      (μ := μ) (Pstar := Pstar) (Xstar := Xstar) (Ystar := Ystar)
      (c := c) hc hX hPstar hXstar hYstar hTail hY

/-- Hansen Definition 10.2 face of studentization from scalar numerator
compact-tail control. -/
theorem chapter10_bootstrap_studentized_ratio_distribution_of_scalarTail
    {Pstar : ℕ → Ω → Measure Ωs}
    {Xstar Ystar : ℕ → Ω → Ωs → ℝ} {c : ℝ}
    (hc : 0 < c)
    (hX :
      TendstoInBootstrapWeakDistribution μ Pstar Xstar
        (gaussianReal 0 1) (fun z : ℝ => c * z))
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hXstar : ∀ n ω, Measurable (Xstar n ω))
    (hYstar : ∀ n ω, Measurable (Ystar n ω))
    (hXtail : ∀ η : ℝ, 0 < η →
      ∃ Kx : Set ℝ, IsCompact Kx ∧
        TendstoInMeasure μ
          (fun n ω => (Pstar n ω).real {ωs | Xstar n ω ωs ∉ Kx})
          atTop (fun _ => 0))
    (hY :
      TendstoInBootstrapProbability μ Pstar Ystar (fun _ => c)) :
    TendstoInBootstrapDistribution μ Pstar
      (fun n ω ωs (_ : Unit) => Xstar n ω ωs / Ystar n ω ωs)
      (gaussianReal 0 1) (fun z : ℝ => fun _ : Unit => z) := by
  have hTail :=
    chapter10_bootstrap_pair_compactTail_of_scalar_compactTail
      (μ := μ) (Pstar := Pstar) (Xstar := Xstar) (Ystar := Ystar)
      (c := c) hPstar hXtail hY
  exact
    chapter10_bootstrap_studentized_ratio_distribution_standardNormal_of_numerator_tight
      (μ := μ) (Pstar := Pstar) (Xstar := Xstar) (Ystar := Ystar)
      (c := c) hc hX hPstar hXstar hYstar hTail hY

/-- Indexed Hansen Definition 10.2 face of studentization from scalar numerator
compact-tail control. -/
theorem chapter10_indexed_bootstrap_studentized_ratio_distribution_of_scalarTail
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Xstar Ystar : ∀ n, Ω → Ωboot n → ℝ} {c : ℝ}
    (hc : 0 < c)
    (hX :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar Xstar
        (gaussianReal 0 1) (fun z : ℝ => c * z))
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hXstar : ∀ n ω, Measurable (Xstar n ω))
    (hYstar : ∀ n ω, Measurable (Ystar n ω))
    (hXtail : ∀ η : ℝ, 0 < η →
      ∃ Kx : Set ℝ, IsCompact Kx ∧
        TendstoInMeasure μ
          (fun n ω => (Pstar n ω).real {ωs | Xstar n ω ωs ∉ Kx})
          atTop (fun _ => 0))
    (hY :
      TendstoInBootstrapProbabilityIndexed μ Pstar Ystar (fun _ => c)) :
    TendstoInBootstrapDistributionIndexed μ Pstar
      (fun n ω ωs (_ : Unit) => Xstar n ω ωs / Ystar n ω ωs)
      (gaussianReal 0 1) (fun z : ℝ => fun _ : Unit => z) := by
  have hTail :=
    chapter10_indexed_bootstrap_pair_compactTail_of_scalar_compactTail
      (μ := μ) (Pstar := Pstar) (Xstar := Xstar) (Ystar := Ystar)
      (c := c) hPstar hXtail hY
  exact
    chapter10_indexed_bootstrap_studentized_ratio_distribution_standardNormal_of_numerator_tight
      (μ := μ) (Pstar := Pstar) (Xstar := Xstar) (Ystar := Ystar)
      (c := c) hc hX hPstar hXstar hYstar hTail hY

/-- Absolute studentized statistic from scalar numerator compact-tail control. -/
theorem chapter10_bootstrap_studentized_ratio_abs_of_scalarTail
    {Pstar : ℕ → Ω → Measure Ωs}
    {Xstar Ystar : ℕ → Ω → Ωs → ℝ} {c : ℝ}
    (hc : 0 < c)
    (hX :
      TendstoInBootstrapWeakDistribution μ Pstar Xstar
        (gaussianReal 0 1) (fun z : ℝ => c * z))
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hXstar : ∀ n ω, Measurable (Xstar n ω))
    (hYstar : ∀ n ω, Measurable (Ystar n ω))
    (hXtail : ∀ η : ℝ, 0 < η →
      ∃ Kx : Set ℝ, IsCompact Kx ∧
        TendstoInMeasure μ
          (fun n ω => (Pstar n ω).real {ωs | Xstar n ω ωs ∉ Kx})
          atTop (fun _ => 0))
    (hY :
      TendstoInBootstrapProbability μ Pstar Ystar (fun _ => c)) :
    TendstoInBootstrapWeakDistribution μ Pstar
      (fun n ω ωs => |Xstar n ω ωs / Ystar n ω ωs|)
      ((gaussianReal 0 1).map (fun z : ℝ => |z|)) (fun z : ℝ => z) := by
  have hTail :=
    chapter10_bootstrap_pair_compactTail_of_scalar_compactTail
      (μ := μ) (Pstar := Pstar) (Xstar := Xstar) (Ystar := Ystar)
      (c := c) hPstar hXtail hY
  exact
    chapter10_bootstrap_studentized_ratio_abs_standardNormalAbs_of_numerator_tight
      (μ := μ) (Pstar := Pstar) (Xstar := Xstar) (Ystar := Ystar)
      (c := c) hc hX hPstar hXstar hYstar hTail hY

/-- Indexed absolute studentized statistic from scalar numerator compact-tail
control. -/
theorem chapter10_indexed_bootstrap_studentized_ratio_abs_of_scalarTail
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Xstar Ystar : ∀ n, Ω → Ωboot n → ℝ} {c : ℝ}
    (hc : 0 < c)
    (hX :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar Xstar
        (gaussianReal 0 1) (fun z : ℝ => c * z))
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hXstar : ∀ n ω, Measurable (Xstar n ω))
    (hYstar : ∀ n ω, Measurable (Ystar n ω))
    (hXtail : ∀ η : ℝ, 0 < η →
      ∃ Kx : Set ℝ, IsCompact Kx ∧
        TendstoInMeasure μ
          (fun n ω => (Pstar n ω).real {ωs | Xstar n ω ωs ∉ Kx})
          atTop (fun _ => 0))
    (hY :
      TendstoInBootstrapProbabilityIndexed μ Pstar Ystar (fun _ => c)) :
    TendstoInBootstrapWeakDistributionIndexed μ Pstar
      (fun n ω ωs => |Xstar n ω ωs / Ystar n ω ωs|)
      ((gaussianReal 0 1).map (fun z : ℝ => |z|)) (fun z : ℝ => z) := by
  have hTail :=
    chapter10_indexed_bootstrap_pair_compactTail_of_scalar_compactTail
      (μ := μ) (Pstar := Pstar) (Xstar := Xstar) (Ystar := Ystar)
      (c := c) hPstar hXtail hY
  exact
    chapter10_indexed_bootstrap_studentized_ratio_abs_standardNormalAbs_of_numerator_tight
      (μ := μ) (Pstar := Pstar) (Xstar := Xstar) (Ystar := Ystar)
      (c := c) hc hX hPstar hXstar hYstar hTail hY

/-- Hansen Definition 10.2 face of the absolute studentized statistic from
scalar numerator compact-tail control. -/
theorem chapter10_bootstrap_studentized_abs_distribution_of_scalarTail
    {Pstar : ℕ → Ω → Measure Ωs}
    {Xstar Ystar : ℕ → Ω → Ωs → ℝ} {c : ℝ}
    (hc : 0 < c)
    (hX :
      TendstoInBootstrapWeakDistribution μ Pstar Xstar
        (gaussianReal 0 1) (fun z : ℝ => c * z))
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hXstar : ∀ n ω, Measurable (Xstar n ω))
    (hYstar : ∀ n ω, Measurable (Ystar n ω))
    (hXtail : ∀ η : ℝ, 0 < η →
      ∃ Kx : Set ℝ, IsCompact Kx ∧
        TendstoInMeasure μ
          (fun n ω => (Pstar n ω).real {ωs | Xstar n ω ωs ∉ Kx})
          atTop (fun _ => 0))
    (hY :
      TendstoInBootstrapProbability μ Pstar Ystar (fun _ => c)) :
    TendstoInBootstrapDistribution μ Pstar
      (fun n ω ωs (_ : Unit) => |Xstar n ω ωs / Ystar n ω ωs|)
      ((gaussianReal 0 1).map (fun z : ℝ => |z|))
      (fun z : ℝ => fun _ : Unit => z) := by
  have hTail :=
    chapter10_bootstrap_pair_compactTail_of_scalar_compactTail
      (μ := μ) (Pstar := Pstar) (Xstar := Xstar) (Ystar := Ystar)
      (c := c) hPstar hXtail hY
  exact
    chapter10_bootstrap_studentized_abs_distribution_of_numerator_tight
      (μ := μ) (Pstar := Pstar) (Xstar := Xstar) (Ystar := Ystar)
      (c := c) hc hX hPstar hXstar hYstar hTail hY

/-- Indexed Hansen Definition 10.2 face of the absolute studentized statistic
from scalar numerator compact-tail control. -/
theorem chapter10_indexed_bootstrap_studentized_abs_distribution_of_scalarTail
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Xstar Ystar : ∀ n, Ω → Ωboot n → ℝ} {c : ℝ}
    (hc : 0 < c)
    (hX :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar Xstar
        (gaussianReal 0 1) (fun z : ℝ => c * z))
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hXstar : ∀ n ω, Measurable (Xstar n ω))
    (hYstar : ∀ n ω, Measurable (Ystar n ω))
    (hXtail : ∀ η : ℝ, 0 < η →
      ∃ Kx : Set ℝ, IsCompact Kx ∧
        TendstoInMeasure μ
          (fun n ω => (Pstar n ω).real {ωs | Xstar n ω ωs ∉ Kx})
          atTop (fun _ => 0))
    (hY :
      TendstoInBootstrapProbabilityIndexed μ Pstar Ystar (fun _ => c)) :
    TendstoInBootstrapDistributionIndexed μ Pstar
      (fun n ω ωs (_ : Unit) => |Xstar n ω ωs / Ystar n ω ωs|)
      ((gaussianReal 0 1).map (fun z : ℝ => |z|))
      (fun z : ℝ => fun _ : Unit => z) := by
  have hTail :=
    chapter10_indexed_bootstrap_pair_compactTail_of_scalar_compactTail
      (μ := μ) (Pstar := Pstar) (Xstar := Xstar) (Ystar := Ystar)
      (c := c) hPstar hXtail hY
  exact
    chapter10_indexed_bootstrap_studentized_abs_distribution_of_numerator_tight
      (μ := μ) (Pstar := Pstar) (Xstar := Xstar) (Ystar := Ystar)
      (c := c) hc hX hPstar hXstar hYstar hTail hY

/-- Standard-normal studentization from an eventually bounded numerator and
feasible-scale consistency.

This is the compact-range face of
`chapter10_bootstrap_studentized_ratio_standardNormal_of_scalarTail`: the
eventual deterministic bound supplies the scalar compact-tail premise directly. -/
theorem chapter10_bootstrap_studentized_ratio_standardNormal_of_eventually_bound
    {Pstar : ℕ → Ω → Measure Ωs}
    {Xstar Ystar : ℕ → Ω → Ωs → ℝ} {c C : ℝ}
    (hc : 0 < c)
    (hX :
      TendstoInBootstrapWeakDistribution μ Pstar Xstar
        (gaussianReal 0 1) (fun z : ℝ => c * z))
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hXstar : ∀ n ω, Measurable (Xstar n ω))
    (hYstar : ∀ n ω, Measurable (Ystar n ω))
    (hbound : ∀ᶠ n in atTop, ∀ ω ωs, |Xstar n ω ωs| ≤ C)
    (hY :
      TendstoInBootstrapProbability μ Pstar Ystar (fun _ => c)) :
    TendstoInBootstrapWeakDistribution μ Pstar
      (fun n ω ωs => Xstar n ω ωs / Ystar n ω ωs)
      (gaussianReal 0 1) (fun z : ℝ => z) :=
  chapter10_bootstrap_studentized_ratio_standardNormal_of_scalarTail
    (μ := μ) (Pstar := Pstar) (Xstar := Xstar) (Ystar := Ystar)
    (c := c) hc hX hPstar hXstar hYstar
    (chapter10_bootstrap_scalar_compactTail_of_eventually_bound
      (μ := μ) (Pstar := Pstar) (Xstar := Xstar) hbound)
    hY

/-- Indexed standard-normal studentization from an eventually bounded numerator
and feasible-scale consistency. -/
theorem
chapter10_indexed_bootstrap_studentized_ratio_standardNormal_of_eventually_bound
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Xstar Ystar : ∀ n, Ω → Ωboot n → ℝ} {c C : ℝ}
    (hc : 0 < c)
    (hX :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar Xstar
        (gaussianReal 0 1) (fun z : ℝ => c * z))
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hXstar : ∀ n ω, Measurable (Xstar n ω))
    (hYstar : ∀ n ω, Measurable (Ystar n ω))
    (hbound : ∀ᶠ n in atTop, ∀ ω ωs, |Xstar n ω ωs| ≤ C)
    (hY :
      TendstoInBootstrapProbabilityIndexed μ Pstar Ystar (fun _ => c)) :
    TendstoInBootstrapWeakDistributionIndexed μ Pstar
      (fun n ω ωs => Xstar n ω ωs / Ystar n ω ωs)
      (gaussianReal 0 1) (fun z : ℝ => z) :=
  chapter10_indexed_bootstrap_studentized_ratio_standardNormal_of_scalarTail
    (μ := μ) (Pstar := Pstar) (Xstar := Xstar) (Ystar := Ystar)
    (c := c) hc hX hPstar hXstar hYstar
    (chapter10_indexed_bootstrap_scalar_compactTail_of_eventually_bound
      (μ := μ) (Pstar := Pstar) (Xstar := Xstar) hbound)
    hY

/-- Hansen Definition 10.2 face of studentization from an eventually bounded
numerator. -/
theorem chapter10_bootstrap_studentized_ratio_distribution_of_eventually_bound
    {Pstar : ℕ → Ω → Measure Ωs}
    {Xstar Ystar : ℕ → Ω → Ωs → ℝ} {c C : ℝ}
    (hc : 0 < c)
    (hX :
      TendstoInBootstrapWeakDistribution μ Pstar Xstar
        (gaussianReal 0 1) (fun z : ℝ => c * z))
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hXstar : ∀ n ω, Measurable (Xstar n ω))
    (hYstar : ∀ n ω, Measurable (Ystar n ω))
    (hbound : ∀ᶠ n in atTop, ∀ ω ωs, |Xstar n ω ωs| ≤ C)
    (hY :
      TendstoInBootstrapProbability μ Pstar Ystar (fun _ => c)) :
    TendstoInBootstrapDistribution μ Pstar
      (fun n ω ωs (_ : Unit) => Xstar n ω ωs / Ystar n ω ωs)
      (gaussianReal 0 1) (fun z : ℝ => fun _ : Unit => z) :=
  chapter10_bootstrap_studentized_ratio_distribution_of_scalarTail
    (μ := μ) (Pstar := Pstar) (Xstar := Xstar) (Ystar := Ystar)
    (c := c) hc hX hPstar hXstar hYstar
    (chapter10_bootstrap_scalar_compactTail_of_eventually_bound
      (μ := μ) (Pstar := Pstar) (Xstar := Xstar) hbound)
    hY

/-- Indexed Hansen Definition 10.2 face of studentization from an eventually
bounded numerator. -/
theorem
chapter10_indexed_bootstrap_studentized_ratio_distribution_of_eventually_bound
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Xstar Ystar : ∀ n, Ω → Ωboot n → ℝ} {c C : ℝ}
    (hc : 0 < c)
    (hX :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar Xstar
        (gaussianReal 0 1) (fun z : ℝ => c * z))
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hXstar : ∀ n ω, Measurable (Xstar n ω))
    (hYstar : ∀ n ω, Measurable (Ystar n ω))
    (hbound : ∀ᶠ n in atTop, ∀ ω ωs, |Xstar n ω ωs| ≤ C)
    (hY :
      TendstoInBootstrapProbabilityIndexed μ Pstar Ystar (fun _ => c)) :
    TendstoInBootstrapDistributionIndexed μ Pstar
      (fun n ω ωs (_ : Unit) => Xstar n ω ωs / Ystar n ω ωs)
      (gaussianReal 0 1) (fun z : ℝ => fun _ : Unit => z) :=
  chapter10_indexed_bootstrap_studentized_ratio_distribution_of_scalarTail
    (μ := μ) (Pstar := Pstar) (Xstar := Xstar) (Ystar := Ystar)
    (c := c) hc hX hPstar hXstar hYstar
    (chapter10_indexed_bootstrap_scalar_compactTail_of_eventually_bound
      (μ := μ) (Pstar := Pstar) (Xstar := Xstar) hbound)
    hY

/-- Absolute studentized statistic from an eventually bounded numerator and
feasible-scale consistency. -/
theorem chapter10_bootstrap_studentized_ratio_abs_of_eventually_bound
    {Pstar : ℕ → Ω → Measure Ωs}
    {Xstar Ystar : ℕ → Ω → Ωs → ℝ} {c C : ℝ}
    (hc : 0 < c)
    (hX :
      TendstoInBootstrapWeakDistribution μ Pstar Xstar
        (gaussianReal 0 1) (fun z : ℝ => c * z))
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hXstar : ∀ n ω, Measurable (Xstar n ω))
    (hYstar : ∀ n ω, Measurable (Ystar n ω))
    (hbound : ∀ᶠ n in atTop, ∀ ω ωs, |Xstar n ω ωs| ≤ C)
    (hY :
      TendstoInBootstrapProbability μ Pstar Ystar (fun _ => c)) :
    TendstoInBootstrapWeakDistribution μ Pstar
      (fun n ω ωs => |Xstar n ω ωs / Ystar n ω ωs|)
      ((gaussianReal 0 1).map (fun z : ℝ => |z|)) (fun z : ℝ => z) :=
  chapter10_bootstrap_studentized_ratio_abs_of_scalarTail
    (μ := μ) (Pstar := Pstar) (Xstar := Xstar) (Ystar := Ystar)
    (c := c) hc hX hPstar hXstar hYstar
    (chapter10_bootstrap_scalar_compactTail_of_eventually_bound
      (μ := μ) (Pstar := Pstar) (Xstar := Xstar) hbound)
    hY

/-- Indexed absolute studentized statistic from an eventually bounded numerator
and feasible-scale consistency. -/
theorem chapter10_indexed_bootstrap_studentized_ratio_abs_of_eventually_bound
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Xstar Ystar : ∀ n, Ω → Ωboot n → ℝ} {c C : ℝ}
    (hc : 0 < c)
    (hX :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar Xstar
        (gaussianReal 0 1) (fun z : ℝ => c * z))
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hXstar : ∀ n ω, Measurable (Xstar n ω))
    (hYstar : ∀ n ω, Measurable (Ystar n ω))
    (hbound : ∀ᶠ n in atTop, ∀ ω ωs, |Xstar n ω ωs| ≤ C)
    (hY :
      TendstoInBootstrapProbabilityIndexed μ Pstar Ystar (fun _ => c)) :
    TendstoInBootstrapWeakDistributionIndexed μ Pstar
      (fun n ω ωs => |Xstar n ω ωs / Ystar n ω ωs|)
      ((gaussianReal 0 1).map (fun z : ℝ => |z|)) (fun z : ℝ => z) :=
  chapter10_indexed_bootstrap_studentized_ratio_abs_of_scalarTail
    (μ := μ) (Pstar := Pstar) (Xstar := Xstar) (Ystar := Ystar)
    (c := c) hc hX hPstar hXstar hYstar
    (chapter10_indexed_bootstrap_scalar_compactTail_of_eventually_bound
      (μ := μ) (Pstar := Pstar) (Xstar := Xstar) hbound)
    hY

/-- Hansen Definition 10.2 face of the absolute studentized statistic from an
eventually bounded numerator. -/
theorem chapter10_bootstrap_studentized_abs_distribution_of_eventually_bound
    {Pstar : ℕ → Ω → Measure Ωs}
    {Xstar Ystar : ℕ → Ω → Ωs → ℝ} {c C : ℝ}
    (hc : 0 < c)
    (hX :
      TendstoInBootstrapWeakDistribution μ Pstar Xstar
        (gaussianReal 0 1) (fun z : ℝ => c * z))
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hXstar : ∀ n ω, Measurable (Xstar n ω))
    (hYstar : ∀ n ω, Measurable (Ystar n ω))
    (hbound : ∀ᶠ n in atTop, ∀ ω ωs, |Xstar n ω ωs| ≤ C)
    (hY :
      TendstoInBootstrapProbability μ Pstar Ystar (fun _ => c)) :
    TendstoInBootstrapDistribution μ Pstar
      (fun n ω ωs (_ : Unit) => |Xstar n ω ωs / Ystar n ω ωs|)
      ((gaussianReal 0 1).map (fun z : ℝ => |z|))
      (fun z : ℝ => fun _ : Unit => z) :=
  chapter10_bootstrap_studentized_abs_distribution_of_scalarTail
    (μ := μ) (Pstar := Pstar) (Xstar := Xstar) (Ystar := Ystar)
    (c := c) hc hX hPstar hXstar hYstar
    (chapter10_bootstrap_scalar_compactTail_of_eventually_bound
      (μ := μ) (Pstar := Pstar) (Xstar := Xstar) hbound)
    hY

/-- Indexed Hansen Definition 10.2 face of the absolute studentized statistic
from an eventually bounded numerator. -/
theorem
chapter10_indexed_bootstrap_studentized_abs_distribution_of_eventually_bound
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Xstar Ystar : ∀ n, Ω → Ωboot n → ℝ} {c C : ℝ}
    (hc : 0 < c)
    (hX :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar Xstar
        (gaussianReal 0 1) (fun z : ℝ => c * z))
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hXstar : ∀ n ω, Measurable (Xstar n ω))
    (hYstar : ∀ n ω, Measurable (Ystar n ω))
    (hbound : ∀ᶠ n in atTop, ∀ ω ωs, |Xstar n ω ωs| ≤ C)
    (hY :
      TendstoInBootstrapProbabilityIndexed μ Pstar Ystar (fun _ => c)) :
    TendstoInBootstrapDistributionIndexed μ Pstar
      (fun n ω ωs (_ : Unit) => |Xstar n ω ωs / Ystar n ω ωs|)
      ((gaussianReal 0 1).map (fun z : ℝ => |z|))
      (fun z : ℝ => fun _ : Unit => z) :=
  chapter10_indexed_bootstrap_studentized_abs_distribution_of_scalarTail
    (μ := μ) (Pstar := Pstar) (Xstar := Xstar) (Ystar := Ystar)
    (c := c) hc hX hPstar hXstar hYstar
    (chapter10_indexed_bootstrap_scalar_compactTail_of_eventually_bound
      (μ := μ) (Pstar := Pstar) (Xstar := Xstar) hbound)
    hY

end BootstrapStudentization

end HansenEconometrics
