import HansenEconometrics.Chapter10Bootstrap.Quantiles
import HansenEconometrics.Chapter10Bootstrap.Regression

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology MeasureTheory ProbabilityTheory Matrix
open scoped Matrix.Norms.Elementwise Function

namespace HansenEconometrics

variable {Ω Ωs Ωlim E F k : Type*}
variable {mΩ : MeasurableSpace Ω} {mΩs : MeasurableSpace Ωs}
variable {mΩlim : MeasurableSpace Ωlim}
variable {μ : Measure Ω} {ν : Measure Ωlim}

section PercentileIntervals

/-- Hansen percentile confidence interval event, `qLower <= θ <= qUpper`. -/
def percentileCIEvent (θ qLower qUpper : ℝ) : Prop :=
  qLower ≤ θ ∧ θ ≤ qUpper

/-- Three-coordinate statistic used in the percentile-interval coverage proof:

* coordinate `0`: `aₙ(θhatₙ - θ)`;
* coordinate `1`: `aₙ(q*_{α/2,n} - θhatₙ)`;
* coordinate `2`: `aₙ(q*_{1-α/2,n} - θhatₙ)`.

The confidence event is the lower/upper half-space intersection encoded by
`percentileCoverageSet`. -/
noncomputable def percentileCoverageVector
    (a : ℕ → ℝ) (θ : ℝ) (θhat qLower qUpper : ℕ → Ω → ℝ)
    (n : ℕ) (ω : Ω) : Fin 3 → ℝ :=
  fun i =>
    if i = 0 then a n * (θhat n ω - θ)
    else if i = 1 then a n * (qLower n ω - θhat n ω)
    else a n * (qUpper n ω - θhat n ω)

/-- Limit vector for the percentile-interval coverage proof. -/
noncomputable def percentileCoverageLimitVector
    (ξ : Ωlim → ℝ) (qLower qUpper : ℝ) (ω : Ωlim) : Fin 3 → ℝ :=
  fun i =>
    if i = 0 then ξ ω
    else if i = 1 then qLower
    else qUpper

/-- Componentwise Slutsky constructor for the percentile-coverage joint vector.

This assembles the joint convergence premise in
`chapter10_percentileCI_coverage_tendsto_of_joint_quantile_limit` from the
scaled estimator-error limit and the two bootstrap endpoint limits. -/
theorem percentileCoverageVector_tendstoInDistribution_of_components
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {a : ℕ → ℝ} {θ : ℝ} {θhat qLower qUpper : ℕ → Ω → ℝ}
    {ξ : Ωlim → ℝ} {qLowerLim qUpperLim : ℝ}
    (hstat :
      TendstoInDistribution
        (fun n ω => a n * (θhat n ω - θ))
        atTop ξ (fun _ => μ) ν)
    (hlower :
      TendstoInMeasure μ
        (fun n ω => a n * (qLower n ω - θhat n ω))
        atTop (fun _ => qLowerLim))
    (hupper :
      TendstoInMeasure μ
        (fun n ω => a n * (qUpper n ω - θhat n ω))
        atTop (fun _ => qUpperLim))
    (hlower_meas :
      ∀ n, AEMeasurable (fun ω => a n * (qLower n ω - θhat n ω)) μ)
    (hupper_meas :
      ∀ n, AEMeasurable (fun ω => a n * (qUpper n ω - θhat n ω)) μ) :
    TendstoInDistribution
      (percentileCoverageVector a θ θhat qLower qUpper)
      atTop
      (percentileCoverageLimitVector ξ qLowerLim qUpperLim)
      (fun _ => μ) ν := by
  classical
  let statSeq : ℕ → Ω → ℝ := fun n ω => a n * (θhat n ω - θ)
  let lowerSeq : ℕ → Ω → ℝ := fun n ω => a n * (qLower n ω - θhat n ω)
  let upperSeq : ℕ → Ω → ℝ := fun n ω => a n * (qUpper n ω - θhat n ω)
  let pack : (ℝ × ℝ) × ℝ → Fin 3 → ℝ :=
    fun p i => if i = 0 then p.1.1 else if i = 1 then p.1.2 else p.2
  have hpack_cont : Continuous pack := by
    refine continuous_pi ?_
    intro i
    by_cases hi0 : i = 0
    · simpa [pack, hi0] using
        ((continuous_fst : Continuous (fun p : (ℝ × ℝ) × ℝ => p.1)).fst)
    · by_cases hi1 : i = 1
      · simpa [pack, hi0, hi1] using
          ((continuous_fst : Continuous (fun p : (ℝ × ℝ) × ℝ => p.1)).snd)
      · simpa [pack, hi0, hi1] using
          (continuous_snd : Continuous (fun p : (ℝ × ℝ) × ℝ => p.2))
  have hpair :
      TendstoInDistribution
        (fun n ω => (statSeq n ω, lowerSeq n ω))
        atTop (fun ω => (ξ ω, qLowerLim)) (fun _ => μ) ν :=
    hstat.prodMk_of_tendstoInMeasure_const statSeq lowerSeq ξ
      (by simpa [lowerSeq] using hlower)
      (by simpa [lowerSeq] using hlower_meas)
  have hpacked :
      TendstoInDistribution
        (fun n ω => pack ((statSeq n ω, lowerSeq n ω), upperSeq n ω))
        atTop (fun ω => pack ((ξ ω, qLowerLim), qUpperLim))
        (fun _ => μ) ν := by
    have hraw := hpair.continuous_comp_prodMk_of_tendstoInMeasure_const
      (g := pack) hpack_cont
      (by simpa [upperSeq] using hupper)
      (by simpa [upperSeq] using hupper_meas)
    simpa [Function.comp_def] using hraw
  refine TendstoInDistribution.congr ?_ ?_ hpacked
  · intro n
    exact ae_of_all μ fun ω => by
      ext i
      by_cases hi0 : i = 0 <;> by_cases hi1 : i = 1 <;>
        simp [percentileCoverageVector, statSeq, lowerSeq, upperSeq, pack, hi0, hi1]
  · exact ae_of_all ν fun ω => by
      ext i
      by_cases hi0 : i = 0 <;> by_cases hi1 : i = 1 <;>
        simp [percentileCoverageLimitVector, pack, hi0, hi1]

/-- Limit event corresponding to percentile-interval coverage:
`qLower <= -ξ <= qUpper`. -/
def percentileCoverageSet : Set (Fin 3 → ℝ) :=
  {z | z 1 ≤ -z 0 ∧ -z 0 ≤ z 2}

private theorem isClosed_percentileCoverageSet : IsClosed percentileCoverageSet := by
  have hleft : IsClosed {z : Fin 3 → ℝ | z 1 ≤ -z 0} :=
    isClosed_le (continuous_apply 1) ((continuous_apply 0).neg)
  have hright : IsClosed {z : Fin 3 → ℝ | -z 0 ≤ z 2} :=
    isClosed_le ((continuous_apply 0).neg) (continuous_apply 2)
  simpa [percentileCoverageSet] using hleft.inter hright

theorem percentileCoverageVector_mem_set_iff
    {a : ℕ → ℝ} {θ : ℝ} {θhat qLower qUpper : ℕ → Ω → ℝ}
    {n : ℕ} {ω : Ω} (ha : 0 < a n) :
    percentileCoverageVector a θ θhat qLower qUpper n ω ∈ percentileCoverageSet ↔
      percentileCIEvent θ (qLower n ω) (qUpper n ω) := by
  change
    (a n * (qLower n ω - θhat n ω) ≤ -(a n * (θhat n ω - θ)) ∧
        -(a n * (θhat n ω - θ)) ≤ a n * (qUpper n ω - θhat n ω)) ↔
      qLower n ω ≤ θ ∧ θ ≤ qUpper n ω
  constructor
  · intro h
    constructor <;> nlinarith [ha, h.1, h.2]
  · intro h
    constructor <;> nlinarith [ha, h.1, h.2]

/-- The percentile-coverage limit vector belongs to the coverage set exactly
when the scalar limit error lies between the limiting percentile endpoints. -/
theorem percentileCoverageLimitVector_mem_set_iff
    {ξ : Ωlim → ℝ} {qLower qUpper : ℝ} {ω : Ωlim} :
    percentileCoverageLimitVector ξ qLower qUpper ω ∈ percentileCoverageSet ↔
      qLower ≤ -ξ ω ∧ -ξ ω ≤ qUpper := by
  change
    (qLower ≤ -ξ ω ∧ -ξ ω ≤ qUpper) ↔
      qLower ≤ -ξ ω ∧ -ξ ω ≤ qUpper
  rfl

/-- A scalar a.e.-measurable limit statistic yields an a.e.-measurable
percentile-coverage limit vector. -/
private theorem aemeasurable_percentileCoverageLimitVector
    {ξ : Ωlim → ℝ} (hξ : AEMeasurable ξ ν) (qLower qUpper : ℝ) :
    AEMeasurable (percentileCoverageLimitVector ξ qLower qUpper) ν := by
  refine aemeasurable_pi_lambda _ ?_
  intro i
  by_cases hi0 : i = 0
  · subst i
    simpa [percentileCoverageLimitVector] using hξ
  by_cases hi1 : i = 1
  · subst i
    simp [percentileCoverageLimitVector]
  · simp [percentileCoverageLimitVector, hi0, hi1]

/-- The vector-law probability of the percentile-coverage limit set is the
scalar event probability `P[qL <= -ξ <= qU]`. -/
theorem percentileCoverageLimit_measure_set_eq
    {ξ : Ωlim → ℝ} {qLower qUpper : ℝ}
    (hξ : AEMeasurable ξ ν) :
    (ν.map (percentileCoverageLimitVector ξ qLower qUpper))
        percentileCoverageSet =
      ν {ω | qLower ≤ -ξ ω ∧ -ξ ω ≤ qUpper} := by
  rw [Measure.map_apply_of_aemeasurable
    (aemeasurable_percentileCoverageLimitVector (ν := ν) hξ qLower qUpper)
    isClosed_percentileCoverageSet.measurableSet]
  apply congrArg ν
  ext ω
  exact percentileCoverageLimitVector_mem_set_iff

/-- The frontier of the percentile-coverage set is contained in the union of
the two binding endpoint hyperplanes. -/
theorem frontier_percentileCoverageSet_subset :
    frontier percentileCoverageSet ⊆
      {z : Fin 3 → ℝ | z 1 = -z 0} ∪
        {z : Fin 3 → ℝ | -z 0 = z 2} := by
  let lowerSet : Set (Fin 3 → ℝ) := {z | z 1 ≤ -z 0}
  let upperSet : Set (Fin 3 → ℝ) := {z | -z 0 ≤ z 2}
  have hfront :
      frontier percentileCoverageSet ⊆
        frontier lowerSet ∩ closure upperSet ∪
          closure lowerSet ∩ frontier upperSet := by
    simpa [percentileCoverageSet, lowerSet, upperSet] using
      frontier_inter_subset lowerSet upperSet
  intro z hz
  rcases hfront hz with ⟨hzlower, _⟩ | ⟨_, hzupper⟩
  · exact Or.inl
      (frontier_le_subset_eq (continuous_apply 1) ((continuous_apply 0).neg) hzlower)
  · exact Or.inr
      (frontier_le_subset_eq ((continuous_apply 0).neg) (continuous_apply 2) hzupper)

/-- Scalar endpoint-boundary null mass implies the vector-law null-frontier
premise for the percentile-coverage set. -/
theorem percentileCoverage_frontier_null_of_boundary_null
    {ξ : Ωlim → ℝ} {qLower qUpper : ℝ}
    (hξ : AEMeasurable ξ ν)
    (hleft : ν {ω | qLower = -ξ ω} = 0)
    (hright : ν {ω | -ξ ω = qUpper} = 0) :
    (ν.map (percentileCoverageLimitVector ξ qLower qUpper))
      (frontier percentileCoverageSet) = 0 := by
  let boundary : Set (Fin 3 → ℝ) :=
    {z | z 1 = -z 0} ∪ {z | -z 0 = z 2}
  have hboundary_meas : MeasurableSet boundary := by
    exact
      ((isClosed_eq (continuous_apply 1) ((continuous_apply 0).neg)).measurableSet).union
        ((isClosed_eq ((continuous_apply 0).neg) (continuous_apply 2)).measurableSet)
  have hboundary_zero :
      (ν.map (percentileCoverageLimitVector ξ qLower qUpper)) boundary = 0 := by
    rw [Measure.map_apply_of_aemeasurable
      (aemeasurable_percentileCoverageLimitVector (ν := ν) hξ qLower qUpper)
      hboundary_meas]
    have hpre :
        (percentileCoverageLimitVector ξ qLower qUpper) ⁻¹' boundary =
          {ω | qLower = -ξ ω} ∪ {ω | -ξ ω = qUpper} := by
      ext ω
      simp [boundary, percentileCoverageLimitVector]
    rw [hpre]
    exact measure_union_null hleft hright
  exact measure_mono_null (μ := ν.map (percentileCoverageLimitVector ξ qLower qUpper))
    frontier_percentileCoverageSet_subset hboundary_zero

/-- The scalar percentile-coverage event can be read from the law of the
limit statistic as the interval `[-qU, -qL]`. -/
theorem percentileCoverage_scalar_event_eq_law
    {ξ : Ωlim → ℝ} {η : Measure ℝ} (hξ : HasLaw ξ η ν)
    (qLower qUpper : ℝ) :
    ν {ω | qLower ≤ -ξ ω ∧ -ξ ω ≤ qUpper} =
      η (Set.Icc (-qUpper) (-qLower)) := by
  have hpre :
      {ω | qLower ≤ -ξ ω ∧ -ξ ω ≤ qUpper} =
        ξ ⁻¹' Set.Icc (-qUpper) (-qLower) := by
    ext ω
    constructor
    · intro h
      exact ⟨by linarith [h.2], by linarith [h.1]⟩
    · intro h
      exact ⟨by linarith [h.2], by linarith [h.1]⟩
  rw [hpre]
  exact HasLaw.preimage_eq hξ measurableSet_Icc

/-- If the scalar limit law has no atoms, then the percentile-coverage
frontier has zero mass under the limit vector law. -/
theorem percentileCoverage_frontier_null_of_hasLaw_noAtoms
    {ξ : Ωlim → ℝ} {η : Measure ℝ} [NoAtoms η] (hξ : HasLaw ξ η ν)
    (qLower qUpper : ℝ) :
    (ν.map (percentileCoverageLimitVector ξ qLower qUpper))
      (frontier percentileCoverageSet) = 0 := by
  refine percentileCoverage_frontier_null_of_boundary_null
    (ν := ν) (qLower := qLower) (qUpper := qUpper)
    hξ.aemeasurable ?_ ?_
  · have hpre :
        {ω | qLower = -ξ ω} = ξ ⁻¹' ({-qLower} : Set ℝ) := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_singleton_iff]
      constructor <;> intro h <;> linarith
    rw [hpre, HasLaw.preimage_eq hξ (measurableSet_singleton (-qLower))]
    exact measure_singleton (-qLower)
  · have hpre :
        {ω | -ξ ω = qUpper} = ξ ⁻¹' ({-qUpper} : Set ℝ) := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_singleton_iff]
      constructor <;> intro h <;> linarith
    rw [hpre, HasLaw.preimage_eq hξ (measurableSet_singleton (-qUpper))]
    exact measure_singleton (-qUpper)

/-- Hansen Theorem 10.13, percentile-interval coverage bridge.

If the scaled estimator error and the scaled bootstrap percentile endpoints
jointly converge to `(ξ, qL, qU)`, and the limiting coverage boundary has zero
probability, then the percentile interval coverage converges to
`P[qL <= -ξ <= qU]`.  Hansen's symmetric continuous-limit conclusion
`1 - α` is obtained by instantiating this bridge with the appropriate
bootstrap quantile limits and symmetry identity for the limit law. -/
theorem chapter10_percentileCI_coverage_tendsto_of_joint_quantile_limit
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {a : ℕ → ℝ} (ha : ∀ n, 0 < a n)
    {θ : ℝ} {θhat qLower qUpper : ℕ → Ω → ℝ}
    {ξ : Ωlim → ℝ} {qLowerLim qUpperLim : ℝ}
    (hjoint :
      TendstoInDistribution
        (percentileCoverageVector a θ θhat qLower qUpper)
        atTop
        (percentileCoverageLimitVector ξ qLowerLim qUpperLim)
        (fun _ => μ) ν)
    (hfrontier :
      (ν.map (percentileCoverageLimitVector ξ qLowerLim qUpperLim))
        (frontier percentileCoverageSet) = 0) :
    Tendsto
      (fun n => μ {ω | percentileCIEvent θ (qLower n ω) (qUpper n ω)})
      atTop
      (𝓝 ((ν.map (percentileCoverageLimitVector ξ qLowerLim qUpperLim))
        percentileCoverageSet)) := by
  have hset_meas : MeasurableSet percentileCoverageSet :=
    isClosed_percentileCoverageSet.measurableSet
  have hcoverage :=
    TendstoInDistribution.tendsto_measure_preimage_of_null_frontier
      (h := hjoint) hset_meas hfrontier
  have hseq_eq :
      (fun n =>
        μ {ω | percentileCoverageVector a θ θhat qLower qUpper n ω ∈
          percentileCoverageSet}) =
        fun n => μ {ω | percentileCIEvent θ (qLower n ω) (qUpper n ω)} := by
    funext n
    congr 1
    ext ω
    exact percentileCoverageVector_mem_set_iff (Ω := Ω) (ha n)
  simpa [hseq_eq] using hcoverage

/-- Calibrated percentile-interval coverage bridge. -/
theorem chapter10_percentileCI_coverage_tendsto
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {a : ℕ → ℝ} (ha : ∀ n, 0 < a n)
    {θ : ℝ} {θhat qLower qUpper : ℕ → Ω → ℝ}
    {ξ : Ωlim → ℝ} {qLowerLim qUpperLim : ℝ} {coverage : ℝ≥0∞}
    (hjoint :
      TendstoInDistribution
        (percentileCoverageVector a θ θhat qLower qUpper)
        atTop
        (percentileCoverageLimitVector ξ qLowerLim qUpperLim)
        (fun _ => μ) ν)
    (hfrontier :
      (ν.map (percentileCoverageLimitVector ξ qLowerLim qUpperLim))
        (frontier percentileCoverageSet) = 0)
    (hcoverage :
      (ν.map (percentileCoverageLimitVector ξ qLowerLim qUpperLim))
        percentileCoverageSet = coverage) :
    Tendsto
      (fun n => μ {ω | percentileCIEvent θ (qLower n ω) (qUpper n ω)})
      atTop (𝓝 coverage) := by
  simpa [hcoverage] using
    chapter10_percentileCI_coverage_tendsto_of_joint_quantile_limit
      (μ := μ) (ν := ν) (a := a) ha
      (θ := θ) (θhat := θhat) (qLower := qLower) (qUpper := qUpper)
      (ξ := ξ) (qLowerLim := qLowerLim) (qUpperLim := qUpperLim)
      hjoint hfrontier

/-- Calibrated percentile-interval coverage bridge with the limit coverage
stated as the scalar event probability `P[qL <= -ξ <= qU]`. -/
theorem chapter10_percentileCI_coverage_tendsto_of_scalar_limit_coverage
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {a : ℕ → ℝ} (ha : ∀ n, 0 < a n)
    {θ : ℝ} {θhat qLower qUpper : ℕ → Ω → ℝ}
    {ξ : Ωlim → ℝ} {qLowerLim qUpperLim : ℝ} {coverage : ℝ≥0∞}
    (hjoint :
      TendstoInDistribution
        (percentileCoverageVector a θ θhat qLower qUpper)
        atTop
        (percentileCoverageLimitVector ξ qLowerLim qUpperLim)
        (fun _ => μ) ν)
    (hfrontier :
      (ν.map (percentileCoverageLimitVector ξ qLowerLim qUpperLim))
        (frontier percentileCoverageSet) = 0)
    (hcoverage :
      ν {ω | qLowerLim ≤ -ξ ω ∧ -ξ ω ≤ qUpperLim} = coverage) :
    Tendsto
      (fun n => μ {ω | percentileCIEvent θ (qLower n ω) (qUpper n ω)})
      atTop (𝓝 coverage) := by
  have hcoverage_map :
      (ν.map (percentileCoverageLimitVector ξ qLowerLim qUpperLim))
        percentileCoverageSet = coverage := by
    rw [Measure.map_apply_of_aemeasurable hjoint.aemeasurable_limit
      isClosed_percentileCoverageSet.measurableSet]
    have hpre :
        {ω | percentileCoverageLimitVector ξ qLowerLim qUpperLim ω ∈
            percentileCoverageSet} =
          {ω | qLowerLim ≤ -ξ ω ∧ -ξ ω ≤ qUpperLim} := by
      ext ω
      exact percentileCoverageLimitVector_mem_set_iff
    simpa [hpre] using hcoverage
  exact
    chapter10_percentileCI_coverage_tendsto
      (μ := μ) (ν := ν) (a := a) ha
      (θ := θ) (θhat := θhat) (qLower := qLower) (qUpper := qUpper)
      (ξ := ξ) (qLowerLim := qLowerLim) (qUpperLim := qUpperLim)
      hjoint hfrontier hcoverage_map

/-- Calibrated percentile-interval coverage bridge with scalar endpoint
boundary-null and scalar coverage assumptions. -/
theorem chapter10_percentileCI_coverage_tendsto_of_scalar_limit
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {a : ℕ → ℝ} (ha : ∀ n, 0 < a n)
    {θ : ℝ} {θhat qLower qUpper : ℕ → Ω → ℝ}
    {ξ : Ωlim → ℝ} {qLowerLim qUpperLim : ℝ} {coverage : ℝ≥0∞}
    (hjoint :
      TendstoInDistribution
        (percentileCoverageVector a θ θhat qLower qUpper)
        atTop
        (percentileCoverageLimitVector ξ qLowerLim qUpperLim)
        (fun _ => μ) ν)
    (hξ : AEMeasurable ξ ν)
    (hleft : ν {ω | qLowerLim = -ξ ω} = 0)
    (hright : ν {ω | -ξ ω = qUpperLim} = 0)
    (hcoverage :
      ν {ω | qLowerLim ≤ -ξ ω ∧ -ξ ω ≤ qUpperLim} = coverage) :
    Tendsto
      (fun n => μ {ω | percentileCIEvent θ (qLower n ω) (qUpper n ω)})
      atTop (𝓝 coverage) := by
  exact
    chapter10_percentileCI_coverage_tendsto_of_scalar_limit_coverage
      (μ := μ) (ν := ν) (a := a) ha
      (θ := θ) (θhat := θhat) (qLower := qLower) (qUpper := qUpper)
      (ξ := ξ) (qLowerLim := qLowerLim) (qUpperLim := qUpperLim)
      hjoint
      (percentileCoverage_frontier_null_of_boundary_null
        (ν := ν) (qLower := qLowerLim) (qUpper := qUpperLim)
        hξ hleft hright)
      hcoverage

/-- Calibrated percentile-interval coverage bridge with calibration stated
under the scalar law of the limit statistic.  A non-atomic limit law supplies
the required null-frontier premise. -/
theorem chapter10_percentileCI_coverage_tendsto_of_limit_law
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {η : Measure ℝ} [NoAtoms η]
    {a : ℕ → ℝ} (ha : ∀ n, 0 < a n)
    {θ : ℝ} {θhat qLower qUpper : ℕ → Ω → ℝ}
    {ξ : Ωlim → ℝ} {qLowerLim qUpperLim : ℝ} {coverage : ℝ≥0∞}
    (hjoint :
      TendstoInDistribution
        (percentileCoverageVector a θ θhat qLower qUpper)
        atTop
        (percentileCoverageLimitVector ξ qLowerLim qUpperLim)
        (fun _ => μ) ν)
    (hξ : HasLaw ξ η ν)
    (hcoverage : η (Set.Icc (-qUpperLim) (-qLowerLim)) = coverage) :
    Tendsto
      (fun n => μ {ω | percentileCIEvent θ (qLower n ω) (qUpper n ω)})
      atTop (𝓝 coverage) := by
  refine chapter10_percentileCI_coverage_tendsto_of_scalar_limit
    (μ := μ) (ν := ν) (a := a) ha
    (θ := θ) (θhat := θhat) (qLower := qLower) (qUpper := qUpper)
    (ξ := ξ) (qLowerLim := qLowerLim) (qUpperLim := qUpperLim)
    hjoint hξ.aemeasurable ?_ ?_ ?_
  · have hpre :
        {ω | qLowerLim = -ξ ω} = ξ ⁻¹' ({-qLowerLim} : Set ℝ) := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_singleton_iff]
      constructor <;> intro h <;> linarith
    rw [hpre, HasLaw.preimage_eq hξ (measurableSet_singleton (-qLowerLim))]
    exact measure_singleton (-qLowerLim)
  · have hpre :
        {ω | -ξ ω = qUpperLim} = ξ ⁻¹' ({-qUpperLim} : Set ℝ) := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_singleton_iff]
      constructor <;> intro h <;> linarith
    rw [hpre, HasLaw.preimage_eq hξ (measurableSet_singleton (-qUpperLim))]
    exact measure_singleton (-qUpperLim)
  · rw [percentileCoverage_scalar_event_eq_law hξ qLowerLim qUpperLim]
    exact hcoverage

/-- CDF-calibrated percentile-interval coverage bridge.

For a non-atomic scalar limit law, the limiting percentile coverage
`η[-qU,-qL]` can be supplied as the CDF increment
`F(-qL) - F(-qU)`. -/
theorem chapter10_percentileCI_coverage_tendsto_of_limit_law_cdf
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {η : Measure ℝ} [IsProbabilityMeasure η] [NoAtoms η]
    {a : ℕ → ℝ} (ha : ∀ n, 0 < a n)
    {θ : ℝ} {θhat qLower qUpper : ℕ → Ω → ℝ}
    {ξ : Ωlim → ℝ} {qLowerLim qUpperLim coverage : ℝ}
    (hjoint :
      TendstoInDistribution
        (percentileCoverageVector a θ θhat qLower qUpper)
        atTop
        (percentileCoverageLimitVector ξ qLowerLim qUpperLim)
        (fun _ => μ) ν)
    (hξ : HasLaw ξ η ν)
    (hquantiles : qLowerLim ≤ qUpperLim)
    (hcoverage : cdf η (-qLowerLim) - cdf η (-qUpperLim) = coverage) :
    Tendsto
      (fun n => μ {ω | percentileCIEvent θ (qLower n ω) (qUpper n ω)})
      atTop (𝓝 (ENNReal.ofReal coverage)) := by
  refine
    chapter10_percentileCI_coverage_tendsto_of_limit_law
      (μ := μ) (ν := ν) (η := η) (a := a) ha
      (θ := θ) (θhat := θhat) (qLower := qLower) (qUpper := qUpper)
      (ξ := ξ) (qLowerLim := qLowerLim) (qUpperLim := qUpperLim)
      (coverage := ENNReal.ofReal coverage) hjoint hξ ?_
  rw [measure_Icc_eq_ofReal_cdf_sub_of_noAtoms
    (ν := η) (a := -qUpperLim) (b := -qLowerLim)]
  · rw [hcoverage]
  · linarith

/-- Endpoint-CDF percentile-interval calibration with limiting coverage
`1 - α`.  The endpoint premises encode the limiting lower and upper
percentile masses. -/
theorem chapter10_percentileCI_coverage_tendsto_one_sub_alpha_of_limit_law_cdf
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {η : Measure ℝ} [IsProbabilityMeasure η] [NoAtoms η]
    {a : ℕ → ℝ} (ha : ∀ n, 0 < a n)
    {θ : ℝ} {θhat qLower qUpper : ℕ → Ω → ℝ}
    {ξ : Ωlim → ℝ} {qLowerLim qUpperLim α : ℝ}
    (hjoint :
      TendstoInDistribution
        (percentileCoverageVector a θ θhat qLower qUpper)
        atTop
        (percentileCoverageLimitVector ξ qLowerLim qUpperLim)
        (fun _ => μ) ν)
    (hξ : HasLaw ξ η ν)
    (hquantiles : qLowerLim ≤ qUpperLim)
    (hlower : cdf η (-qUpperLim) = α / 2)
    (hupper : cdf η (-qLowerLim) = 1 - α / 2) :
    Tendsto
      (fun n => μ {ω | percentileCIEvent θ (qLower n ω) (qUpper n ω)})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) := by
  refine
    chapter10_percentileCI_coverage_tendsto_of_limit_law_cdf
      (μ := μ) (ν := ν) (η := η) (a := a) ha
      (θ := θ) (θhat := θhat) (qLower := qLower) (qUpper := qUpper)
      (ξ := ξ) (qLowerLim := qLowerLim) (qUpperLim := qUpperLim)
      (coverage := 1 - α) hjoint hξ hquantiles ?_
  rw [hlower, hupper]
  ring

/-- Componentwise endpoint-CDF percentile-interval calibration with limiting
coverage `1 - α`.

This is the Theorem 10.13 coverage bridge stated directly from scalar
estimator-error convergence and bootstrap endpoint convergence in probability. -/
theorem chapter10_percentileCI_coverage_tendsto_one_sub_alpha_of_components_law_cdf
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {η : Measure ℝ} [IsProbabilityMeasure η] [NoAtoms η]
    {a : ℕ → ℝ} (ha : ∀ n, 0 < a n)
    {θ : ℝ} {θhat qLower qUpper : ℕ → Ω → ℝ}
    {ξ : Ωlim → ℝ} {qLowerLim qUpperLim α : ℝ}
    (hstat :
      TendstoInDistribution
        (fun n ω => a n * (θhat n ω - θ))
        atTop ξ (fun _ => μ) ν)
    (hlower :
      TendstoInMeasure μ
        (fun n ω => a n * (qLower n ω - θhat n ω))
        atTop (fun _ => qLowerLim))
    (hupper :
      TendstoInMeasure μ
        (fun n ω => a n * (qUpper n ω - θhat n ω))
        atTop (fun _ => qUpperLim))
    (hlower_meas :
      ∀ n, AEMeasurable (fun ω => a n * (qLower n ω - θhat n ω)) μ)
    (hupper_meas :
      ∀ n, AEMeasurable (fun ω => a n * (qUpper n ω - θhat n ω)) μ)
    (hξ : HasLaw ξ η ν)
    (hquantiles : qLowerLim ≤ qUpperLim)
    (hcdfLower : cdf η (-qUpperLim) = α / 2)
    (hcdfUpper : cdf η (-qLowerLim) = 1 - α / 2) :
    Tendsto
      (fun n => μ {ω | percentileCIEvent θ (qLower n ω) (qUpper n ω)})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) := by
  exact
    chapter10_percentileCI_coverage_tendsto_one_sub_alpha_of_limit_law_cdf
      (μ := μ) (ν := ν) (η := η) (a := a) ha
      (θ := θ) (θhat := θhat) (qLower := qLower) (qUpper := qUpper)
      (ξ := ξ) (qLowerLim := qLowerLim) (qUpperLim := qUpperLim)
      (percentileCoverageVector_tendstoInDistribution_of_components
        (μ := μ) (ν := ν) (a := a) (θ := θ)
        (θhat := θhat) (qLower := qLower) (qUpper := qUpper)
        (ξ := ξ) (qLowerLim := qLowerLim) (qUpperLim := qUpperLim)
        hstat hlower hupper hlower_meas hupper_meas)
      hξ hquantiles hcdfLower hcdfUpper

/-- Symmetric endpoint-CDF percentile-interval calibration.

This is the Hansen Theorem 10.13 specialization where the limiting bootstrap
percentile endpoints are `-q` and `q`, and the scalar limit law has endpoint
CDF masses `α / 2` and `1 - α / 2`. -/
theorem chapter10_percentileCI_coverage_tendsto_one_sub_alpha_of_components_symmetric_cdf
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {η : Measure ℝ} [IsProbabilityMeasure η] [NoAtoms η]
    {a : ℕ → ℝ} (ha : ∀ n, 0 < a n)
    {θ : ℝ} {θhat qLower qUpper : ℕ → Ω → ℝ}
    {ξ : Ωlim → ℝ} {q α : ℝ}
    (hstat :
      TendstoInDistribution
        (fun n ω => a n * (θhat n ω - θ))
        atTop ξ (fun _ => μ) ν)
    (hlower :
      TendstoInMeasure μ
        (fun n ω => a n * (qLower n ω - θhat n ω))
        atTop (fun _ => -q))
    (hupper :
      TendstoInMeasure μ
        (fun n ω => a n * (qUpper n ω - θhat n ω))
        atTop (fun _ => q))
    (hlower_meas :
      ∀ n, AEMeasurable (fun ω => a n * (qLower n ω - θhat n ω)) μ)
    (hupper_meas :
      ∀ n, AEMeasurable (fun ω => a n * (qUpper n ω - θhat n ω)) μ)
    (hξ : HasLaw ξ η ν)
    (hq_nonneg : 0 ≤ q)
    (hcdfLower : cdf η (-q) = α / 2)
    (hcdfUpper : cdf η q = 1 - α / 2) :
    Tendsto
      (fun n => μ {ω | percentileCIEvent θ (qLower n ω) (qUpper n ω)})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) := by
  exact
    chapter10_percentileCI_coverage_tendsto_one_sub_alpha_of_components_law_cdf
      (μ := μ) (ν := ν) (η := η) (a := a) ha
      (θ := θ) (θhat := θhat) (qLower := qLower) (qUpper := qUpper)
      (ξ := ξ) (qLowerLim := -q) (qUpperLim := q) (α := α)
      hstat hlower hupper hlower_meas hupper_meas hξ
      (by linarith) hcdfLower (by simpa using hcdfUpper)

private theorem mul_add_div_sub_eq {a θ q : ℝ} (ha : a ≠ 0) :
    a * ((θ + q / a) - θ) = q := by
  field_simp [ha]
  ring

/-- Hansen equation (10.20), algebraic endpoint form.

If a bootstrap offset `Qstar` converges to the limiting quantile `q`, then the
original-scale endpoint `θhat + Qstar / a` has the displayed scaled endpoint
convergence `aₙ(q*ₙ - θhatₙ) →p q`. -/
theorem chapter10_percentileEndpoint_scaled_sub_tendstoInMeasure
    {a : ℕ → ℝ} (ha : ∀ n, 0 < a n)
    {θhat Qstar : ℕ → Ω → ℝ} {q : ℝ}
    (hQstar : TendstoInMeasure μ Qstar atTop (fun _ => q)) :
    TendstoInMeasure μ
      (fun n ω => a n * ((θhat n ω + Qstar n ω / a n) - θhat n ω))
      atTop (fun _ => q) := by
  refine TendstoInMeasure.congr
    (f := Qstar)
    (f' := fun n ω => a n * ((θhat n ω + Qstar n ω / a n) - θhat n ω))
    (g := fun _ : Ω => q)
    (g' := fun _ : Ω => q)
    (fun n => ?_) EventuallyEq.rfl hQstar
  exact ae_of_all μ fun ω =>
    (mul_add_div_sub_eq
      (a := a n) (θ := θhat n ω) (q := Qstar n ω)
      (ne_of_gt (ha n))).symm

/-- Hansen equation (10.20), lower-generalized-inverse route.

Pointwise conditional-CDF convergence identifies the bootstrap lower quantile;
the original-scale endpoint then satisfies
`aₙ(q*ₙ - θhatₙ) →p q`. -/
theorem
chapter10_percentileEndpoint_scaled_sub_tendstoInMeasure_of_lowerQuantile
    {Pstar : ℕ → Ω → Measure Ωs} {Tstar : ℕ → Ω → Ωs → ℝ}
    {a : ℕ → ℝ} (ha : ∀ n, 0 < a n)
    {θhat : ℕ → Ω → ℝ} {G : ℝ → ℝ} {p q : ℝ}
    (hmono :
      ∀ n ω, Monotone (fun x => bootstrapScalarCDF Pstar Tstar x n ω))
    (hne :
      ∀ n ω,
        ({x : ℝ | p ≤ bootstrapScalarCDF Pstar Tstar x n ω} : Set ℝ).Nonempty)
    (hbdd :
      ∀ n ω, BddBelow {x : ℝ | p ≤ bootstrapScalarCDF Pstar Tstar x n ω})
    (hlocal :
      ∀ n ω x, bootstrapScalarCDF Pstar Tstar x n ω < p →
        ∃ δ : ℝ, 0 < δ ∧ bootstrapScalarCDF Pstar Tstar (x + δ) n ω < p)
    (hstrict : StrictMono G)
    (hq : G q = p)
    (hG :
      ∀ x : ℝ,
        TendstoInMeasure μ
          (fun n ω => bootstrapScalarCDF Pstar Tstar x n ω)
          atTop (fun _ => G x)) :
    TendstoInMeasure μ
      (fun n ω =>
        a n * ((θhat n ω +
          bootstrapScalarLowerQuantile Pstar Tstar p n ω / a n) -
          θhat n ω))
      atTop (fun _ => q) :=
  chapter10_percentileEndpoint_scaled_sub_tendstoInMeasure
    (μ := μ) (a := a) ha (θhat := θhat)
    (Qstar := bootstrapScalarLowerQuantile Pstar Tstar p) (q := q)
    (bootstrapScalarLowerQuantile_tendsto_of_strictMono_cdf
      (μ := μ) (Pstar := Pstar) (Zstar := Tstar) (G := G)
      (p := p) (q := q) hmono hne hbdd hlocal hstrict hq hG)

/-- Symmetric percentile-interval coverage from abstract scaled endpoint
quantiles.

This is the reusable endpoint-conversion bridge behind the lower-quantile
routes: if the scaled lower and upper endpoint deviations converge to `-q` and
`q`, then adding them to `θhat` on the original scale gives the percentile
coverage conclusion. -/
theorem
chapter10_percentileCI_coverage_tendsto_one_sub_alpha_of_scaled_quantiles
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {η : Measure ℝ} [IsProbabilityMeasure η] [NoAtoms η]
    {a : ℕ → ℝ} (ha : ∀ n, 0 < a n)
    {θ : ℝ} {θhat Qlower Qupper : ℕ → Ω → ℝ}
    {ξ : Ωlim → ℝ} {q α : ℝ}
    (hstat :
      TendstoInDistribution
        (fun n ω => a n * (θhat n ω - θ))
        atTop ξ (fun _ => μ) ν)
    (hQlower : TendstoInMeasure μ Qlower atTop (fun _ => -q))
    (hQupper : TendstoInMeasure μ Qupper atTop (fun _ => q))
    (hQlower_meas : ∀ n, AEMeasurable (Qlower n) μ)
    (hQupper_meas : ∀ n, AEMeasurable (Qupper n) μ)
    (hξ : HasLaw ξ η ν)
    (hq_nonneg : 0 ≤ q)
    (hcdfLower : cdf η (-q) = α / 2)
    (hcdfUpper : cdf η q = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | percentileCIEvent θ
          (θhat n ω + Qlower n ω / a n)
          (θhat n ω + Qupper n ω / a n)})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) := by
  let qLowerEndpoint : ℕ → Ω → ℝ :=
    fun n ω => θhat n ω + Qlower n ω / a n
  let qUpperEndpoint : ℕ → Ω → ℝ :=
    fun n ω => θhat n ω + Qupper n ω / a n
  have hlower :
      TendstoInMeasure μ
        (fun n ω => a n * (qLowerEndpoint n ω - θhat n ω))
        atTop (fun _ => -q) := by
    refine TendstoInMeasure.congr
      (f := Qlower)
      (f' := fun n ω => a n * (qLowerEndpoint n ω - θhat n ω))
      (g := fun _ : Ω => -q)
      (g' := fun _ : Ω => -q)
      (fun n => ?_) EventuallyEq.rfl hQlower
    exact ae_of_all μ fun ω =>
      (mul_add_div_sub_eq
        (a := a n) (θ := θhat n ω) (q := Qlower n ω)
        (ne_of_gt (ha n))).symm
  have hupper :
      TendstoInMeasure μ
        (fun n ω => a n * (qUpperEndpoint n ω - θhat n ω))
        atTop (fun _ => q) := by
    refine TendstoInMeasure.congr
      (f := Qupper)
      (f' := fun n ω => a n * (qUpperEndpoint n ω - θhat n ω))
      (g := fun _ : Ω => q)
      (g' := fun _ : Ω => q)
      (fun n => ?_) EventuallyEq.rfl hQupper
    exact ae_of_all μ fun ω =>
      (mul_add_div_sub_eq
        (a := a n) (θ := θhat n ω) (q := Qupper n ω)
        (ne_of_gt (ha n))).symm
  have hlower_scaled_meas :
      ∀ n,
        AEMeasurable
          (fun ω => a n * (qLowerEndpoint n ω - θhat n ω)) μ := by
    intro n
    exact (hQlower_meas n).congr
      (ae_of_all μ fun ω =>
        (mul_add_div_sub_eq
          (a := a n) (θ := θhat n ω) (q := Qlower n ω)
          (ne_of_gt (ha n))).symm)
  have hupper_scaled_meas :
      ∀ n,
        AEMeasurable
          (fun ω => a n * (qUpperEndpoint n ω - θhat n ω)) μ := by
    intro n
    exact (hQupper_meas n).congr
      (ae_of_all μ fun ω =>
        (mul_add_div_sub_eq
          (a := a n) (θ := θhat n ω) (q := Qupper n ω)
          (ne_of_gt (ha n))).symm)
  have hcoverage :=
    chapter10_percentileCI_coverage_tendsto_one_sub_alpha_of_components_symmetric_cdf
      (μ := μ) (ν := ν) (η := η) (a := a) ha
      (θ := θ) (θhat := θhat)
      (qLower := qLowerEndpoint) (qUpper := qUpperEndpoint)
      (ξ := ξ) (q := q) (α := α)
      hstat hlower hupper hlower_scaled_meas hupper_scaled_meas hξ
      hq_nonneg hcdfLower hcdfUpper
  simpa [qLowerEndpoint, qUpperEndpoint] using hcoverage

/-- Symmetric percentile-interval coverage from bootstrap lower quantiles,
using local limit-CDF bracketing.

This is the non-strict-CDF version of the lower-generalized-inverse endpoint
route for Hansen Theorem 10.13.  It identifies the limiting lower and upper
bootstrap quantiles by local CDF bracketing at `-q` and `q`, then converts the
scaled bootstrap endpoints back to the original parameter scale. -/
theorem
chapter10_percentileCI_coverage_tendsto_one_sub_alpha_of_bootstrap_lowerQuantiles_brackets
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {η : Measure ℝ} [IsProbabilityMeasure η] [NoAtoms η]
    {Pstar : ℕ → Ω → Measure Ωs} {Tstar : ℕ → Ω → Ωs → ℝ}
    {a : ℕ → ℝ} (ha : ∀ n, 0 < a n)
    {θ : ℝ} {θhat : ℕ → Ω → ℝ}
    {ξ : Ωlim → ℝ} {q α : ℝ}
    (hstat :
      TendstoInDistribution
        (fun n ω => a n * (θhat n ω - θ))
        atTop ξ (fun _ => μ) ν)
    (hmono :
      ∀ n ω, Monotone (fun x => bootstrapScalarCDF Pstar Tstar x n ω))
    (hneLower :
      ∀ n ω,
        ({x : ℝ | α / 2 ≤ bootstrapScalarCDF Pstar Tstar x n ω} :
          Set ℝ).Nonempty)
    (hbddLower :
      ∀ n ω, BddBelow
        {x : ℝ | α / 2 ≤ bootstrapScalarCDF Pstar Tstar x n ω})
    (hlocalLower :
      ∀ n ω x, bootstrapScalarCDF Pstar Tstar x n ω < α / 2 →
        ∃ δ : ℝ, 0 < δ ∧ bootstrapScalarCDF Pstar Tstar (x + δ) n ω < α / 2)
    (hneUpper :
      ∀ n ω,
        ({x : ℝ | 1 - α / 2 ≤ bootstrapScalarCDF Pstar Tstar x n ω} :
          Set ℝ).Nonempty)
    (hbddUpper :
      ∀ n ω, BddBelow
        {x : ℝ | 1 - α / 2 ≤ bootstrapScalarCDF Pstar Tstar x n ω})
    (hlocalUpper :
      ∀ n ω x, bootstrapScalarCDF Pstar Tstar x n ω < 1 - α / 2 →
        ∃ δ : ℝ, 0 < δ ∧ bootstrapScalarCDF Pstar Tstar (x + δ) n ω <
          1 - α / 2)
    (hleftLower : ∀ ε : ℝ, 0 < ε → cdf η (-q - ε) < α / 2)
    (hrightLower : ∀ ε : ℝ, 0 < ε → α / 2 < cdf η (-q + ε))
    (hleftUpper : ∀ ε : ℝ, 0 < ε → cdf η (q - ε) < 1 - α / 2)
    (hrightUpper : ∀ ε : ℝ, 0 < ε → 1 - α / 2 < cdf η (q + ε))
    (hcdf :
      ∀ x : ℝ,
        TendstoInMeasure μ
          (fun n ω => bootstrapScalarCDF Pstar Tstar x n ω)
          atTop (fun _ => cdf η x))
    (hlower_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantile Pstar Tstar (α / 2) n) μ)
    (hupper_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantile Pstar Tstar (1 - α / 2) n) μ)
    (hξ : HasLaw ξ η ν)
    (hq_nonneg : 0 ≤ q)
    (hcdfLower : cdf η (-q) = α / 2)
    (hcdfUpper : cdf η q = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | percentileCIEvent θ
          (θhat n ω +
            bootstrapScalarLowerQuantile Pstar Tstar (α / 2) n ω / a n)
          (θhat n ω +
            bootstrapScalarLowerQuantile Pstar Tstar (1 - α / 2) n ω / a n)})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) := by
  let Qlower : ℕ → Ω → ℝ :=
    bootstrapScalarLowerQuantile Pstar Tstar (α / 2)
  let Qupper : ℕ → Ω → ℝ :=
    bootstrapScalarLowerQuantile Pstar Tstar (1 - α / 2)
  let qLowerEndpoint : ℕ → Ω → ℝ :=
    fun n ω => θhat n ω + Qlower n ω / a n
  let qUpperEndpoint : ℕ → Ω → ℝ :=
    fun n ω => θhat n ω + Qupper n ω / a n
  have hQlower :
      TendstoInMeasure μ Qlower atTop (fun _ => -q) :=
    bootstrapScalarLowerQuantile_tendsto_of_cdf_brackets
      (μ := μ) (Pstar := Pstar) (Zstar := Tstar)
      (G := fun x => cdf η x) (p := α / 2) (q := -q)
      hmono hneLower hbddLower hlocalLower hleftLower hrightLower hcdf
  have hQupper :
      TendstoInMeasure μ Qupper atTop (fun _ => q) :=
    bootstrapScalarLowerQuantile_tendsto_of_cdf_brackets
      (μ := μ) (Pstar := Pstar) (Zstar := Tstar)
      (G := fun x => cdf η x) (p := 1 - α / 2) (q := q)
      hmono hneUpper hbddUpper hlocalUpper hleftUpper hrightUpper hcdf
  have hlower :
      TendstoInMeasure μ
        (fun n ω => a n * (qLowerEndpoint n ω - θhat n ω))
        atTop (fun _ => -q) := by
    refine TendstoInMeasure.congr
      (f := Qlower)
      (f' := fun n ω => a n * (qLowerEndpoint n ω - θhat n ω))
      (g := fun _ : Ω => -q)
      (g' := fun _ : Ω => -q)
      (fun n => ?_) EventuallyEq.rfl hQlower
    refine ae_of_all μ fun ω => ?_
    exact (mul_add_div_sub_eq
      (a := a n) (θ := θhat n ω) (q := Qlower n ω)
      (ne_of_gt (ha n))).symm
  have hupper :
      TendstoInMeasure μ
        (fun n ω => a n * (qUpperEndpoint n ω - θhat n ω))
        atTop (fun _ => q) := by
    refine TendstoInMeasure.congr
      (f := Qupper)
      (f' := fun n ω => a n * (qUpperEndpoint n ω - θhat n ω))
      (g := fun _ : Ω => q)
      (g' := fun _ : Ω => q)
      (fun n => ?_) EventuallyEq.rfl hQupper
    refine ae_of_all μ fun ω => ?_
    exact (mul_add_div_sub_eq
      (a := a n) (θ := θhat n ω) (q := Qupper n ω)
      (ne_of_gt (ha n))).symm
  have hlower_scaled_meas :
      ∀ n,
        AEMeasurable
          (fun ω => a n * (qLowerEndpoint n ω - θhat n ω)) μ := by
    intro n
    have hQlower_meas : AEMeasurable (Qlower n) μ := by
      simpa [Qlower] using hlower_meas n
    exact hQlower_meas.congr
      (ae_of_all μ fun ω =>
        (mul_add_div_sub_eq
          (a := a n) (θ := θhat n ω) (q := Qlower n ω)
          (ne_of_gt (ha n))).symm)
  have hupper_scaled_meas :
      ∀ n,
        AEMeasurable
          (fun ω => a n * (qUpperEndpoint n ω - θhat n ω)) μ := by
    intro n
    have hQupper_meas : AEMeasurable (Qupper n) μ := by
      simpa [Qupper] using hupper_meas n
    exact hQupper_meas.congr
      (ae_of_all μ fun ω =>
        (mul_add_div_sub_eq
          (a := a n) (θ := θhat n ω) (q := Qupper n ω)
          (ne_of_gt (ha n))).symm)
  exact
    chapter10_percentileCI_coverage_tendsto_one_sub_alpha_of_components_symmetric_cdf
      (μ := μ) (ν := ν) (η := η) (a := a) ha
      (θ := θ) (θhat := θhat) (qLower := qLowerEndpoint)
      (qUpper := qUpperEndpoint) (ξ := ξ) (q := q) (α := α)
      hstat hlower hupper hlower_scaled_meas hupper_scaled_meas hξ
      hq_nonneg hcdfLower hcdfUpper

/-- Symmetric percentile-interval coverage from bootstrap lower quantiles.

The bootstrap lower quantiles identify the scaled endpoint deviations
`aₙ(q* - θhatₙ)`.  Dividing by `aₙ` and adding `θhatₙ` puts the endpoints on
the original parameter scale, after which the symmetric percentile-coverage
wrapper applies. -/
theorem chapter10_percentileCI_coverage_tendsto_one_sub_alpha_of_bootstrap_lowerQuantiles
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {η : Measure ℝ} [IsProbabilityMeasure η] [NoAtoms η]
    {Pstar : ℕ → Ω → Measure Ωs} {Tstar : ℕ → Ω → Ωs → ℝ}
    {a : ℕ → ℝ} (ha : ∀ n, 0 < a n)
    {θ : ℝ} {θhat : ℕ → Ω → ℝ}
    {ξ : Ωlim → ℝ} {q α : ℝ}
    (hstat :
      TendstoInDistribution
        (fun n ω => a n * (θhat n ω - θ))
        atTop ξ (fun _ => μ) ν)
    (hmono :
      ∀ n ω, Monotone (fun x => bootstrapScalarCDF Pstar Tstar x n ω))
    (hneLower :
      ∀ n ω,
        ({x : ℝ | α / 2 ≤ bootstrapScalarCDF Pstar Tstar x n ω} :
          Set ℝ).Nonempty)
    (hbddLower :
      ∀ n ω, BddBelow
        {x : ℝ | α / 2 ≤ bootstrapScalarCDF Pstar Tstar x n ω})
    (hlocalLower :
      ∀ n ω x, bootstrapScalarCDF Pstar Tstar x n ω < α / 2 →
        ∃ δ : ℝ, 0 < δ ∧ bootstrapScalarCDF Pstar Tstar (x + δ) n ω < α / 2)
    (hneUpper :
      ∀ n ω,
        ({x : ℝ | 1 - α / 2 ≤ bootstrapScalarCDF Pstar Tstar x n ω} :
          Set ℝ).Nonempty)
    (hbddUpper :
      ∀ n ω, BddBelow
        {x : ℝ | 1 - α / 2 ≤ bootstrapScalarCDF Pstar Tstar x n ω})
    (hlocalUpper :
      ∀ n ω x, bootstrapScalarCDF Pstar Tstar x n ω < 1 - α / 2 →
        ∃ δ : ℝ, 0 < δ ∧ bootstrapScalarCDF Pstar Tstar (x + δ) n ω <
          1 - α / 2)
    (hstrict : StrictMono (fun x => cdf η x))
    (hcdf :
      ∀ x : ℝ,
        TendstoInMeasure μ
          (fun n ω => bootstrapScalarCDF Pstar Tstar x n ω)
          atTop (fun _ => cdf η x))
    (hlower_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantile Pstar Tstar (α / 2) n) μ)
    (hupper_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantile Pstar Tstar (1 - α / 2) n) μ)
    (hξ : HasLaw ξ η ν)
    (hq_nonneg : 0 ≤ q)
    (hcdfLower : cdf η (-q) = α / 2)
    (hcdfUpper : cdf η q = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | percentileCIEvent θ
          (θhat n ω +
            bootstrapScalarLowerQuantile Pstar Tstar (α / 2) n ω / a n)
          (θhat n ω +
            bootstrapScalarLowerQuantile Pstar Tstar (1 - α / 2) n ω / a n)})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) := by
  let Qlower : ℕ → Ω → ℝ :=
    bootstrapScalarLowerQuantile Pstar Tstar (α / 2)
  let Qupper : ℕ → Ω → ℝ :=
    bootstrapScalarLowerQuantile Pstar Tstar (1 - α / 2)
  let qLowerEndpoint : ℕ → Ω → ℝ :=
    fun n ω => θhat n ω + Qlower n ω / a n
  let qUpperEndpoint : ℕ → Ω → ℝ :=
    fun n ω => θhat n ω + Qupper n ω / a n
  have hQlower :
      TendstoInMeasure μ Qlower atTop (fun _ => -q) :=
    bootstrapScalarLowerQuantile_tendsto_of_strictMono_cdf
      (μ := μ) (Pstar := Pstar) (Zstar := Tstar)
      (G := fun x => cdf η x) (p := α / 2) (q := -q)
      hmono hneLower hbddLower hlocalLower hstrict hcdfLower hcdf
  have hQupper :
      TendstoInMeasure μ Qupper atTop (fun _ => q) :=
    bootstrapScalarLowerQuantile_tendsto_of_strictMono_cdf
      (μ := μ) (Pstar := Pstar) (Zstar := Tstar)
      (G := fun x => cdf η x) (p := 1 - α / 2) (q := q)
      hmono hneUpper hbddUpper hlocalUpper hstrict hcdfUpper hcdf
  have hlower :
      TendstoInMeasure μ
        (fun n ω => a n * (qLowerEndpoint n ω - θhat n ω))
        atTop (fun _ => -q) := by
    refine TendstoInMeasure.congr
      (f := Qlower)
      (f' := fun n ω => a n * (qLowerEndpoint n ω - θhat n ω))
      (g := fun _ : Ω => -q)
      (g' := fun _ : Ω => -q)
      (fun n => ?_) EventuallyEq.rfl hQlower
    refine ae_of_all μ fun ω => ?_
    exact (mul_add_div_sub_eq
      (a := a n) (θ := θhat n ω) (q := Qlower n ω)
      (ne_of_gt (ha n))).symm
  have hupper :
      TendstoInMeasure μ
        (fun n ω => a n * (qUpperEndpoint n ω - θhat n ω))
        atTop (fun _ => q) := by
    refine TendstoInMeasure.congr
      (f := Qupper)
      (f' := fun n ω => a n * (qUpperEndpoint n ω - θhat n ω))
      (g := fun _ : Ω => q)
      (g' := fun _ : Ω => q)
      (fun n => ?_) EventuallyEq.rfl hQupper
    refine ae_of_all μ fun ω => ?_
    exact (mul_add_div_sub_eq
      (a := a n) (θ := θhat n ω) (q := Qupper n ω)
      (ne_of_gt (ha n))).symm
  have hlower_scaled_meas :
      ∀ n,
        AEMeasurable
          (fun ω => a n * (qLowerEndpoint n ω - θhat n ω)) μ := by
    intro n
    have hQlower_meas : AEMeasurable (Qlower n) μ := by
      simpa [Qlower] using hlower_meas n
    exact hQlower_meas.congr
      (ae_of_all μ fun ω =>
        (mul_add_div_sub_eq
          (a := a n) (θ := θhat n ω) (q := Qlower n ω)
          (ne_of_gt (ha n))).symm)
  have hupper_scaled_meas :
      ∀ n,
        AEMeasurable
          (fun ω => a n * (qUpperEndpoint n ω - θhat n ω)) μ := by
    intro n
    have hQupper_meas : AEMeasurable (Qupper n) μ := by
      simpa [Qupper] using hupper_meas n
    exact hQupper_meas.congr
      (ae_of_all μ fun ω =>
        (mul_add_div_sub_eq
          (a := a n) (θ := θhat n ω) (q := Qupper n ω)
          (ne_of_gt (ha n))).symm)
  have hcoverage :=
    chapter10_percentileCI_coverage_tendsto_one_sub_alpha_of_components_symmetric_cdf
      (μ := μ) (ν := ν) (η := η) (a := a) ha
      (θ := θ) (θhat := θhat)
      (qLower := qLowerEndpoint) (qUpper := qUpperEndpoint)
      (ξ := ξ) (q := q) (α := α)
      hstat hlower hupper hlower_scaled_meas hupper_scaled_meas hξ
      hq_nonneg hcdfLower hcdfUpper
  simpa [qLowerEndpoint, qUpperEndpoint, Qlower, Qupper] using hcoverage

/-- Symmetric percentile-interval coverage from bootstrap-distribution
convergence of the scaled bootstrap endpoint statistic.

This is the Definition 10.2-facing version of
`chapter10_percentileCI_coverage_tendsto_one_sub_alpha_of_bootstrap_lowerQuantiles`:
scalar-law CDF convergence is extracted from one-dimensional bootstrap
distribution convergence to the law `η`. -/
theorem
    chapter10_percentileCI_coverage_tendsto_one_sub_alpha_of_bootstrapDistribution_lowerQuantiles
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {η : Measure ℝ} [IsProbabilityMeasure η] [NoAtoms η]
    {Pstar : ℕ → Ω → Measure Ωs} {Tstar : ℕ → Ω → Ωs → ℝ}
    {a : ℕ → ℝ} (ha : ∀ n, 0 < a n)
    {θ : ℝ} {θhat : ℕ → Ω → ℝ}
    {ξ : Ωlim → ℝ} {q α : ℝ}
    (hstat :
      TendstoInDistribution
        (fun n ω => a n * (θhat n ω - θ))
        atTop ξ (fun _ => μ) ν)
    (hPstar : ∀ n ω, IsFiniteMeasure (Pstar n ω))
    (hneLower :
      ∀ n ω,
        ({x : ℝ | α / 2 ≤ bootstrapScalarCDF Pstar Tstar x n ω} :
          Set ℝ).Nonempty)
    (hbddLower :
      ∀ n ω, BddBelow
        {x : ℝ | α / 2 ≤ bootstrapScalarCDF Pstar Tstar x n ω})
    (hlocalLower :
      ∀ n ω x, bootstrapScalarCDF Pstar Tstar x n ω < α / 2 →
        ∃ δ : ℝ, 0 < δ ∧ bootstrapScalarCDF Pstar Tstar (x + δ) n ω < α / 2)
    (hneUpper :
      ∀ n ω,
        ({x : ℝ | 1 - α / 2 ≤ bootstrapScalarCDF Pstar Tstar x n ω} :
          Set ℝ).Nonempty)
    (hbddUpper :
      ∀ n ω, BddBelow
        {x : ℝ | 1 - α / 2 ≤ bootstrapScalarCDF Pstar Tstar x n ω})
    (hlocalUpper :
      ∀ n ω x, bootstrapScalarCDF Pstar Tstar x n ω < 1 - α / 2 →
        ∃ δ : ℝ, 0 < δ ∧ bootstrapScalarCDF Pstar Tstar (x + δ) n ω <
          1 - α / 2)
    (hstrict : StrictMono (fun x => cdf η x))
    (hTstar :
      TendstoInBootstrapDistribution μ Pstar
        (fun n ω ωs (_ : Unit) => Tstar n ω ωs) η
        (fun x (_ : Unit) => x))
    (hcont : ∀ x : ℝ, ContinuousAt (fun y => cdf η y) x)
    (hlower_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantile Pstar Tstar (α / 2) n) μ)
    (hupper_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantile Pstar Tstar (1 - α / 2) n) μ)
    (hξ : HasLaw ξ η ν)
    (hq_nonneg : 0 ≤ q)
    (hcdfLower : cdf η (-q) = α / 2)
    (hcdfUpper : cdf η q = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | percentileCIEvent θ
          (θhat n ω +
            bootstrapScalarLowerQuantile Pstar Tstar (α / 2) n ω / a n)
          (θhat n ω +
            bootstrapScalarLowerQuantile Pstar Tstar (1 - α / 2) n ω / a n)})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) := by
  have hmono :
      ∀ n ω, Monotone (fun x => bootstrapScalarCDF Pstar Tstar x n ω) := by
    intro n ω
    haveI : IsFiniteMeasure (Pstar n ω) := hPstar n ω
    exact bootstrapScalarCDF_mono (Pstar := Pstar) (Zstar := Tstar)
      (n := n) (ω := ω)
  have hcdf :
      ∀ x : ℝ,
        TendstoInMeasure μ
          (fun n ω => bootstrapScalarCDF Pstar Tstar x n ω)
          atTop (fun _ => cdf η x) :=
    fun x =>
      hTstar.bootstrapScalarCDF_tendsto_unit_id_cdf
        (Pstar := Pstar) (Zstar := Tstar) (x := x) (hcont x)
  exact
    chapter10_percentileCI_coverage_tendsto_one_sub_alpha_of_bootstrap_lowerQuantiles
      (μ := μ) (ν := ν) (η := η) (Pstar := Pstar) (Tstar := Tstar)
      (a := a) ha (θ := θ) (θhat := θhat) (ξ := ξ) (q := q)
      (α := α)
      hstat hmono hneLower hbddLower hlocalLower hneUpper hbddUpper
      hlocalUpper hstrict hcdf hlower_meas hupper_meas hξ hq_nonneg
      hcdfLower hcdfUpper

/-- Symmetric percentile-interval coverage from one-dimensional bootstrap
distribution convergence, using local limit-CDF bracketing at the lower and
upper quantiles.

This variant avoids a global strict-monotonicity premise on the scalar limit
CDF. -/
theorem
chapter10_percentileCI_coverage_tendsto_one_sub_alpha_of_bootstrapDistribution_brackets
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {η : Measure ℝ} [IsProbabilityMeasure η] [NoAtoms η]
    {Pstar : ℕ → Ω → Measure Ωs} {Tstar : ℕ → Ω → Ωs → ℝ}
    {a : ℕ → ℝ} (ha : ∀ n, 0 < a n)
    {θ : ℝ} {θhat : ℕ → Ω → ℝ}
    {ξ : Ωlim → ℝ} {q α : ℝ}
    (hstat :
      TendstoInDistribution
        (fun n ω => a n * (θhat n ω - θ))
        atTop ξ (fun _ => μ) ν)
    (hPstar : ∀ n ω, IsFiniteMeasure (Pstar n ω))
    (hneLower :
      ∀ n ω,
        ({x : ℝ | α / 2 ≤ bootstrapScalarCDF Pstar Tstar x n ω} :
          Set ℝ).Nonempty)
    (hbddLower :
      ∀ n ω, BddBelow
        {x : ℝ | α / 2 ≤ bootstrapScalarCDF Pstar Tstar x n ω})
    (hlocalLower :
      ∀ n ω x, bootstrapScalarCDF Pstar Tstar x n ω < α / 2 →
        ∃ δ : ℝ, 0 < δ ∧ bootstrapScalarCDF Pstar Tstar (x + δ) n ω < α / 2)
    (hneUpper :
      ∀ n ω,
        ({x : ℝ | 1 - α / 2 ≤ bootstrapScalarCDF Pstar Tstar x n ω} :
          Set ℝ).Nonempty)
    (hbddUpper :
      ∀ n ω, BddBelow
        {x : ℝ | 1 - α / 2 ≤ bootstrapScalarCDF Pstar Tstar x n ω})
    (hlocalUpper :
      ∀ n ω x, bootstrapScalarCDF Pstar Tstar x n ω < 1 - α / 2 →
        ∃ δ : ℝ, 0 < δ ∧ bootstrapScalarCDF Pstar Tstar (x + δ) n ω <
          1 - α / 2)
    (hleftLower : ∀ ε : ℝ, 0 < ε → cdf η (-q - ε) < α / 2)
    (hrightLower : ∀ ε : ℝ, 0 < ε → α / 2 < cdf η (-q + ε))
    (hleftUpper : ∀ ε : ℝ, 0 < ε → cdf η (q - ε) < 1 - α / 2)
    (hrightUpper : ∀ ε : ℝ, 0 < ε → 1 - α / 2 < cdf η (q + ε))
    (hTstar :
      TendstoInBootstrapDistribution μ Pstar
        (fun n ω ωs (_ : Unit) => Tstar n ω ωs) η
        (fun x (_ : Unit) => x))
    (hcont : ∀ x : ℝ, ContinuousAt (fun y => cdf η y) x)
    (hlower_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantile Pstar Tstar (α / 2) n) μ)
    (hupper_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantile Pstar Tstar (1 - α / 2) n) μ)
    (hξ : HasLaw ξ η ν)
    (hq_nonneg : 0 ≤ q)
    (hcdfLower : cdf η (-q) = α / 2)
    (hcdfUpper : cdf η q = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | percentileCIEvent θ
          (θhat n ω +
            bootstrapScalarLowerQuantile Pstar Tstar (α / 2) n ω / a n)
          (θhat n ω +
            bootstrapScalarLowerQuantile Pstar Tstar (1 - α / 2) n ω / a n)})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) := by
  have hmono :
      ∀ n ω, Monotone (fun x => bootstrapScalarCDF Pstar Tstar x n ω) := by
    intro n ω
    haveI : IsFiniteMeasure (Pstar n ω) := hPstar n ω
    exact bootstrapScalarCDF_mono (Pstar := Pstar) (Zstar := Tstar)
      (n := n) (ω := ω)
  have hcdf :
      ∀ x : ℝ,
        TendstoInMeasure μ
          (fun n ω => bootstrapScalarCDF Pstar Tstar x n ω)
          atTop (fun _ => cdf η x) :=
    fun x =>
      hTstar.bootstrapScalarCDF_tendsto_unit_id_cdf
        (Pstar := Pstar) (Zstar := Tstar) (x := x) (hcont x)
  exact
    chapter10_percentileCI_coverage_tendsto_one_sub_alpha_of_bootstrap_lowerQuantiles_brackets
      (μ := μ) (ν := ν) (η := η) (Pstar := Pstar) (Tstar := Tstar)
      (a := a) ha (θ := θ) (θhat := θhat) (ξ := ξ) (q := q)
      (α := α)
      hstat hmono hneLower hbddLower hlocalLower hneUpper hbddUpper
      hlocalUpper hleftLower hrightLower hleftUpper hrightUpper hcdf
      hlower_meas hupper_meas hξ hq_nonneg hcdfLower hcdfUpper

/-- Symmetric percentile-interval coverage from one-dimensional bootstrap
distribution convergence, with probability-CDF bracketing discharged at
levels `α / 2` and `1 - α / 2`.

For `0 < α < 1`, probability conditional bootstrap laws and pointwise
a.e.-measurability of the bootstrap endpoint statistic supply the lower
generalized-inverse nonemptiness, boundedness, monotonicity, and right-local
CDF bracketing premises. -/
theorem
chapter10_percentileCI_coverage_tendsto_one_sub_alpha_of_bootstrapDistribution_quantile_prob
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {η : Measure ℝ} [IsProbabilityMeasure η] [NoAtoms η]
    {Pstar : ℕ → Ω → Measure Ωs} {Tstar : ℕ → Ω → Ωs → ℝ}
    {a : ℕ → ℝ} (ha : ∀ n, 0 < a n)
    {θ : ℝ} {θhat : ℕ → Ω → ℝ}
    {ξ : Ωlim → ℝ} {q α : ℝ}
    (hstat :
      TendstoInDistribution
        (fun n ω => a n * (θhat n ω - θ))
        atTop ξ (fun _ => μ) ν)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hTmeas : ∀ n ω, AEMeasurable (Tstar n ω) (Pstar n ω))
    (hα_pos : 0 < α) (hα_lt_one : α < 1)
    (hstrict : StrictMono (fun x => cdf η x))
    (hTstar :
      TendstoInBootstrapDistribution μ Pstar
        (fun n ω ωs (_ : Unit) => Tstar n ω ωs) η
        (fun x (_ : Unit) => x))
    (hcont : ∀ x : ℝ, ContinuousAt (fun y => cdf η y) x)
    (hlower_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantile Pstar Tstar (α / 2) n) μ)
    (hupper_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantile Pstar Tstar (1 - α / 2) n) μ)
    (hξ : HasLaw ξ η ν)
    (hq_nonneg : 0 ≤ q)
    (hcdfLower : cdf η (-q) = α / 2)
    (hcdfUpper : cdf η q = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | percentileCIEvent θ
          (θhat n ω +
            bootstrapScalarLowerQuantile Pstar Tstar (α / 2) n ω / a n)
          (θhat n ω +
            bootstrapScalarLowerQuantile Pstar Tstar (1 - α / 2) n ω / a n)})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) := by
  have hPstarFinite : ∀ n ω, IsFiniteMeasure (Pstar n ω) := by
    intro n ω
    haveI : IsProbabilityMeasure (Pstar n ω) := hPstar n ω
    infer_instance
  exact
    chapter10_percentileCI_coverage_tendsto_one_sub_alpha_of_bootstrapDistribution_lowerQuantiles
      (μ := μ) (ν := ν) (η := η) (Pstar := Pstar) (Tstar := Tstar)
      (a := a) ha (θ := θ) (θhat := θhat) (ξ := ξ) (q := q)
      (α := α) hstat hPstarFinite
      (bootstrapScalarCDF_level_nonempty_of_aemeasurable
        (Pstar := Pstar) (Zstar := Tstar) hPstar hTmeas
        (by linarith : α / 2 < 1))
      (bootstrapScalarCDF_level_bddBelow_of_aemeasurable
        (Pstar := Pstar) (Zstar := Tstar) hPstar hTmeas
        (by linarith : 0 < α / 2))
      (bootstrapScalarCDF_local_right_lt_of_aemeasurable
        (Pstar := Pstar) (Zstar := Tstar) hPstar hTmeas)
      (bootstrapScalarCDF_level_nonempty_of_aemeasurable
        (Pstar := Pstar) (Zstar := Tstar) hPstar hTmeas
        (by linarith : 1 - α / 2 < 1))
      (bootstrapScalarCDF_level_bddBelow_of_aemeasurable
        (Pstar := Pstar) (Zstar := Tstar) hPstar hTmeas
        (by linarith : 0 < 1 - α / 2))
      (bootstrapScalarCDF_local_right_lt_of_aemeasurable
        (Pstar := Pstar) (Zstar := Tstar) hPstar hTmeas)
      hstrict hTstar hcont hlower_meas hupper_meas hξ hq_nonneg
      hcdfLower hcdfUpper

/-- Symmetric percentile-interval coverage from a one-dimensional bootstrap
distribution whose scalar limit has law `η`.

This law-facing variant is useful when the bootstrap limit is naturally stated
on an auxiliary probability space, such as a coordinate projection of a
finite-dimensional Gaussian vector. -/
theorem
chapter10_percentileCI_coverage_tendsto_one_sub_alpha_of_bootstrapDistribution_law_quantile_prob
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {Ωstar : Type*} [MeasurableSpace Ωstar]
    {η : Measure ℝ} [IsProbabilityMeasure η] [NoAtoms η]
    {νstar : Measure Ωstar} {Zlim : Ωstar → ℝ}
    {Pstar : ℕ → Ω → Measure Ωs} {Tstar : ℕ → Ω → Ωs → ℝ}
    {a : ℕ → ℝ} (ha : ∀ n, 0 < a n)
    {θ : ℝ} {θhat : ℕ → Ω → ℝ}
    {ξ : Ωlim → ℝ} {q α : ℝ}
    (hstat :
      TendstoInDistribution
        (fun n ω => a n * (θhat n ω - θ))
        atTop ξ (fun _ => μ) ν)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hTmeas : ∀ n ω, AEMeasurable (Tstar n ω) (Pstar n ω))
    (hα_pos : 0 < α) (hα_lt_one : α < 1)
    (hstrict : StrictMono (fun x => cdf η x))
    (hTstar :
      TendstoInBootstrapDistribution μ Pstar
        (fun n ω ωs (_ : Unit) => Tstar n ω ωs) νstar
        (fun ωstar (_ : Unit) => Zlim ωstar))
    (hZlaw : HasLaw Zlim η νstar)
    (hcont : ∀ x : ℝ, ContinuousAt (fun y => cdf η y) x)
    (hlower_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantile Pstar Tstar (α / 2) n) μ)
    (hupper_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantile Pstar Tstar (1 - α / 2) n) μ)
    (hξ : HasLaw ξ η ν)
    (hq_nonneg : 0 ≤ q)
    (hcdfLower : cdf η (-q) = α / 2)
    (hcdfUpper : cdf η q = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | percentileCIEvent θ
          (θhat n ω +
            bootstrapScalarLowerQuantile Pstar Tstar (α / 2) n ω / a n)
          (θhat n ω +
            bootstrapScalarLowerQuantile Pstar Tstar (1 - α / 2) n ω / a n)})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) := by
  obtain ⟨hleftLower, hrightLower⟩ :=
    strictMono_cdf_brackets hstrict hcdfLower
  obtain ⟨hleftUpper, hrightUpper⟩ :=
    strictMono_cdf_brackets hstrict hcdfUpper
  let Qlower : ℕ → Ω → ℝ :=
    bootstrapScalarLowerQuantile Pstar Tstar (α / 2)
  let Qupper : ℕ → Ω → ℝ :=
    bootstrapScalarLowerQuantile Pstar Tstar (1 - α / 2)
  have hQlower :
      TendstoInMeasure μ Qlower atTop (fun _ => -q) := by
    simpa [Qlower] using
      bootstrapScalarLowerQuantile_tendsto_of_bootstrapDistribution_unit_law_cdf_probability
        (μ := μ) (Pstar := Pstar) (Zstar := Tstar)
        (ν := νstar) (Z := Zlim) (η := η)
        (p := α / 2) (q := -q)
        hPstar hTmeas (by linarith : 0 < α / 2)
        (by linarith : α / 2 < 1)
        hleftLower hrightLower hTstar hZlaw hcont
  have hQupper :
      TendstoInMeasure μ Qupper atTop (fun _ => q) := by
    simpa [Qupper] using
      bootstrapScalarLowerQuantile_tendsto_of_bootstrapDistribution_unit_law_cdf_probability
        (μ := μ) (Pstar := Pstar) (Zstar := Tstar)
        (ν := νstar) (Z := Zlim) (η := η)
        (p := 1 - α / 2) (q := q)
        hPstar hTmeas (by linarith : 0 < 1 - α / 2)
        (by linarith : 1 - α / 2 < 1)
        hleftUpper hrightUpper hTstar hZlaw hcont
  have hQlower_meas : ∀ n, AEMeasurable (Qlower n) μ := by
    intro n
    simpa [Qlower] using hlower_meas n
  have hQupper_meas : ∀ n, AEMeasurable (Qupper n) μ := by
    intro n
    simpa [Qupper] using hupper_meas n
  exact
    chapter10_percentileCI_coverage_tendsto_one_sub_alpha_of_scaled_quantiles
      (μ := μ) (ν := ν) (η := η) (a := a) ha
      (θ := θ) (θhat := θhat) (Qlower := Qlower) (Qupper := Qupper)
      (ξ := ξ) (q := q) (α := α)
      hstat hQlower hQupper hQlower_meas hQupper_meas hξ
      hq_nonneg hcdfLower hcdfUpper

/-- Symmetric percentile-interval coverage from an auxiliary one-dimensional
bootstrap limit, retaining local CDF bracketing at the lower generalized
inverse endpoints.

This is the law-facing counterpart of
`chapter10_percentileCI_coverage_tendsto_one_sub_alpha_quantile_prob_brackets`:
`HasLaw` identifies the auxiliary bootstrap limit's scalar CDF with `cdf η`,
while local left/right CDF brackets replace any global strict-CDF premise. -/
theorem
chapter10_percentileCI_coverage_bootstrapDistribution_law_quantile_prob_brackets
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {Ωstar : Type*} [MeasurableSpace Ωstar]
    {η : Measure ℝ} [IsProbabilityMeasure η] [NoAtoms η]
    {νstar : Measure Ωstar} {Zlim : Ωstar → ℝ}
    {Pstar : ℕ → Ω → Measure Ωs} {Tstar : ℕ → Ω → Ωs → ℝ}
    {a : ℕ → ℝ} (ha : ∀ n, 0 < a n)
    {θ : ℝ} {θhat : ℕ → Ω → ℝ}
    {ξ : Ωlim → ℝ} {q α : ℝ}
    (hstat :
      TendstoInDistribution
        (fun n ω => a n * (θhat n ω - θ))
        atTop ξ (fun _ => μ) ν)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hTmeas : ∀ n ω, AEMeasurable (Tstar n ω) (Pstar n ω))
    (hα_pos : 0 < α) (hα_lt_one : α < 1)
    (hleftLower : ∀ ε : ℝ, 0 < ε → cdf η (-q - ε) < α / 2)
    (hrightLower : ∀ ε : ℝ, 0 < ε → α / 2 < cdf η (-q + ε))
    (hleftUpper : ∀ ε : ℝ, 0 < ε → cdf η (q - ε) < 1 - α / 2)
    (hrightUpper : ∀ ε : ℝ, 0 < ε → 1 - α / 2 < cdf η (q + ε))
    (hTstar :
      TendstoInBootstrapDistribution μ Pstar
        (fun n ω ωs (_ : Unit) => Tstar n ω ωs) νstar
        (fun ωstar (_ : Unit) => Zlim ωstar))
    (hZlaw : HasLaw Zlim η νstar)
    (hcont : ∀ x : ℝ, ContinuousAt (fun y => cdf η y) x)
    (hlower_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantile Pstar Tstar (α / 2) n) μ)
    (hupper_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantile Pstar Tstar (1 - α / 2) n) μ)
    (hξ : HasLaw ξ η ν)
    (hq_nonneg : 0 ≤ q)
    (hcdfLower : cdf η (-q) = α / 2)
    (hcdfUpper : cdf η q = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | percentileCIEvent θ
          (θhat n ω +
            bootstrapScalarLowerQuantile Pstar Tstar (α / 2) n ω / a n)
          (θhat n ω +
            bootstrapScalarLowerQuantile Pstar Tstar (1 - α / 2) n ω / a n)})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) := by
  let Qlower : ℕ → Ω → ℝ :=
    bootstrapScalarLowerQuantile Pstar Tstar (α / 2)
  let Qupper : ℕ → Ω → ℝ :=
    bootstrapScalarLowerQuantile Pstar Tstar (1 - α / 2)
  have hQlower :
      TendstoInMeasure μ Qlower atTop (fun _ => -q) := by
    simpa [Qlower] using
      bootstrapScalarLowerQuantile_tendsto_of_bootstrapDistribution_unit_law_cdf_probability
        (μ := μ) (Pstar := Pstar) (Zstar := Tstar)
        (ν := νstar) (Z := Zlim) (η := η)
        (p := α / 2) (q := -q)
        hPstar hTmeas (by linarith : 0 < α / 2)
        (by linarith : α / 2 < 1)
        hleftLower hrightLower hTstar hZlaw hcont
  have hQupper :
      TendstoInMeasure μ Qupper atTop (fun _ => q) := by
    simpa [Qupper] using
      bootstrapScalarLowerQuantile_tendsto_of_bootstrapDistribution_unit_law_cdf_probability
        (μ := μ) (Pstar := Pstar) (Zstar := Tstar)
        (ν := νstar) (Z := Zlim) (η := η)
        (p := 1 - α / 2) (q := q)
        hPstar hTmeas (by linarith : 0 < 1 - α / 2)
        (by linarith : 1 - α / 2 < 1)
        hleftUpper hrightUpper hTstar hZlaw hcont
  have hQlower_meas : ∀ n, AEMeasurable (Qlower n) μ := by
    intro n
    simpa [Qlower] using hlower_meas n
  have hQupper_meas : ∀ n, AEMeasurable (Qupper n) μ := by
    intro n
    simpa [Qupper] using hupper_meas n
  exact
    chapter10_percentileCI_coverage_tendsto_one_sub_alpha_of_scaled_quantiles
      (μ := μ) (ν := ν) (η := η) (a := a) ha
      (θ := θ) (θhat := θhat) (Qlower := Qlower) (Qupper := Qupper)
      (ξ := ξ) (q := q) (α := α)
      hstat hQlower hQupper hQlower_meas hQupper_meas hξ
      hq_nonneg hcdfLower hcdfUpper

/-- Symmetric percentile-interval coverage from one-dimensional bootstrap
distribution convergence, with bootstrap-side probability-CDF bracketing
discharged and local limit-CDF bracketing retained at `-q` and `q`. -/
theorem
chapter10_percentileCI_coverage_tendsto_one_sub_alpha_quantile_prob_brackets
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {η : Measure ℝ} [IsProbabilityMeasure η] [NoAtoms η]
    {Pstar : ℕ → Ω → Measure Ωs} {Tstar : ℕ → Ω → Ωs → ℝ}
    {a : ℕ → ℝ} (ha : ∀ n, 0 < a n)
    {θ : ℝ} {θhat : ℕ → Ω → ℝ}
    {ξ : Ωlim → ℝ} {q α : ℝ}
    (hstat :
      TendstoInDistribution
        (fun n ω => a n * (θhat n ω - θ))
        atTop ξ (fun _ => μ) ν)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hTmeas : ∀ n ω, AEMeasurable (Tstar n ω) (Pstar n ω))
    (hα_pos : 0 < α) (hα_lt_one : α < 1)
    (hleftLower : ∀ ε : ℝ, 0 < ε → cdf η (-q - ε) < α / 2)
    (hrightLower : ∀ ε : ℝ, 0 < ε → α / 2 < cdf η (-q + ε))
    (hleftUpper : ∀ ε : ℝ, 0 < ε → cdf η (q - ε) < 1 - α / 2)
    (hrightUpper : ∀ ε : ℝ, 0 < ε → 1 - α / 2 < cdf η (q + ε))
    (hTstar :
      TendstoInBootstrapDistribution μ Pstar
        (fun n ω ωs (_ : Unit) => Tstar n ω ωs) η
        (fun x (_ : Unit) => x))
    (hcont : ∀ x : ℝ, ContinuousAt (fun y => cdf η y) x)
    (hlower_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantile Pstar Tstar (α / 2) n) μ)
    (hupper_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantile Pstar Tstar (1 - α / 2) n) μ)
    (hξ : HasLaw ξ η ν)
    (hq_nonneg : 0 ≤ q)
    (hcdfLower : cdf η (-q) = α / 2)
    (hcdfUpper : cdf η q = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | percentileCIEvent θ
          (θhat n ω +
            bootstrapScalarLowerQuantile Pstar Tstar (α / 2) n ω / a n)
          (θhat n ω +
            bootstrapScalarLowerQuantile Pstar Tstar (1 - α / 2) n ω / a n)})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) := by
  have hPstarFinite : ∀ n ω, IsFiniteMeasure (Pstar n ω) := by
    intro n ω
    haveI : IsProbabilityMeasure (Pstar n ω) := hPstar n ω
    infer_instance
  exact
    chapter10_percentileCI_coverage_tendsto_one_sub_alpha_of_bootstrapDistribution_brackets
      (μ := μ) (ν := ν) (η := η) (Pstar := Pstar) (Tstar := Tstar)
      (a := a) ha (θ := θ) (θhat := θhat) (ξ := ξ) (q := q)
      (α := α) hstat hPstarFinite
      (bootstrapScalarCDF_level_nonempty_of_aemeasurable
        (Pstar := Pstar) (Zstar := Tstar) hPstar hTmeas
        (by linarith : α / 2 < 1))
      (bootstrapScalarCDF_level_bddBelow_of_aemeasurable
        (Pstar := Pstar) (Zstar := Tstar) hPstar hTmeas
        (by linarith : 0 < α / 2))
      (bootstrapScalarCDF_local_right_lt_of_aemeasurable
        (Pstar := Pstar) (Zstar := Tstar) hPstar hTmeas)
      (bootstrapScalarCDF_level_nonempty_of_aemeasurable
        (Pstar := Pstar) (Zstar := Tstar) hPstar hTmeas
        (by linarith : 1 - α / 2 < 1))
      (bootstrapScalarCDF_level_bddBelow_of_aemeasurable
        (Pstar := Pstar) (Zstar := Tstar) hPstar hTmeas
        (by linarith : 0 < 1 - α / 2))
      (bootstrapScalarCDF_local_right_lt_of_aemeasurable
        (Pstar := Pstar) (Zstar := Tstar) hPstar hTmeas)
      hleftLower hrightLower hleftUpper hrightUpper hTstar hcont
      hlower_meas hupper_meas hξ hq_nonneg hcdfLower hcdfUpper

variable {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]

/-- Indexed symmetric percentile-interval coverage from one-dimensional
bootstrap-distribution convergence, with bootstrap-side probability-CDF
bracketing discharged and local limit-CDF bracketing retained at `-q` and
`q`.

This is the sample-size-dependent counterpart of
`chapter10_percentileCI_coverage_tendsto_one_sub_alpha_quantile_prob_brackets`
for ordinary nonparametric bootstrap laws whose resampling spaces vary with
`n`. -/
theorem
chapter10_percentileCI_coverage_tendsto_one_sub_alpha_indexed_quantile_prob_brackets
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {η : Measure ℝ} [IsProbabilityMeasure η] [NoAtoms η]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Tstar : ∀ n, Ω → Ωboot n → ℝ}
    {a : ℕ → ℝ} (ha : ∀ n, 0 < a n)
    {θ : ℝ} {θhat : ℕ → Ω → ℝ}
    {ξ : Ωlim → ℝ} {q α : ℝ}
    (hstat :
      TendstoInDistribution
        (fun n ω => a n * (θhat n ω - θ))
        atTop ξ (fun _ => μ) ν)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hTmeas : ∀ n ω, AEMeasurable (Tstar n ω) (Pstar n ω))
    (hα_pos : 0 < α) (hα_lt_one : α < 1)
    (hleftLower : ∀ ε : ℝ, 0 < ε → cdf η (-q - ε) < α / 2)
    (hrightLower : ∀ ε : ℝ, 0 < ε → α / 2 < cdf η (-q + ε))
    (hleftUpper : ∀ ε : ℝ, 0 < ε → cdf η (q - ε) < 1 - α / 2)
    (hrightUpper : ∀ ε : ℝ, 0 < ε → 1 - α / 2 < cdf η (q + ε))
    (hTstar :
      TendstoInBootstrapDistributionIndexed μ Pstar
        (fun n ω ωs (_ : Unit) => Tstar n ω ωs) η
        (fun x (_ : Unit) => x))
    (hcont : ∀ x : ℝ, ContinuousAt (fun y => cdf η y) x)
    (hlower_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed Pstar Tstar (α / 2) n) μ)
    (hupper_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed Pstar Tstar (1 - α / 2) n) μ)
    (hξ : HasLaw ξ η ν)
    (hq_nonneg : 0 ≤ q)
    (hcdfLower : cdf η (-q) = α / 2)
    (hcdfUpper : cdf η q = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | percentileCIEvent θ
          (θhat n ω +
            bootstrapScalarLowerQuantileIndexed Pstar Tstar (α / 2) n ω / a n)
          (θhat n ω +
            bootstrapScalarLowerQuantileIndexed Pstar Tstar (1 - α / 2) n ω / a n)})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) := by
  let Qlower : ℕ → Ω → ℝ :=
    bootstrapScalarLowerQuantileIndexed Pstar Tstar (α / 2)
  let Qupper : ℕ → Ω → ℝ :=
    bootstrapScalarLowerQuantileIndexed Pstar Tstar (1 - α / 2)
  have hQlower :
      TendstoInMeasure μ Qlower atTop (fun _ => -q) :=
    bootstrapScalarLowerQuantileIndexed_tendsto_of_bootstrapDistribution_unit_id_cdf_probability
      (μ := μ) (Pstar := Pstar) (Zstar := Tstar) (η := η)
      (p := α / 2) (q := -q)
      hPstar hTmeas (by linarith : 0 < α / 2)
      (by linarith : α / 2 < 1)
      hleftLower hrightLower hTstar hcont
  have hQupper :
      TendstoInMeasure μ Qupper atTop (fun _ => q) :=
    bootstrapScalarLowerQuantileIndexed_tendsto_of_bootstrapDistribution_unit_id_cdf_probability
      (μ := μ) (Pstar := Pstar) (Zstar := Tstar) (η := η)
      (p := 1 - α / 2) (q := q)
      hPstar hTmeas (by linarith : 0 < 1 - α / 2)
      (by linarith : 1 - α / 2 < 1)
      hleftUpper hrightUpper hTstar hcont
  have hQlower_meas : ∀ n, AEMeasurable (Qlower n) μ := by
    intro n
    simpa [Qlower] using hlower_meas n
  have hQupper_meas : ∀ n, AEMeasurable (Qupper n) μ := by
    intro n
    simpa [Qupper] using hupper_meas n
  have hcoverage :=
    chapter10_percentileCI_coverage_tendsto_one_sub_alpha_of_scaled_quantiles
      (μ := μ) (ν := ν) (η := η) (a := a) ha
      (θ := θ) (θhat := θhat) (Qlower := Qlower) (Qupper := Qupper)
      (ξ := ξ) (q := q) (α := α)
      hstat hQlower hQupper hQlower_meas hQupper_meas hξ
      hq_nonneg hcdfLower hcdfUpper
  simpa [Qlower, Qupper] using hcoverage

/-- Indexed symmetric percentile-interval coverage from one-dimensional
bootstrap-distribution convergence, with probability-CDF bracketing discharged
at levels `α / 2` and `1 - α / 2`.

This is the strict-CDF counterpart of
`chapter10_percentileCI_coverage_tendsto_one_sub_alpha_indexed_quantile_prob_brackets`. -/
theorem
chapter10_percentileCI_coverage_tendsto_one_sub_alpha_indexed_bootstrapDistribution_quantile_prob
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {η : Measure ℝ} [IsProbabilityMeasure η] [NoAtoms η]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Tstar : ∀ n, Ω → Ωboot n → ℝ}
    {a : ℕ → ℝ} (ha : ∀ n, 0 < a n)
    {θ : ℝ} {θhat : ℕ → Ω → ℝ}
    {ξ : Ωlim → ℝ} {q α : ℝ}
    (hstat :
      TendstoInDistribution
        (fun n ω => a n * (θhat n ω - θ))
        atTop ξ (fun _ => μ) ν)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hTmeas : ∀ n ω, AEMeasurable (Tstar n ω) (Pstar n ω))
    (hα_pos : 0 < α) (hα_lt_one : α < 1)
    (hstrict : StrictMono (fun x => cdf η x))
    (hTstar :
      TendstoInBootstrapDistributionIndexed μ Pstar
        (fun n ω ωs (_ : Unit) => Tstar n ω ωs) η
        (fun x (_ : Unit) => x))
    (hcont : ∀ x : ℝ, ContinuousAt (fun y => cdf η y) x)
    (hlower_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed Pstar Tstar (α / 2) n) μ)
    (hupper_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed Pstar Tstar (1 - α / 2) n) μ)
    (hξ : HasLaw ξ η ν)
    (hq_nonneg : 0 ≤ q)
    (hcdfLower : cdf η (-q) = α / 2)
    (hcdfUpper : cdf η q = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | percentileCIEvent θ
          (θhat n ω +
            bootstrapScalarLowerQuantileIndexed Pstar Tstar (α / 2) n ω / a n)
          (θhat n ω +
            bootstrapScalarLowerQuantileIndexed Pstar Tstar (1 - α / 2) n ω / a n)})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) := by
  obtain ⟨hleftLower, hrightLower⟩ :=
    strictMono_cdf_brackets hstrict hcdfLower
  obtain ⟨hleftUpper, hrightUpper⟩ :=
    strictMono_cdf_brackets hstrict hcdfUpper
  exact
    chapter10_percentileCI_coverage_tendsto_one_sub_alpha_indexed_quantile_prob_brackets
      (μ := μ) (ν := ν) (η := η) (Pstar := Pstar) (Tstar := Tstar)
      (a := a) ha (θ := θ) (θhat := θhat) (ξ := ξ) (q := q)
      (α := α) hstat hPstar hTmeas hα_pos hα_lt_one
      hleftLower hrightLower hleftUpper hrightUpper hTstar hcont
      hlower_meas hupper_meas hξ hq_nonneg hcdfLower hcdfUpper

/-- Indexed symmetric percentile-interval coverage from a one-dimensional
bootstrap distribution whose scalar limit has law `η`.

This sample-size-dependent law-facing wrapper connects the percentile interval
endpoint route to bootstrap limits stated on auxiliary spaces, including
coordinate projections of multivariate Gaussian ordinary-bootstrap CLTs. -/
theorem
chapter10_indexed_percentileCI_coverage_bootstrapDistribution_law_quantile_prob
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {Ωstar : Type*} [MeasurableSpace Ωstar]
    {η : Measure ℝ} [IsProbabilityMeasure η] [NoAtoms η]
    {νstar : Measure Ωstar} {Zlim : Ωstar → ℝ}
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Tstar : ∀ n, Ω → Ωboot n → ℝ}
    {a : ℕ → ℝ} (ha : ∀ n, 0 < a n)
    {θ : ℝ} {θhat : ℕ → Ω → ℝ}
    {ξ : Ωlim → ℝ} {q α : ℝ}
    (hstat :
      TendstoInDistribution
        (fun n ω => a n * (θhat n ω - θ))
        atTop ξ (fun _ => μ) ν)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hTmeas : ∀ n ω, AEMeasurable (Tstar n ω) (Pstar n ω))
    (hα_pos : 0 < α) (hα_lt_one : α < 1)
    (hstrict : StrictMono (fun x => cdf η x))
    (hTstar :
      TendstoInBootstrapDistributionIndexed μ Pstar
        (fun n ω ωs (_ : Unit) => Tstar n ω ωs) νstar
        (fun ωstar (_ : Unit) => Zlim ωstar))
    (hZlaw : HasLaw Zlim η νstar)
    (hcont : ∀ x : ℝ, ContinuousAt (fun y => cdf η y) x)
    (hlower_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed Pstar Tstar (α / 2) n) μ)
    (hupper_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed Pstar Tstar (1 - α / 2) n) μ)
    (hξ : HasLaw ξ η ν)
    (hq_nonneg : 0 ≤ q)
    (hcdfLower : cdf η (-q) = α / 2)
    (hcdfUpper : cdf η q = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | percentileCIEvent θ
          (θhat n ω +
            bootstrapScalarLowerQuantileIndexed Pstar Tstar (α / 2) n ω / a n)
          (θhat n ω +
            bootstrapScalarLowerQuantileIndexed Pstar Tstar (1 - α / 2) n ω / a n)})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) := by
  obtain ⟨hleftLower, hrightLower⟩ :=
    strictMono_cdf_brackets hstrict hcdfLower
  obtain ⟨hleftUpper, hrightUpper⟩ :=
    strictMono_cdf_brackets hstrict hcdfUpper
  let Qlower : ℕ → Ω → ℝ :=
    bootstrapScalarLowerQuantileIndexed Pstar Tstar (α / 2)
  let Qupper : ℕ → Ω → ℝ :=
    bootstrapScalarLowerQuantileIndexed Pstar Tstar (1 - α / 2)
  have hQlower :
      TendstoInMeasure μ Qlower atTop (fun _ => -q) := by
    simpa [Qlower] using
      bootstrapScalarLowerQuantileIndexed_tendsto_of_bootstrapDistribution_unit_law_cdf_probability
        (μ := μ) (Pstar := Pstar) (Zstar := Tstar)
        (ν := νstar) (Z := Zlim) (η := η)
        (p := α / 2) (q := -q)
        hPstar hTmeas (by linarith : 0 < α / 2)
        (by linarith : α / 2 < 1)
        hleftLower hrightLower hTstar hZlaw hcont
  have hQupper :
      TendstoInMeasure μ Qupper atTop (fun _ => q) := by
    simpa [Qupper] using
      bootstrapScalarLowerQuantileIndexed_tendsto_of_bootstrapDistribution_unit_law_cdf_probability
        (μ := μ) (Pstar := Pstar) (Zstar := Tstar)
        (ν := νstar) (Z := Zlim) (η := η)
        (p := 1 - α / 2) (q := q)
        hPstar hTmeas (by linarith : 0 < 1 - α / 2)
        (by linarith : 1 - α / 2 < 1)
        hleftUpper hrightUpper hTstar hZlaw hcont
  have hQlower_meas : ∀ n, AEMeasurable (Qlower n) μ := by
    intro n
    simpa [Qlower] using hlower_meas n
  have hQupper_meas : ∀ n, AEMeasurable (Qupper n) μ := by
    intro n
    simpa [Qupper] using hupper_meas n
  exact
    chapter10_percentileCI_coverage_tendsto_one_sub_alpha_of_scaled_quantiles
      (μ := μ) (ν := ν) (η := η) (a := a) ha
      (θ := θ) (θhat := θhat) (Qlower := Qlower) (Qupper := Qupper)
      (ξ := ξ) (q := q) (α := α)
      hstat hQlower hQupper hQlower_meas hQupper_meas hξ
      hq_nonneg hcdfLower hcdfUpper

/-- Indexed symmetric percentile-interval coverage from an auxiliary
one-dimensional bootstrap limit, retaining local CDF bracketing at the lower
generalized-inverse endpoints.

This sample-size-dependent law-facing wrapper is the indexed counterpart of
`chapter10_percentileCI_coverage_bootstrapDistribution_law_quantile_prob_brackets`. -/
theorem
chapter10_indexed_percentileCI_coverage_bootstrapDistribution_law_quantile_prob_brackets
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {Ωstar : Type*} [MeasurableSpace Ωstar]
    {η : Measure ℝ} [IsProbabilityMeasure η] [NoAtoms η]
    {νstar : Measure Ωstar} {Zlim : Ωstar → ℝ}
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Tstar : ∀ n, Ω → Ωboot n → ℝ}
    {a : ℕ → ℝ} (ha : ∀ n, 0 < a n)
    {θ : ℝ} {θhat : ℕ → Ω → ℝ}
    {ξ : Ωlim → ℝ} {q α : ℝ}
    (hstat :
      TendstoInDistribution
        (fun n ω => a n * (θhat n ω - θ))
        atTop ξ (fun _ => μ) ν)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hTmeas : ∀ n ω, AEMeasurable (Tstar n ω) (Pstar n ω))
    (hα_pos : 0 < α) (hα_lt_one : α < 1)
    (hleftLower : ∀ ε : ℝ, 0 < ε → cdf η (-q - ε) < α / 2)
    (hrightLower : ∀ ε : ℝ, 0 < ε → α / 2 < cdf η (-q + ε))
    (hleftUpper : ∀ ε : ℝ, 0 < ε → cdf η (q - ε) < 1 - α / 2)
    (hrightUpper : ∀ ε : ℝ, 0 < ε → 1 - α / 2 < cdf η (q + ε))
    (hTstar :
      TendstoInBootstrapDistributionIndexed μ Pstar
        (fun n ω ωs (_ : Unit) => Tstar n ω ωs) νstar
        (fun ωstar (_ : Unit) => Zlim ωstar))
    (hZlaw : HasLaw Zlim η νstar)
    (hcont : ∀ x : ℝ, ContinuousAt (fun y => cdf η y) x)
    (hlower_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed Pstar Tstar (α / 2) n) μ)
    (hupper_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed Pstar Tstar (1 - α / 2) n) μ)
    (hξ : HasLaw ξ η ν)
    (hq_nonneg : 0 ≤ q)
    (hcdfLower : cdf η (-q) = α / 2)
    (hcdfUpper : cdf η q = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | percentileCIEvent θ
          (θhat n ω +
            bootstrapScalarLowerQuantileIndexed Pstar Tstar (α / 2) n ω / a n)
          (θhat n ω +
            bootstrapScalarLowerQuantileIndexed Pstar Tstar (1 - α / 2) n ω / a n)})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) := by
  let Qlower : ℕ → Ω → ℝ :=
    bootstrapScalarLowerQuantileIndexed Pstar Tstar (α / 2)
  let Qupper : ℕ → Ω → ℝ :=
    bootstrapScalarLowerQuantileIndexed Pstar Tstar (1 - α / 2)
  have hQlower :
      TendstoInMeasure μ Qlower atTop (fun _ => -q) := by
    simpa [Qlower] using
      bootstrapScalarLowerQuantileIndexed_tendsto_of_bootstrapDistribution_unit_law_cdf_probability
        (μ := μ) (Pstar := Pstar) (Zstar := Tstar)
        (ν := νstar) (Z := Zlim) (η := η)
        (p := α / 2) (q := -q)
        hPstar hTmeas (by linarith : 0 < α / 2)
        (by linarith : α / 2 < 1)
        hleftLower hrightLower hTstar hZlaw hcont
  have hQupper :
      TendstoInMeasure μ Qupper atTop (fun _ => q) := by
    simpa [Qupper] using
      bootstrapScalarLowerQuantileIndexed_tendsto_of_bootstrapDistribution_unit_law_cdf_probability
        (μ := μ) (Pstar := Pstar) (Zstar := Tstar)
        (ν := νstar) (Z := Zlim) (η := η)
        (p := 1 - α / 2) (q := q)
        hPstar hTmeas (by linarith : 0 < 1 - α / 2)
        (by linarith : 1 - α / 2 < 1)
        hleftUpper hrightUpper hTstar hZlaw hcont
  have hQlower_meas : ∀ n, AEMeasurable (Qlower n) μ := by
    intro n
    simpa [Qlower] using hlower_meas n
  have hQupper_meas : ∀ n, AEMeasurable (Qupper n) μ := by
    intro n
    simpa [Qupper] using hupper_meas n
  exact
    chapter10_percentileCI_coverage_tendsto_one_sub_alpha_of_scaled_quantiles
      (μ := μ) (ν := ν) (η := η) (a := a) ha
      (θ := θ) (θhat := θhat) (Qlower := Qlower) (Qupper := Qupper)
      (ξ := ξ) (q := q) (α := α)
      hstat hQlower hQupper hQlower_meas hQupper_meas hξ
      hq_nonneg hcdfLower hcdfUpper

/-- Indexed ordinary nonparametric-bootstrap percentile-interval coverage from
the concrete normalized scalar `Fin (n+1)` resample-mean CLT.

The bootstrap endpoint statistic is no longer abstract: it is the lower
generalized inverse of the conditional CDF of
`sqrt(n+1) (Ybar*_n - Ybar_n)` under the finite ordinary resampling law.  The
sample-side limit and percentile calibration remain explicit, as in Hansen
Theorem 10.13. -/
theorem
chapter10_percentileCI_coverage_indexed_finSucc_resampleMean_of_iIndep_tail_posDef_brackets
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {η : Measure ℝ} [IsProbabilityMeasure η] [NoAtoms η]
    (Y : ℕ → Ω → ℝ)
    (hYmem : MemLp (Y 0) 2 μ)
    (hindep : iIndepFun Y μ)
    (hident : ∀ i, IdentDistrib (Y i) (Y 0) μ μ)
    (hS : (covMat μ (fun ω (_ : Unit) => Y 0 ω)).PosDef)
    {a : ℕ → ℝ} (ha : ∀ n, 0 < a n)
    {θ : ℝ} {θhat : ℕ → Ω → ℝ}
    {ξ : Ωlim → ℝ} {q α : ℝ}
    (hstat :
      TendstoInDistribution
        (fun n ω => a n * (θhat n ω - θ))
        atTop ξ (fun _ => μ) ν)
    (hα_pos : 0 < α) (hα_lt_one : α < 1)
    (hleftLower : ∀ ε : ℝ, 0 < ε → cdf η (-q - ε) < α / 2)
    (hrightLower : ∀ ε : ℝ, 0 < ε → α / 2 < cdf η (-q + ε))
    (hleftUpper : ∀ ε : ℝ, 0 < ε → cdf η (q - ε) < 1 - α / 2)
    (hrightUpper : ∀ ε : ℝ, 0 < ε → 1 - α / 2 < cdf η (q + ε))
    (hcont : ∀ x : ℝ, ContinuousAt (fun y => cdf η y) x)
    (hlower_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed
            (fun n _ =>
              (ProbabilityTheory.uniformOn
                (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                  Measure (Fin (n + 1) → Fin (n + 1))))
            (fun n ω ωs =>
              Real.sqrt (n + 1 : ℝ) *
                (empiricalBootstrapResampleMean
                    (fun i : Fin (n + 1) => Y i.val ω)
                    (fun ωs t => ωs t) ωs -
                  empiricalMean (fun i : Fin (n + 1) => Y i.val ω)))
            (α / 2) n) μ)
    (hupper_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed
            (fun n _ =>
              (ProbabilityTheory.uniformOn
                (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                  Measure (Fin (n + 1) → Fin (n + 1))))
            (fun n ω ωs =>
              Real.sqrt (n + 1 : ℝ) *
                (empiricalBootstrapResampleMean
                    (fun i : Fin (n + 1) => Y i.val ω)
                    (fun ωs t => ωs t) ωs -
                  empiricalMean (fun i : Fin (n + 1) => Y i.val ω)))
            (1 - α / 2) n) μ)
    (hξ : HasLaw ξ η ν)
    (hZlaw :
      HasLaw
        (fun z : EuclideanSpace ℝ Unit => (z : Unit → ℝ) ()) η
        (multivariateGaussian (0 : EuclideanSpace ℝ Unit)
          (covMat μ (fun ω (_ : Unit) => Y 0 ω))))
    (hq_nonneg : 0 ≤ q)
    (hcdfLower : cdf η (-q) = α / 2)
    (hcdfUpper : cdf η q = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | percentileCIEvent θ
          (θhat n ω +
            bootstrapScalarLowerQuantileIndexed
              (fun n _ =>
                (ProbabilityTheory.uniformOn
                  (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                    Measure (Fin (n + 1) → Fin (n + 1))))
              (fun n ω ωs =>
                Real.sqrt (n + 1 : ℝ) *
                  (empiricalBootstrapResampleMean
                      (fun i : Fin (n + 1) => Y i.val ω)
                      (fun ωs t => ωs t) ωs -
                    empiricalMean (fun i : Fin (n + 1) => Y i.val ω)))
              (α / 2) n ω / a n)
          (θhat n ω +
            bootstrapScalarLowerQuantileIndexed
              (fun n _ =>
                (ProbabilityTheory.uniformOn
                  (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                    Measure (Fin (n + 1) → Fin (n + 1))))
              (fun n ω ωs =>
                Real.sqrt (n + 1 : ℝ) *
                  (empiricalBootstrapResampleMean
                      (fun i : Fin (n + 1) => Y i.val ω)
                      (fun ωs t => ωs t) ωs -
                    empiricalMean (fun i : Fin (n + 1) => Y i.val ω)))
              (1 - α / 2) n ω / a n)})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) := by
  have hPstar :
      ∀ n : ℕ, ∀ ω : Ω,
        IsProbabilityMeasure
          ((ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
              Measure (Fin (n + 1) → Fin (n + 1)))) := by
    intro n ω
    infer_instance
  have hTmeas :
      ∀ n : ℕ, ∀ ω : Ω,
        AEMeasurable
          (fun ωs =>
            Real.sqrt (n + 1 : ℝ) *
              (empiricalBootstrapResampleMean
                  (fun i : Fin (n + 1) => Y i.val ω)
                  (fun ωs t => ωs t) ωs -
                empiricalMean (fun i : Fin (n + 1) => Y i.val ω)))
          ((ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
              Measure (Fin (n + 1) → Fin (n + 1)))) := by
    intro n ω
    exact (measurable_of_finite _).aemeasurable
  have hTstar :
      TendstoInBootstrapDistributionIndexed μ
        (fun n _ =>
          (ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
              Measure (Fin (n + 1) → Fin (n + 1))))
        (fun n ω ωs (_ : Unit) =>
          Real.sqrt (n + 1 : ℝ) *
            (empiricalBootstrapResampleMean
                (fun i : Fin (n + 1) => Y i.val ω)
                (fun ωs t => ωs t) ωs -
              empiricalMean (fun i : Fin (n + 1) => Y i.val ω)))
        (multivariateGaussian (0 : EuclideanSpace ℝ Unit)
          (covMat μ (fun ω (_ : Unit) => Y 0 ω)))
        (fun z : EuclideanSpace ℝ Unit => fun _ : Unit => (z : Unit → ℝ) ()) :=
    chapter10_indexed_bootstrap_clt_scalar_finSucc_resampleMean_of_iIndep_tail_posDef
      (μ := μ) Y hYmem hindep hident hS
  exact
    chapter10_indexed_percentileCI_coverage_bootstrapDistribution_law_quantile_prob_brackets
      (μ := μ) (ν := ν)
      (Ωstar := EuclideanSpace ℝ Unit) (η := η)
      (νstar := multivariateGaussian (0 : EuclideanSpace ℝ Unit)
        (covMat μ (fun ω (_ : Unit) => Y 0 ω)))
      (Zlim := fun z : EuclideanSpace ℝ Unit => (z : Unit → ℝ) ())
      (Pstar := fun n _ =>
        (ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))))
      (Tstar := fun n ω ωs =>
        Real.sqrt (n + 1 : ℝ) *
          (empiricalBootstrapResampleMean
              (fun i : Fin (n + 1) => Y i.val ω)
              (fun ωs t => ωs t) ωs -
            empiricalMean (fun i : Fin (n + 1) => Y i.val ω)))
      (a := a) ha (θ := θ) (θhat := θhat) (ξ := ξ) (q := q)
      (α := α) hstat hPstar hTmeas hα_pos hα_lt_one
      hleftLower hrightLower hleftUpper hrightUpper hTstar hZlaw hcont
      hlower_meas hupper_meas hξ hq_nonneg hcdfLower hcdfUpper

/-- Strict-CDF counterpart of
`chapter10_percentileCI_coverage_indexed_finSucc_resampleMean_of_iIndep_tail_posDef_brackets`.

The strict monotonicity of the scalar limit CDF supplies the local endpoint
bracketing needed by the concrete ordinary-bootstrap percentile constructor. -/
theorem
chapter10_percentileCI_coverage_indexed_finSucc_resampleMean_of_iIndep_tail_posDef
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {η : Measure ℝ} [IsProbabilityMeasure η] [NoAtoms η]
    (Y : ℕ → Ω → ℝ)
    (hYmem : MemLp (Y 0) 2 μ)
    (hindep : iIndepFun Y μ)
    (hident : ∀ i, IdentDistrib (Y i) (Y 0) μ μ)
    (hS : (covMat μ (fun ω (_ : Unit) => Y 0 ω)).PosDef)
    {a : ℕ → ℝ} (ha : ∀ n, 0 < a n)
    {θ : ℝ} {θhat : ℕ → Ω → ℝ}
    {ξ : Ωlim → ℝ} {q α : ℝ}
    (hstat :
      TendstoInDistribution
        (fun n ω => a n * (θhat n ω - θ))
        atTop ξ (fun _ => μ) ν)
    (hα_pos : 0 < α) (hα_lt_one : α < 1)
    (hstrict : StrictMono (fun x => cdf η x))
    (hcont : ∀ x : ℝ, ContinuousAt (fun y => cdf η y) x)
    (hlower_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed
            (fun n _ =>
              (ProbabilityTheory.uniformOn
                (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                  Measure (Fin (n + 1) → Fin (n + 1))))
            (fun n ω ωs =>
              Real.sqrt (n + 1 : ℝ) *
                (empiricalBootstrapResampleMean
                    (fun i : Fin (n + 1) => Y i.val ω)
                    (fun ωs t => ωs t) ωs -
                  empiricalMean (fun i : Fin (n + 1) => Y i.val ω)))
            (α / 2) n) μ)
    (hupper_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed
            (fun n _ =>
              (ProbabilityTheory.uniformOn
                (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                  Measure (Fin (n + 1) → Fin (n + 1))))
            (fun n ω ωs =>
              Real.sqrt (n + 1 : ℝ) *
                (empiricalBootstrapResampleMean
                    (fun i : Fin (n + 1) => Y i.val ω)
                    (fun ωs t => ωs t) ωs -
                  empiricalMean (fun i : Fin (n + 1) => Y i.val ω)))
            (1 - α / 2) n) μ)
    (hξ : HasLaw ξ η ν)
    (hZlaw :
      HasLaw
        (fun z : EuclideanSpace ℝ Unit => (z : Unit → ℝ) ()) η
        (multivariateGaussian (0 : EuclideanSpace ℝ Unit)
          (covMat μ (fun ω (_ : Unit) => Y 0 ω))))
    (hq_nonneg : 0 ≤ q)
    (hcdfLower : cdf η (-q) = α / 2)
    (hcdfUpper : cdf η q = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | percentileCIEvent θ
          (θhat n ω +
            bootstrapScalarLowerQuantileIndexed
              (fun n _ =>
                (ProbabilityTheory.uniformOn
                  (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                    Measure (Fin (n + 1) → Fin (n + 1))))
              (fun n ω ωs =>
                Real.sqrt (n + 1 : ℝ) *
                  (empiricalBootstrapResampleMean
                      (fun i : Fin (n + 1) => Y i.val ω)
                      (fun ωs t => ωs t) ωs -
                    empiricalMean (fun i : Fin (n + 1) => Y i.val ω)))
              (α / 2) n ω / a n)
          (θhat n ω +
            bootstrapScalarLowerQuantileIndexed
              (fun n _ =>
                (ProbabilityTheory.uniformOn
                  (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                    Measure (Fin (n + 1) → Fin (n + 1))))
              (fun n ω ωs =>
                Real.sqrt (n + 1 : ℝ) *
                  (empiricalBootstrapResampleMean
                      (fun i : Fin (n + 1) => Y i.val ω)
                      (fun ωs t => ωs t) ωs -
                    empiricalMean (fun i : Fin (n + 1) => Y i.val ω)))
              (1 - α / 2) n ω / a n)})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) := by
  obtain ⟨hleftLower, hrightLower⟩ :=
    strictMono_cdf_brackets hstrict hcdfLower
  obtain ⟨hleftUpper, hrightUpper⟩ :=
    strictMono_cdf_brackets hstrict hcdfUpper
  exact
    chapter10_percentileCI_coverage_indexed_finSucc_resampleMean_of_iIndep_tail_posDef_brackets
      (μ := μ) (ν := ν) (η := η) Y hYmem hindep hident hS ha
      (θ := θ) (θhat := θhat) (ξ := ξ) (q := q) (α := α)
      hstat hα_pos hα_lt_one hleftLower hrightLower hleftUpper
      hrightUpper hcont hlower_meas hupper_meas hξ hZlaw hq_nonneg
      hcdfLower hcdfUpper

set_option linter.style.longLine false in
/-- Local-CDF bracketing finite OLS percentile-interval wrapper.

The bootstrap endpoint statistic is the concrete one-row ordinary-bootstrap
OLS numerator `sqrt(n+1)(R βhat* - R βhat)`.  The sample-side OLS distribution
limit and scalar limit-law calibration remain explicit, matching Hansen
Theorem 10.13. -/
theorem
    chapter10_percentileCI_coverage_indexed_finSucc_olsBetaOrZero_gapEnvelope_bounds_brackets
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {k : Type*} [Fintype k] [DecidableEq k]
    {η : Measure ℝ} [IsProbabilityMeasure η] [NoAtoms η]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    {a : ℕ → ℝ} (ha : ∀ n, 0 < a n)
    {ξ : Ωlim → ℝ} {Clin Cbeta q α : ℝ}
    (β : k → ℝ) (R : Matrix Unit k ℝ)
    (hstat :
      TendstoInDistribution
        (fun n ω =>
          a n *
            (linearRestrictionEstimate R
                (olsBetaOrZero
                  (stackRegressors X n ω) (stackOutcomes y n ω)) -
              linearRestrictionEstimate R β))
        atTop ξ (fun _ => μ) ν)
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
        atTop (fun _ => 0))
    (hα_pos : 0 < α) (hα_lt_one : α < 1)
    (hleftLower : ∀ ε : ℝ, 0 < ε → cdf η (-q - ε) < α / 2)
    (hrightLower : ∀ ε : ℝ, 0 < ε → α / 2 < cdf η (-q + ε))
    (hleftUpper : ∀ ε : ℝ, 0 < ε → cdf η (q - ε) < 1 - α / 2)
    (hrightUpper : ∀ ε : ℝ, 0 < ε → 1 - α / 2 < cdf η (q + ε))
    (hcont : ∀ x : ℝ, ContinuousAt (fun y => cdf η y) x)
    (hlower_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed
            (fun n _ =>
              (ProbabilityTheory.uniformOn
                (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                  Measure (Fin (n + 1) → Fin (n + 1))))
            (fun n ω ωs =>
              regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs)
            (α / 2) n) μ)
    (hupper_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed
            (fun n _ =>
              (ProbabilityTheory.uniformOn
                (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                  Measure (Fin (n + 1) → Fin (n + 1))))
            (fun n ω ωs =>
              regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs)
            (1 - α / 2) n) μ)
    (hξ : HasLaw ξ η ν)
    (hZlaw :
      HasLaw
        (fun z : EuclideanSpace ℝ Unit => (z : Unit → ℝ) ()) η
        (multivariateGaussian (0 : EuclideanSpace ℝ Unit)
          (R * heteroAsymCov μ X e * Rᵀ)))
    (hq_nonneg : 0 ≤ q)
    (hcdfLower : cdf η (-q) = α / 2)
    (hcdfUpper : cdf η q = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | percentileCIEvent (linearRestrictionEstimate R β)
          (linearRestrictionEstimate R
              (olsBetaOrZero
                (stackRegressors X n ω) (stackOutcomes y n ω)) +
            bootstrapScalarLowerQuantileIndexed
              (fun n _ =>
                (ProbabilityTheory.uniformOn
                  (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                    Measure (Fin (n + 1) → Fin (n + 1))))
              (fun n ω ωs =>
                regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs)
              (α / 2) n ω / a n)
          (linearRestrictionEstimate R
              (olsBetaOrZero
                (stackRegressors X n ω) (stackOutcomes y n ω)) +
            bootstrapScalarLowerQuantileIndexed
              (fun n _ =>
                (ProbabilityTheory.uniformOn
                  (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                    Measure (Fin (n + 1) → Fin (n + 1))))
              (fun n ω ωs =>
                regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs)
              (1 - α / 2) n ω / a n)})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) := by
  have hPstar :
      ∀ n : ℕ, ∀ ω : Ω,
        IsProbabilityMeasure
          ((ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
              Measure (Fin (n + 1) → Fin (n + 1)))) := by
    intro n ω
    infer_instance
  have hTmeas :
      ∀ n : ℕ, ∀ ω : Ω,
        AEMeasurable
          (fun ωs =>
            regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs)
          ((ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
              Measure (Fin (n + 1) → Fin (n + 1)))) := by
    intro n ω
    exact (measurable_of_finite _).aemeasurable
  have hTstarRaw :
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
      β R hmodel h hΩ hRVR hLinBound hBetaBound hGapTail
  have hTstar :
      TendstoInBootstrapDistributionIndexed μ
        (fun n _ =>
          (ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
              Measure (Fin (n + 1) → Fin (n + 1))))
        (fun n ω ωs (_ : Unit) =>
          regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs)
        (multivariateGaussian (0 : EuclideanSpace ℝ Unit)
          (R * heteroAsymCov μ X e * Rᵀ))
        (fun z : EuclideanSpace ℝ Unit =>
          fun _ : Unit => (z : Unit → ℝ) ()) :=
    hTstarRaw.congr_limit (by
      intro z
      funext u
      cases u
      rfl)
  exact
    chapter10_indexed_percentileCI_coverage_bootstrapDistribution_law_quantile_prob_brackets
      (μ := μ) (ν := ν)
      (Ωstar := EuclideanSpace ℝ Unit) (η := η)
      (νstar := multivariateGaussian (0 : EuclideanSpace ℝ Unit)
        (R * heteroAsymCov μ X e * Rᵀ))
      (Zlim := fun z : EuclideanSpace ℝ Unit => (z : Unit → ℝ) ())
      (Pstar := fun n _ =>
        (ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))))
      (Tstar := fun n ω ωs =>
        regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs)
      (a := a) ha (θ := linearRestrictionEstimate R β)
      (θhat := fun n ω =>
        linearRestrictionEstimate R
          (olsBetaOrZero
            (stackRegressors X n ω) (stackOutcomes y n ω)))
      (ξ := ξ) (q := q) (α := α) hstat hPstar hTmeas hα_pos
      hα_lt_one hleftLower hrightLower hleftUpper hrightUpper hTstar
      hZlaw hcont hlower_meas hupper_meas hξ hq_nonneg hcdfLower
      hcdfUpper

set_option linter.style.longLine false in
/-- Strict-CDF finite OLS percentile-interval wrapper. -/
theorem
    chapter10_percentileCI_coverage_indexed_finSucc_olsBetaOrZero_gapEnvelope_bounds
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {k : Type*} [Fintype k] [DecidableEq k]
    {η : Measure ℝ} [IsProbabilityMeasure η] [NoAtoms η]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    {a : ℕ → ℝ} (ha : ∀ n, 0 < a n)
    {ξ : Ωlim → ℝ} {Clin Cbeta q α : ℝ}
    (β : k → ℝ) (R : Matrix Unit k ℝ)
    (hstat :
      TendstoInDistribution
        (fun n ω =>
          a n *
            (linearRestrictionEstimate R
                (olsBetaOrZero
                  (stackRegressors X n ω) (stackOutcomes y n ω)) -
              linearRestrictionEstimate R β))
        atTop ξ (fun _ => μ) ν)
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
        atTop (fun _ => 0))
    (hα_pos : 0 < α) (hα_lt_one : α < 1)
    (hstrict : StrictMono (fun x => cdf η x))
    (hcont : ∀ x : ℝ, ContinuousAt (fun y => cdf η y) x)
    (hlower_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed
            (fun n _ =>
              (ProbabilityTheory.uniformOn
                (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                  Measure (Fin (n + 1) → Fin (n + 1))))
            (fun n ω ωs =>
              regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs)
            (α / 2) n) μ)
    (hupper_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed
            (fun n _ =>
              (ProbabilityTheory.uniformOn
                (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                  Measure (Fin (n + 1) → Fin (n + 1))))
            (fun n ω ωs =>
              regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs)
            (1 - α / 2) n) μ)
    (hξ : HasLaw ξ η ν)
    (hZlaw :
      HasLaw
        (fun z : EuclideanSpace ℝ Unit => (z : Unit → ℝ) ()) η
        (multivariateGaussian (0 : EuclideanSpace ℝ Unit)
          (R * heteroAsymCov μ X e * Rᵀ)))
    (hq_nonneg : 0 ≤ q)
    (hcdfLower : cdf η (-q) = α / 2)
    (hcdfUpper : cdf η q = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | percentileCIEvent (linearRestrictionEstimate R β)
          (linearRestrictionEstimate R
              (olsBetaOrZero
                (stackRegressors X n ω) (stackOutcomes y n ω)) +
            bootstrapScalarLowerQuantileIndexed
              (fun n _ =>
                (ProbabilityTheory.uniformOn
                  (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                    Measure (Fin (n + 1) → Fin (n + 1))))
              (fun n ω ωs =>
                regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs)
              (α / 2) n ω / a n)
          (linearRestrictionEstimate R
              (olsBetaOrZero
                (stackRegressors X n ω) (stackOutcomes y n ω)) +
            bootstrapScalarLowerQuantileIndexed
              (fun n _ =>
                (ProbabilityTheory.uniformOn
                  (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                    Measure (Fin (n + 1) → Fin (n + 1))))
              (fun n ω ωs =>
                regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs)
              (1 - α / 2) n ω / a n)})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) := by
  obtain ⟨hleftLower, hrightLower⟩ :=
    strictMono_cdf_brackets hstrict hcdfLower
  obtain ⟨hleftUpper, hrightUpper⟩ :=
    strictMono_cdf_brackets hstrict hcdfUpper
  exact
    chapter10_percentileCI_coverage_indexed_finSucc_olsBetaOrZero_gapEnvelope_bounds_brackets
      (μ := μ) (ν := ν) (η := η) (X := X) (e := e) (y := y)
      ha β R hstat hmodel h hΩ hRVR hLinBound hBetaBound hGapTail
      hα_pos hα_lt_one hleftLower hrightLower hleftUpper hrightUpper
      hcont hlower_meas hupper_meas hξ hZlaw hq_nonneg hcdfLower
      hcdfUpper

set_option linter.style.longLine false in
/-- Robust-feasible HC specialization of the local-CDF finite OLS
percentile-interval wrapper. -/
theorem
    chapter10_percentileCI_coverage_indexed_finSucc_olsBetaOrZero_gapEnvelope_bounds_brackets_of_robustFeasibleHCMomentConditions
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {k : Type*} [Fintype k] [DecidableEq k]
    {η : Measure ℝ} [IsProbabilityMeasure η] [NoAtoms η]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    {a : ℕ → ℝ} (ha : ∀ n, 0 < a n)
    {ξ : Ωlim → ℝ} {Clin Cbeta q α : ℝ}
    (β : k → ℝ) (R : Matrix Unit k ℝ)
    (hstat :
      TendstoInDistribution
        (fun n ω =>
          a n *
            (linearRestrictionEstimate R
                (olsBetaOrZero
                  (stackRegressors X n ω) (stackOutcomes y n ω)) -
              linearRestrictionEstimate R β))
        atTop ξ (fun _ => μ) ν)
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
        atTop (fun _ => 0))
    (hα_pos : 0 < α) (hα_lt_one : α < 1)
    (hleftLower : ∀ ε : ℝ, 0 < ε → cdf η (-q - ε) < α / 2)
    (hrightLower : ∀ ε : ℝ, 0 < ε → α / 2 < cdf η (-q + ε))
    (hleftUpper : ∀ ε : ℝ, 0 < ε → cdf η (q - ε) < 1 - α / 2)
    (hrightUpper : ∀ ε : ℝ, 0 < ε → 1 - α / 2 < cdf η (q + ε))
    (hcont : ∀ x : ℝ, ContinuousAt (fun y => cdf η y) x)
    (hlower_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed
            (fun n _ =>
              (ProbabilityTheory.uniformOn
                (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                  Measure (Fin (n + 1) → Fin (n + 1))))
            (fun n ω ωs =>
              regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs)
            (α / 2) n) μ)
    (hupper_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed
            (fun n _ =>
              (ProbabilityTheory.uniformOn
                (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                  Measure (Fin (n + 1) → Fin (n + 1))))
            (fun n ω ωs =>
              regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs)
            (1 - α / 2) n) μ)
    (hξ : HasLaw ξ η ν)
    (hZlaw :
      HasLaw
        (fun z : EuclideanSpace ℝ Unit => (z : Unit → ℝ) ()) η
        (multivariateGaussian (0 : EuclideanSpace ℝ Unit)
          (R * heteroAsymCov μ X e * Rᵀ)))
    (hq_nonneg : 0 ≤ q)
    (hcdfLower : cdf η (-q) = α / 2)
    (hcdfUpper : cdf η q = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | percentileCIEvent (linearRestrictionEstimate R β)
          (linearRestrictionEstimate R
              (olsBetaOrZero
                (stackRegressors X n ω) (stackOutcomes y n ω)) +
            bootstrapScalarLowerQuantileIndexed
              (fun n _ =>
                (ProbabilityTheory.uniformOn
                  (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                    Measure (Fin (n + 1) → Fin (n + 1))))
              (fun n ω ωs =>
                regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs)
              (α / 2) n ω / a n)
          (linearRestrictionEstimate R
              (olsBetaOrZero
                (stackRegressors X n ω) (stackOutcomes y n ω)) +
            bootstrapScalarLowerQuantileIndexed
              (fun n _ =>
                (ProbabilityTheory.uniformOn
                  (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                    Measure (Fin (n + 1) → Fin (n + 1))))
              (fun n ω ωs =>
                regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs)
              (1 - α / 2) n ω / a n)})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) :=
  chapter10_percentileCI_coverage_indexed_finSucc_olsBetaOrZero_gapEnvelope_bounds_brackets
    (μ := μ) (ν := ν) (η := η) (X := X) (e := e) (y := y)
    ha β R hstat hm.model hm.toScoreCLTConditions hΩ hRVR hLinBound
    hBetaBound hGapTail hα_pos hα_lt_one hleftLower hrightLower
    hleftUpper hrightUpper hcont hlower_meas hupper_meas hξ hZlaw
    hq_nonneg hcdfLower hcdfUpper

set_option linter.style.longLine false in
/-- Robust-feasible HC specialization of the strict-CDF finite OLS
percentile-interval wrapper. -/
theorem
    chapter10_percentileCI_coverage_indexed_finSucc_olsBetaOrZero_gapEnvelope_bounds_of_robustFeasibleHCMomentConditions
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {k : Type*} [Fintype k] [DecidableEq k]
    {η : Measure ℝ} [IsProbabilityMeasure η] [NoAtoms η]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    {a : ℕ → ℝ} (ha : ∀ n, 0 < a n)
    {ξ : Ωlim → ℝ} {Clin Cbeta q α : ℝ}
    (β : k → ℝ) (R : Matrix Unit k ℝ)
    (hstat :
      TendstoInDistribution
        (fun n ω =>
          a n *
            (linearRestrictionEstimate R
                (olsBetaOrZero
                  (stackRegressors X n ω) (stackOutcomes y n ω)) -
              linearRestrictionEstimate R β))
        atTop ξ (fun _ => μ) ν)
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
        atTop (fun _ => 0))
    (hα_pos : 0 < α) (hα_lt_one : α < 1)
    (hstrict : StrictMono (fun x => cdf η x))
    (hcont : ∀ x : ℝ, ContinuousAt (fun y => cdf η y) x)
    (hlower_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed
            (fun n _ =>
              (ProbabilityTheory.uniformOn
                (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                  Measure (Fin (n + 1) → Fin (n + 1))))
            (fun n ω ωs =>
              regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs)
            (α / 2) n) μ)
    (hupper_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed
            (fun n _ =>
              (ProbabilityTheory.uniformOn
                (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                  Measure (Fin (n + 1) → Fin (n + 1))))
            (fun n ω ωs =>
              regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs)
            (1 - α / 2) n) μ)
    (hξ : HasLaw ξ η ν)
    (hZlaw :
      HasLaw
        (fun z : EuclideanSpace ℝ Unit => (z : Unit → ℝ) ()) η
        (multivariateGaussian (0 : EuclideanSpace ℝ Unit)
          (R * heteroAsymCov μ X e * Rᵀ)))
    (hq_nonneg : 0 ≤ q)
    (hcdfLower : cdf η (-q) = α / 2)
    (hcdfUpper : cdf η q = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | percentileCIEvent (linearRestrictionEstimate R β)
          (linearRestrictionEstimate R
              (olsBetaOrZero
                (stackRegressors X n ω) (stackOutcomes y n ω)) +
            bootstrapScalarLowerQuantileIndexed
              (fun n _ =>
                (ProbabilityTheory.uniformOn
                  (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                    Measure (Fin (n + 1) → Fin (n + 1))))
              (fun n ω ωs =>
                regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs)
              (α / 2) n ω / a n)
          (linearRestrictionEstimate R
              (olsBetaOrZero
                (stackRegressors X n ω) (stackOutcomes y n ω)) +
            bootstrapScalarLowerQuantileIndexed
              (fun n _ =>
                (ProbabilityTheory.uniformOn
                  (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                    Measure (Fin (n + 1) → Fin (n + 1))))
              (fun n ω ωs =>
                regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs)
              (1 - α / 2) n ω / a n)})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) :=
  chapter10_percentileCI_coverage_indexed_finSucc_olsBetaOrZero_gapEnvelope_bounds
    (μ := μ) (ν := ν) (η := η) (X := X) (e := e) (y := y)
    ha β R hstat hm.model hm.toScoreCLTConditions hΩ hRVR hLinBound
    hBetaBound hGapTail hα_pos hα_lt_one hstrict hcont hlower_meas
    hupper_meas hξ hZlaw hq_nonneg hcdfLower hcdfUpper

theorem tendstoInDistribution_congr_eventually
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    [TopologicalSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    {X Y : ℕ → Ω → E} {Z : Ωlim → E}
    (hY : ∀ n, AEMeasurable (Y n) μ)
    (hXY : ∀ᶠ n in atTop, X n =ᵐ[μ] Y n)
    (h : TendstoInDistribution X atTop Z (fun _ => μ) ν) :
    TendstoInDistribution Y atTop Z (fun _ => μ) ν where
  forall_aemeasurable := hY
  aemeasurable_limit := h.aemeasurable_limit
  tendsto := by
    refine Tendsto.congr' ?_ h.tendsto
    exact hXY.mono fun n hn => Subtype.ext (Measure.map_congr hn)

private theorem
    olsLinearRestrictionEstimate_tendstoInDistribution_gaussian_posRoot
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {k : Type*} [Fintype k] [DecidableEq k]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    (β : k → ℝ) (R : Matrix Unit k ℝ)
    {ξ : Ωlim → ℝ}
    (h : ScoreCLTConditions μ X e)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hξ :
      HasLaw ξ
        (gaussianReal 0
          (olsProjectionAsymVar μ X e
            (Rᵀ *ᵥ (fun _ : Unit => 1))).toNNReal) ν) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        (if n = 0 then 1 else Real.sqrt (n : ℝ)) *
          (linearRestrictionEstimate R
              (olsBetaOrZero
                (stackRegressors X n ω) (stackOutcomes y n ω)) -
            linearRestrictionEstimate R β))
      atTop ξ (fun _ => μ) ν := by
  let Xsample : ℕ → Ω → ℝ := fun n ω =>
    (Real.sqrt (n : ℝ) •
      (R *ᵥ
        (olsBetaOrZero (stackRegressors X n ω) (stackOutcomes y n ω) - β))) ⬝ᵥ
        (fun _ : Unit => 1)
  let Ysample : ℕ → Ω → ℝ := fun n ω =>
    (if n = 0 then 1 else Real.sqrt (n : ℝ)) *
      (linearRestrictionEstimate R
          (olsBetaOrZero (stackRegressors X n ω) (stackOutcomes y n ω)) -
        linearRestrictionEstimate R β)
  have hraw :
      TendstoInDistribution Xsample atTop ξ (fun _ => μ) ν := by
    simpa [Xsample] using
      scoreProj_linMap_olsBetaOrZero_tendstoInDistribution_gaussian_cov
        (μ := μ) (ν := ν) (X := X) (e := e) (y := y)
        h.toSampleCLTAssumption72 β R (fun _ : Unit => 1) hmodel hξ
  have hmeas : ∀ n, AEMeasurable (Ysample n) μ := by
    intro n
    have hbeta :
        AEStronglyMeasurable
          (fun ω =>
            olsBetaOrZero
              (stackRegressors X n ω) (stackOutcomes y n ω)) μ :=
      olsBetaOrZero_stack_aestronglyMeasurable
        (μ := μ) (X := X) (e := e) (y := y) β
        h.toLeastSquaresConsistencyConditions hmodel n
    have hθhat :
        AEMeasurable
          (fun ω =>
            linearRestrictionEstimate R
              (olsBetaOrZero
                (stackRegressors X n ω) (stackOutcomes y n ω))) μ := by
      have hcont :
          Continuous (fun b : k → ℝ => linearRestrictionEstimate R b) := by
        have hmul : Continuous (fun b : k → ℝ => R *ᵥ b) :=
          Continuous.matrix_mulVec
            (continuous_const : Continuous (fun _ : k → ℝ => R))
            (continuous_id : Continuous (fun b : k → ℝ => b))
        have hone :
            Continuous (fun _ : k → ℝ => (fun _ : Unit => (1 : ℝ))) :=
          continuous_const
        simpa [linearRestrictionEstimate] using
          hmul.dotProduct hone
      exact hcont.measurable.comp_aemeasurable hbeta.aemeasurable
    have hθ :
        AEMeasurable
          (fun _ : Ω => linearRestrictionEstimate R β) μ :=
      aemeasurable_const
    simpa [Ysample] using
      (hθhat.sub hθ).const_mul
        (if n = 0 then 1 else Real.sqrt (n : ℝ))
  have hcongr : ∀ᶠ n in atTop, Xsample n =ᵐ[μ] Ysample n := by
    filter_upwards [eventually_ne_atTop 0] with n hn
    refine ae_of_all μ fun ω => ?_
    dsimp [Xsample, Ysample, linearRestrictionEstimate]
    simp only [hn, if_false]
    rw [linearMapUnit_smul_sub_dot_one]
  simpa [Ysample] using
    tendstoInDistribution_congr_eventually
      (μ := μ) (ν := ν) (hY := hmeas) hcongr hraw

private theorem
    olsLinearRestriction_multivariateGaussian_coord_hasLaw
    [IsProbabilityMeasure μ]
    {k : Type*} [Fintype k] [DecidableEq k]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ}
    (R : Matrix Unit k ℝ)
    (h : ScoreCLTConditions μ X e) :
    HasLaw
      (fun z : EuclideanSpace ℝ Unit => (z : Unit → ℝ) ())
      (gaussianReal 0
        (olsProjectionAsymVar μ X e
          (Rᵀ *ᵥ (fun _ : Unit => 1))).toNNReal)
      (multivariateGaussian (0 : EuclideanSpace ℝ Unit)
        (R * heteroAsymCov μ X e * Rᵀ)) := by
  let S : Matrix Unit Unit ℝ := R * heteroAsymCov μ X e * Rᵀ
  have hS : S.PosSemidef := by
    have hVβ :
        (heteroAsymCov μ X e).PosSemidef :=
      heteroAsymCov_posSemidef_of_scoreCLTConditions
        (μ := μ) (X := X) (e := e) h
    simpa [S, Matrix.conjTranspose] using
      Matrix.PosSemidef.conjTranspose_mul_mul_same hVβ Rᵀ
  have hcoord :
      HasLaw (fun z : EuclideanSpace ℝ Unit => (z : Unit → ℝ) ())
        (gaussianReal 0 (S () ()).toNNReal)
        (multivariateGaussian (0 : EuclideanSpace ℝ Unit) S) := by
    simpa using
      (multivariateGaussian_eval_hasLaw (μ := (0 : EuclideanSpace ℝ Unit))
        (S := S) hS ())
  have hvar :
      S () () =
        olsProjectionAsymVar μ X e
          (Rᵀ *ᵥ (fun _ : Unit => 1)) := by
    simpa [S] using
      linMapCov_unit_apply_eq_olsProjectionAsymVar
        (μ := μ) (X := X) (e := e) h.int_outer R
  simpa [S, hvar] using hcoord

set_option linter.style.longLine false in
/-- Finite OLS percentile-interval wrapper with the sample-side OLS
linear-restriction CLT discharged by Chapter 7.

The scale is `if n = 0 then 1 else sqrt n`: it is positive for every `n`, as
required by the percentile endpoint API, and agrees eventually with Hansen's
usual `sqrt n` scaling. -/
theorem
    chapter10_percentileCI_coverage_indexed_finSucc_olsBetaOrZero_gapEnvelope_bounds_sampleCLT_brackets
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {k : Type*} [Fintype k] [DecidableEq k]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    {ξ : Ωlim → ℝ} {Clin Cbeta q α : ℝ}
    (β : k → ℝ) (R : Matrix Unit k ℝ)
    (hξ :
      HasLaw ξ
        (gaussianReal 0
          (olsProjectionAsymVar μ X e
            (Rᵀ *ᵥ (fun _ : Unit => 1))).toNNReal) ν)
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
        atTop (fun _ => 0))
    (hα_pos : 0 < α) (hα_lt_one : α < 1)
    (hleftLower :
      ∀ ε : ℝ, 0 < ε →
        cdf
          (gaussianReal 0
            (olsProjectionAsymVar μ X e
              (Rᵀ *ᵥ (fun _ : Unit => 1))).toNNReal)
          (-q - ε) < α / 2)
    (hrightLower :
      ∀ ε : ℝ, 0 < ε →
        α / 2 <
          cdf
            (gaussianReal 0
              (olsProjectionAsymVar μ X e
                (Rᵀ *ᵥ (fun _ : Unit => 1))).toNNReal)
            (-q + ε))
    (hleftUpper :
      ∀ ε : ℝ, 0 < ε →
        cdf
          (gaussianReal 0
            (olsProjectionAsymVar μ X e
              (Rᵀ *ᵥ (fun _ : Unit => 1))).toNNReal)
          (q - ε) < 1 - α / 2)
    (hrightUpper :
      ∀ ε : ℝ, 0 < ε →
        1 - α / 2 <
          cdf
            (gaussianReal 0
              (olsProjectionAsymVar μ X e
                (Rᵀ *ᵥ (fun _ : Unit => 1))).toNNReal)
            (q + ε))
    (hlower_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed
            (fun n _ =>
              (ProbabilityTheory.uniformOn
                (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                  Measure (Fin (n + 1) → Fin (n + 1))))
            (fun n ω ωs =>
              regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs)
            (α / 2) n) μ)
    (hupper_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed
            (fun n _ =>
              (ProbabilityTheory.uniformOn
                (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                  Measure (Fin (n + 1) → Fin (n + 1))))
            (fun n ω ωs =>
              regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs)
            (1 - α / 2) n) μ)
    (hq_nonneg : 0 ≤ q)
    (hcdfLower :
      cdf
        (gaussianReal 0
          (olsProjectionAsymVar μ X e
            (Rᵀ *ᵥ (fun _ : Unit => 1))).toNNReal)
        (-q) = α / 2)
    (hcdfUpper :
      cdf
        (gaussianReal 0
          (olsProjectionAsymVar μ X e
            (Rᵀ *ᵥ (fun _ : Unit => 1))).toNNReal)
        q = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | percentileCIEvent (linearRestrictionEstimate R β)
          (linearRestrictionEstimate R
              (olsBetaOrZero
                (stackRegressors X n ω) (stackOutcomes y n ω)) +
            bootstrapScalarLowerQuantileIndexed
              (fun n _ =>
                (ProbabilityTheory.uniformOn
                  (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                    Measure (Fin (n + 1) → Fin (n + 1))))
              (fun n ω ωs =>
                regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs)
              (α / 2) n ω /
                (if n = 0 then 1 else Real.sqrt (n : ℝ)))
          (linearRestrictionEstimate R
              (olsBetaOrZero
                (stackRegressors X n ω) (stackOutcomes y n ω)) +
            bootstrapScalarLowerQuantileIndexed
              (fun n _ =>
                (ProbabilityTheory.uniformOn
                  (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                    Measure (Fin (n + 1) → Fin (n + 1))))
              (fun n ω ωs =>
                regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs)
              (1 - α / 2) n ω /
                (if n = 0 then 1 else Real.sqrt (n : ℝ)))})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) := by
  let a : ℕ → ℝ := fun n => if n = 0 then 1 else Real.sqrt (n : ℝ)
  have ha : ∀ n, 0 < a n := by
    intro n
    by_cases hn : n = 0
    · simp [a, hn]
    · have hnpos : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
      simp [a, hn, Real.sqrt_pos.2 hnpos]
  have hstat :
      TendstoInDistribution
        (fun n ω =>
          a n *
            (linearRestrictionEstimate R
                (olsBetaOrZero
                  (stackRegressors X n ω) (stackOutcomes y n ω)) -
              linearRestrictionEstimate R β))
        atTop ξ (fun _ => μ) ν := by
    simpa [a] using
      olsLinearRestrictionEstimate_tendstoInDistribution_gaussian_posRoot
        (μ := μ) (ν := ν) (X := X) (e := e) (y := y)
        β R h hmodel hξ
  have hZlaw :
      HasLaw
        (fun z : EuclideanSpace ℝ Unit => (z : Unit → ℝ) ())
        (gaussianReal 0
          (olsProjectionAsymVar μ X e
            (Rᵀ *ᵥ (fun _ : Unit => 1))).toNNReal)
        (multivariateGaussian (0 : EuclideanSpace ℝ Unit)
          (R * heteroAsymCov μ X e * Rᵀ)) :=
    olsLinearRestriction_multivariateGaussian_coord_hasLaw
      (μ := μ) (X := X) (e := e) R h
  have hvar_pos :
      0 <
        olsProjectionAsymVar μ X e
          (Rᵀ *ᵥ (fun _ : Unit => 1)) := by
    have hentry : 0 < (R * heteroAsymCov μ X e * Rᵀ) () () :=
      hRVR.diag_pos
    have hvar_eq :
        (R * heteroAsymCov μ X e * Rᵀ) () () =
          olsProjectionAsymVar μ X e
            (Rᵀ *ᵥ (fun _ : Unit => 1)) := by
      exact linMapCov_unit_apply_eq_olsProjectionAsymVar
        (μ := μ) (X := X) (e := e) h.int_outer R
    simpa [hvar_eq] using hentry
  haveI :
      NoAtoms
        (gaussianReal 0
          (olsProjectionAsymVar μ X e
            (Rᵀ *ᵥ (fun _ : Unit => 1))).toNNReal) :=
    noAtoms_gaussianReal (ne_of_gt (Real.toNNReal_pos.mpr hvar_pos))
  exact
    chapter10_percentileCI_coverage_indexed_finSucc_olsBetaOrZero_gapEnvelope_bounds_brackets
      (μ := μ) (ν := ν)
      (η := gaussianReal 0
        (olsProjectionAsymVar μ X e
          (Rᵀ *ᵥ (fun _ : Unit => 1))).toNNReal)
      (X := X) (e := e) (y := y)
      (a := a) ha β R hstat hmodel h hΩ hRVR hLinBound hBetaBound
      hGapTail hα_pos hα_lt_one hleftLower hrightLower hleftUpper
      hrightUpper
      (fun x =>
        continuousAt_cdf_gaussianReal
          (m := 0)
          (v :=
            (olsProjectionAsymVar μ X e
              (Rᵀ *ᵥ (fun _ : Unit => 1))).toNNReal)
          (ne_of_gt (Real.toNNReal_pos.mpr hvar_pos)) x)
      hlower_meas hupper_meas hξ hZlaw hq_nonneg hcdfLower hcdfUpper

set_option linter.style.longLine false in
/-- Direct Gaussian-law version of the local-CDF finite OLS
percentile-interval wrapper whose sample-side OLS linear-restriction CLT is
supplied by Chapter 7.

This fixes the auxiliary limit space to the Gaussian law itself and the limit
random variable to the identity map, while retaining local CDF bracketing at
the percentile endpoints. -/
theorem
    chapter10_percentileCI_coverage_indexed_finSucc_olsBetaOrZero_gapEnvelope_bounds_sampleCLT_brackets_gaussian
    [IsProbabilityMeasure μ]
    {k : Type*} [Fintype k] [DecidableEq k]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    {Clin Cbeta q α : ℝ}
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
        atTop (fun _ => 0))
    (hα_pos : 0 < α) (hα_lt_one : α < 1)
    (hleftLower :
      ∀ ε : ℝ, 0 < ε →
        cdf
          (gaussianReal 0
            (olsProjectionAsymVar μ X e
              (Rᵀ *ᵥ (fun _ : Unit => 1))).toNNReal)
          (-q - ε) < α / 2)
    (hrightLower :
      ∀ ε : ℝ, 0 < ε →
        α / 2 <
          cdf
            (gaussianReal 0
              (olsProjectionAsymVar μ X e
                (Rᵀ *ᵥ (fun _ : Unit => 1))).toNNReal)
            (-q + ε))
    (hleftUpper :
      ∀ ε : ℝ, 0 < ε →
        cdf
          (gaussianReal 0
            (olsProjectionAsymVar μ X e
              (Rᵀ *ᵥ (fun _ : Unit => 1))).toNNReal)
          (q - ε) < 1 - α / 2)
    (hrightUpper :
      ∀ ε : ℝ, 0 < ε →
        1 - α / 2 <
          cdf
            (gaussianReal 0
              (olsProjectionAsymVar μ X e
                (Rᵀ *ᵥ (fun _ : Unit => 1))).toNNReal)
            (q + ε))
    (hlower_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed
            (fun n _ =>
              (ProbabilityTheory.uniformOn
                (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                  Measure (Fin (n + 1) → Fin (n + 1))))
            (fun n ω ωs =>
              regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs)
            (α / 2) n) μ)
    (hupper_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed
            (fun n _ =>
              (ProbabilityTheory.uniformOn
                (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                  Measure (Fin (n + 1) → Fin (n + 1))))
            (fun n ω ωs =>
              regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs)
            (1 - α / 2) n) μ)
    (hq_nonneg : 0 ≤ q)
    (hcdfLower :
      cdf
        (gaussianReal 0
          (olsProjectionAsymVar μ X e
            (Rᵀ *ᵥ (fun _ : Unit => 1))).toNNReal)
        (-q) = α / 2)
    (hcdfUpper :
      cdf
        (gaussianReal 0
          (olsProjectionAsymVar μ X e
            (Rᵀ *ᵥ (fun _ : Unit => 1))).toNNReal)
        q = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | percentileCIEvent (linearRestrictionEstimate R β)
          (linearRestrictionEstimate R
              (olsBetaOrZero
                (stackRegressors X n ω) (stackOutcomes y n ω)) +
            bootstrapScalarLowerQuantileIndexed
              (fun n _ =>
                (ProbabilityTheory.uniformOn
                  (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                    Measure (Fin (n + 1) → Fin (n + 1))))
              (fun n ω ωs =>
                regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs)
              (α / 2) n ω /
                (if n = 0 then 1 else Real.sqrt (n : ℝ)))
          (linearRestrictionEstimate R
              (olsBetaOrZero
                (stackRegressors X n ω) (stackOutcomes y n ω)) +
            bootstrapScalarLowerQuantileIndexed
              (fun n _ =>
                (ProbabilityTheory.uniformOn
                  (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                    Measure (Fin (n + 1) → Fin (n + 1))))
              (fun n ω ωs =>
                regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs)
              (1 - α / 2) n ω /
                (if n = 0 then 1 else Real.sqrt (n : ℝ)))})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) := by
  have hξ :
      HasLaw (fun x : ℝ => x)
        (gaussianReal 0
          (olsProjectionAsymVar μ X e
            (Rᵀ *ᵥ (fun _ : Unit => 1))).toNNReal)
        (gaussianReal 0
          (olsProjectionAsymVar μ X e
            (Rᵀ *ᵥ (fun _ : Unit => 1))).toNNReal) := by
    simpa [id] using
      (HasLaw.id
        (μ := gaussianReal 0
          (olsProjectionAsymVar μ X e
            (Rᵀ *ᵥ (fun _ : Unit => 1))).toNNReal))
  exact
    chapter10_percentileCI_coverage_indexed_finSucc_olsBetaOrZero_gapEnvelope_bounds_sampleCLT_brackets
      (μ := μ)
      (ν := gaussianReal 0
        (olsProjectionAsymVar μ X e
          (Rᵀ *ᵥ (fun _ : Unit => 1))).toNNReal)
      (X := X) (e := e) (y := y)
      β R hξ hmodel h hΩ hRVR hLinBound hBetaBound hGapTail
      hα_pos hα_lt_one hleftLower hrightLower hleftUpper hrightUpper
      hlower_meas hupper_meas hq_nonneg hcdfLower hcdfUpper

set_option linter.style.longLine false in
/-- Strict-CDF version of the finite OLS percentile-interval wrapper whose
sample-side OLS linear-restriction CLT is supplied by Chapter 7. -/
theorem
    chapter10_percentileCI_coverage_indexed_finSucc_olsBetaOrZero_gapEnvelope_bounds_sampleCLT
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {k : Type*} [Fintype k] [DecidableEq k]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    {ξ : Ωlim → ℝ} {Clin Cbeta q α : ℝ}
    (β : k → ℝ) (R : Matrix Unit k ℝ)
    (hξ :
      HasLaw ξ
        (gaussianReal 0
          (olsProjectionAsymVar μ X e
            (Rᵀ *ᵥ (fun _ : Unit => 1))).toNNReal) ν)
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
        atTop (fun _ => 0))
    (hα_pos : 0 < α) (hα_lt_one : α < 1)
    (hstrict :
      StrictMono
        (fun x =>
          cdf
            (gaussianReal 0
              (olsProjectionAsymVar μ X e
                (Rᵀ *ᵥ (fun _ : Unit => 1))).toNNReal) x))
    (hlower_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed
            (fun n _ =>
              (ProbabilityTheory.uniformOn
                (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                  Measure (Fin (n + 1) → Fin (n + 1))))
            (fun n ω ωs =>
              regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs)
            (α / 2) n) μ)
    (hupper_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed
            (fun n _ =>
              (ProbabilityTheory.uniformOn
                (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                  Measure (Fin (n + 1) → Fin (n + 1))))
            (fun n ω ωs =>
              regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs)
            (1 - α / 2) n) μ)
    (hq_nonneg : 0 ≤ q)
    (hcdfLower :
      cdf
        (gaussianReal 0
          (olsProjectionAsymVar μ X e
            (Rᵀ *ᵥ (fun _ : Unit => 1))).toNNReal)
        (-q) = α / 2)
    (hcdfUpper :
      cdf
        (gaussianReal 0
          (olsProjectionAsymVar μ X e
            (Rᵀ *ᵥ (fun _ : Unit => 1))).toNNReal)
        q = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | percentileCIEvent (linearRestrictionEstimate R β)
          (linearRestrictionEstimate R
              (olsBetaOrZero
                (stackRegressors X n ω) (stackOutcomes y n ω)) +
            bootstrapScalarLowerQuantileIndexed
              (fun n _ =>
                (ProbabilityTheory.uniformOn
                  (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                    Measure (Fin (n + 1) → Fin (n + 1))))
              (fun n ω ωs =>
                regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs)
              (α / 2) n ω /
                (if n = 0 then 1 else Real.sqrt (n : ℝ)))
          (linearRestrictionEstimate R
              (olsBetaOrZero
                (stackRegressors X n ω) (stackOutcomes y n ω)) +
            bootstrapScalarLowerQuantileIndexed
              (fun n _ =>
                (ProbabilityTheory.uniformOn
                  (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                    Measure (Fin (n + 1) → Fin (n + 1))))
              (fun n ω ωs =>
                regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs)
              (1 - α / 2) n ω /
                (if n = 0 then 1 else Real.sqrt (n : ℝ)))})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) := by
  obtain ⟨hleftLower, hrightLower⟩ :=
    strictMono_cdf_brackets hstrict hcdfLower
  obtain ⟨hleftUpper, hrightUpper⟩ :=
    strictMono_cdf_brackets hstrict hcdfUpper
  exact
    chapter10_percentileCI_coverage_indexed_finSucc_olsBetaOrZero_gapEnvelope_bounds_sampleCLT_brackets
      (μ := μ) (ν := ν) (X := X) (e := e) (y := y)
      β R hξ hmodel h hΩ hRVR hLinBound hBetaBound hGapTail
      hα_pos hα_lt_one hleftLower hrightLower hleftUpper hrightUpper
      hlower_meas hupper_meas hq_nonneg hcdfLower hcdfUpper

set_option linter.style.longLine false in
/-- Robust-feasible HC specialization of the local-CDF finite OLS
percentile-interval wrapper whose sample-side OLS linear-restriction CLT is
supplied by Chapter 7. -/
theorem
    chapter10_percentileCI_coverage_indexed_finSucc_olsBetaOrZero_gapEnvelope_bounds_sampleCLT_brackets_of_robustFeasibleHCMomentConditions
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {k : Type*} [Fintype k] [DecidableEq k]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    {ξ : Ωlim → ℝ} {Clin Cbeta q α : ℝ}
    (β : k → ℝ) (R : Matrix Unit k ℝ)
    (hξ :
      HasLaw ξ
        (gaussianReal 0
          (olsProjectionAsymVar μ X e
            (Rᵀ *ᵥ (fun _ : Unit => 1))).toNNReal) ν)
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
        atTop (fun _ => 0))
    (hα_pos : 0 < α) (hα_lt_one : α < 1)
    (hleftLower :
      ∀ ε : ℝ, 0 < ε →
        cdf
          (gaussianReal 0
            (olsProjectionAsymVar μ X e
              (Rᵀ *ᵥ (fun _ : Unit => 1))).toNNReal)
          (-q - ε) < α / 2)
    (hrightLower :
      ∀ ε : ℝ, 0 < ε →
        α / 2 <
          cdf
            (gaussianReal 0
              (olsProjectionAsymVar μ X e
                (Rᵀ *ᵥ (fun _ : Unit => 1))).toNNReal)
            (-q + ε))
    (hleftUpper :
      ∀ ε : ℝ, 0 < ε →
        cdf
          (gaussianReal 0
            (olsProjectionAsymVar μ X e
              (Rᵀ *ᵥ (fun _ : Unit => 1))).toNNReal)
          (q - ε) < 1 - α / 2)
    (hrightUpper :
      ∀ ε : ℝ, 0 < ε →
        1 - α / 2 <
          cdf
            (gaussianReal 0
              (olsProjectionAsymVar μ X e
                (Rᵀ *ᵥ (fun _ : Unit => 1))).toNNReal)
            (q + ε))
    (hlower_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed
            (fun n _ =>
              (ProbabilityTheory.uniformOn
                (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                  Measure (Fin (n + 1) → Fin (n + 1))))
            (fun n ω ωs =>
              regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs)
            (α / 2) n) μ)
    (hupper_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed
            (fun n _ =>
              (ProbabilityTheory.uniformOn
                (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                  Measure (Fin (n + 1) → Fin (n + 1))))
            (fun n ω ωs =>
              regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs)
            (1 - α / 2) n) μ)
    (hq_nonneg : 0 ≤ q)
    (hcdfLower :
      cdf
        (gaussianReal 0
          (olsProjectionAsymVar μ X e
            (Rᵀ *ᵥ (fun _ : Unit => 1))).toNNReal)
        (-q) = α / 2)
    (hcdfUpper :
      cdf
        (gaussianReal 0
          (olsProjectionAsymVar μ X e
            (Rᵀ *ᵥ (fun _ : Unit => 1))).toNNReal)
        q = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | percentileCIEvent (linearRestrictionEstimate R β)
          (linearRestrictionEstimate R
              (olsBetaOrZero
                (stackRegressors X n ω) (stackOutcomes y n ω)) +
            bootstrapScalarLowerQuantileIndexed
              (fun n _ =>
                (ProbabilityTheory.uniformOn
                  (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                    Measure (Fin (n + 1) → Fin (n + 1))))
              (fun n ω ωs =>
                regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs)
              (α / 2) n ω /
                (if n = 0 then 1 else Real.sqrt (n : ℝ)))
          (linearRestrictionEstimate R
              (olsBetaOrZero
                (stackRegressors X n ω) (stackOutcomes y n ω)) +
            bootstrapScalarLowerQuantileIndexed
              (fun n _ =>
                (ProbabilityTheory.uniformOn
                  (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                    Measure (Fin (n + 1) → Fin (n + 1))))
              (fun n ω ωs =>
                regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs)
              (1 - α / 2) n ω /
                (if n = 0 then 1 else Real.sqrt (n : ℝ)))})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) :=
  chapter10_percentileCI_coverage_indexed_finSucc_olsBetaOrZero_gapEnvelope_bounds_sampleCLT_brackets
    (μ := μ) (ν := ν) (X := X) (e := e) (y := y)
    β R hξ hm.model hm.toScoreCLTConditions hΩ hRVR hLinBound
    hBetaBound hGapTail hα_pos hα_lt_one hleftLower hrightLower
    hleftUpper hrightUpper hlower_meas hupper_meas hq_nonneg hcdfLower
    hcdfUpper

set_option linter.style.longLine false in
/-- Robust-feasible HC specialization of the direct Gaussian-law local-CDF
finite OLS percentile-interval wrapper whose sample-side OLS
linear-restriction CLT is supplied by Chapter 7. -/
theorem
    chapter10_percentileCI_coverage_indexed_finSucc_olsBetaOrZero_gapEnvelope_bounds_sampleCLT_brackets_gaussian_of_robustFeasibleHCMomentConditions
    [IsProbabilityMeasure μ]
    {k : Type*} [Fintype k] [DecidableEq k]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    {Clin Cbeta q α : ℝ}
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
        atTop (fun _ => 0))
    (hα_pos : 0 < α) (hα_lt_one : α < 1)
    (hleftLower :
      ∀ ε : ℝ, 0 < ε →
        cdf
          (gaussianReal 0
            (olsProjectionAsymVar μ X e
              (Rᵀ *ᵥ (fun _ : Unit => 1))).toNNReal)
          (-q - ε) < α / 2)
    (hrightLower :
      ∀ ε : ℝ, 0 < ε →
        α / 2 <
          cdf
            (gaussianReal 0
              (olsProjectionAsymVar μ X e
                (Rᵀ *ᵥ (fun _ : Unit => 1))).toNNReal)
            (-q + ε))
    (hleftUpper :
      ∀ ε : ℝ, 0 < ε →
        cdf
          (gaussianReal 0
            (olsProjectionAsymVar μ X e
              (Rᵀ *ᵥ (fun _ : Unit => 1))).toNNReal)
          (q - ε) < 1 - α / 2)
    (hrightUpper :
      ∀ ε : ℝ, 0 < ε →
        1 - α / 2 <
          cdf
            (gaussianReal 0
              (olsProjectionAsymVar μ X e
                (Rᵀ *ᵥ (fun _ : Unit => 1))).toNNReal)
            (q + ε))
    (hlower_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed
            (fun n _ =>
              (ProbabilityTheory.uniformOn
                (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                  Measure (Fin (n + 1) → Fin (n + 1))))
            (fun n ω ωs =>
              regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs)
            (α / 2) n) μ)
    (hupper_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed
            (fun n _ =>
              (ProbabilityTheory.uniformOn
                (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                  Measure (Fin (n + 1) → Fin (n + 1))))
            (fun n ω ωs =>
              regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs)
            (1 - α / 2) n) μ)
    (hq_nonneg : 0 ≤ q)
    (hcdfLower :
      cdf
        (gaussianReal 0
          (olsProjectionAsymVar μ X e
            (Rᵀ *ᵥ (fun _ : Unit => 1))).toNNReal)
        (-q) = α / 2)
    (hcdfUpper :
      cdf
        (gaussianReal 0
          (olsProjectionAsymVar μ X e
            (Rᵀ *ᵥ (fun _ : Unit => 1))).toNNReal)
        q = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | percentileCIEvent (linearRestrictionEstimate R β)
          (linearRestrictionEstimate R
              (olsBetaOrZero
                (stackRegressors X n ω) (stackOutcomes y n ω)) +
            bootstrapScalarLowerQuantileIndexed
              (fun n _ =>
                (ProbabilityTheory.uniformOn
                  (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                    Measure (Fin (n + 1) → Fin (n + 1))))
              (fun n ω ωs =>
                regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs)
              (α / 2) n ω /
                (if n = 0 then 1 else Real.sqrt (n : ℝ)))
          (linearRestrictionEstimate R
              (olsBetaOrZero
                (stackRegressors X n ω) (stackOutcomes y n ω)) +
            bootstrapScalarLowerQuantileIndexed
              (fun n _ =>
                (ProbabilityTheory.uniformOn
                  (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                    Measure (Fin (n + 1) → Fin (n + 1))))
              (fun n ω ωs =>
                regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs)
              (1 - α / 2) n ω /
                (if n = 0 then 1 else Real.sqrt (n : ℝ)))})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) :=
  chapter10_percentileCI_coverage_indexed_finSucc_olsBetaOrZero_gapEnvelope_bounds_sampleCLT_brackets_gaussian
    (μ := μ) (X := X) (e := e) (y := y)
    β R hm.model hm.toScoreCLTConditions hΩ hRVR hLinBound hBetaBound
    hGapTail hα_pos hα_lt_one hleftLower hrightLower hleftUpper
    hrightUpper hlower_meas hupper_meas hq_nonneg hcdfLower hcdfUpper

set_option linter.style.longLine false in
/-- Robust-feasible HC specialization of the strict-CDF finite OLS
percentile-interval wrapper whose sample-side OLS linear-restriction CLT is
supplied by Chapter 7. -/
theorem
    chapter10_percentileCI_coverage_indexed_finSucc_olsBetaOrZero_gapEnvelope_bounds_sampleCLT_of_robustFeasibleHCMomentConditions
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {k : Type*} [Fintype k] [DecidableEq k]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    {ξ : Ωlim → ℝ} {Clin Cbeta q α : ℝ}
    (β : k → ℝ) (R : Matrix Unit k ℝ)
    (hξ :
      HasLaw ξ
        (gaussianReal 0
          (olsProjectionAsymVar μ X e
            (Rᵀ *ᵥ (fun _ : Unit => 1))).toNNReal) ν)
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
        atTop (fun _ => 0))
    (hα_pos : 0 < α) (hα_lt_one : α < 1)
    (hstrict :
      StrictMono
        (fun x =>
          cdf
            (gaussianReal 0
              (olsProjectionAsymVar μ X e
                (Rᵀ *ᵥ (fun _ : Unit => 1))).toNNReal) x))
    (hlower_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed
            (fun n _ =>
              (ProbabilityTheory.uniformOn
                (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                  Measure (Fin (n + 1) → Fin (n + 1))))
            (fun n ω ωs =>
              regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs)
            (α / 2) n) μ)
    (hupper_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed
            (fun n _ =>
              (ProbabilityTheory.uniformOn
                (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                  Measure (Fin (n + 1) → Fin (n + 1))))
            (fun n ω ωs =>
              regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs)
            (1 - α / 2) n) μ)
    (hq_nonneg : 0 ≤ q)
    (hcdfLower :
      cdf
        (gaussianReal 0
          (olsProjectionAsymVar μ X e
            (Rᵀ *ᵥ (fun _ : Unit => 1))).toNNReal)
        (-q) = α / 2)
    (hcdfUpper :
      cdf
        (gaussianReal 0
          (olsProjectionAsymVar μ X e
            (Rᵀ *ᵥ (fun _ : Unit => 1))).toNNReal)
        q = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | percentileCIEvent (linearRestrictionEstimate R β)
          (linearRestrictionEstimate R
              (olsBetaOrZero
                (stackRegressors X n ω) (stackOutcomes y n ω)) +
            bootstrapScalarLowerQuantileIndexed
              (fun n _ =>
                (ProbabilityTheory.uniformOn
                  (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                    Measure (Fin (n + 1) → Fin (n + 1))))
              (fun n ω ωs =>
                regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs)
              (α / 2) n ω /
                (if n = 0 then 1 else Real.sqrt (n : ℝ)))
          (linearRestrictionEstimate R
              (olsBetaOrZero
                (stackRegressors X n ω) (stackOutcomes y n ω)) +
            bootstrapScalarLowerQuantileIndexed
              (fun n _ =>
                (ProbabilityTheory.uniformOn
                  (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                    Measure (Fin (n + 1) → Fin (n + 1))))
              (fun n ω ωs =>
                regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs)
              (1 - α / 2) n ω /
                (if n = 0 then 1 else Real.sqrt (n : ℝ)))})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) :=
  chapter10_percentileCI_coverage_indexed_finSucc_olsBetaOrZero_gapEnvelope_bounds_sampleCLT
    (μ := μ) (ν := ν) (X := X) (e := e) (y := y)
    β R hξ hm.model hm.toScoreCLTConditions hΩ hRVR hLinBound
    hBetaBound hGapTail hα_pos hα_lt_one hstrict hlower_meas hupper_meas
    hq_nonneg hcdfLower hcdfUpper

set_option linter.style.longLine false in
/-- Direct Gaussian-law version of the strict-CDF finite OLS percentile-interval
wrapper whose sample-side OLS linear-restriction CLT is supplied by Chapter 7.

This fixes the auxiliary limit space to the Gaussian law itself and the limit
random variable to the identity map. -/
theorem
    chapter10_percentileCI_coverage_indexed_finSucc_olsBetaOrZero_gapEnvelope_bounds_sampleCLT_gaussian
    [IsProbabilityMeasure μ]
    {k : Type*} [Fintype k] [DecidableEq k]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    {Clin Cbeta q α : ℝ}
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
        atTop (fun _ => 0))
    (hα_pos : 0 < α) (hα_lt_one : α < 1)
    (hstrict :
      StrictMono
        (fun x =>
          cdf
            (gaussianReal 0
              (olsProjectionAsymVar μ X e
                (Rᵀ *ᵥ (fun _ : Unit => 1))).toNNReal) x))
    (hlower_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed
            (fun n _ =>
              (ProbabilityTheory.uniformOn
                (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                  Measure (Fin (n + 1) → Fin (n + 1))))
            (fun n ω ωs =>
              regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs)
            (α / 2) n) μ)
    (hupper_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed
            (fun n _ =>
              (ProbabilityTheory.uniformOn
                (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                  Measure (Fin (n + 1) → Fin (n + 1))))
            (fun n ω ωs =>
              regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs)
            (1 - α / 2) n) μ)
    (hq_nonneg : 0 ≤ q)
    (hcdfLower :
      cdf
        (gaussianReal 0
          (olsProjectionAsymVar μ X e
            (Rᵀ *ᵥ (fun _ : Unit => 1))).toNNReal)
        (-q) = α / 2)
    (hcdfUpper :
      cdf
        (gaussianReal 0
          (olsProjectionAsymVar μ X e
            (Rᵀ *ᵥ (fun _ : Unit => 1))).toNNReal)
        q = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | percentileCIEvent (linearRestrictionEstimate R β)
          (linearRestrictionEstimate R
              (olsBetaOrZero
                (stackRegressors X n ω) (stackOutcomes y n ω)) +
            bootstrapScalarLowerQuantileIndexed
              (fun n _ =>
                (ProbabilityTheory.uniformOn
                  (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                    Measure (Fin (n + 1) → Fin (n + 1))))
              (fun n ω ωs =>
                regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs)
              (α / 2) n ω /
                (if n = 0 then 1 else Real.sqrt (n : ℝ)))
          (linearRestrictionEstimate R
              (olsBetaOrZero
                (stackRegressors X n ω) (stackOutcomes y n ω)) +
            bootstrapScalarLowerQuantileIndexed
              (fun n _ =>
                (ProbabilityTheory.uniformOn
                  (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                    Measure (Fin (n + 1) → Fin (n + 1))))
              (fun n ω ωs =>
                regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs)
              (1 - α / 2) n ω /
                (if n = 0 then 1 else Real.sqrt (n : ℝ)))})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) := by
  have hξ :
      HasLaw (fun x : ℝ => x)
        (gaussianReal 0
          (olsProjectionAsymVar μ X e
            (Rᵀ *ᵥ (fun _ : Unit => 1))).toNNReal)
        (gaussianReal 0
          (olsProjectionAsymVar μ X e
            (Rᵀ *ᵥ (fun _ : Unit => 1))).toNNReal) := by
    simpa [id] using
      (HasLaw.id
        (μ := gaussianReal 0
          (olsProjectionAsymVar μ X e
            (Rᵀ *ᵥ (fun _ : Unit => 1))).toNNReal))
  exact
    chapter10_percentileCI_coverage_indexed_finSucc_olsBetaOrZero_gapEnvelope_bounds_sampleCLT
      (μ := μ)
      (ν := gaussianReal 0
        (olsProjectionAsymVar μ X e
          (Rᵀ *ᵥ (fun _ : Unit => 1))).toNNReal)
      (X := X) (e := e) (y := y)
      β R hξ hmodel h hΩ hRVR hLinBound hBetaBound hGapTail
      hα_pos hα_lt_one hstrict hlower_meas hupper_meas hq_nonneg hcdfLower
      hcdfUpper

set_option linter.style.longLine false in
/-- Robust-feasible HC specialization of the direct Gaussian-law strict-CDF
finite OLS percentile-interval wrapper whose sample-side OLS
linear-restriction CLT is supplied by Chapter 7. -/
theorem
    chapter10_percentileCI_coverage_indexed_finSucc_olsBetaOrZero_gapEnvelope_bounds_sampleCLT_gaussian_of_robustFeasibleHCMomentConditions
    [IsProbabilityMeasure μ]
    {k : Type*} [Fintype k] [DecidableEq k]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    {Clin Cbeta q α : ℝ}
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
        atTop (fun _ => 0))
    (hα_pos : 0 < α) (hα_lt_one : α < 1)
    (hstrict :
      StrictMono
        (fun x =>
          cdf
            (gaussianReal 0
              (olsProjectionAsymVar μ X e
                (Rᵀ *ᵥ (fun _ : Unit => 1))).toNNReal) x))
    (hlower_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed
            (fun n _ =>
              (ProbabilityTheory.uniformOn
                (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                  Measure (Fin (n + 1) → Fin (n + 1))))
            (fun n ω ωs =>
              regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs)
            (α / 2) n) μ)
    (hupper_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed
            (fun n _ =>
              (ProbabilityTheory.uniformOn
                (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                  Measure (Fin (n + 1) → Fin (n + 1))))
            (fun n ω ωs =>
              regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs)
            (1 - α / 2) n) μ)
    (hq_nonneg : 0 ≤ q)
    (hcdfLower :
      cdf
        (gaussianReal 0
          (olsProjectionAsymVar μ X e
            (Rᵀ *ᵥ (fun _ : Unit => 1))).toNNReal)
        (-q) = α / 2)
    (hcdfUpper :
      cdf
        (gaussianReal 0
          (olsProjectionAsymVar μ X e
            (Rᵀ *ᵥ (fun _ : Unit => 1))).toNNReal)
        q = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | percentileCIEvent (linearRestrictionEstimate R β)
          (linearRestrictionEstimate R
              (olsBetaOrZero
                (stackRegressors X n ω) (stackOutcomes y n ω)) +
            bootstrapScalarLowerQuantileIndexed
              (fun n _ =>
                (ProbabilityTheory.uniformOn
                  (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                    Measure (Fin (n + 1) → Fin (n + 1))))
              (fun n ω ωs =>
                regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs)
              (α / 2) n ω /
                (if n = 0 then 1 else Real.sqrt (n : ℝ)))
          (linearRestrictionEstimate R
              (olsBetaOrZero
                (stackRegressors X n ω) (stackOutcomes y n ω)) +
            bootstrapScalarLowerQuantileIndexed
              (fun n _ =>
                (ProbabilityTheory.uniformOn
                  (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                    Measure (Fin (n + 1) → Fin (n + 1))))
              (fun n ω ωs =>
                regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs)
              (1 - α / 2) n ω /
                (if n = 0 then 1 else Real.sqrt (n : ℝ)))})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) :=
  chapter10_percentileCI_coverage_indexed_finSucc_olsBetaOrZero_gapEnvelope_bounds_sampleCLT_gaussian
    (μ := μ) (X := X) (e := e) (y := y)
    β R hm.model hm.toScoreCLTConditions hΩ hRVR hLinBound hBetaBound
    hGapTail hα_pos hα_lt_one hstrict hlower_meas hupper_meas hq_nonneg
    hcdfLower hcdfUpper

/-- Hansen equation (10.22): finite-replication bootstrap median-bias share
`p* = B^{-1} sum_b 1{theta*_b <= thetaHat}`. -/
noncomputable def bootstrapMedianBiasShare
    {B : Type*} [Fintype B] (thetaHat : ℝ) (thetaStar : B → ℝ) : ℝ :=
  (Fintype.card B : ℝ)⁻¹ *
    ∑ b, if thetaStar b ≤ thetaHat then (1 : ℝ) else 0

/-- Hansen equation (10.23): normal-scale bias correction from a quantile
function.  For the BC interval this quantile function is `Phi^{-1}`. -/
noncomputable def bootstrapBiasCorrection
    (normalQuantile : ℝ → ℝ) (pstar : ℝ) : ℝ :=
  normalQuantile pstar

/-- Hansen equation (10.24): BC adjusted percentile level
`x(alpha) = Phi(z_alpha + 2 z0)`. -/
noncomputable def biasCorrectedAdjustedLevel
    (Phi normalQuantile : ℝ → ℝ) (z0 alpha : ℝ) : ℝ :=
  Phi (normalQuantile alpha + 2 * z0)

/-- Hansen equation (10.25): the bias-corrected percentile interval event
formed from bootstrap quantiles at the adjusted endpoint levels. -/
def biasCorrectedPercentileCIEvent
    (theta : ℝ) (bootstrapQuantile : ℝ → ℝ)
    (Phi normalQuantile : ℝ → ℝ) (z0 alpha : ℝ) : Prop :=
  percentileCIEvent theta
    (bootstrapQuantile
      (biasCorrectedAdjustedLevel Phi normalQuantile z0 (alpha / 2)))
    (bootstrapQuantile
      (biasCorrectedAdjustedLevel Phi normalQuantile z0 (1 - alpha / 2)))

/-- Hansen equation (10.21): transformed BC pivot
`psi(thetaHat) - psi(theta) + z0`. -/
noncomputable def biasCorrectedPivot
    (psi : ℝ → ℝ) (theta z0 thetaHat : ℝ) : ℝ :=
  psi thetaHat - psi theta + z0

/-- The ideal transformed-endpoint BC event used in Hansen's exact-coverage
proof after the adjusted bootstrap quantiles have been identified. -/
def biasCorrectedIdealCIEvent
    (psi : ℝ → ℝ) (theta thetaHat z0 zLower zUpper : ℝ) : Prop :=
  psi thetaHat + z0 + zLower ≤ psi theta ∧
    psi theta ≤ psi thetaHat + z0 + zUpper

/-- Algebraic form of Hansen's BC exact-coverage argument: the transformed
endpoint event is the same as the pivot lying between `-zUpper` and
`-zLower`. -/
theorem biasCorrectedIdealCIEvent_iff_pivot_mem_Icc
    {psi : ℝ → ℝ} {theta thetaHat z0 zLower zUpper : ℝ} :
    biasCorrectedIdealCIEvent psi theta thetaHat z0 zLower zUpper ↔
      biasCorrectedPivot psi theta z0 thetaHat ∈ Set.Icc (-zUpper) (-zLower) := by
  change
    (psi thetaHat + z0 + zLower ≤ psi theta ∧
        psi theta ≤ psi thetaHat + z0 + zUpper) ↔
      -zUpper ≤ psi thetaHat - psi theta + z0 ∧
        psi thetaHat - psi theta + z0 ≤ -zLower
  constructor
  · intro h
    exact ⟨by linarith [h.2], by linarith [h.1]⟩
  · intro h
    exact ⟨by linarith [h.2], by linarith [h.1]⟩

/-- Hansen BC exact-coverage bridge in CDF-increment form.

Under the transformed pivotal model (10.21), the ideal BC interval coverage is
the probability that the pivot lies in `[-zUpper, -zLower]`.  A non-atomic
limit law reads this probability as a CDF increment. -/
theorem biasCorrectedIdealCIEvent_probability_eq_cdf_sub
    [IsProbabilityMeasure μ]
    {eta : Measure ℝ} [IsProbabilityMeasure eta] [NoAtoms eta]
    {psi : ℝ → ℝ} {theta z0 zLower zUpper : ℝ} {thetaHat : Ω → ℝ}
    (hZ :
      HasLaw
        (fun ω => biasCorrectedPivot psi theta z0 (thetaHat ω)) eta μ)
    (hz : zLower ≤ zUpper) :
    μ {ω | biasCorrectedIdealCIEvent psi theta (thetaHat ω) z0 zLower zUpper} =
      ENNReal.ofReal (cdf eta (-zLower) - cdf eta (-zUpper)) := by
  have hset :
      {ω | biasCorrectedIdealCIEvent psi theta (thetaHat ω) z0 zLower zUpper} =
        (fun ω => biasCorrectedPivot psi theta z0 (thetaHat ω)) ⁻¹'
          Set.Icc (-zUpper) (-zLower) := by
    ext ω
    exact biasCorrectedIdealCIEvent_iff_pivot_mem_Icc
  rw [hset]
  exact HasLaw.preimage_Icc_eq_ofReal_cdf_sub_of_noAtoms
    (μ := μ) (ν := eta) hZ (by linarith)

/-- Hansen BC exact coverage: if the pivot critical values have endpoint CDF
masses `alpha / 2` and `1 - alpha / 2`, then the ideal BC interval has
coverage `1 - alpha`. -/
theorem biasCorrectedIdealCIEvent_probability_eq_one_sub_alpha
    [IsProbabilityMeasure μ]
    {eta : Measure ℝ} [IsProbabilityMeasure eta] [NoAtoms eta]
    {psi : ℝ → ℝ} {theta z0 zLower zUpper alpha : ℝ}
    {thetaHat : Ω → ℝ}
    (hZ :
      HasLaw
        (fun ω => biasCorrectedPivot psi theta z0 (thetaHat ω)) eta μ)
    (hz : zLower ≤ zUpper)
    (hcdfLower : cdf eta (-zUpper) = alpha / 2)
    (hcdfUpper : cdf eta (-zLower) = 1 - alpha / 2) :
    μ {ω | biasCorrectedIdealCIEvent psi theta (thetaHat ω) z0 zLower zUpper} =
      ENNReal.ofReal (1 - alpha) := by
  rw [biasCorrectedIdealCIEvent_probability_eq_cdf_sub
    (μ := μ) (eta := eta) hZ hz]
  congr 1
  rw [hcdfLower, hcdfUpper]
  ring

/-- Symmetric-critical-value version of Hansen's BC exact coverage proof.

This is the textbook specialization where `zLower = z_{alpha/2}`,
`zUpper = z_{1-alpha/2}`, and symmetry gives `-zUpper = zLower` and
`-zLower = zUpper`. -/
theorem biasCorrectedIdealCIEvent_probability_eq_one_sub_alpha_of_symmetric
    [IsProbabilityMeasure μ]
    {eta : Measure ℝ} [IsProbabilityMeasure eta] [NoAtoms eta]
    {psi : ℝ → ℝ} {theta z0 zLower zUpper alpha : ℝ}
    {thetaHat : Ω → ℝ}
    (hZ :
      HasLaw
        (fun ω => biasCorrectedPivot psi theta z0 (thetaHat ω)) eta μ)
    (hz : zLower ≤ zUpper)
    (hsymLower : -zUpper = zLower)
    (hsymUpper : -zLower = zUpper)
    (hcdfLower : cdf eta zLower = alpha / 2)
    (hcdfUpper : cdf eta zUpper = 1 - alpha / 2) :
    μ {ω | biasCorrectedIdealCIEvent psi theta (thetaHat ω) z0 zLower zUpper} =
      ENNReal.ofReal (1 - alpha) :=
  biasCorrectedIdealCIEvent_probability_eq_one_sub_alpha
    (μ := μ) (eta := eta) (psi := psi) (theta := theta) (z0 := z0)
    (zLower := zLower) (zUpper := zUpper) (alpha := alpha)
    (thetaHat := thetaHat) hZ hz
    (by simpa [hsymLower] using hcdfLower)
    (by simpa [hsymUpper] using hcdfUpper)

/-- Hansen's BCa adjusted percentile level:
`Phi(z0 + (z_alpha + z0) / (1 - a (z_alpha + z0)))`. -/
noncomputable def bcaAdjustedLevel
    (Phi normalQuantile : ℝ → ℝ) (z0 accel alpha : ℝ) : ℝ :=
  Phi (z0 + (normalQuantile alpha + z0) /
    (1 - accel * (normalQuantile alpha + z0)))

@[simp]
theorem bcaAdjustedLevel_accel_zero
    {Phi normalQuantile : ℝ → ℝ} {z0 alpha : ℝ} :
    bcaAdjustedLevel Phi normalQuantile z0 0 alpha =
      biasCorrectedAdjustedLevel Phi normalQuantile z0 alpha := by
  simp [bcaAdjustedLevel, biasCorrectedAdjustedLevel]
  ring_nf

/-- Hansen's jackknife acceleration estimate for the BCa interval. -/
noncomputable def bcaJackknifeAcceleration
    {ι : Type*} [Fintype ι] (thetaLeaveOneOut : ι → ℝ) : ℝ :=
  let thetaBar : ℝ := (Fintype.card ι : ℝ)⁻¹ * ∑ i, thetaLeaveOneOut i
  (∑ i, (thetaBar - thetaLeaveOneOut i) ^ 3) /
    (6 * (∑ i, (thetaBar - thetaLeaveOneOut i) ^ 2) ^ ((3 : ℝ) / 2))

/-- Hansen's BCa percentile interval event formed from bootstrap quantiles at
the accelerated adjusted endpoint levels. -/
def bcaPercentileCIEvent
    (theta : ℝ) (bootstrapQuantile : ℝ → ℝ)
    (Phi normalQuantile : ℝ → ℝ) (z0 accel alpha : ℝ) : Prop :=
  percentileCIEvent theta
    (bootstrapQuantile
      (bcaAdjustedLevel Phi normalQuantile z0 accel (alpha / 2)))
    (bootstrapQuantile
      (bcaAdjustedLevel Phi normalQuantile z0 accel (1 - alpha / 2)))

/-- Hansen equation (10.28): BCa transformed pivot
`(psi(thetaHat) - psi(theta)) / (1 + a * psi(theta)) + z0`. -/
noncomputable def bcaPivot
    (psi : ℝ → ℝ) (theta accel z0 thetaHat : ℝ) : ℝ :=
  (psi thetaHat - psi theta) / (1 + accel * psi theta) + z0

/-- Hansen equation (10.29): the bootstrap analogue of the BCa transformed
pivot, centered at the sample estimate. -/
noncomputable def bcaBootstrapPivot
    (psi : ℝ → ℝ) (thetaHat accel z0 thetaStar : ℝ) : ℝ :=
  (psi thetaStar - psi thetaHat) / (1 + accel * psi thetaHat) + z0

/-- A law-facing form of Hansen equation (10.29): if the BCa bootstrap pivot
has law `eta`, then its lower-tail probability is `cdf eta x`. -/
theorem bcaBootstrapPivot_probability_le_eq_cdf
    {eta : Measure ℝ} [IsProbabilityMeasure eta]
    {psi : ℝ → ℝ} {thetaHat accel z0 x : ℝ}
    {thetaStar : Ω → ℝ}
    (hZ :
      HasLaw
        (fun ω => bcaBootstrapPivot psi thetaHat accel z0 (thetaStar ω))
        eta μ) :
    μ.real {ω | bcaBootstrapPivot psi thetaHat accel z0 (thetaStar ω) ≤ x} =
      cdf eta x := by
  change
    μ.real
      ((fun ω => bcaBootstrapPivot psi thetaHat accel z0 (thetaStar ω)) ⁻¹'
        Set.Iic x) = cdf eta x
  exact HasLaw.real_preimage_Iic_eq_cdf hZ x

/-- Ideal BCa transformed endpoint used in Hansen's exact-coverage proof:
`(psi(thetaHat) + z + z0) / (1 - a * (z + z0))`. -/
noncomputable def bcaIdealEndpoint
    (psiThetaHat accel z0 z : ℝ) : ℝ :=
  (psiThetaHat + z + z0) / (1 - accel * (z + z0))

/-- The ideal transformed-endpoint BCa interval event used after the adjusted
bootstrap quantiles have been identified through (10.29). -/
def bcaIdealCIEvent
    (psi : ℝ → ℝ) (theta thetaHat accel z0 zLower zUpper : ℝ) : Prop :=
  bcaIdealEndpoint (psi thetaHat) accel z0 zLower ≤ psi theta ∧
    psi theta ≤ bcaIdealEndpoint (psi thetaHat) accel z0 zUpper

private theorem bcaIdealEndpoint_le_iff_pivot_le_neg
    {psiTheta psiThetaHat accel z0 z : ℝ}
    (hden : 0 < 1 - accel * (z + z0))
    (hpivot : 0 < 1 + accel * psiTheta) :
    bcaIdealEndpoint psiThetaHat accel z0 z ≤ psiTheta ↔
      (psiThetaHat - psiTheta) / (1 + accel * psiTheta) + z0 ≤ -z := by
  constructor
  · intro h
    have hmul :
        psiThetaHat + z + z0 ≤
          psiTheta * (1 - accel * (z + z0)) := by
      simpa [bcaIdealEndpoint] using (div_le_iff₀ hden).1 h
    have htarget :
        psiThetaHat - psiTheta ≤
          (-z - z0) * (1 + accel * psiTheta) := by
      nlinarith
    have hdiv :
        (psiThetaHat - psiTheta) / (1 + accel * psiTheta) ≤
          -z - z0 :=
      (div_le_iff₀ hpivot).2 htarget
    linarith
  · intro h
    have hdiv :
        (psiThetaHat - psiTheta) / (1 + accel * psiTheta) ≤
          -z - z0 := by
      linarith
    have hmul :
        psiThetaHat - psiTheta ≤
          (-z - z0) * (1 + accel * psiTheta) :=
      (div_le_iff₀ hpivot).1 hdiv
    have htarget :
        psiThetaHat + z + z0 ≤
          psiTheta * (1 - accel * (z + z0)) := by
      nlinarith
    exact (div_le_iff₀ hden).2 (by
      simpa [bcaIdealEndpoint] using htarget)

private theorem le_bcaIdealEndpoint_iff_neg_le_pivot
    {psiTheta psiThetaHat accel z0 z : ℝ}
    (hden : 0 < 1 - accel * (z + z0))
    (hpivot : 0 < 1 + accel * psiTheta) :
    psiTheta ≤ bcaIdealEndpoint psiThetaHat accel z0 z ↔
      -z ≤ (psiThetaHat - psiTheta) / (1 + accel * psiTheta) + z0 := by
  constructor
  · intro h
    have hmul :
        psiTheta * (1 - accel * (z + z0)) ≤
          psiThetaHat + z + z0 := by
      simpa [bcaIdealEndpoint] using (le_div_iff₀ hden).1 h
    have htarget :
        (-z - z0) * (1 + accel * psiTheta) ≤
          psiThetaHat - psiTheta := by
      nlinarith
    have hdiv :
        -z - z0 ≤
          (psiThetaHat - psiTheta) / (1 + accel * psiTheta) :=
      (le_div_iff₀ hpivot).2 htarget
    linarith
  · intro h
    have hdiv :
        -z - z0 ≤
          (psiThetaHat - psiTheta) / (1 + accel * psiTheta) := by
      linarith
    have hmul :
        (-z - z0) * (1 + accel * psiTheta) ≤
          psiThetaHat - psiTheta :=
      (le_div_iff₀ hpivot).1 hdiv
    have htarget :
        psiTheta * (1 - accel * (z + z0)) ≤
          psiThetaHat + z + z0 := by
      nlinarith
    exact (le_div_iff₀ hden).2 (by
      simpa [bcaIdealEndpoint] using htarget)

/-- Algebraic form of Hansen's BCa exact-coverage argument: the transformed
endpoint event is equivalent to the BCa pivot lying between `-zUpper` and
`-zLower`.  The denominator assumptions are the well-definedness conditions
for the BCa transformation and adjusted endpoint levels. -/
theorem bcaIdealCIEvent_iff_pivot_mem_Icc
    {psi : ℝ → ℝ} {theta thetaHat accel z0 zLower zUpper : ℝ}
    (hpivot : 0 < 1 + accel * psi theta)
    (hdenLower : 0 < 1 - accel * (zLower + z0))
    (hdenUpper : 0 < 1 - accel * (zUpper + z0)) :
    bcaIdealCIEvent psi theta thetaHat accel z0 zLower zUpper ↔
      bcaPivot psi theta accel z0 thetaHat ∈ Set.Icc (-zUpper) (-zLower) := by
  constructor
  · intro h
    constructor
    · simpa [bcaPivot] using
        (le_bcaIdealEndpoint_iff_neg_le_pivot
          (psiTheta := psi theta) (psiThetaHat := psi thetaHat)
          hdenUpper hpivot).1 h.2
    · simpa [bcaPivot] using
        (bcaIdealEndpoint_le_iff_pivot_le_neg
          (psiTheta := psi theta) (psiThetaHat := psi thetaHat)
          hdenLower hpivot).1 h.1
  · intro h
    constructor
    · exact
        (bcaIdealEndpoint_le_iff_pivot_le_neg
          (psiTheta := psi theta) (psiThetaHat := psi thetaHat)
          hdenLower hpivot).2 (by simpa [bcaPivot] using h.2)
    · exact
        (le_bcaIdealEndpoint_iff_neg_le_pivot
          (psiTheta := psi theta) (psiThetaHat := psi thetaHat)
          hdenUpper hpivot).2 (by simpa [bcaPivot] using h.1)

/-- Hansen BCa exact-coverage bridge in CDF-increment form.

Under the transformed pivotal model (10.28), the ideal BCa interval coverage is
the probability that the BCa pivot lies in `[-zUpper, -zLower]`. -/
theorem bcaIdealCIEvent_probability_eq_cdf_sub
    [IsProbabilityMeasure μ]
    {eta : Measure ℝ} [IsProbabilityMeasure eta] [NoAtoms eta]
    {psi : ℝ → ℝ} {theta accel z0 zLower zUpper : ℝ}
    {thetaHat : Ω → ℝ}
    (hZ :
      HasLaw
        (fun ω => bcaPivot psi theta accel z0 (thetaHat ω)) eta μ)
    (hpivot : 0 < 1 + accel * psi theta)
    (hdenLower : 0 < 1 - accel * (zLower + z0))
    (hdenUpper : 0 < 1 - accel * (zUpper + z0))
    (hz : zLower ≤ zUpper) :
    μ {ω | bcaIdealCIEvent psi theta (thetaHat ω) accel z0 zLower zUpper} =
      ENNReal.ofReal (cdf eta (-zLower) - cdf eta (-zUpper)) := by
  have hset :
      {ω | bcaIdealCIEvent psi theta (thetaHat ω) accel z0 zLower zUpper} =
        (fun ω => bcaPivot psi theta accel z0 (thetaHat ω)) ⁻¹'
          Set.Icc (-zUpper) (-zLower) := by
    ext ω
    exact bcaIdealCIEvent_iff_pivot_mem_Icc hpivot hdenLower hdenUpper
  rw [hset]
  exact HasLaw.preimage_Icc_eq_ofReal_cdf_sub_of_noAtoms
    (μ := μ) (ν := eta) hZ (by linarith)

/-- Hansen BCa exact coverage: endpoint CDF masses `alpha / 2` and
`1 - alpha / 2` imply coverage `1 - alpha`. -/
theorem bcaIdealCIEvent_probability_eq_one_sub_alpha
    [IsProbabilityMeasure μ]
    {eta : Measure ℝ} [IsProbabilityMeasure eta] [NoAtoms eta]
    {psi : ℝ → ℝ} {theta accel z0 zLower zUpper alpha : ℝ}
    {thetaHat : Ω → ℝ}
    (hZ :
      HasLaw
        (fun ω => bcaPivot psi theta accel z0 (thetaHat ω)) eta μ)
    (hpivot : 0 < 1 + accel * psi theta)
    (hdenLower : 0 < 1 - accel * (zLower + z0))
    (hdenUpper : 0 < 1 - accel * (zUpper + z0))
    (hz : zLower ≤ zUpper)
    (hcdfLower : cdf eta (-zUpper) = alpha / 2)
    (hcdfUpper : cdf eta (-zLower) = 1 - alpha / 2) :
    μ {ω | bcaIdealCIEvent psi theta (thetaHat ω) accel z0 zLower zUpper} =
      ENNReal.ofReal (1 - alpha) := by
  rw [bcaIdealCIEvent_probability_eq_cdf_sub
    (μ := μ) (eta := eta) hZ hpivot hdenLower hdenUpper hz]
  congr 1
  rw [hcdfLower, hcdfUpper]
  ring

/-- Symmetric-critical-value version of Hansen's BCa exact coverage proof. -/
theorem bcaIdealCIEvent_probability_eq_one_sub_alpha_of_symmetric
    [IsProbabilityMeasure μ]
    {eta : Measure ℝ} [IsProbabilityMeasure eta] [NoAtoms eta]
    {psi : ℝ → ℝ} {theta accel z0 zLower zUpper alpha : ℝ}
    {thetaHat : Ω → ℝ}
    (hZ :
      HasLaw
        (fun ω => bcaPivot psi theta accel z0 (thetaHat ω)) eta μ)
    (hpivot : 0 < 1 + accel * psi theta)
    (hdenLower : 0 < 1 - accel * (zLower + z0))
    (hdenUpper : 0 < 1 - accel * (zUpper + z0))
    (hz : zLower ≤ zUpper)
    (hsymLower : -zUpper = zLower)
    (hsymUpper : -zLower = zUpper)
    (hcdfLower : cdf eta zLower = alpha / 2)
    (hcdfUpper : cdf eta zUpper = 1 - alpha / 2) :
    μ {ω | bcaIdealCIEvent psi theta (thetaHat ω) accel z0 zLower zUpper} =
      ENNReal.ofReal (1 - alpha) :=
  bcaIdealCIEvent_probability_eq_one_sub_alpha
    (μ := μ) (eta := eta) (psi := psi) (theta := theta)
    (accel := accel) (z0 := z0) (zLower := zLower)
    (zUpper := zUpper) (alpha := alpha) (thetaHat := thetaHat)
    hZ hpivot hdenLower hdenUpper hz
    (by simpa [hsymLower] using hcdfLower)
    (by simpa [hsymUpper] using hcdfUpper)

end PercentileIntervals

end HansenEconometrics
