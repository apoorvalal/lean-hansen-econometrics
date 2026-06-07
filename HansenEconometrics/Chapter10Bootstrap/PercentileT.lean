import HansenEconometrics.Chapter10Bootstrap.Percentile

/-!
# Chapter 10 — Percentile-t intervals

Percentile-`t` (studentized bootstrap) confidence intervals and their coverage:
the rejection/coverage event characterizations and the percentile-`t` coverage
convergence results.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology MeasureTheory ProbabilityTheory Matrix
open scoped Matrix.Norms.Elementwise Function

namespace HansenEconometrics

variable {Ω Ωs Ωlim E F k : Type*}
variable {mΩ : MeasurableSpace Ω} {mΩs : MeasurableSpace Ωs}
variable {mΩlim : MeasurableSpace Ωlim}
variable {μ : Measure Ω} {ν : Measure Ωlim}

section PercentileTIntervals

/-- Percentile-`t` statistic `T = (θhat - θ) / se`. -/
noncomputable def percentileTStatistic (θ θhat se : ℝ) : ℝ :=
  (θhat - θ) / se

/-- Hansen percentile-`t` confidence interval event:
`θhat - se * qUpper <= θ <= θhat - se * qLower`. -/
def percentileTCIEvent (θ θhat se qLower qUpper : ℝ) : Prop :=
  θhat - se * qUpper ≤ θ ∧ θ ≤ θhat - se * qLower

/-- Three-coordinate statistic used in the percentile-`t` coverage proof:

* coordinate `0`: sample t-ratio `Tₙ`;
* coordinate `1`: lower bootstrap t-ratio quantile `q*_{α/2,n}`;
* coordinate `2`: upper bootstrap t-ratio quantile `q*_{1-α/2,n}`. -/
noncomputable def percentileTCoverageVector
    (θ : ℝ) (θhat se qLower qUpper : ℕ → Ω → ℝ)
    (n : ℕ) (ω : Ω) : Fin 3 → ℝ :=
  fun i =>
    if i = 0 then percentileTStatistic θ (θhat n ω) (se n ω)
    else if i = 1 then qLower n ω
    else qUpper n ω

/-- Limit vector for the percentile-`t` coverage proof. -/
noncomputable def percentileTCoverageLimitVector
    (ξ : Ωlim → ℝ) (qLower qUpper : ℝ) (ω : Ωlim) : Fin 3 → ℝ :=
  fun i =>
    if i = 0 then ξ ω
    else if i = 1 then qLower
    else qUpper

/-- Componentwise Slutsky constructor for the percentile-`t` coverage joint
vector.

This assembles the joint convergence premise in
`chapter10_percentileTCI_coverage_tendsto_of_joint_quantile_limit` from the
sample t-ratio limit and the two bootstrap percentile-`t` endpoint limits. -/
theorem percentileTCoverageVector_tendstoInDistribution_of_components
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {θ : ℝ} {θhat se qLower qUpper : ℕ → Ω → ℝ}
    {ξ : Ωlim → ℝ} {qLowerLim qUpperLim : ℝ}
    (htstat :
      TendstoInDistribution
        (fun n ω => percentileTStatistic θ (θhat n ω) (se n ω))
        atTop ξ (fun _ => μ) ν)
    (hlower : TendstoInMeasure μ qLower atTop (fun _ => qLowerLim))
    (hupper : TendstoInMeasure μ qUpper atTop (fun _ => qUpperLim))
    (hlower_meas : ∀ n, AEMeasurable (qLower n) μ)
    (hupper_meas : ∀ n, AEMeasurable (qUpper n) μ) :
    TendstoInDistribution
      (percentileTCoverageVector θ θhat se qLower qUpper)
      atTop
      (percentileTCoverageLimitVector ξ qLowerLim qUpperLim)
      (fun _ => μ) ν := by
  classical
  let tstatSeq : ℕ → Ω → ℝ :=
    fun n ω => percentileTStatistic θ (θhat n ω) (se n ω)
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
        (fun n ω => (tstatSeq n ω, qLower n ω))
        atTop (fun ω => (ξ ω, qLowerLim)) (fun _ => μ) ν :=
    htstat.prodMk_of_tendstoInMeasure_const tstatSeq qLower ξ
      hlower hlower_meas
  have hpacked :
      TendstoInDistribution
        (fun n ω => pack ((tstatSeq n ω, qLower n ω), qUpper n ω))
        atTop (fun ω => pack ((ξ ω, qLowerLim), qUpperLim))
        (fun _ => μ) ν := by
    have hraw := hpair.continuous_comp_prodMk_of_tendstoInMeasure_const
      (g := pack) hpack_cont hupper hupper_meas
    simpa [Function.comp_def] using hraw
  refine TendstoInDistribution.congr ?_ ?_ hpacked
  · intro n
    exact ae_of_all μ fun ω => by
      ext i
      by_cases hi0 : i = 0 <;> by_cases hi1 : i = 1 <;>
        simp [percentileTCoverageVector, tstatSeq, pack, hi0, hi1]
  · exact ae_of_all ν fun ω => by
      ext i
      by_cases hi0 : i = 0 <;> by_cases hi1 : i = 1 <;>
        simp [percentileTCoverageLimitVector, pack, hi0, hi1]

/-- Limit event corresponding to percentile-`t` coverage:
`qLower <= ξ <= qUpper`. -/
def percentileTCoverageSet : Set (Fin 3 → ℝ) :=
  {z | z 1 ≤ z 0 ∧ z 0 ≤ z 2}

private theorem isClosed_percentileTCoverageSet : IsClosed percentileTCoverageSet := by
  have hleft : IsClosed {z : Fin 3 → ℝ | z 1 ≤ z 0} :=
    isClosed_le (continuous_apply 1) (continuous_apply 0)
  have hright : IsClosed {z : Fin 3 → ℝ | z 0 ≤ z 2} :=
    isClosed_le (continuous_apply 0) (continuous_apply 2)
  simpa [percentileTCoverageSet] using hleft.inter hright

/-- Positive standard errors turn Hansen's percentile-`t` interval event into
the t-ratio event `qLower <= T <= qUpper`. -/
private theorem percentileTCIEvent_iff_tstat_between
    {θ θhat se qLower qUpper : ℝ} (hse : 0 < se) :
    percentileTCIEvent θ θhat se qLower qUpper ↔
      qLower ≤ percentileTStatistic θ θhat se ∧
        percentileTStatistic θ θhat se ≤ qUpper := by
  constructor
  · intro h
    constructor
    · have hmul : qLower * se ≤ θhat - θ := by nlinarith [h.2]
      exact (le_div_iff₀ hse).2 (by simpa [mul_comm] using hmul)
    · have hmul : θhat - θ ≤ qUpper * se := by nlinarith [h.1]
      exact (div_le_iff₀ hse).2 (by simpa [mul_comm] using hmul)
  · intro h
    constructor
    · have hmul : θhat - θ ≤ qUpper * se := by
        simpa [percentileTStatistic, mul_comm] using (div_le_iff₀ hse).1 h.2
      nlinarith
    · have hmul : qLower * se ≤ θhat - θ := by
        simpa [percentileTStatistic, mul_comm] using (le_div_iff₀ hse).1 h.1
      nlinarith

private theorem percentileTCoverageVector_mem_set_iff
    {θ : ℝ} {θhat se qLower qUpper : ℕ → Ω → ℝ}
    {n : ℕ} {ω : Ω} (hse : 0 < se n ω) :
    percentileTCoverageVector θ θhat se qLower qUpper n ω ∈
        percentileTCoverageSet ↔
      percentileTCIEvent θ (θhat n ω) (se n ω) (qLower n ω) (qUpper n ω) := by
  change
    (qLower n ω ≤ percentileTStatistic θ (θhat n ω) (se n ω) ∧
        percentileTStatistic θ (θhat n ω) (se n ω) ≤ qUpper n ω) ↔
      percentileTCIEvent θ (θhat n ω) (se n ω) (qLower n ω) (qUpper n ω)
  exact (percentileTCIEvent_iff_tstat_between hse).symm

/-- The percentile-`t` coverage limit vector belongs to the coverage set
exactly when the scalar t-ratio limit lies between the limiting endpoints. -/
theorem percentileTCoverageLimitVector_mem_set_iff
    {ξ : Ωlim → ℝ} {qLower qUpper : ℝ} {ω : Ωlim} :
    percentileTCoverageLimitVector ξ qLower qUpper ω ∈
        percentileTCoverageSet ↔
      qLower ≤ ξ ω ∧ ξ ω ≤ qUpper := by
  change
    (qLower ≤ ξ ω ∧ ξ ω ≤ qUpper) ↔
      qLower ≤ ξ ω ∧ ξ ω ≤ qUpper
  rfl

/-- A scalar a.e.-measurable limit t-ratio yields an a.e.-measurable
percentile-`t` coverage limit vector. -/
private theorem aemeasurable_percentileTCoverageLimitVector
    {ξ : Ωlim → ℝ} (hξ : AEMeasurable ξ ν) (qLower qUpper : ℝ) :
    AEMeasurable (percentileTCoverageLimitVector ξ qLower qUpper) ν := by
  refine aemeasurable_pi_lambda _ ?_
  intro i
  by_cases hi0 : i = 0
  · subst i
    simpa [percentileTCoverageLimitVector] using hξ
  by_cases hi1 : i = 1
  · subst i
    simp [percentileTCoverageLimitVector]
  · simp [percentileTCoverageLimitVector, hi0, hi1]

/-- The vector-law probability of the percentile-`t` limit set is the scalar
event probability `P[qL <= ξ <= qU]`. -/
theorem percentileTCoverageLimit_measure_set_eq
    {ξ : Ωlim → ℝ} {qLower qUpper : ℝ}
    (hξ : AEMeasurable ξ ν) :
    (ν.map (percentileTCoverageLimitVector ξ qLower qUpper))
        percentileTCoverageSet =
      ν {ω | qLower ≤ ξ ω ∧ ξ ω ≤ qUpper} := by
  rw [Measure.map_apply_of_aemeasurable
    (aemeasurable_percentileTCoverageLimitVector (ν := ν) hξ qLower qUpper)
    isClosed_percentileTCoverageSet.measurableSet]
  apply congrArg ν
  ext ω
  exact percentileTCoverageLimitVector_mem_set_iff

/-- The frontier of the percentile-`t` coverage set is contained in the union
of the two binding endpoint hyperplanes. -/
theorem frontier_percentileTCoverageSet_subset :
    frontier percentileTCoverageSet ⊆
      {z : Fin 3 → ℝ | z 1 = z 0} ∪
        {z : Fin 3 → ℝ | z 0 = z 2} := by
  let lowerSet : Set (Fin 3 → ℝ) := {z | z 1 ≤ z 0}
  let upperSet : Set (Fin 3 → ℝ) := {z | z 0 ≤ z 2}
  have hfront :
      frontier percentileTCoverageSet ⊆
        frontier lowerSet ∩ closure upperSet ∪
          closure lowerSet ∩ frontier upperSet := by
    simpa [percentileTCoverageSet, lowerSet, upperSet] using
      frontier_inter_subset lowerSet upperSet
  intro z hz
  rcases hfront hz with ⟨hzlower, _⟩ | ⟨_, hzupper⟩
  · exact Or.inl
      (frontier_le_subset_eq (continuous_apply 1) (continuous_apply 0) hzlower)
  · exact Or.inr
      (frontier_le_subset_eq (continuous_apply 0) (continuous_apply 2) hzupper)

/-- Scalar endpoint-boundary null mass implies the vector-law null-frontier
premise for the percentile-`t` coverage set. -/
theorem percentileTCoverage_frontier_null_of_boundary_null
    {ξ : Ωlim → ℝ} {qLower qUpper : ℝ}
    (hξ : AEMeasurable ξ ν)
    (hleft : ν {ω | qLower = ξ ω} = 0)
    (hright : ν {ω | ξ ω = qUpper} = 0) :
    (ν.map (percentileTCoverageLimitVector ξ qLower qUpper))
      (frontier percentileTCoverageSet) = 0 := by
  let boundary : Set (Fin 3 → ℝ) :=
    {z | z 1 = z 0} ∪ {z | z 0 = z 2}
  have hboundary_meas : MeasurableSet boundary := by
    exact
      ((isClosed_eq (continuous_apply 1) (continuous_apply 0)).measurableSet).union
        ((isClosed_eq (continuous_apply 0) (continuous_apply 2)).measurableSet)
  have hboundary_zero :
      (ν.map (percentileTCoverageLimitVector ξ qLower qUpper)) boundary = 0 := by
    rw [Measure.map_apply_of_aemeasurable
      (aemeasurable_percentileTCoverageLimitVector (ν := ν) hξ qLower qUpper)
      hboundary_meas]
    have hpre :
        (percentileTCoverageLimitVector ξ qLower qUpper) ⁻¹' boundary =
          {ω | qLower = ξ ω} ∪ {ω | ξ ω = qUpper} := by
      ext ω
      simp [boundary, percentileTCoverageLimitVector]
    rw [hpre]
    exact measure_union_null hleft hright
  exact measure_mono_null (μ := ν.map (percentileTCoverageLimitVector ξ qLower qUpper))
    frontier_percentileTCoverageSet_subset hboundary_zero

/-- The scalar percentile-`t` coverage event can be read from the law of the
limit t-ratio as the interval `[qL, qU]`. -/
theorem percentileTCoverage_scalar_event_eq_law
    {ξ : Ωlim → ℝ} {η : Measure ℝ} (hξ : HasLaw ξ η ν)
    (qLower qUpper : ℝ) :
    ν {ω | qLower ≤ ξ ω ∧ ξ ω ≤ qUpper} =
      η (Set.Icc qLower qUpper) := by
  have hpre :
      {ω | qLower ≤ ξ ω ∧ ξ ω ≤ qUpper} =
        ξ ⁻¹' Set.Icc qLower qUpper := by
    rfl
  rw [hpre]
  exact HasLaw.preimage_eq hξ measurableSet_Icc

/-- If the scalar limit law has no atoms, then the percentile-`t` coverage
frontier has zero mass under the limit vector law. -/
theorem percentileTCoverage_frontier_null_of_hasLaw_noAtoms
    {ξ : Ωlim → ℝ} {η : Measure ℝ} [NoAtoms η] (hξ : HasLaw ξ η ν)
    (qLower qUpper : ℝ) :
    (ν.map (percentileTCoverageLimitVector ξ qLower qUpper))
      (frontier percentileTCoverageSet) = 0 := by
  refine percentileTCoverage_frontier_null_of_boundary_null
    (ν := ν) (qLower := qLower) (qUpper := qUpper)
    hξ.aemeasurable ?_ ?_
  · have hpre :
        {ω | qLower = ξ ω} = ξ ⁻¹' ({qLower} : Set ℝ) := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_singleton_iff]
      exact eq_comm
    rw [hpre, HasLaw.preimage_eq hξ (measurableSet_singleton qLower)]
    exact measure_singleton qLower
  · have hpre :
        {ω | ξ ω = qUpper} = ξ ⁻¹' ({qUpper} : Set ℝ) := by
      rfl
    rw [hpre, HasLaw.preimage_eq hξ (measurableSet_singleton qUpper)]
    exact measure_singleton qUpper

/-- Hansen Theorem 10.14, percentile-`t` interval coverage bridge.

If the sample t-ratio and bootstrap percentile-`t` critical values jointly
converge to `(ξ, qL, qU)`, and the limiting coverage boundary has zero
probability, then percentile-`t` interval coverage converges to
`P[qL <= ξ <= qU]`. Hansen's first-order validity conclusion `1 - α` is
obtained by instantiating this bridge with the bootstrap quantile limits from
(10.31). -/
theorem chapter10_percentileTCI_coverage_tendsto_of_joint_quantile_limit
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {θ : ℝ} {θhat se qLower qUpper : ℕ → Ω → ℝ}
    {ξ : Ωlim → ℝ} {qLowerLim qUpperLim : ℝ}
    (hse : ∀ n ω, 0 < se n ω)
    (hjoint :
      TendstoInDistribution
        (percentileTCoverageVector θ θhat se qLower qUpper)
        atTop
        (percentileTCoverageLimitVector ξ qLowerLim qUpperLim)
        (fun _ => μ) ν)
    (hfrontier :
      (ν.map (percentileTCoverageLimitVector ξ qLowerLim qUpperLim))
        (frontier percentileTCoverageSet) = 0) :
    Tendsto
      (fun n =>
        μ {ω | percentileTCIEvent θ (θhat n ω) (se n ω)
          (qLower n ω) (qUpper n ω)})
      atTop
      (𝓝 ((ν.map (percentileTCoverageLimitVector ξ qLowerLim qUpperLim))
        percentileTCoverageSet)) := by
  have hset_meas : MeasurableSet percentileTCoverageSet :=
    isClosed_percentileTCoverageSet.measurableSet
  have hcoverage :=
    TendstoInDistribution.tendsto_measure_preimage_of_null_frontier
      (h := hjoint) hset_meas hfrontier
  have hseq_eq :
      (fun n =>
        μ {ω | percentileTCoverageVector θ θhat se qLower qUpper n ω ∈
          percentileTCoverageSet}) =
        fun n =>
          μ {ω | percentileTCIEvent θ (θhat n ω) (se n ω)
            (qLower n ω) (qUpper n ω)} := by
    funext n
    congr 1
    ext ω
    exact percentileTCoverageVector_mem_set_iff (Ω := Ω) (hse n ω)
  simpa [hseq_eq] using hcoverage

/-- Calibrated percentile-`t` coverage bridge. -/
theorem chapter10_percentileTCI_coverage_tendsto
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {θ : ℝ} {θhat se qLower qUpper : ℕ → Ω → ℝ}
    {ξ : Ωlim → ℝ} {qLowerLim qUpperLim : ℝ} {coverage : ℝ≥0∞}
    (hse : ∀ n ω, 0 < se n ω)
    (hjoint :
      TendstoInDistribution
        (percentileTCoverageVector θ θhat se qLower qUpper)
        atTop
        (percentileTCoverageLimitVector ξ qLowerLim qUpperLim)
        (fun _ => μ) ν)
    (hfrontier :
      (ν.map (percentileTCoverageLimitVector ξ qLowerLim qUpperLim))
        (frontier percentileTCoverageSet) = 0)
    (hcoverage :
      (ν.map (percentileTCoverageLimitVector ξ qLowerLim qUpperLim))
        percentileTCoverageSet = coverage) :
    Tendsto
      (fun n =>
        μ {ω | percentileTCIEvent θ (θhat n ω) (se n ω)
          (qLower n ω) (qUpper n ω)})
      atTop (𝓝 coverage) := by
  simpa [hcoverage] using
    chapter10_percentileTCI_coverage_tendsto_of_joint_quantile_limit
      (μ := μ) (ν := ν) (θ := θ) (θhat := θhat) (se := se)
      (qLower := qLower) (qUpper := qUpper) (ξ := ξ)
      (qLowerLim := qLowerLim) (qUpperLim := qUpperLim)
      hse hjoint hfrontier

/-- Calibrated percentile-`t` coverage bridge with the limit coverage stated
as the scalar event probability `P[qL <= ξ <= qU]`. -/
theorem chapter10_percentileTCI_coverage_tendsto_of_scalar_limit_coverage
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {θ : ℝ} {θhat se qLower qUpper : ℕ → Ω → ℝ}
    {ξ : Ωlim → ℝ} {qLowerLim qUpperLim : ℝ} {coverage : ℝ≥0∞}
    (hse : ∀ n ω, 0 < se n ω)
    (hjoint :
      TendstoInDistribution
        (percentileTCoverageVector θ θhat se qLower qUpper)
        atTop
        (percentileTCoverageLimitVector ξ qLowerLim qUpperLim)
        (fun _ => μ) ν)
    (hfrontier :
      (ν.map (percentileTCoverageLimitVector ξ qLowerLim qUpperLim))
        (frontier percentileTCoverageSet) = 0)
    (hcoverage :
      ν {ω | qLowerLim ≤ ξ ω ∧ ξ ω ≤ qUpperLim} = coverage) :
    Tendsto
      (fun n =>
        μ {ω | percentileTCIEvent θ (θhat n ω) (se n ω)
          (qLower n ω) (qUpper n ω)})
      atTop (𝓝 coverage) := by
  have hcoverage_map :
      (ν.map (percentileTCoverageLimitVector ξ qLowerLim qUpperLim))
        percentileTCoverageSet = coverage := by
    rw [Measure.map_apply_of_aemeasurable hjoint.aemeasurable_limit
      isClosed_percentileTCoverageSet.measurableSet]
    have hpre :
        {ω | percentileTCoverageLimitVector ξ qLowerLim qUpperLim ω ∈
            percentileTCoverageSet} =
          {ω | qLowerLim ≤ ξ ω ∧ ξ ω ≤ qUpperLim} := by
      ext ω
      exact percentileTCoverageLimitVector_mem_set_iff
    simpa [hpre] using hcoverage
  exact
    chapter10_percentileTCI_coverage_tendsto
      (μ := μ) (ν := ν) (θ := θ) (θhat := θhat) (se := se)
      (qLower := qLower) (qUpper := qUpper) (ξ := ξ)
      (qLowerLim := qLowerLim) (qUpperLim := qUpperLim)
      hse hjoint hfrontier hcoverage_map

/-- Calibrated percentile-`t` coverage bridge with scalar endpoint
boundary-null and scalar coverage assumptions. -/
theorem chapter10_percentileTCI_coverage_tendsto_of_scalar_limit
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {θ : ℝ} {θhat se qLower qUpper : ℕ → Ω → ℝ}
    {ξ : Ωlim → ℝ} {qLowerLim qUpperLim : ℝ} {coverage : ℝ≥0∞}
    (hse : ∀ n ω, 0 < se n ω)
    (hjoint :
      TendstoInDistribution
        (percentileTCoverageVector θ θhat se qLower qUpper)
        atTop
        (percentileTCoverageLimitVector ξ qLowerLim qUpperLim)
        (fun _ => μ) ν)
    (hξ : AEMeasurable ξ ν)
    (hleft : ν {ω | qLowerLim = ξ ω} = 0)
    (hright : ν {ω | ξ ω = qUpperLim} = 0)
    (hcoverage :
      ν {ω | qLowerLim ≤ ξ ω ∧ ξ ω ≤ qUpperLim} = coverage) :
    Tendsto
      (fun n =>
        μ {ω | percentileTCIEvent θ (θhat n ω) (se n ω)
          (qLower n ω) (qUpper n ω)})
      atTop (𝓝 coverage) := by
  exact
    chapter10_percentileTCI_coverage_tendsto_of_scalar_limit_coverage
      (μ := μ) (ν := ν) (θ := θ) (θhat := θhat) (se := se)
      (qLower := qLower) (qUpper := qUpper) (ξ := ξ)
      (qLowerLim := qLowerLim) (qUpperLim := qUpperLim)
      hse hjoint
      (percentileTCoverage_frontier_null_of_boundary_null
        (ν := ν) (qLower := qLowerLim) (qUpper := qUpperLim)
        hξ hleft hright)
      hcoverage

/-- Calibrated percentile-`t` coverage bridge with calibration stated under
the scalar law of the limit t-ratio.  A non-atomic limit law supplies the
required null-frontier premise. -/
theorem chapter10_percentileTCI_coverage_tendsto_of_limit_law
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {η : Measure ℝ} [NoAtoms η]
    {θ : ℝ} {θhat se qLower qUpper : ℕ → Ω → ℝ}
    {ξ : Ωlim → ℝ} {qLowerLim qUpperLim : ℝ} {coverage : ℝ≥0∞}
    (hse : ∀ n ω, 0 < se n ω)
    (hjoint :
      TendstoInDistribution
        (percentileTCoverageVector θ θhat se qLower qUpper)
        atTop
        (percentileTCoverageLimitVector ξ qLowerLim qUpperLim)
        (fun _ => μ) ν)
    (hξ : HasLaw ξ η ν)
    (hcoverage : η (Set.Icc qLowerLim qUpperLim) = coverage) :
    Tendsto
      (fun n =>
        μ {ω | percentileTCIEvent θ (θhat n ω) (se n ω)
          (qLower n ω) (qUpper n ω)})
      atTop (𝓝 coverage) := by
  refine chapter10_percentileTCI_coverage_tendsto_of_scalar_limit
    (μ := μ) (ν := ν) (θ := θ) (θhat := θhat) (se := se)
    (qLower := qLower) (qUpper := qUpper) (ξ := ξ)
    (qLowerLim := qLowerLim) (qUpperLim := qUpperLim)
    hse hjoint hξ.aemeasurable ?_ ?_ ?_
  · have hpre :
        {ω | qLowerLim = ξ ω} = ξ ⁻¹' ({qLowerLim} : Set ℝ) := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_singleton_iff]
      exact eq_comm
    rw [hpre, HasLaw.preimage_eq hξ (measurableSet_singleton qLowerLim)]
    exact measure_singleton qLowerLim
  · have hpre :
        {ω | ξ ω = qUpperLim} = ξ ⁻¹' ({qUpperLim} : Set ℝ) := by
      rfl
    rw [hpre, HasLaw.preimage_eq hξ (measurableSet_singleton qUpperLim)]
    exact measure_singleton qUpperLim
  · rw [percentileTCoverage_scalar_event_eq_law hξ qLowerLim qUpperLim]
    exact hcoverage

/-- CDF-calibrated percentile-`t` coverage bridge.

For a non-atomic scalar t-ratio limit law, the limiting coverage
`η[qL,qU]` can be supplied as the CDF increment `F(qU) - F(qL)`. -/
theorem chapter10_percentileTCI_coverage_tendsto_of_limit_law_cdf
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {η : Measure ℝ} [IsProbabilityMeasure η] [NoAtoms η]
    {θ : ℝ} {θhat se qLower qUpper : ℕ → Ω → ℝ}
    {ξ : Ωlim → ℝ} {qLowerLim qUpperLim coverage : ℝ}
    (hse : ∀ n ω, 0 < se n ω)
    (hjoint :
      TendstoInDistribution
        (percentileTCoverageVector θ θhat se qLower qUpper)
        atTop
        (percentileTCoverageLimitVector ξ qLowerLim qUpperLim)
        (fun _ => μ) ν)
    (hξ : HasLaw ξ η ν)
    (hquantiles : qLowerLim ≤ qUpperLim)
    (hcoverage : cdf η qUpperLim - cdf η qLowerLim = coverage) :
    Tendsto
      (fun n =>
        μ {ω | percentileTCIEvent θ (θhat n ω) (se n ω)
          (qLower n ω) (qUpper n ω)})
      atTop (𝓝 (ENNReal.ofReal coverage)) := by
  refine
    chapter10_percentileTCI_coverage_tendsto_of_limit_law
      (μ := μ) (ν := ν) (η := η) (θ := θ) (θhat := θhat)
      (se := se) (qLower := qLower) (qUpper := qUpper)
      (ξ := ξ) (qLowerLim := qLowerLim) (qUpperLim := qUpperLim)
      (coverage := ENNReal.ofReal coverage) hse hjoint hξ ?_
  rw [measure_Icc_eq_ofReal_cdf_sub_of_noAtoms
    (ν := η) (a := qLowerLim) (b := qUpperLim) hquantiles]
  rw [hcoverage]

/-- Endpoint-CDF percentile-`t` calibration with limiting coverage
`1 - α`.  The endpoint premises encode the limiting lower and upper
percentile-`t` masses. -/
theorem chapter10_percentileTCI_coverage_tendsto_one_sub_alpha_of_limit_law_cdf
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {η : Measure ℝ} [IsProbabilityMeasure η] [NoAtoms η]
    {θ : ℝ} {θhat se qLower qUpper : ℕ → Ω → ℝ}
    {ξ : Ωlim → ℝ} {qLowerLim qUpperLim α : ℝ}
    (hse : ∀ n ω, 0 < se n ω)
    (hjoint :
      TendstoInDistribution
        (percentileTCoverageVector θ θhat se qLower qUpper)
        atTop
        (percentileTCoverageLimitVector ξ qLowerLim qUpperLim)
        (fun _ => μ) ν)
    (hξ : HasLaw ξ η ν)
    (hquantiles : qLowerLim ≤ qUpperLim)
    (hlower : cdf η qLowerLim = α / 2)
    (hupper : cdf η qUpperLim = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | percentileTCIEvent θ (θhat n ω) (se n ω)
          (qLower n ω) (qUpper n ω)})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) := by
  refine
    chapter10_percentileTCI_coverage_tendsto_of_limit_law_cdf
      (μ := μ) (ν := ν) (η := η) (θ := θ) (θhat := θhat)
      (se := se) (qLower := qLower) (qUpper := qUpper)
      (ξ := ξ) (qLowerLim := qLowerLim) (qUpperLim := qUpperLim)
      (coverage := 1 - α) hse hjoint hξ hquantiles ?_
  rw [hlower, hupper]
  ring

/-- Componentwise endpoint-CDF percentile-`t` calibration with limiting
coverage `1 - α`.

This is the Theorem 10.14 coverage bridge stated directly from sample t-ratio
convergence and bootstrap percentile-`t` endpoint convergence in probability. -/
theorem chapter10_percentileTCI_coverage_tendsto_one_sub_alpha_of_components_law_cdf
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {η : Measure ℝ} [IsProbabilityMeasure η] [NoAtoms η]
    {θ : ℝ} {θhat se qLower qUpper : ℕ → Ω → ℝ}
    {ξ : Ωlim → ℝ} {qLowerLim qUpperLim α : ℝ}
    (hse : ∀ n ω, 0 < se n ω)
    (htstat :
      TendstoInDistribution
        (fun n ω => percentileTStatistic θ (θhat n ω) (se n ω))
        atTop ξ (fun _ => μ) ν)
    (hlower : TendstoInMeasure μ qLower atTop (fun _ => qLowerLim))
    (hupper : TendstoInMeasure μ qUpper atTop (fun _ => qUpperLim))
    (hlower_meas : ∀ n, AEMeasurable (qLower n) μ)
    (hupper_meas : ∀ n, AEMeasurable (qUpper n) μ)
    (hξ : HasLaw ξ η ν)
    (hquantiles : qLowerLim ≤ qUpperLim)
    (hcdfLower : cdf η qLowerLim = α / 2)
    (hcdfUpper : cdf η qUpperLim = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | percentileTCIEvent θ (θhat n ω) (se n ω)
          (qLower n ω) (qUpper n ω)})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) := by
  exact
    chapter10_percentileTCI_coverage_tendsto_one_sub_alpha_of_limit_law_cdf
      (μ := μ) (ν := ν) (η := η) (θ := θ) (θhat := θhat)
      (se := se) (qLower := qLower) (qUpper := qUpper)
      (ξ := ξ) (qLowerLim := qLowerLim) (qUpperLim := qUpperLim)
      hse
      (percentileTCoverageVector_tendstoInDistribution_of_components
        (μ := μ) (ν := ν) (θ := θ) (θhat := θhat) (se := se)
        (qLower := qLower) (qUpper := qUpper)
        (ξ := ξ) (qLowerLim := qLowerLim) (qUpperLim := qUpperLim)
        htstat hlower hupper hlower_meas hupper_meas)
      hξ hquantiles hcdfLower hcdfUpper

/-- Symmetric endpoint-CDF percentile-`t` calibration.

This is the Hansen Theorem 10.14 specialization where the limiting bootstrap
percentile-`t` endpoints are `-q` and `q`, and the scalar t-ratio limit law has
endpoint CDF masses `α / 2` and `1 - α / 2`. -/
theorem chapter10_percentileTCI_coverage_tendsto_one_sub_alpha_of_components_symmetric_cdf
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {η : Measure ℝ} [IsProbabilityMeasure η] [NoAtoms η]
    {θ : ℝ} {θhat se qLower qUpper : ℕ → Ω → ℝ}
    {ξ : Ωlim → ℝ} {q α : ℝ}
    (hse : ∀ n ω, 0 < se n ω)
    (htstat :
      TendstoInDistribution
        (fun n ω => percentileTStatistic θ (θhat n ω) (se n ω))
        atTop ξ (fun _ => μ) ν)
    (hlower : TendstoInMeasure μ qLower atTop (fun _ => -q))
    (hupper : TendstoInMeasure μ qUpper atTop (fun _ => q))
    (hlower_meas : ∀ n, AEMeasurable (qLower n) μ)
    (hupper_meas : ∀ n, AEMeasurable (qUpper n) μ)
    (hξ : HasLaw ξ η ν)
    (hq_nonneg : 0 ≤ q)
    (hcdfLower : cdf η (-q) = α / 2)
    (hcdfUpper : cdf η q = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | percentileTCIEvent θ (θhat n ω) (se n ω)
          (qLower n ω) (qUpper n ω)})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) := by
  exact
    chapter10_percentileTCI_coverage_tendsto_one_sub_alpha_of_components_law_cdf
      (μ := μ) (ν := ν) (η := η) (θ := θ) (θhat := θhat)
      (se := se) (qLower := qLower) (qUpper := qUpper)
      (ξ := ξ) (qLowerLim := -q) (qUpperLim := q) (α := α)
      hse htstat hlower hupper hlower_meas hupper_meas hξ
      (by linarith) hcdfLower hcdfUpper

/-- Symmetric percentile-`t` coverage from bootstrap lower quantiles, using
local limit-CDF bracketing.

This is the non-strict-CDF version of the lower-generalized-inverse endpoint
route for Hansen Theorem 10.14. -/
theorem
chapter10_percentileTCI_coverage_tendsto_one_sub_alpha_of_bootstrap_lowerQuantiles_brackets
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {η : Measure ℝ} [IsProbabilityMeasure η] [NoAtoms η]
    {Pstar : ℕ → Ω → Measure Ωs} {Tstar : ℕ → Ω → Ωs → ℝ}
    {θ : ℝ} {θhat se : ℕ → Ω → ℝ}
    {ξ : Ωlim → ℝ} {q α : ℝ}
    (hse : ∀ n ω, 0 < se n ω)
    (htstat :
      TendstoInDistribution
        (fun n ω => percentileTStatistic θ (θhat n ω) (se n ω))
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
        μ {ω | percentileTCIEvent θ (θhat n ω) (se n ω)
          (bootstrapScalarLowerQuantile Pstar Tstar (α / 2) n ω)
          (bootstrapScalarLowerQuantile Pstar Tstar (1 - α / 2) n ω)})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) := by
  have hlower :
      TendstoInMeasure μ
        (bootstrapScalarLowerQuantile Pstar Tstar (α / 2))
        atTop (fun _ => -q) :=
    bootstrapScalarLowerQuantile_tendsto_of_cdf_brackets
      (μ := μ) (Pstar := Pstar) (Zstar := Tstar)
      (G := fun x => cdf η x) (p := α / 2) (q := -q)
      hmono hneLower hbddLower hlocalLower hleftLower hrightLower hcdf
  have hupper :
      TendstoInMeasure μ
        (bootstrapScalarLowerQuantile Pstar Tstar (1 - α / 2))
        atTop (fun _ => q) :=
    bootstrapScalarLowerQuantile_tendsto_of_cdf_brackets
      (μ := μ) (Pstar := Pstar) (Zstar := Tstar)
      (G := fun x => cdf η x) (p := 1 - α / 2) (q := q)
      hmono hneUpper hbddUpper hlocalUpper hleftUpper hrightUpper hcdf
  exact
    chapter10_percentileTCI_coverage_tendsto_one_sub_alpha_of_components_symmetric_cdf
      (μ := μ) (ν := ν) (η := η) (θ := θ) (θhat := θhat)
      (se := se)
      (qLower := bootstrapScalarLowerQuantile Pstar Tstar (α / 2))
      (qUpper := bootstrapScalarLowerQuantile Pstar Tstar (1 - α / 2))
      (ξ := ξ) (q := q) (α := α)
      hse htstat hlower hupper hlower_meas hupper_meas hξ
      hq_nonneg hcdfLower hcdfUpper

/-- Symmetric percentile-`t` coverage from bootstrap lower quantiles.

Pointwise convergence in probability of the conditional bootstrap CDF, plus
the concrete lower-generalized-inverse bracketing assumptions, identifies the
bootstrap percentile-`t` endpoints at levels `α / 2` and `1 - α / 2`.  The
result then feeds those endpoint limits into the symmetric `[-q, q]` coverage
wrapper. -/
theorem chapter10_percentileTCI_coverage_tendsto_one_sub_alpha_of_bootstrap_lowerQuantiles
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {η : Measure ℝ} [IsProbabilityMeasure η] [NoAtoms η]
    {Pstar : ℕ → Ω → Measure Ωs} {Tstar : ℕ → Ω → Ωs → ℝ}
    {θ : ℝ} {θhat se : ℕ → Ω → ℝ}
    {ξ : Ωlim → ℝ} {q α : ℝ}
    (hse : ∀ n ω, 0 < se n ω)
    (htstat :
      TendstoInDistribution
        (fun n ω => percentileTStatistic θ (θhat n ω) (se n ω))
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
        μ {ω | percentileTCIEvent θ (θhat n ω) (se n ω)
          (bootstrapScalarLowerQuantile Pstar Tstar (α / 2) n ω)
          (bootstrapScalarLowerQuantile Pstar Tstar (1 - α / 2) n ω)})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) := by
  have hlower :
      TendstoInMeasure μ
        (bootstrapScalarLowerQuantile Pstar Tstar (α / 2))
        atTop (fun _ => -q) :=
    bootstrapScalarLowerQuantile_tendsto_of_strictMono_cdf
      (μ := μ) (Pstar := Pstar) (Zstar := Tstar)
      (G := fun x => cdf η x) (p := α / 2) (q := -q)
      hmono hneLower hbddLower hlocalLower hstrict hcdfLower hcdf
  have hupper :
      TendstoInMeasure μ
        (bootstrapScalarLowerQuantile Pstar Tstar (1 - α / 2))
        atTop (fun _ => q) :=
    bootstrapScalarLowerQuantile_tendsto_of_strictMono_cdf
      (μ := μ) (Pstar := Pstar) (Zstar := Tstar)
      (G := fun x => cdf η x) (p := 1 - α / 2) (q := q)
      hmono hneUpper hbddUpper hlocalUpper hstrict hcdfUpper hcdf
  exact
    chapter10_percentileTCI_coverage_tendsto_one_sub_alpha_of_components_symmetric_cdf
      (μ := μ) (ν := ν) (η := η) (θ := θ) (θhat := θhat)
      (se := se)
      (qLower := bootstrapScalarLowerQuantile Pstar Tstar (α / 2))
      (qUpper := bootstrapScalarLowerQuantile Pstar Tstar (1 - α / 2))
      (ξ := ξ) (q := q) (α := α)
      hse htstat hlower hupper hlower_meas hupper_meas hξ
      hq_nonneg hcdfLower hcdfUpper

/-- Symmetric percentile-`t` coverage from bootstrap-distribution convergence
of the bootstrap t-ratio statistic.

This is the Definition 10.2-facing version of
`chapter10_percentileTCI_coverage_tendsto_one_sub_alpha_of_bootstrap_lowerQuantiles`. -/
theorem
    chapter10_percentileTCI_coverage_tendsto_one_sub_alpha_of_bootstrapDistribution_lowerQuantiles
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {η : Measure ℝ} [IsProbabilityMeasure η] [NoAtoms η]
    {Pstar : ℕ → Ω → Measure Ωs} {Tstar : ℕ → Ω → Ωs → ℝ}
    {θ : ℝ} {θhat se : ℕ → Ω → ℝ}
    {ξ : Ωlim → ℝ} {q α : ℝ}
    (hse : ∀ n ω, 0 < se n ω)
    (htstat :
      TendstoInDistribution
        (fun n ω => percentileTStatistic θ (θhat n ω) (se n ω))
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
        μ {ω | percentileTCIEvent θ (θhat n ω) (se n ω)
          (bootstrapScalarLowerQuantile Pstar Tstar (α / 2) n ω)
          (bootstrapScalarLowerQuantile Pstar Tstar (1 - α / 2) n ω)})
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
    chapter10_percentileTCI_coverage_tendsto_one_sub_alpha_of_bootstrap_lowerQuantiles
      (μ := μ) (ν := ν) (η := η) (Pstar := Pstar) (Tstar := Tstar)
      (θ := θ) (θhat := θhat) (se := se) (ξ := ξ) (q := q)
      (α := α)
      hse htstat hmono hneLower hbddLower hlocalLower hneUpper hbddUpper
      hlocalUpper hstrict hcdf hlower_meas hupper_meas hξ hq_nonneg
      hcdfLower hcdfUpper

/-- Symmetric percentile-`t` coverage from bootstrap-distribution convergence,
using local limit-CDF bracketing at the lower and upper quantiles.

This variant avoids a global strict-monotonicity premise on the scalar limit
CDF. -/
theorem
chapter10_percentileTCI_coverage_tendsto_one_sub_alpha_of_bootstrapDistribution_brackets
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {η : Measure ℝ} [IsProbabilityMeasure η] [NoAtoms η]
    {Pstar : ℕ → Ω → Measure Ωs} {Tstar : ℕ → Ω → Ωs → ℝ}
    {θ : ℝ} {θhat se : ℕ → Ω → ℝ}
    {ξ : Ωlim → ℝ} {q α : ℝ}
    (hse : ∀ n ω, 0 < se n ω)
    (htstat :
      TendstoInDistribution
        (fun n ω => percentileTStatistic θ (θhat n ω) (se n ω))
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
        μ {ω | percentileTCIEvent θ (θhat n ω) (se n ω)
          (bootstrapScalarLowerQuantile Pstar Tstar (α / 2) n ω)
          (bootstrapScalarLowerQuantile Pstar Tstar (1 - α / 2) n ω)})
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
    chapter10_percentileTCI_coverage_tendsto_one_sub_alpha_of_bootstrap_lowerQuantiles_brackets
      (μ := μ) (ν := ν) (η := η) (Pstar := Pstar) (Tstar := Tstar)
      (θ := θ) (θhat := θhat) (se := se) (ξ := ξ) (q := q)
      (α := α)
      hse htstat hmono hneLower hbddLower hlocalLower hneUpper hbddUpper
      hlocalUpper hleftLower hrightLower hleftUpper hrightUpper hcdf
      hlower_meas hupper_meas hξ hq_nonneg hcdfLower hcdfUpper

/-- Symmetric percentile-`t` coverage from one-dimensional bootstrap
distribution convergence, with probability-CDF bracketing discharged at
levels `α / 2` and `1 - α / 2`. -/
theorem
chapter10_percentileTCI_coverage_tendsto_one_sub_alpha_of_bootstrapDistribution_quantile_prob
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {η : Measure ℝ} [IsProbabilityMeasure η] [NoAtoms η]
    {Pstar : ℕ → Ω → Measure Ωs} {Tstar : ℕ → Ω → Ωs → ℝ}
    {θ : ℝ} {θhat se : ℕ → Ω → ℝ}
    {ξ : Ωlim → ℝ} {q α : ℝ}
    (hse : ∀ n ω, 0 < se n ω)
    (htstat :
      TendstoInDistribution
        (fun n ω => percentileTStatistic θ (θhat n ω) (se n ω))
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
        μ {ω | percentileTCIEvent θ (θhat n ω) (se n ω)
          (bootstrapScalarLowerQuantile Pstar Tstar (α / 2) n ω)
          (bootstrapScalarLowerQuantile Pstar Tstar (1 - α / 2) n ω)})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) := by
  have hPstarFinite : ∀ n ω, IsFiniteMeasure (Pstar n ω) := by
    intro n ω
    haveI : IsProbabilityMeasure (Pstar n ω) := hPstar n ω
    infer_instance
  exact
    chapter10_percentileTCI_coverage_tendsto_one_sub_alpha_of_bootstrapDistribution_lowerQuantiles
      (μ := μ) (ν := ν) (η := η) (Pstar := Pstar) (Tstar := Tstar)
      (θ := θ) (θhat := θhat) (se := se) (ξ := ξ) (q := q)
      (α := α) hse htstat hPstarFinite
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

/-- Symmetric percentile-`t` coverage from a one-dimensional bootstrap
distribution whose scalar limit has law `η`.

This law-facing variant lets the bootstrap t-ratio limit live on an auxiliary
probability space while `HasLaw` supplies the scalar CDF used to identify the
lower generalized-inverse endpoints. -/
theorem
chapter10_percentileTCI_coverage_bootstrapDistribution_law_quantile_prob
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {Ωstar : Type*} [MeasurableSpace Ωstar]
    {η : Measure ℝ} [IsProbabilityMeasure η] [NoAtoms η]
    {νstar : Measure Ωstar} {Zlim : Ωstar → ℝ}
    {Pstar : ℕ → Ω → Measure Ωs} {Tstar : ℕ → Ω → Ωs → ℝ}
    {θ : ℝ} {θhat se : ℕ → Ω → ℝ}
    {ξ : Ωlim → ℝ} {q α : ℝ}
    (hse : ∀ n ω, 0 < se n ω)
    (htstat :
      TendstoInDistribution
        (fun n ω => percentileTStatistic θ (θhat n ω) (se n ω))
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
        μ {ω | percentileTCIEvent θ (θhat n ω) (se n ω)
          (bootstrapScalarLowerQuantile Pstar Tstar (α / 2) n ω)
          (bootstrapScalarLowerQuantile Pstar Tstar (1 - α / 2) n ω)})
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
    chapter10_percentileTCI_coverage_tendsto_one_sub_alpha_of_components_symmetric_cdf
      (μ := μ) (ν := ν) (η := η) (θ := θ) (θhat := θhat)
      (se := se) (qLower := Qlower) (qUpper := Qupper) (ξ := ξ)
      (q := q) (α := α)
      hse htstat hQlower hQupper hQlower_meas hQupper_meas hξ
      hq_nonneg hcdfLower hcdfUpper

/-- Symmetric percentile-`t` coverage from an auxiliary one-dimensional
bootstrap limit, retaining local CDF bracketing at the lower generalized
inverse endpoints.

This law-facing variant is the local-bracketing counterpart of
`chapter10_percentileTCI_coverage_bootstrapDistribution_law_quantile_prob`:
the bootstrap t-ratio limit may live on an auxiliary probability space, and
`HasLaw` identifies its scalar CDF with `cdf η`. -/
theorem
chapter10_percentileTCI_coverage_bootstrapDistribution_law_quantile_prob_brackets
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {Ωstar : Type*} [MeasurableSpace Ωstar]
    {η : Measure ℝ} [IsProbabilityMeasure η] [NoAtoms η]
    {νstar : Measure Ωstar} {Zlim : Ωstar → ℝ}
    {Pstar : ℕ → Ω → Measure Ωs} {Tstar : ℕ → Ω → Ωs → ℝ}
    {θ : ℝ} {θhat se : ℕ → Ω → ℝ}
    {ξ : Ωlim → ℝ} {q α : ℝ}
    (hse : ∀ n ω, 0 < se n ω)
    (htstat :
      TendstoInDistribution
        (fun n ω => percentileTStatistic θ (θhat n ω) (se n ω))
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
        μ {ω | percentileTCIEvent θ (θhat n ω) (se n ω)
          (bootstrapScalarLowerQuantile Pstar Tstar (α / 2) n ω)
          (bootstrapScalarLowerQuantile Pstar Tstar (1 - α / 2) n ω)})
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
    chapter10_percentileTCI_coverage_tendsto_one_sub_alpha_of_components_symmetric_cdf
      (μ := μ) (ν := ν) (η := η) (θ := θ) (θhat := θhat)
      (se := se) (qLower := Qlower) (qUpper := Qupper) (ξ := ξ)
      (q := q) (α := α)
      hse htstat hQlower hQupper hQlower_meas hQupper_meas hξ
      hq_nonneg hcdfLower hcdfUpper

/-- Symmetric percentile-`t` coverage from bootstrap-distribution convergence,
with bootstrap-side probability-CDF bracketing discharged and local
limit-CDF bracketing retained at `-q` and `q`. -/
theorem
chapter10_percentileTCI_coverage_tendsto_one_sub_alpha_quantile_prob_brackets
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {η : Measure ℝ} [IsProbabilityMeasure η] [NoAtoms η]
    {Pstar : ℕ → Ω → Measure Ωs} {Tstar : ℕ → Ω → Ωs → ℝ}
    {θ : ℝ} {θhat se : ℕ → Ω → ℝ}
    {ξ : Ωlim → ℝ} {q α : ℝ}
    (hse : ∀ n ω, 0 < se n ω)
    (htstat :
      TendstoInDistribution
        (fun n ω => percentileTStatistic θ (θhat n ω) (se n ω))
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
        μ {ω | percentileTCIEvent θ (θhat n ω) (se n ω)
          (bootstrapScalarLowerQuantile Pstar Tstar (α / 2) n ω)
          (bootstrapScalarLowerQuantile Pstar Tstar (1 - α / 2) n ω)})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) := by
  have hPstarFinite : ∀ n ω, IsFiniteMeasure (Pstar n ω) := by
    intro n ω
    haveI : IsProbabilityMeasure (Pstar n ω) := hPstar n ω
    infer_instance
  exact
    chapter10_percentileTCI_coverage_tendsto_one_sub_alpha_of_bootstrapDistribution_brackets
      (μ := μ) (ν := ν) (η := η) (Pstar := Pstar) (Tstar := Tstar)
      (θ := θ) (θhat := θhat) (se := se) (ξ := ξ) (q := q)
      (α := α) hse htstat hPstarFinite
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

/-- Indexed symmetric percentile-`t` coverage from one-dimensional bootstrap
distribution convergence, with bootstrap-side probability-CDF bracketing
discharged and local limit-CDF bracketing retained at `-q` and `q`. -/
theorem
chapter10_percentileTCI_coverage_tendsto_one_sub_alpha_indexed_quantile_prob_brackets
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {η : Measure ℝ} [IsProbabilityMeasure η] [NoAtoms η]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Tstar : ∀ n, Ω → Ωboot n → ℝ}
    {θ : ℝ} {θhat se : ℕ → Ω → ℝ}
    {ξ : Ωlim → ℝ} {q α : ℝ}
    (hse : ∀ n ω, 0 < se n ω)
    (htstat :
      TendstoInDistribution
        (fun n ω => percentileTStatistic θ (θhat n ω) (se n ω))
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
        μ {ω | percentileTCIEvent θ (θhat n ω) (se n ω)
          (bootstrapScalarLowerQuantileIndexed Pstar Tstar (α / 2) n ω)
          (bootstrapScalarLowerQuantileIndexed Pstar Tstar (1 - α / 2) n ω)})
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
    chapter10_percentileTCI_coverage_tendsto_one_sub_alpha_of_components_symmetric_cdf
      (μ := μ) (ν := ν) (η := η) (θ := θ) (θhat := θhat)
      (se := se) (qLower := Qlower) (qUpper := Qupper) (ξ := ξ)
      (q := q) (α := α)
      hse htstat hQlower hQupper hQlower_meas hQupper_meas hξ
      hq_nonneg hcdfLower hcdfUpper
  simpa [Qlower, Qupper] using hcoverage

/-- Indexed symmetric percentile-`t` coverage from one-dimensional bootstrap
distribution convergence, with probability-CDF bracketing discharged at levels
`α / 2` and `1 - α / 2`.

This is the strict-CDF counterpart of
`chapter10_percentileTCI_coverage_tendsto_one_sub_alpha_indexed_quantile_prob_brackets`. -/
theorem
chapter10_percentileTCI_coverage_tendsto_one_sub_alpha_indexed_bootstrapDistribution_quantile_prob
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {η : Measure ℝ} [IsProbabilityMeasure η] [NoAtoms η]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Tstar : ∀ n, Ω → Ωboot n → ℝ}
    {θ : ℝ} {θhat se : ℕ → Ω → ℝ}
    {ξ : Ωlim → ℝ} {q α : ℝ}
    (hse : ∀ n ω, 0 < se n ω)
    (htstat :
      TendstoInDistribution
        (fun n ω => percentileTStatistic θ (θhat n ω) (se n ω))
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
        μ {ω | percentileTCIEvent θ (θhat n ω) (se n ω)
          (bootstrapScalarLowerQuantileIndexed Pstar Tstar (α / 2) n ω)
          (bootstrapScalarLowerQuantileIndexed Pstar Tstar (1 - α / 2) n ω)})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) := by
  obtain ⟨hleftLower, hrightLower⟩ :=
    strictMono_cdf_brackets hstrict hcdfLower
  obtain ⟨hleftUpper, hrightUpper⟩ :=
    strictMono_cdf_brackets hstrict hcdfUpper
  exact
    chapter10_percentileTCI_coverage_tendsto_one_sub_alpha_indexed_quantile_prob_brackets
      (μ := μ) (ν := ν) (η := η) (Pstar := Pstar) (Tstar := Tstar)
      (θ := θ) (θhat := θhat) (se := se) (ξ := ξ) (q := q)
      (α := α) hse htstat hPstar hTmeas hα_pos hα_lt_one
      hleftLower hrightLower hleftUpper hrightUpper hTstar hcont
      hlower_meas hupper_meas hξ hq_nonneg hcdfLower hcdfUpper

/-- Indexed symmetric percentile-`t` coverage from a one-dimensional bootstrap
distribution whose scalar limit has law `η`.

This sample-size-dependent law-facing wrapper lets the bootstrap t-ratio limit
live on an auxiliary probability space while `HasLaw` supplies the scalar CDF
used to identify the lower generalized-inverse endpoints. -/
theorem
chapter10_indexed_percentileTCI_coverage_bootstrapDistribution_law_quantile_prob
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {Ωstar : Type*} [MeasurableSpace Ωstar]
    {η : Measure ℝ} [IsProbabilityMeasure η] [NoAtoms η]
    {νstar : Measure Ωstar} {Zlim : Ωstar → ℝ}
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Tstar : ∀ n, Ω → Ωboot n → ℝ}
    {θ : ℝ} {θhat se : ℕ → Ω → ℝ}
    {ξ : Ωlim → ℝ} {q α : ℝ}
    (hse : ∀ n ω, 0 < se n ω)
    (htstat :
      TendstoInDistribution
        (fun n ω => percentileTStatistic θ (θhat n ω) (se n ω))
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
        μ {ω | percentileTCIEvent θ (θhat n ω) (se n ω)
          (bootstrapScalarLowerQuantileIndexed Pstar Tstar (α / 2) n ω)
          (bootstrapScalarLowerQuantileIndexed Pstar Tstar (1 - α / 2) n ω)})
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
    chapter10_percentileTCI_coverage_tendsto_one_sub_alpha_of_components_symmetric_cdf
      (μ := μ) (ν := ν) (η := η) (θ := θ) (θhat := θhat)
      (se := se) (qLower := Qlower) (qUpper := Qupper) (ξ := ξ)
      (q := q) (α := α)
      hse htstat hQlower hQupper hQlower_meas hQupper_meas hξ
      hq_nonneg hcdfLower hcdfUpper

/-- Indexed symmetric percentile-`t` coverage from an auxiliary
one-dimensional bootstrap limit, retaining local CDF bracketing at the lower
generalized-inverse endpoints.

This sample-size-dependent law-facing wrapper is the indexed counterpart of
`chapter10_percentileTCI_coverage_bootstrapDistribution_law_quantile_prob_brackets`. -/
theorem
chapter10_indexed_percentileTCI_coverage_bootstrapDistribution_law_quantile_prob_brackets
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {Ωstar : Type*} [MeasurableSpace Ωstar]
    {η : Measure ℝ} [IsProbabilityMeasure η] [NoAtoms η]
    {νstar : Measure Ωstar} {Zlim : Ωstar → ℝ}
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Tstar : ∀ n, Ω → Ωboot n → ℝ}
    {θ : ℝ} {θhat se : ℕ → Ω → ℝ}
    {ξ : Ωlim → ℝ} {q α : ℝ}
    (hse : ∀ n ω, 0 < se n ω)
    (htstat :
      TendstoInDistribution
        (fun n ω => percentileTStatistic θ (θhat n ω) (se n ω))
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
        μ {ω | percentileTCIEvent θ (θhat n ω) (se n ω)
          (bootstrapScalarLowerQuantileIndexed Pstar Tstar (α / 2) n ω)
          (bootstrapScalarLowerQuantileIndexed Pstar Tstar (1 - α / 2) n ω)})
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
    chapter10_percentileTCI_coverage_tendsto_one_sub_alpha_of_components_symmetric_cdf
      (μ := μ) (ν := ν) (η := η) (θ := θ) (θhat := θhat)
      (se := se) (qLower := Qlower) (qUpper := Qupper) (ξ := ξ)
      (q := q) (α := α)
      hse htstat hQlower hQupper hQlower_meas hQupper_meas hξ
      hq_nonneg hcdfLower hcdfUpper

/-- Indexed ordinary nonparametric-bootstrap percentile-`t` coverage from the
concrete normalized scalar `Fin (n+1)` resample-mean CLT.

The bootstrap percentile-`t` critical values are the lower generalized
inverses of the conditional CDF of `sqrt(n+1) (Ybar*_n - Ybar_n)` under the
finite ordinary resampling law.  The sample-side t-ratio convergence,
positive-standard-error premise, and endpoint calibration remain explicit, as
in Hansen Theorem 10.14. -/
theorem
chapter10_percentileTCI_coverage_indexed_finSucc_resampleMean_brackets
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {η : Measure ℝ} [IsProbabilityMeasure η] [NoAtoms η]
    (Y : ℕ → Ω → ℝ)
    (hYmem : MemLp (Y 0) 2 μ)
    (hindep : iIndepFun Y μ)
    (hident : ∀ i, IdentDistrib (Y i) (Y 0) μ μ)
    (hS : (covMat μ (fun ω (_ : Unit) => Y 0 ω)).PosDef)
    {θ : ℝ} {θhat se : ℕ → Ω → ℝ}
    {ξ : Ωlim → ℝ} {q α : ℝ}
    (hse : ∀ n ω, 0 < se n ω)
    (htstat :
      TendstoInDistribution
        (fun n ω => percentileTStatistic θ (θhat n ω) (se n ω))
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
        μ {ω | percentileTCIEvent θ (θhat n ω) (se n ω)
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
            (α / 2) n ω)
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
            (1 - α / 2) n ω)})
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
    chapter10_indexed_percentileTCI_coverage_bootstrapDistribution_law_quantile_prob_brackets
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
      (θ := θ) (θhat := θhat) (se := se) (ξ := ξ) (q := q)
      (α := α) hse htstat hPstar hTmeas hα_pos hα_lt_one
      hleftLower hrightLower hleftUpper hrightUpper hTstar hZlaw hcont
      hlower_meas hupper_meas hξ hq_nonneg hcdfLower hcdfUpper

/-- Strict-CDF counterpart of
`chapter10_percentileTCI_coverage_indexed_finSucc_resampleMean_brackets`.

The strict monotonicity of the scalar t-ratio limit CDF supplies the local
endpoint bracketing needed by the concrete ordinary-bootstrap percentile-`t`
constructor. -/
theorem
chapter10_percentileTCI_coverage_indexed_finSucc_resampleMean
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {η : Measure ℝ} [IsProbabilityMeasure η] [NoAtoms η]
    (Y : ℕ → Ω → ℝ)
    (hYmem : MemLp (Y 0) 2 μ)
    (hindep : iIndepFun Y μ)
    (hident : ∀ i, IdentDistrib (Y i) (Y 0) μ μ)
    (hS : (covMat μ (fun ω (_ : Unit) => Y 0 ω)).PosDef)
    {θ : ℝ} {θhat se : ℕ → Ω → ℝ}
    {ξ : Ωlim → ℝ} {q α : ℝ}
    (hse : ∀ n ω, 0 < se n ω)
    (htstat :
      TendstoInDistribution
        (fun n ω => percentileTStatistic θ (θhat n ω) (se n ω))
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
        μ {ω | percentileTCIEvent θ (θhat n ω) (se n ω)
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
            (α / 2) n ω)
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
            (1 - α / 2) n ω)})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) := by
  obtain ⟨hleftLower, hrightLower⟩ :=
    strictMono_cdf_brackets hstrict hcdfLower
  obtain ⟨hleftUpper, hrightUpper⟩ :=
    strictMono_cdf_brackets hstrict hcdfUpper
  exact
    chapter10_percentileTCI_coverage_indexed_finSucc_resampleMean_brackets
      (μ := μ) (ν := ν) (η := η) Y hYmem hindep hident hS
      (θ := θ) (θhat := θhat) (se := se) (ξ := ξ) (q := q)
      (α := α) hse htstat hα_pos hα_lt_one hleftLower hrightLower
      hleftUpper hrightUpper hcont hlower_meas hupper_meas hξ hZlaw
      hq_nonneg hcdfLower hcdfUpper

/-- Regression-facing percentile-`t` coverage from the Theorem 10.18
bootstrap t-statistic route.

The bootstrap lower quantiles are computed from the studentized transformed
statistic `TthetaStar / seThetaStar`.  The joint numerator/standard-error weak
limit and scale consistency feed Theorem 10.18's standard-normal bootstrap CDF
wrapper; the existing Theorem 10.14 quantile route then gives `1 - α`
coverage. -/
theorem
chapter10_percentileTCI_coverage_tendsto_one_sub_alpha_of_bootstrap_regression_tstat
    [IsProbabilityMeasure μ]
    {Pstar : ℕ → Ω → Measure Ωs}
    {TthetaStar seThetaStar : ℕ → Ω → Ωs → ℝ}
    {θ : ℝ} {θhat se : ℕ → Ω → ℝ} {seθ q α : ℝ}
    (hsampleSe : ∀ n ω, 0 < se n ω)
    (htstat :
      TendstoInDistribution
        (fun n ω => percentileTStatistic θ (θhat n ω) (se n ω))
        atTop (fun x : ℝ => x) (fun _ => μ) (gaussianReal 0 1))
    (hseθ : 0 < seθ)
    (hjoint :
      TendstoInBootstrapWeakDistribution μ Pstar
        (fun n ω ωs => (TthetaStar n ω ωs, seThetaStar n ω ωs))
        (gaussianReal 0 1) (fun z : ℝ => (seθ * z, seθ)))
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hTthetaStar : ∀ n ω, Measurable (TthetaStar n ω))
    (hseThetaStar : ∀ n ω, Measurable (seThetaStar n ω))
    (hseStar :
      TendstoInBootstrapProbability μ Pstar seThetaStar (fun _ => seθ))
    (hα_pos : 0 < α) (hα_lt_one : α < 1)
    (hstrict : StrictMono (fun x => cdf (gaussianReal 0 1) x))
    (hlower_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantile Pstar
            (fun n ω ωs => TthetaStar n ω ωs / seThetaStar n ω ωs)
            (α / 2) n) μ)
    (hupper_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantile Pstar
            (fun n ω ωs => TthetaStar n ω ωs / seThetaStar n ω ωs)
            (1 - α / 2) n) μ)
    (hq_nonneg : 0 ≤ q)
    (hcdfLower : cdf (gaussianReal 0 1) (-q) = α / 2)
    (hcdfUpper : cdf (gaussianReal 0 1) q = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | percentileTCIEvent θ (θhat n ω) (se n ω)
          (bootstrapScalarLowerQuantile Pstar
            (fun n ω ωs => TthetaStar n ω ωs / seThetaStar n ω ωs)
            (α / 2) n ω)
          (bootstrapScalarLowerQuantile Pstar
            (fun n ω ωs => TthetaStar n ω ωs / seThetaStar n ω ωs)
            (1 - α / 2) n ω)})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) := by
  let Tstar : ℕ → Ω → Ωs → ℝ :=
    fun n ω ωs => TthetaStar n ω ωs / seThetaStar n ω ωs
  haveI : NoAtoms (gaussianReal 0 1) :=
    noAtoms_gaussianReal (μ := 0) (v := 1) (by norm_num)
  have hTmeas : ∀ n ω, AEMeasurable (Tstar n ω) (Pstar n ω) := by
    intro n ω
    exact ((hTthetaStar n ω).div (hseThetaStar n ω)).aemeasurable
  have hTstar :
      TendstoInBootstrapDistribution μ Pstar
        (fun n ω ωs (_ : Unit) => Tstar n ω ωs)
        (gaussianReal 0 1) (fun x : ℝ => fun _ : Unit => x) := by
    simpa [Tstar] using
      chapter10_bootstrap_regression_tstat_distribution_standardNormal
        (μ := μ) (Pstar := Pstar) (TthetaStar := TthetaStar)
        (seThetaStar := seThetaStar) (seθ := seθ)
        hseθ hjoint hPstar hTthetaStar hseThetaStar hseStar
  have hlower_meas' :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantile Pstar Tstar (α / 2) n) μ := by
    intro n
    simpa [Tstar] using hlower_meas n
  have hupper_meas' :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantile Pstar Tstar (1 - α / 2) n) μ := by
    intro n
    simpa [Tstar] using hupper_meas n
  have hξ : HasLaw (fun x : ℝ => x) (gaussianReal 0 1) (gaussianReal 0 1) := by
    simpa [id] using (HasLaw.id (μ := gaussianReal 0 1))
  have hcoverage :=
    chapter10_percentileTCI_coverage_tendsto_one_sub_alpha_of_bootstrapDistribution_quantile_prob
      (μ := μ) (ν := gaussianReal 0 1) (η := gaussianReal 0 1)
      (Pstar := Pstar) (Tstar := Tstar) (θ := θ) (θhat := θhat)
      (se := se) (ξ := fun x : ℝ => x) (q := q) (α := α)
      hsampleSe htstat hPstar hTmeas hα_pos hα_lt_one hstrict hTstar
      (fun x => continuousAt_cdf_standardNormal x)
      hlower_meas' hupper_meas' hξ hq_nonneg hcdfLower hcdfUpper
  simpa [Tstar] using hcoverage

set_option linter.style.longLine false

/-- Regression-facing percentile-`t` coverage from the Theorem 10.18
bootstrap t-statistic route, using local standard-normal CDF bracketing.

This is the local-bracketing counterpart of
`chapter10_percentileTCI_coverage_tendsto_one_sub_alpha_of_bootstrap_regression_tstat`;
it avoids requiring global strict monotonicity of the standard-normal CDF. -/
theorem
chapter10_percentileTCI_coverage_tendsto_one_sub_alpha_of_bootstrap_regression_tstat_brackets
    [IsProbabilityMeasure μ]
    {Pstar : ℕ → Ω → Measure Ωs}
    {TthetaStar seThetaStar : ℕ → Ω → Ωs → ℝ}
    {θ : ℝ} {θhat se : ℕ → Ω → ℝ} {seθ q α : ℝ}
    (hsampleSe : ∀ n ω, 0 < se n ω)
    (htstat :
      TendstoInDistribution
        (fun n ω => percentileTStatistic θ (θhat n ω) (se n ω))
        atTop (fun x : ℝ => x) (fun _ => μ) (gaussianReal 0 1))
    (hseθ : 0 < seθ)
    (hjoint :
      TendstoInBootstrapWeakDistribution μ Pstar
        (fun n ω ωs => (TthetaStar n ω ωs, seThetaStar n ω ωs))
        (gaussianReal 0 1) (fun z : ℝ => (seθ * z, seθ)))
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hTthetaStar : ∀ n ω, Measurable (TthetaStar n ω))
    (hseThetaStar : ∀ n ω, Measurable (seThetaStar n ω))
    (hseStar :
      TendstoInBootstrapProbability μ Pstar seThetaStar (fun _ => seθ))
    (hα_pos : 0 < α) (hα_lt_one : α < 1)
    (hleftLower :
      ∀ ε : ℝ, 0 < ε → cdf (gaussianReal 0 1) (-q - ε) < α / 2)
    (hrightLower :
      ∀ ε : ℝ, 0 < ε → α / 2 < cdf (gaussianReal 0 1) (-q + ε))
    (hleftUpper :
      ∀ ε : ℝ, 0 < ε → cdf (gaussianReal 0 1) (q - ε) < 1 - α / 2)
    (hrightUpper :
      ∀ ε : ℝ, 0 < ε → 1 - α / 2 < cdf (gaussianReal 0 1) (q + ε))
    (hlower_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantile Pstar
            (fun n ω ωs => TthetaStar n ω ωs / seThetaStar n ω ωs)
            (α / 2) n) μ)
    (hupper_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantile Pstar
            (fun n ω ωs => TthetaStar n ω ωs / seThetaStar n ω ωs)
            (1 - α / 2) n) μ)
    (hq_nonneg : 0 ≤ q)
    (hcdfLower : cdf (gaussianReal 0 1) (-q) = α / 2)
    (hcdfUpper : cdf (gaussianReal 0 1) q = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | percentileTCIEvent θ (θhat n ω) (se n ω)
          (bootstrapScalarLowerQuantile Pstar
            (fun n ω ωs => TthetaStar n ω ωs / seThetaStar n ω ωs)
            (α / 2) n ω)
          (bootstrapScalarLowerQuantile Pstar
            (fun n ω ωs => TthetaStar n ω ωs / seThetaStar n ω ωs)
            (1 - α / 2) n ω)})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) := by
  let Tstar : ℕ → Ω → Ωs → ℝ :=
    fun n ω ωs => TthetaStar n ω ωs / seThetaStar n ω ωs
  haveI : NoAtoms (gaussianReal 0 1) :=
    noAtoms_gaussianReal (μ := 0) (v := 1) (by norm_num)
  have hTmeas : ∀ n ω, AEMeasurable (Tstar n ω) (Pstar n ω) := by
    intro n ω
    exact ((hTthetaStar n ω).div (hseThetaStar n ω)).aemeasurable
  have hTstar :
      TendstoInBootstrapDistribution μ Pstar
        (fun n ω ωs (_ : Unit) => Tstar n ω ωs)
        (gaussianReal 0 1) (fun x : ℝ => fun _ : Unit => x) := by
    simpa [Tstar] using
      chapter10_bootstrap_regression_tstat_distribution_standardNormal
        (μ := μ) (Pstar := Pstar) (TthetaStar := TthetaStar)
        (seThetaStar := seThetaStar) (seθ := seθ)
        hseθ hjoint hPstar hTthetaStar hseThetaStar hseStar
  have hlower_meas' :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantile Pstar Tstar (α / 2) n) μ := by
    intro n
    simpa [Tstar] using hlower_meas n
  have hupper_meas' :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantile Pstar Tstar (1 - α / 2) n) μ := by
    intro n
    simpa [Tstar] using hupper_meas n
  have hξ : HasLaw (fun x : ℝ => x) (gaussianReal 0 1) (gaussianReal 0 1) := by
    simpa [id] using (HasLaw.id (μ := gaussianReal 0 1))
  have hcoverage :=
    chapter10_percentileTCI_coverage_tendsto_one_sub_alpha_quantile_prob_brackets
      (μ := μ) (ν := gaussianReal 0 1) (η := gaussianReal 0 1)
      (Pstar := Pstar) (Tstar := Tstar) (θ := θ) (θhat := θhat)
      (se := se) (ξ := fun x : ℝ => x) (q := q) (α := α)
      hsampleSe htstat hPstar hTmeas hα_pos hα_lt_one
      hleftLower hrightLower hleftUpper hrightUpper hTstar
      (fun x => continuousAt_cdf_standardNormal x)
      hlower_meas' hupper_meas' hξ hq_nonneg hcdfLower hcdfUpper
  simpa [Tstar] using hcoverage

/-- Indexed regression-facing percentile-`t` coverage from the Theorem 10.18
bootstrap t-statistic route for sample-size-dependent bootstrap spaces. -/
theorem
chapter10_percentileTCI_coverage_tendsto_one_sub_alpha_indexed_of_bootstrap_regression_tstat
    [IsProbabilityMeasure μ]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {TthetaStar seThetaStar : ∀ n, Ω → Ωboot n → ℝ}
    {θ : ℝ} {θhat se : ℕ → Ω → ℝ} {seθ q α : ℝ}
    (hsampleSe : ∀ n ω, 0 < se n ω)
    (htstat :
      TendstoInDistribution
        (fun n ω => percentileTStatistic θ (θhat n ω) (se n ω))
        atTop (fun x : ℝ => x) (fun _ => μ) (gaussianReal 0 1))
    (hseθ : 0 < seθ)
    (hjoint :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar
        (fun n ω ωs => (TthetaStar n ω ωs, seThetaStar n ω ωs))
        (gaussianReal 0 1) (fun z : ℝ => (seθ * z, seθ)))
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hTthetaStar : ∀ n ω, Measurable (TthetaStar n ω))
    (hseThetaStar : ∀ n ω, Measurable (seThetaStar n ω))
    (hseStar :
      TendstoInBootstrapProbabilityIndexed μ Pstar seThetaStar (fun _ => seθ))
    (hα_pos : 0 < α) (hα_lt_one : α < 1)
    (hstrict : StrictMono (fun x => cdf (gaussianReal 0 1) x))
    (hlower_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed Pstar
            (fun n ω ωs => TthetaStar n ω ωs / seThetaStar n ω ωs)
            (α / 2) n) μ)
    (hupper_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed Pstar
            (fun n ω ωs => TthetaStar n ω ωs / seThetaStar n ω ωs)
            (1 - α / 2) n) μ)
    (hq_nonneg : 0 ≤ q)
    (hcdfLower : cdf (gaussianReal 0 1) (-q) = α / 2)
    (hcdfUpper : cdf (gaussianReal 0 1) q = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | percentileTCIEvent θ (θhat n ω) (se n ω)
          (bootstrapScalarLowerQuantileIndexed Pstar
            (fun n ω ωs => TthetaStar n ω ωs / seThetaStar n ω ωs)
            (α / 2) n ω)
          (bootstrapScalarLowerQuantileIndexed Pstar
            (fun n ω ωs => TthetaStar n ω ωs / seThetaStar n ω ωs)
            (1 - α / 2) n ω)})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) := by
  let Tstar : ∀ n, Ω → Ωboot n → ℝ :=
    fun n ω ωs => TthetaStar n ω ωs / seThetaStar n ω ωs
  haveI : NoAtoms (gaussianReal 0 1) :=
    noAtoms_gaussianReal (μ := 0) (v := 1) (by norm_num)
  have hTmeas : ∀ n ω, AEMeasurable (Tstar n ω) (Pstar n ω) := by
    intro n ω
    exact ((hTthetaStar n ω).div (hseThetaStar n ω)).aemeasurable
  have hTstar :
      TendstoInBootstrapDistributionIndexed μ Pstar
        (fun n ω ωs (_ : Unit) => Tstar n ω ωs)
        (gaussianReal 0 1) (fun x : ℝ => fun _ : Unit => x) := by
    simpa [Tstar] using
      chapter10_indexed_bootstrap_regression_tstat_distribution_standardNormal
        (μ := μ) (Pstar := Pstar) (TthetaStar := TthetaStar)
        (seThetaStar := seThetaStar) (seθ := seθ)
        hseθ hjoint hPstar hTthetaStar hseThetaStar hseStar
  have hlower_meas' :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed Pstar Tstar (α / 2) n) μ := by
    intro n
    simpa [Tstar] using hlower_meas n
  have hupper_meas' :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed Pstar Tstar (1 - α / 2) n) μ := by
    intro n
    simpa [Tstar] using hupper_meas n
  have hξ : HasLaw (fun x : ℝ => x) (gaussianReal 0 1) (gaussianReal 0 1) := by
    simpa [id] using (HasLaw.id (μ := gaussianReal 0 1))
  have hcoverage :=
    chapter10_percentileTCI_coverage_tendsto_one_sub_alpha_indexed_bootstrapDistribution_quantile_prob
      (μ := μ) (ν := gaussianReal 0 1) (η := gaussianReal 0 1)
      (Pstar := Pstar) (Tstar := Tstar) (θ := θ) (θhat := θhat)
      (se := se) (ξ := fun x : ℝ => x) (q := q) (α := α)
      hsampleSe htstat hPstar hTmeas hα_pos hα_lt_one hstrict hTstar
      (fun x => continuousAt_cdf_standardNormal x)
      hlower_meas' hupper_meas' hξ hq_nonneg hcdfLower hcdfUpper
  simpa [Tstar] using hcoverage

/-- Indexed regression-facing percentile-`t` coverage from the Theorem 10.18
bootstrap t-statistic route, using local standard-normal CDF bracketing. -/
theorem
chapter10_percentileTCI_coverage_tendsto_one_sub_alpha_indexed_of_bootstrap_regression_tstat_brackets
    [IsProbabilityMeasure μ]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {TthetaStar seThetaStar : ∀ n, Ω → Ωboot n → ℝ}
    {θ : ℝ} {θhat se : ℕ → Ω → ℝ} {seθ q α : ℝ}
    (hsampleSe : ∀ n ω, 0 < se n ω)
    (htstat :
      TendstoInDistribution
        (fun n ω => percentileTStatistic θ (θhat n ω) (se n ω))
        atTop (fun x : ℝ => x) (fun _ => μ) (gaussianReal 0 1))
    (hseθ : 0 < seθ)
    (hjoint :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar
        (fun n ω ωs => (TthetaStar n ω ωs, seThetaStar n ω ωs))
        (gaussianReal 0 1) (fun z : ℝ => (seθ * z, seθ)))
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hTthetaStar : ∀ n ω, Measurable (TthetaStar n ω))
    (hseThetaStar : ∀ n ω, Measurable (seThetaStar n ω))
    (hseStar :
      TendstoInBootstrapProbabilityIndexed μ Pstar seThetaStar (fun _ => seθ))
    (hα_pos : 0 < α) (hα_lt_one : α < 1)
    (hleftLower :
      ∀ ε : ℝ, 0 < ε → cdf (gaussianReal 0 1) (-q - ε) < α / 2)
    (hrightLower :
      ∀ ε : ℝ, 0 < ε → α / 2 < cdf (gaussianReal 0 1) (-q + ε))
    (hleftUpper :
      ∀ ε : ℝ, 0 < ε → cdf (gaussianReal 0 1) (q - ε) < 1 - α / 2)
    (hrightUpper :
      ∀ ε : ℝ, 0 < ε → 1 - α / 2 < cdf (gaussianReal 0 1) (q + ε))
    (hlower_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed Pstar
            (fun n ω ωs => TthetaStar n ω ωs / seThetaStar n ω ωs)
            (α / 2) n) μ)
    (hupper_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed Pstar
            (fun n ω ωs => TthetaStar n ω ωs / seThetaStar n ω ωs)
            (1 - α / 2) n) μ)
    (hq_nonneg : 0 ≤ q)
    (hcdfLower : cdf (gaussianReal 0 1) (-q) = α / 2)
    (hcdfUpper : cdf (gaussianReal 0 1) q = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | percentileTCIEvent θ (θhat n ω) (se n ω)
          (bootstrapScalarLowerQuantileIndexed Pstar
            (fun n ω ωs => TthetaStar n ω ωs / seThetaStar n ω ωs)
            (α / 2) n ω)
          (bootstrapScalarLowerQuantileIndexed Pstar
            (fun n ω ωs => TthetaStar n ω ωs / seThetaStar n ω ωs)
            (1 - α / 2) n ω)})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) := by
  let Tstar : ∀ n, Ω → Ωboot n → ℝ :=
    fun n ω ωs => TthetaStar n ω ωs / seThetaStar n ω ωs
  haveI : NoAtoms (gaussianReal 0 1) :=
    noAtoms_gaussianReal (μ := 0) (v := 1) (by norm_num)
  have hTmeas : ∀ n ω, AEMeasurable (Tstar n ω) (Pstar n ω) := by
    intro n ω
    exact ((hTthetaStar n ω).div (hseThetaStar n ω)).aemeasurable
  have hTstar :
      TendstoInBootstrapDistributionIndexed μ Pstar
        (fun n ω ωs (_ : Unit) => Tstar n ω ωs)
        (gaussianReal 0 1) (fun x : ℝ => fun _ : Unit => x) := by
    simpa [Tstar] using
      chapter10_indexed_bootstrap_regression_tstat_distribution_standardNormal
        (μ := μ) (Pstar := Pstar) (TthetaStar := TthetaStar)
        (seThetaStar := seThetaStar) (seθ := seθ)
        hseθ hjoint hPstar hTthetaStar hseThetaStar hseStar
  have hlower_meas' :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed Pstar Tstar (α / 2) n) μ := by
    intro n
    simpa [Tstar] using hlower_meas n
  have hupper_meas' :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed Pstar Tstar (1 - α / 2) n) μ := by
    intro n
    simpa [Tstar] using hupper_meas n
  have hξ : HasLaw (fun x : ℝ => x) (gaussianReal 0 1) (gaussianReal 0 1) := by
    simpa [id] using (HasLaw.id (μ := gaussianReal 0 1))
  have hcoverage :=
    chapter10_percentileTCI_coverage_tendsto_one_sub_alpha_indexed_quantile_prob_brackets
      (μ := μ) (ν := gaussianReal 0 1) (η := gaussianReal 0 1)
      (Pstar := Pstar) (Tstar := Tstar) (θ := θ) (θhat := θhat)
      (se := se) (ξ := fun x : ℝ => x) (q := q) (α := α)
      hsampleSe htstat hPstar hTmeas hα_pos hα_lt_one
      hleftLower hrightLower hleftUpper hrightUpper hTstar
      (fun x => continuousAt_cdf_standardNormal x)
      hlower_meas' hupper_meas' hξ hq_nonneg hcdfLower hcdfUpper
  simpa [Tstar] using hcoverage

/-- Regression-facing percentile-`t` coverage from a marginal numerator CLT
and explicit numerator/standard-error compact-tail control, using local
standard-normal CDF bracketing.

This composes the `*_of_numerator_tight` Theorem 10.18 t-statistic CDF route
directly with the Theorem 10.14 percentile-`t` lower-quantile theorem. -/
theorem
chapter10_percentileTCI_coverage_tendsto_one_sub_alpha_of_bootstrap_regression_tstat_numerator_tight_brackets
    [IsProbabilityMeasure μ]
    {Pstar : ℕ → Ω → Measure Ωs}
    {TthetaStar seThetaStar : ℕ → Ω → Ωs → ℝ}
    {θ : ℝ} {θhat se : ℕ → Ω → ℝ} {seθ q α : ℝ}
    (hsampleSe : ∀ n ω, 0 < se n ω)
    (htstat :
      TendstoInDistribution
        (fun n ω => percentileTStatistic θ (θhat n ω) (se n ω))
        atTop (fun x : ℝ => x) (fun _ => μ) (gaussianReal 0 1))
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
    (hseStar :
      TendstoInBootstrapProbability μ Pstar seThetaStar (fun _ => seθ))
    (hα_pos : 0 < α) (hα_lt_one : α < 1)
    (hleftLower :
      ∀ ε : ℝ, 0 < ε → cdf (gaussianReal 0 1) (-q - ε) < α / 2)
    (hrightLower :
      ∀ ε : ℝ, 0 < ε → α / 2 < cdf (gaussianReal 0 1) (-q + ε))
    (hleftUpper :
      ∀ ε : ℝ, 0 < ε → cdf (gaussianReal 0 1) (q - ε) < 1 - α / 2)
    (hrightUpper :
      ∀ ε : ℝ, 0 < ε → 1 - α / 2 < cdf (gaussianReal 0 1) (q + ε))
    (hlower_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantile Pstar
            (fun n ω ωs => TthetaStar n ω ωs / seThetaStar n ω ωs)
            (α / 2) n) μ)
    (hupper_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantile Pstar
            (fun n ω ωs => TthetaStar n ω ωs / seThetaStar n ω ωs)
            (1 - α / 2) n) μ)
    (hq_nonneg : 0 ≤ q)
    (hcdfLower : cdf (gaussianReal 0 1) (-q) = α / 2)
    (hcdfUpper : cdf (gaussianReal 0 1) q = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | percentileTCIEvent θ (θhat n ω) (se n ω)
          (bootstrapScalarLowerQuantile Pstar
            (fun n ω ωs => TthetaStar n ω ωs / seThetaStar n ω ωs)
            (α / 2) n ω)
          (bootstrapScalarLowerQuantile Pstar
            (fun n ω ωs => TthetaStar n ω ωs / seThetaStar n ω ωs)
            (1 - α / 2) n ω)})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) := by
  let Tstar : ℕ → Ω → Ωs → ℝ :=
    fun n ω ωs => TthetaStar n ω ωs / seThetaStar n ω ωs
  haveI : NoAtoms (gaussianReal 0 1) :=
    noAtoms_gaussianReal (μ := 0) (v := 1) (by norm_num)
  have hTmeas : ∀ n ω, AEMeasurable (Tstar n ω) (Pstar n ω) := by
    intro n ω
    exact ((hTthetaStar n ω).div (hseThetaStar n ω)).aemeasurable
  have hTstar :
      TendstoInBootstrapDistribution μ Pstar
        (fun n ω ωs (_ : Unit) => Tstar n ω ωs)
        (gaussianReal 0 1) (fun x : ℝ => fun _ : Unit => x) := by
    simpa [Tstar] using
      chapter10_bootstrap_regression_tstat_distribution_standardNormal_of_numerator_tight
        (μ := μ) (Pstar := Pstar) (TthetaStar := TthetaStar)
        (seThetaStar := seThetaStar) (seθ := seθ)
        hseθ hT hPstar hTthetaStar hseThetaStar hTail hseStar
  have hlower_meas' :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantile Pstar Tstar (α / 2) n) μ := by
    intro n
    simpa [Tstar] using hlower_meas n
  have hupper_meas' :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantile Pstar Tstar (1 - α / 2) n) μ := by
    intro n
    simpa [Tstar] using hupper_meas n
  have hξ : HasLaw (fun x : ℝ => x) (gaussianReal 0 1) (gaussianReal 0 1) := by
    simpa [id] using (HasLaw.id (μ := gaussianReal 0 1))
  have hcoverage :=
    chapter10_percentileTCI_coverage_tendsto_one_sub_alpha_quantile_prob_brackets
      (μ := μ) (ν := gaussianReal 0 1) (η := gaussianReal 0 1)
      (Pstar := Pstar) (Tstar := Tstar) (θ := θ) (θhat := θhat)
      (se := se) (ξ := fun x : ℝ => x) (q := q) (α := α)
      hsampleSe htstat hPstar hTmeas hα_pos hα_lt_one
      hleftLower hrightLower hleftUpper hrightUpper hTstar (fun x => continuousAt_cdf_standardNormal x)
      hlower_meas' hupper_meas' hξ hq_nonneg hcdfLower hcdfUpper
  simpa [Tstar] using hcoverage

/-- Strict-CDF counterpart of
`chapter10_percentileTCI_coverage_tendsto_one_sub_alpha_of_bootstrap_regression_tstat_numerator_tight_brackets`. -/
theorem
chapter10_percentileTCI_coverage_tendsto_one_sub_alpha_of_bootstrap_regression_tstat_numerator_tight
    [IsProbabilityMeasure μ]
    {Pstar : ℕ → Ω → Measure Ωs}
    {TthetaStar seThetaStar : ℕ → Ω → Ωs → ℝ}
    {θ : ℝ} {θhat se : ℕ → Ω → ℝ} {seθ q α : ℝ}
    (hsampleSe : ∀ n ω, 0 < se n ω)
    (htstat :
      TendstoInDistribution
        (fun n ω => percentileTStatistic θ (θhat n ω) (se n ω))
        atTop (fun x : ℝ => x) (fun _ => μ) (gaussianReal 0 1))
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
    (hseStar :
      TendstoInBootstrapProbability μ Pstar seThetaStar (fun _ => seθ))
    (hα_pos : 0 < α) (hα_lt_one : α < 1)
    (hstrict : StrictMono (fun x => cdf (gaussianReal 0 1) x))
    (hlower_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantile Pstar
            (fun n ω ωs => TthetaStar n ω ωs / seThetaStar n ω ωs)
            (α / 2) n) μ)
    (hupper_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantile Pstar
            (fun n ω ωs => TthetaStar n ω ωs / seThetaStar n ω ωs)
            (1 - α / 2) n) μ)
    (hq_nonneg : 0 ≤ q)
    (hcdfLower : cdf (gaussianReal 0 1) (-q) = α / 2)
    (hcdfUpper : cdf (gaussianReal 0 1) q = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | percentileTCIEvent θ (θhat n ω) (se n ω)
          (bootstrapScalarLowerQuantile Pstar
            (fun n ω ωs => TthetaStar n ω ωs / seThetaStar n ω ωs)
            (α / 2) n ω)
          (bootstrapScalarLowerQuantile Pstar
            (fun n ω ωs => TthetaStar n ω ωs / seThetaStar n ω ωs)
            (1 - α / 2) n ω)})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) := by
  obtain ⟨hleftLower, hrightLower⟩ :=
    strictMono_cdf_brackets hstrict hcdfLower
  obtain ⟨hleftUpper, hrightUpper⟩ :=
    strictMono_cdf_brackets hstrict hcdfUpper
  exact
    chapter10_percentileTCI_coverage_tendsto_one_sub_alpha_of_bootstrap_regression_tstat_numerator_tight_brackets
      (μ := μ) (Pstar := Pstar) (TthetaStar := TthetaStar)
      (seThetaStar := seThetaStar) (θ := θ) (θhat := θhat)
      (se := se) (seθ := seθ) (q := q) (α := α)
      hsampleSe htstat hseθ hT hPstar hTthetaStar hseThetaStar hTail
      hseStar hα_pos hα_lt_one hleftLower hrightLower hleftUpper
      hrightUpper hlower_meas hupper_meas hq_nonneg hcdfLower hcdfUpper

/-- Indexed regression-facing percentile-`t` coverage from a marginal
numerator CLT and explicit numerator/standard-error compact-tail control,
using local standard-normal CDF bracketing. -/
theorem
chapter10_percentileTCI_coverage_tendsto_one_sub_alpha_indexed_of_bootstrap_regression_tstat_numerator_tight_brackets
    [IsProbabilityMeasure μ]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {TthetaStar seThetaStar : ∀ n, Ω → Ωboot n → ℝ}
    {θ : ℝ} {θhat se : ℕ → Ω → ℝ} {seθ q α : ℝ}
    (hsampleSe : ∀ n ω, 0 < se n ω)
    (htstat :
      TendstoInDistribution
        (fun n ω => percentileTStatistic θ (θhat n ω) (se n ω))
        atTop (fun x : ℝ => x) (fun _ => μ) (gaussianReal 0 1))
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
    (hseStar :
      TendstoInBootstrapProbabilityIndexed μ Pstar seThetaStar (fun _ => seθ))
    (hα_pos : 0 < α) (hα_lt_one : α < 1)
    (hleftLower :
      ∀ ε : ℝ, 0 < ε → cdf (gaussianReal 0 1) (-q - ε) < α / 2)
    (hrightLower :
      ∀ ε : ℝ, 0 < ε → α / 2 < cdf (gaussianReal 0 1) (-q + ε))
    (hleftUpper :
      ∀ ε : ℝ, 0 < ε → cdf (gaussianReal 0 1) (q - ε) < 1 - α / 2)
    (hrightUpper :
      ∀ ε : ℝ, 0 < ε → 1 - α / 2 < cdf (gaussianReal 0 1) (q + ε))
    (hlower_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed Pstar
            (fun n ω ωs => TthetaStar n ω ωs / seThetaStar n ω ωs)
            (α / 2) n) μ)
    (hupper_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed Pstar
            (fun n ω ωs => TthetaStar n ω ωs / seThetaStar n ω ωs)
            (1 - α / 2) n) μ)
    (hq_nonneg : 0 ≤ q)
    (hcdfLower : cdf (gaussianReal 0 1) (-q) = α / 2)
    (hcdfUpper : cdf (gaussianReal 0 1) q = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | percentileTCIEvent θ (θhat n ω) (se n ω)
          (bootstrapScalarLowerQuantileIndexed Pstar
            (fun n ω ωs => TthetaStar n ω ωs / seThetaStar n ω ωs)
            (α / 2) n ω)
          (bootstrapScalarLowerQuantileIndexed Pstar
            (fun n ω ωs => TthetaStar n ω ωs / seThetaStar n ω ωs)
            (1 - α / 2) n ω)})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) := by
  let Tstar : ∀ n, Ω → Ωboot n → ℝ :=
    fun n ω ωs => TthetaStar n ω ωs / seThetaStar n ω ωs
  haveI : NoAtoms (gaussianReal 0 1) :=
    noAtoms_gaussianReal (μ := 0) (v := 1) (by norm_num)
  have hTmeas : ∀ n ω, AEMeasurable (Tstar n ω) (Pstar n ω) := by
    intro n ω
    exact ((hTthetaStar n ω).div (hseThetaStar n ω)).aemeasurable
  have hTstar :
      TendstoInBootstrapDistributionIndexed μ Pstar
        (fun n ω ωs (_ : Unit) => Tstar n ω ωs)
        (gaussianReal 0 1) (fun x : ℝ => fun _ : Unit => x) := by
    simpa [Tstar] using
      chapter10_indexed_bootstrap_regression_tstat_distribution_standardNormal_of_numerator_tight
        (μ := μ) (Pstar := Pstar) (TthetaStar := TthetaStar)
        (seThetaStar := seThetaStar) (seθ := seθ)
        hseθ hT hPstar hTthetaStar hseThetaStar hTail hseStar
  have hlower_meas' :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed Pstar Tstar (α / 2) n) μ := by
    intro n
    simpa [Tstar] using hlower_meas n
  have hupper_meas' :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed Pstar Tstar (1 - α / 2) n) μ := by
    intro n
    simpa [Tstar] using hupper_meas n
  have hξ : HasLaw (fun x : ℝ => x) (gaussianReal 0 1) (gaussianReal 0 1) := by
    simpa [id] using (HasLaw.id (μ := gaussianReal 0 1))
  have hcoverage :=
    chapter10_percentileTCI_coverage_tendsto_one_sub_alpha_indexed_quantile_prob_brackets
      (μ := μ) (ν := gaussianReal 0 1) (η := gaussianReal 0 1)
      (Pstar := Pstar) (Tstar := Tstar) (θ := θ) (θhat := θhat)
      (se := se) (ξ := fun x : ℝ => x) (q := q) (α := α)
      hsampleSe htstat hPstar hTmeas hα_pos hα_lt_one
      hleftLower hrightLower hleftUpper hrightUpper hTstar (fun x => continuousAt_cdf_standardNormal x)
      hlower_meas' hupper_meas' hξ hq_nonneg hcdfLower hcdfUpper
  simpa [Tstar] using hcoverage

/-- Strict-CDF counterpart of
`chapter10_percentileTCI_coverage_tendsto_one_sub_alpha_indexed_of_bootstrap_regression_tstat_numerator_tight_brackets`. -/
theorem
chapter10_percentileTCI_coverage_tendsto_one_sub_alpha_indexed_of_bootstrap_regression_tstat_numerator_tight
    [IsProbabilityMeasure μ]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {TthetaStar seThetaStar : ∀ n, Ω → Ωboot n → ℝ}
    {θ : ℝ} {θhat se : ℕ → Ω → ℝ} {seθ q α : ℝ}
    (hsampleSe : ∀ n ω, 0 < se n ω)
    (htstat :
      TendstoInDistribution
        (fun n ω => percentileTStatistic θ (θhat n ω) (se n ω))
        atTop (fun x : ℝ => x) (fun _ => μ) (gaussianReal 0 1))
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
    (hseStar :
      TendstoInBootstrapProbabilityIndexed μ Pstar seThetaStar (fun _ => seθ))
    (hα_pos : 0 < α) (hα_lt_one : α < 1)
    (hstrict : StrictMono (fun x => cdf (gaussianReal 0 1) x))
    (hlower_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed Pstar
            (fun n ω ωs => TthetaStar n ω ωs / seThetaStar n ω ωs)
            (α / 2) n) μ)
    (hupper_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed Pstar
            (fun n ω ωs => TthetaStar n ω ωs / seThetaStar n ω ωs)
            (1 - α / 2) n) μ)
    (hq_nonneg : 0 ≤ q)
    (hcdfLower : cdf (gaussianReal 0 1) (-q) = α / 2)
    (hcdfUpper : cdf (gaussianReal 0 1) q = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | percentileTCIEvent θ (θhat n ω) (se n ω)
          (bootstrapScalarLowerQuantileIndexed Pstar
            (fun n ω ωs => TthetaStar n ω ωs / seThetaStar n ω ωs)
            (α / 2) n ω)
          (bootstrapScalarLowerQuantileIndexed Pstar
            (fun n ω ωs => TthetaStar n ω ωs / seThetaStar n ω ωs)
            (1 - α / 2) n ω)})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) := by
  obtain ⟨hleftLower, hrightLower⟩ :=
    strictMono_cdf_brackets hstrict hcdfLower
  obtain ⟨hleftUpper, hrightUpper⟩ :=
    strictMono_cdf_brackets hstrict hcdfUpper
  exact
    chapter10_percentileTCI_coverage_tendsto_one_sub_alpha_indexed_of_bootstrap_regression_tstat_numerator_tight_brackets
      (μ := μ) (Pstar := Pstar) (TthetaStar := TthetaStar)
      (seThetaStar := seThetaStar) (θ := θ) (θhat := θhat)
      (se := se) (seθ := seθ) (q := q) (α := α)
      hsampleSe htstat hseθ hT hPstar hTthetaStar hseThetaStar hTail
      hseStar hα_pos hα_lt_one hleftLower hrightLower hleftUpper
      hrightUpper hlower_meas hupper_meas hq_nonneg hcdfLower hcdfUpper

/-- Regression-facing percentile-`t` coverage from scalar compact-tail control
for the bootstrap numerator, using local standard-normal CDF bracketing.

This composes Theorem 10.18's scalar-tail t-statistic CDF route directly with
the Theorem 10.14 percentile-`t` lower-quantile theorem. -/
theorem
chapter10_percentileTCI_coverage_tendsto_one_sub_alpha_of_bootstrap_regression_tstat_scalarTail_brackets
    [IsProbabilityMeasure μ]
    {Pstar : ℕ → Ω → Measure Ωs}
    {TthetaStar seThetaStar : ℕ → Ω → Ωs → ℝ}
    {θ : ℝ} {θhat se : ℕ → Ω → ℝ} {seθ q α : ℝ}
    (hsampleSe : ∀ n ω, 0 < se n ω)
    (htstat :
      TendstoInDistribution
        (fun n ω => percentileTStatistic θ (θhat n ω) (se n ω))
        atTop (fun x : ℝ => x) (fun _ => μ) (gaussianReal 0 1))
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
    (hseStar :
      TendstoInBootstrapProbability μ Pstar seThetaStar (fun _ => seθ))
    (hα_pos : 0 < α) (hα_lt_one : α < 1)
    (hleftLower :
      ∀ ε : ℝ, 0 < ε → cdf (gaussianReal 0 1) (-q - ε) < α / 2)
    (hrightLower :
      ∀ ε : ℝ, 0 < ε → α / 2 < cdf (gaussianReal 0 1) (-q + ε))
    (hleftUpper :
      ∀ ε : ℝ, 0 < ε → cdf (gaussianReal 0 1) (q - ε) < 1 - α / 2)
    (hrightUpper :
      ∀ ε : ℝ, 0 < ε → 1 - α / 2 < cdf (gaussianReal 0 1) (q + ε))
    (hlower_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantile Pstar
            (fun n ω ωs => TthetaStar n ω ωs / seThetaStar n ω ωs)
            (α / 2) n) μ)
    (hupper_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantile Pstar
            (fun n ω ωs => TthetaStar n ω ωs / seThetaStar n ω ωs)
            (1 - α / 2) n) μ)
    (hq_nonneg : 0 ≤ q)
    (hcdfLower : cdf (gaussianReal 0 1) (-q) = α / 2)
    (hcdfUpper : cdf (gaussianReal 0 1) q = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | percentileTCIEvent θ (θhat n ω) (se n ω)
          (bootstrapScalarLowerQuantile Pstar
            (fun n ω ωs => TthetaStar n ω ωs / seThetaStar n ω ωs)
            (α / 2) n ω)
          (bootstrapScalarLowerQuantile Pstar
            (fun n ω ωs => TthetaStar n ω ωs / seThetaStar n ω ωs)
            (1 - α / 2) n ω)})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) := by
  let Tstar : ℕ → Ω → Ωs → ℝ :=
    fun n ω ωs => TthetaStar n ω ωs / seThetaStar n ω ωs
  haveI : NoAtoms (gaussianReal 0 1) :=
    noAtoms_gaussianReal (μ := 0) (v := 1) (by norm_num)
  have hTmeas : ∀ n ω, AEMeasurable (Tstar n ω) (Pstar n ω) := by
    intro n ω
    exact ((hTthetaStar n ω).div (hseThetaStar n ω)).aemeasurable
  have hTstar :
      TendstoInBootstrapDistribution μ Pstar
        (fun n ω ωs (_ : Unit) => Tstar n ω ωs)
        (gaussianReal 0 1) (fun x : ℝ => fun _ : Unit => x) := by
    simpa [Tstar] using
      chapter10_bootstrap_regression_tstat_distribution_of_scalarTail
        (μ := μ) (Pstar := Pstar) (TthetaStar := TthetaStar)
        (seThetaStar := seThetaStar) (seθ := seθ)
        hseθ hT hPstar hTthetaStar hseThetaStar hTtail hseStar
  have hlower_meas' :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantile Pstar Tstar (α / 2) n) μ := by
    intro n
    simpa [Tstar] using hlower_meas n
  have hupper_meas' :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantile Pstar Tstar (1 - α / 2) n) μ := by
    intro n
    simpa [Tstar] using hupper_meas n
  have hξ : HasLaw (fun x : ℝ => x) (gaussianReal 0 1) (gaussianReal 0 1) := by
    simpa [id] using (HasLaw.id (μ := gaussianReal 0 1))
  have hcoverage :=
    chapter10_percentileTCI_coverage_tendsto_one_sub_alpha_quantile_prob_brackets
      (μ := μ) (ν := gaussianReal 0 1) (η := gaussianReal 0 1)
      (Pstar := Pstar) (Tstar := Tstar) (θ := θ) (θhat := θhat)
      (se := se) (ξ := fun x : ℝ => x) (q := q) (α := α)
      hsampleSe htstat hPstar hTmeas hα_pos hα_lt_one
      hleftLower hrightLower hleftUpper hrightUpper hTstar (fun x => continuousAt_cdf_standardNormal x)
      hlower_meas' hupper_meas' hξ hq_nonneg hcdfLower hcdfUpper
  simpa [Tstar] using hcoverage

/-- Strict-CDF counterpart of
`chapter10_percentileTCI_coverage_tendsto_one_sub_alpha_of_bootstrap_regression_tstat_scalarTail_brackets`. -/
theorem
chapter10_percentileTCI_coverage_tendsto_one_sub_alpha_of_bootstrap_regression_tstat_scalarTail
    [IsProbabilityMeasure μ]
    {Pstar : ℕ → Ω → Measure Ωs}
    {TthetaStar seThetaStar : ℕ → Ω → Ωs → ℝ}
    {θ : ℝ} {θhat se : ℕ → Ω → ℝ} {seθ q α : ℝ}
    (hsampleSe : ∀ n ω, 0 < se n ω)
    (htstat :
      TendstoInDistribution
        (fun n ω => percentileTStatistic θ (θhat n ω) (se n ω))
        atTop (fun x : ℝ => x) (fun _ => μ) (gaussianReal 0 1))
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
    (hseStar :
      TendstoInBootstrapProbability μ Pstar seThetaStar (fun _ => seθ))
    (hα_pos : 0 < α) (hα_lt_one : α < 1)
    (hstrict : StrictMono (fun x => cdf (gaussianReal 0 1) x))
    (hlower_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantile Pstar
            (fun n ω ωs => TthetaStar n ω ωs / seThetaStar n ω ωs)
            (α / 2) n) μ)
    (hupper_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantile Pstar
            (fun n ω ωs => TthetaStar n ω ωs / seThetaStar n ω ωs)
            (1 - α / 2) n) μ)
    (hq_nonneg : 0 ≤ q)
    (hcdfLower : cdf (gaussianReal 0 1) (-q) = α / 2)
    (hcdfUpper : cdf (gaussianReal 0 1) q = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | percentileTCIEvent θ (θhat n ω) (se n ω)
          (bootstrapScalarLowerQuantile Pstar
            (fun n ω ωs => TthetaStar n ω ωs / seThetaStar n ω ωs)
            (α / 2) n ω)
          (bootstrapScalarLowerQuantile Pstar
            (fun n ω ωs => TthetaStar n ω ωs / seThetaStar n ω ωs)
            (1 - α / 2) n ω)})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) := by
  obtain ⟨hleftLower, hrightLower⟩ :=
    strictMono_cdf_brackets hstrict hcdfLower
  obtain ⟨hleftUpper, hrightUpper⟩ :=
    strictMono_cdf_brackets hstrict hcdfUpper
  exact
    chapter10_percentileTCI_coverage_tendsto_one_sub_alpha_of_bootstrap_regression_tstat_scalarTail_brackets
      (μ := μ) (Pstar := Pstar) (TthetaStar := TthetaStar)
      (seThetaStar := seThetaStar) (θ := θ) (θhat := θhat)
      (se := se) (seθ := seθ) (q := q) (α := α)
      hsampleSe htstat hseθ hT hPstar hTthetaStar hseThetaStar hTtail
      hseStar hα_pos hα_lt_one hleftLower hrightLower hleftUpper
      hrightUpper hlower_meas hupper_meas hq_nonneg hcdfLower hcdfUpper

/-- Indexed regression-facing percentile-`t` coverage from scalar compact-tail
control for the bootstrap numerator, using local standard-normal CDF
bracketing. -/
theorem
chapter10_percentileTCI_coverage_tendsto_one_sub_alpha_indexed_of_bootstrap_regression_tstat_scalarTail_brackets
    [IsProbabilityMeasure μ]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {TthetaStar seThetaStar : ∀ n, Ω → Ωboot n → ℝ}
    {θ : ℝ} {θhat se : ℕ → Ω → ℝ} {seθ q α : ℝ}
    (hsampleSe : ∀ n ω, 0 < se n ω)
    (htstat :
      TendstoInDistribution
        (fun n ω => percentileTStatistic θ (θhat n ω) (se n ω))
        atTop (fun x : ℝ => x) (fun _ => μ) (gaussianReal 0 1))
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
    (hseStar :
      TendstoInBootstrapProbabilityIndexed μ Pstar seThetaStar (fun _ => seθ))
    (hα_pos : 0 < α) (hα_lt_one : α < 1)
    (hleftLower :
      ∀ ε : ℝ, 0 < ε → cdf (gaussianReal 0 1) (-q - ε) < α / 2)
    (hrightLower :
      ∀ ε : ℝ, 0 < ε → α / 2 < cdf (gaussianReal 0 1) (-q + ε))
    (hleftUpper :
      ∀ ε : ℝ, 0 < ε → cdf (gaussianReal 0 1) (q - ε) < 1 - α / 2)
    (hrightUpper :
      ∀ ε : ℝ, 0 < ε → 1 - α / 2 < cdf (gaussianReal 0 1) (q + ε))
    (hlower_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed Pstar
            (fun n ω ωs => TthetaStar n ω ωs / seThetaStar n ω ωs)
            (α / 2) n) μ)
    (hupper_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed Pstar
            (fun n ω ωs => TthetaStar n ω ωs / seThetaStar n ω ωs)
            (1 - α / 2) n) μ)
    (hq_nonneg : 0 ≤ q)
    (hcdfLower : cdf (gaussianReal 0 1) (-q) = α / 2)
    (hcdfUpper : cdf (gaussianReal 0 1) q = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | percentileTCIEvent θ (θhat n ω) (se n ω)
          (bootstrapScalarLowerQuantileIndexed Pstar
            (fun n ω ωs => TthetaStar n ω ωs / seThetaStar n ω ωs)
            (α / 2) n ω)
          (bootstrapScalarLowerQuantileIndexed Pstar
            (fun n ω ωs => TthetaStar n ω ωs / seThetaStar n ω ωs)
            (1 - α / 2) n ω)})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) := by
  let Tstar : ∀ n, Ω → Ωboot n → ℝ :=
    fun n ω ωs => TthetaStar n ω ωs / seThetaStar n ω ωs
  haveI : NoAtoms (gaussianReal 0 1) :=
    noAtoms_gaussianReal (μ := 0) (v := 1) (by norm_num)
  have hTmeas : ∀ n ω, AEMeasurable (Tstar n ω) (Pstar n ω) := by
    intro n ω
    exact ((hTthetaStar n ω).div (hseThetaStar n ω)).aemeasurable
  have hTstar :
      TendstoInBootstrapDistributionIndexed μ Pstar
        (fun n ω ωs (_ : Unit) => Tstar n ω ωs)
        (gaussianReal 0 1) (fun x : ℝ => fun _ : Unit => x) := by
    simpa [Tstar] using
      chapter10_indexed_bootstrap_regression_tstat_distribution_of_scalarTail
        (μ := μ) (Pstar := Pstar) (TthetaStar := TthetaStar)
        (seThetaStar := seThetaStar) (seθ := seθ)
        hseθ hT hPstar hTthetaStar hseThetaStar hTtail hseStar
  have hlower_meas' :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed Pstar Tstar (α / 2) n) μ := by
    intro n
    simpa [Tstar] using hlower_meas n
  have hupper_meas' :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed Pstar Tstar (1 - α / 2) n) μ := by
    intro n
    simpa [Tstar] using hupper_meas n
  have hξ : HasLaw (fun x : ℝ => x) (gaussianReal 0 1) (gaussianReal 0 1) := by
    simpa [id] using (HasLaw.id (μ := gaussianReal 0 1))
  have hcoverage :=
    chapter10_percentileTCI_coverage_tendsto_one_sub_alpha_indexed_quantile_prob_brackets
      (μ := μ) (ν := gaussianReal 0 1) (η := gaussianReal 0 1)
      (Pstar := Pstar) (Tstar := Tstar) (θ := θ) (θhat := θhat)
      (se := se) (ξ := fun x : ℝ => x) (q := q) (α := α)
      hsampleSe htstat hPstar hTmeas hα_pos hα_lt_one
      hleftLower hrightLower hleftUpper hrightUpper hTstar (fun x => continuousAt_cdf_standardNormal x)
      hlower_meas' hupper_meas' hξ hq_nonneg hcdfLower hcdfUpper
  simpa [Tstar] using hcoverage

/-- Strict-CDF counterpart of
`chapter10_percentileTCI_coverage_tendsto_one_sub_alpha_indexed_of_bootstrap_regression_tstat_scalarTail_brackets`. -/
theorem
chapter10_percentileTCI_coverage_tendsto_one_sub_alpha_indexed_of_bootstrap_regression_tstat_scalarTail
    [IsProbabilityMeasure μ]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {TthetaStar seThetaStar : ∀ n, Ω → Ωboot n → ℝ}
    {θ : ℝ} {θhat se : ℕ → Ω → ℝ} {seθ q α : ℝ}
    (hsampleSe : ∀ n ω, 0 < se n ω)
    (htstat :
      TendstoInDistribution
        (fun n ω => percentileTStatistic θ (θhat n ω) (se n ω))
        atTop (fun x : ℝ => x) (fun _ => μ) (gaussianReal 0 1))
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
    (hseStar :
      TendstoInBootstrapProbabilityIndexed μ Pstar seThetaStar (fun _ => seθ))
    (hα_pos : 0 < α) (hα_lt_one : α < 1)
    (hstrict : StrictMono (fun x => cdf (gaussianReal 0 1) x))
    (hlower_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed Pstar
            (fun n ω ωs => TthetaStar n ω ωs / seThetaStar n ω ωs)
            (α / 2) n) μ)
    (hupper_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed Pstar
            (fun n ω ωs => TthetaStar n ω ωs / seThetaStar n ω ωs)
            (1 - α / 2) n) μ)
    (hq_nonneg : 0 ≤ q)
    (hcdfLower : cdf (gaussianReal 0 1) (-q) = α / 2)
    (hcdfUpper : cdf (gaussianReal 0 1) q = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | percentileTCIEvent θ (θhat n ω) (se n ω)
          (bootstrapScalarLowerQuantileIndexed Pstar
            (fun n ω ωs => TthetaStar n ω ωs / seThetaStar n ω ωs)
            (α / 2) n ω)
          (bootstrapScalarLowerQuantileIndexed Pstar
            (fun n ω ωs => TthetaStar n ω ωs / seThetaStar n ω ωs)
            (1 - α / 2) n ω)})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) := by
  obtain ⟨hleftLower, hrightLower⟩ :=
    strictMono_cdf_brackets hstrict hcdfLower
  obtain ⟨hleftUpper, hrightUpper⟩ :=
    strictMono_cdf_brackets hstrict hcdfUpper
  exact
    chapter10_percentileTCI_coverage_tendsto_one_sub_alpha_indexed_of_bootstrap_regression_tstat_scalarTail_brackets
      (μ := μ) (Pstar := Pstar) (TthetaStar := TthetaStar)
      (seThetaStar := seThetaStar) (θ := θ) (θhat := θhat)
      (se := se) (seθ := seθ) (q := q) (α := α)
      hsampleSe htstat hseθ hT hPstar hTthetaStar hseThetaStar hTtail
      hseStar hα_pos hα_lt_one hleftLower hrightLower hleftUpper
      hrightUpper hlower_meas hupper_meas hq_nonneg hcdfLower hcdfUpper

set_option linter.style.longLine false in
/-- Local-CDF bracketing face of indexed percentile-`t` coverage with the
bootstrap statistic specialized to the concrete finite ordinary-bootstrap OLS
linear-restriction numerator.

The sample-side statistic is left explicit; this wrapper discharges the
bootstrap-side Theorem 10.18 route from the finite OLS gap-envelope numerator
CLT, scalar compact-tail control, and feasible bootstrap standard-error
consistency. -/
theorem
    chapter10_percentileTCI_coverage_tendsto_one_sub_alpha_indexed_of_bootstrap_regression_tstat_finSucc_olsBetaOrZero_gapEnvelope_scalarTail_brackets
    [IsProbabilityMeasure μ]
    {k : Type*} [Fintype k] [DecidableEq k]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    {seThetaStar : ∀ n, Ω → (Fin (n + 1) → Fin (n + 1)) → ℝ}
    {θ : ℝ} {θhat se : ℕ → Ω → ℝ} {q α : ℝ}
    (β : k → ℝ) (R : Matrix Unit k ℝ)
    (hsampleSe : ∀ n ω, 0 < se n ω)
    (htstat :
      TendstoInDistribution
        (fun n ω => percentileTStatistic θ (θhat n ω) (se n ω))
        atTop (fun x : ℝ => x) (fun _ => μ) (gaussianReal 0 1))
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
    (hseStar :
      TendstoInBootstrapProbabilityIndexed μ
        (fun n _ =>
          (ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
              Measure (Fin (n + 1) → Fin (n + 1))))
        seThetaStar
        (fun _ => linearRestrictionStdError R (heteroAsymCov μ X e)))
    (hα_pos : 0 < α) (hα_lt_one : α < 1)
    (hleftLower :
      ∀ ε : ℝ, 0 < ε → cdf (gaussianReal 0 1) (-q - ε) < α / 2)
    (hrightLower :
      ∀ ε : ℝ, 0 < ε → α / 2 < cdf (gaussianReal 0 1) (-q + ε))
    (hleftUpper :
      ∀ ε : ℝ, 0 < ε → cdf (gaussianReal 0 1) (q - ε) < 1 - α / 2)
    (hrightUpper :
      ∀ ε : ℝ, 0 < ε → 1 - α / 2 < cdf (gaussianReal 0 1) (q + ε))
    (hlower_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed
            (fun n _ =>
              (ProbabilityTheory.uniformOn
                (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                  Measure (Fin (n + 1) → Fin (n + 1))))
            (fun n ω ωs =>
              regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs /
                seThetaStar n ω ωs)
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
              regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs /
                seThetaStar n ω ωs)
            (1 - α / 2) n) μ)
    (hq_nonneg : 0 ≤ q)
    (hcdfLower : cdf (gaussianReal 0 1) (-q) = α / 2)
    (hcdfUpper : cdf (gaussianReal 0 1) q = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | percentileTCIEvent θ (θhat n ω) (se n ω)
          (bootstrapScalarLowerQuantileIndexed
            (fun n _ =>
              (ProbabilityTheory.uniformOn
                (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                  Measure (Fin (n + 1) → Fin (n + 1))))
            (fun n ω ωs =>
              regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs /
                seThetaStar n ω ωs)
            (α / 2) n ω)
          (bootstrapScalarLowerQuantileIndexed
            (fun n _ =>
              (ProbabilityTheory.uniformOn
                (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                  Measure (Fin (n + 1) → Fin (n + 1))))
            (fun n ω ωs =>
              regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs /
                seThetaStar n ω ωs)
            (1 - α / 2) n ω)})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) :=
  chapter10_percentileTCI_coverage_tendsto_one_sub_alpha_indexed_of_bootstrap_regression_tstat_scalarTail_brackets
    (μ := μ)
    (Pstar := fun n _ =>
      (ProbabilityTheory.uniformOn
        (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
          Measure (Fin (n + 1) → Fin (n + 1))))
    (TthetaStar := fun n ω ωs =>
      regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs)
    (seThetaStar := seThetaStar)
    (θ := θ) (θhat := θhat) (se := se)
    (seθ := linearRestrictionStdError R (heteroAsymCov μ X e))
    (q := q) (α := α)
    hsampleSe htstat hseθ
    (chapter10_indexed_bootstrap_regression_linearRestriction_standardNormal_finSucc_olsBetaOrZero_of_gapEnvelope_tight
      (μ := μ) (X := X) (e := e) (y := y)
      β R hmodel h hΩ hTail hGapTail)
    (fun _ _ => inferInstance) (fun _ _ => measurable_of_finite _)
    hseThetaStar hTtail hseStar hα_pos hα_lt_one hleftLower
      hrightLower hleftUpper hrightUpper hlower_meas hupper_meas
    hq_nonneg hcdfLower hcdfUpper

set_option linter.style.longLine false in
/-- Robust-feasible HC specialization of the indexed concrete finite OLS
local-CDF scalar-tail percentile-`t` coverage wrapper. -/
theorem
    chapter10_percentileTCI_coverage_tendsto_one_sub_alpha_indexed_of_bootstrap_regression_tstat_finSucc_olsBetaOrZero_gapEnvelope_scalarTail_brackets_of_robustFeasibleHCMomentConditions
    [IsProbabilityMeasure μ]
    {k : Type*} [Fintype k] [DecidableEq k]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    {seThetaStar : ∀ n, Ω → (Fin (n + 1) → Fin (n + 1)) → ℝ}
    {θ : ℝ} {θhat se : ℕ → Ω → ℝ} {q α : ℝ}
    (β : k → ℝ) (R : Matrix Unit k ℝ)
    (hsampleSe : ∀ n ω, 0 < se n ω)
    (htstat :
      TendstoInDistribution
        (fun n ω => percentileTStatistic θ (θhat n ω) (se n ω))
        atTop (fun x : ℝ => x) (fun _ => μ) (gaussianReal 0 1))
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
    (hseStar :
      TendstoInBootstrapProbabilityIndexed μ
        (fun n _ =>
          (ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
              Measure (Fin (n + 1) → Fin (n + 1))))
        seThetaStar
        (fun _ => linearRestrictionStdError R (heteroAsymCov μ X e)))
    (hα_pos : 0 < α) (hα_lt_one : α < 1)
    (hleftLower :
      ∀ ε : ℝ, 0 < ε → cdf (gaussianReal 0 1) (-q - ε) < α / 2)
    (hrightLower :
      ∀ ε : ℝ, 0 < ε → α / 2 < cdf (gaussianReal 0 1) (-q + ε))
    (hleftUpper :
      ∀ ε : ℝ, 0 < ε → cdf (gaussianReal 0 1) (q - ε) < 1 - α / 2)
    (hrightUpper :
      ∀ ε : ℝ, 0 < ε → 1 - α / 2 < cdf (gaussianReal 0 1) (q + ε))
    (hlower_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed
            (fun n _ =>
              (ProbabilityTheory.uniformOn
                (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                  Measure (Fin (n + 1) → Fin (n + 1))))
            (fun n ω ωs =>
              regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs /
                seThetaStar n ω ωs)
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
              regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs /
                seThetaStar n ω ωs)
            (1 - α / 2) n) μ)
    (hq_nonneg : 0 ≤ q)
    (hcdfLower : cdf (gaussianReal 0 1) (-q) = α / 2)
    (hcdfUpper : cdf (gaussianReal 0 1) q = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | percentileTCIEvent θ (θhat n ω) (se n ω)
          (bootstrapScalarLowerQuantileIndexed
            (fun n _ =>
              (ProbabilityTheory.uniformOn
                (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                  Measure (Fin (n + 1) → Fin (n + 1))))
            (fun n ω ωs =>
              regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs /
                seThetaStar n ω ωs)
            (α / 2) n ω)
          (bootstrapScalarLowerQuantileIndexed
            (fun n _ =>
              (ProbabilityTheory.uniformOn
                (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                  Measure (Fin (n + 1) → Fin (n + 1))))
            (fun n ω ωs =>
              regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs /
                seThetaStar n ω ωs)
            (1 - α / 2) n ω)})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) :=
  chapter10_percentileTCI_coverage_tendsto_one_sub_alpha_indexed_of_bootstrap_regression_tstat_finSucc_olsBetaOrZero_gapEnvelope_scalarTail_brackets
    (μ := μ) (X := X) (e := e) (y := y)
    β R hsampleSe htstat hseθ hm.model hm.toScoreCLTConditions hΩ hTail
    hGapTail hseThetaStar hTtail hseStar hα_pos hα_lt_one
      hleftLower hrightLower hleftUpper hrightUpper hlower_meas
    hupper_meas hq_nonneg hcdfLower hcdfUpper

set_option linter.style.longLine false in
/-- Indexed percentile-`t` coverage with the bootstrap statistic specialized
to the concrete finite ordinary-bootstrap OLS linear-restriction numerator.

The sample-side statistic is left explicit; this wrapper discharges the
bootstrap-side Theorem 10.18 route from the finite OLS gap-envelope numerator
CLT, scalar compact-tail control, and feasible bootstrap standard-error
consistency. -/
theorem
    chapter10_percentileTCI_coverage_tendsto_one_sub_alpha_indexed_of_bootstrap_regression_tstat_finSucc_olsBetaOrZero_gapEnvelope_scalarTail
    [IsProbabilityMeasure μ]
    {k : Type*} [Fintype k] [DecidableEq k]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    {seThetaStar : ∀ n, Ω → (Fin (n + 1) → Fin (n + 1)) → ℝ}
    {θ : ℝ} {θhat se : ℕ → Ω → ℝ} {q α : ℝ}
    (β : k → ℝ) (R : Matrix Unit k ℝ)
    (hsampleSe : ∀ n ω, 0 < se n ω)
    (htstat :
      TendstoInDistribution
        (fun n ω => percentileTStatistic θ (θhat n ω) (se n ω))
        atTop (fun x : ℝ => x) (fun _ => μ) (gaussianReal 0 1))
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
    (hseStar :
      TendstoInBootstrapProbabilityIndexed μ
        (fun n _ =>
          (ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
              Measure (Fin (n + 1) → Fin (n + 1))))
        seThetaStar
        (fun _ => linearRestrictionStdError R (heteroAsymCov μ X e)))
    (hα_pos : 0 < α) (hα_lt_one : α < 1)
    (hstrict : StrictMono (fun x => cdf (gaussianReal 0 1) x))
    (hlower_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed
            (fun n _ =>
              (ProbabilityTheory.uniformOn
                (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                  Measure (Fin (n + 1) → Fin (n + 1))))
            (fun n ω ωs =>
              regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs /
                seThetaStar n ω ωs)
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
              regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs /
                seThetaStar n ω ωs)
            (1 - α / 2) n) μ)
    (hq_nonneg : 0 ≤ q)
    (hcdfLower : cdf (gaussianReal 0 1) (-q) = α / 2)
    (hcdfUpper : cdf (gaussianReal 0 1) q = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | percentileTCIEvent θ (θhat n ω) (se n ω)
          (bootstrapScalarLowerQuantileIndexed
            (fun n _ =>
              (ProbabilityTheory.uniformOn
                (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                  Measure (Fin (n + 1) → Fin (n + 1))))
            (fun n ω ωs =>
              regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs /
                seThetaStar n ω ωs)
            (α / 2) n ω)
          (bootstrapScalarLowerQuantileIndexed
            (fun n _ =>
              (ProbabilityTheory.uniformOn
                (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                  Measure (Fin (n + 1) → Fin (n + 1))))
            (fun n ω ωs =>
              regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs /
                seThetaStar n ω ωs)
            (1 - α / 2) n ω)})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) :=
  chapter10_percentileTCI_coverage_tendsto_one_sub_alpha_indexed_of_bootstrap_regression_tstat_scalarTail
    (μ := μ)
    (Pstar := fun n _ =>
      (ProbabilityTheory.uniformOn
        (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
          Measure (Fin (n + 1) → Fin (n + 1))))
    (TthetaStar := fun n ω ωs =>
      regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs)
    (seThetaStar := seThetaStar)
    (θ := θ) (θhat := θhat) (se := se)
    (seθ := linearRestrictionStdError R (heteroAsymCov μ X e))
    (q := q) (α := α)
    hsampleSe htstat hseθ
    (chapter10_indexed_bootstrap_regression_linearRestriction_standardNormal_finSucc_olsBetaOrZero_of_gapEnvelope_tight
      (μ := μ) (X := X) (e := e) (y := y)
      β R hmodel h hΩ hTail hGapTail)
    (fun _ _ => inferInstance) (fun _ _ => measurable_of_finite _)
    hseThetaStar hTtail hseStar hα_pos hα_lt_one hstrict
    hlower_meas hupper_meas hq_nonneg hcdfLower hcdfUpper

set_option linter.style.longLine false in
/-- Robust-feasible HC specialization of the indexed concrete finite OLS
percentile-`t` coverage wrapper. -/
theorem
    chapter10_percentileTCI_coverage_tendsto_one_sub_alpha_indexed_of_bootstrap_regression_tstat_finSucc_olsBetaOrZero_gapEnvelope_scalarTail_of_robustFeasibleHCMomentConditions
    [IsProbabilityMeasure μ]
    {k : Type*} [Fintype k] [DecidableEq k]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    {seThetaStar : ∀ n, Ω → (Fin (n + 1) → Fin (n + 1)) → ℝ}
    {θ : ℝ} {θhat se : ℕ → Ω → ℝ} {q α : ℝ}
    (β : k → ℝ) (R : Matrix Unit k ℝ)
    (hsampleSe : ∀ n ω, 0 < se n ω)
    (htstat :
      TendstoInDistribution
        (fun n ω => percentileTStatistic θ (θhat n ω) (se n ω))
        atTop (fun x : ℝ => x) (fun _ => μ) (gaussianReal 0 1))
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
    (hseStar :
      TendstoInBootstrapProbabilityIndexed μ
        (fun n _ =>
          (ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
              Measure (Fin (n + 1) → Fin (n + 1))))
        seThetaStar
        (fun _ => linearRestrictionStdError R (heteroAsymCov μ X e)))
    (hα_pos : 0 < α) (hα_lt_one : α < 1)
    (hstrict : StrictMono (fun x => cdf (gaussianReal 0 1) x))
    (hlower_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed
            (fun n _ =>
              (ProbabilityTheory.uniformOn
                (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                  Measure (Fin (n + 1) → Fin (n + 1))))
            (fun n ω ωs =>
              regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs /
                seThetaStar n ω ωs)
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
              regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs /
                seThetaStar n ω ωs)
            (1 - α / 2) n) μ)
    (hq_nonneg : 0 ≤ q)
    (hcdfLower : cdf (gaussianReal 0 1) (-q) = α / 2)
    (hcdfUpper : cdf (gaussianReal 0 1) q = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | percentileTCIEvent θ (θhat n ω) (se n ω)
          (bootstrapScalarLowerQuantileIndexed
            (fun n _ =>
              (ProbabilityTheory.uniformOn
                (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                  Measure (Fin (n + 1) → Fin (n + 1))))
            (fun n ω ωs =>
              regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs /
                seThetaStar n ω ωs)
            (α / 2) n ω)
          (bootstrapScalarLowerQuantileIndexed
            (fun n _ =>
              (ProbabilityTheory.uniformOn
                (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                  Measure (Fin (n + 1) → Fin (n + 1))))
            (fun n ω ωs =>
              regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs /
                seThetaStar n ω ωs)
            (1 - α / 2) n ω)})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) :=
  chapter10_percentileTCI_coverage_tendsto_one_sub_alpha_indexed_of_bootstrap_regression_tstat_finSucc_olsBetaOrZero_gapEnvelope_scalarTail
    (μ := μ) (X := X) (e := e) (y := y)
    β R hsampleSe htstat hseθ hm.model hm.toScoreCLTConditions hΩ hTail
    hGapTail hseThetaStar hTtail hseStar hα_pos hα_lt_one hstrict
    hlower_meas hupper_meas hq_nonneg hcdfLower hcdfUpper

/-- Regression-facing percentile-`t` coverage from an eventually bounded
bootstrap numerator, using local standard-normal CDF bracketing.

This is the bounded-numerator face of
`chapter10_percentileTCI_coverage_tendsto_one_sub_alpha_of_bootstrap_regression_tstat_brackets`:
the eventual deterministic numerator bound feeds Theorem 10.18's scalar-tail
studentization route before the percentile-`t` quantile theorem is applied. -/
theorem
chapter10_percentileTCI_coverage_tendsto_one_sub_alpha_of_bootstrap_regression_tstat_eventually_bound_brackets
    [IsProbabilityMeasure μ]
    {Pstar : ℕ → Ω → Measure Ωs}
    {TthetaStar seThetaStar : ℕ → Ω → Ωs → ℝ}
    {θ : ℝ} {θhat se : ℕ → Ω → ℝ} {seθ C q α : ℝ}
    (hsampleSe : ∀ n ω, 0 < se n ω)
    (htstat :
      TendstoInDistribution
        (fun n ω => percentileTStatistic θ (θhat n ω) (se n ω))
        atTop (fun x : ℝ => x) (fun _ => μ) (gaussianReal 0 1))
    (hseθ : 0 < seθ)
    (hT :
      TendstoInBootstrapWeakDistribution μ Pstar TthetaStar
        (gaussianReal 0 1) (fun z : ℝ => seθ * z))
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hTthetaStar : ∀ n ω, Measurable (TthetaStar n ω))
    (hseThetaStar : ∀ n ω, Measurable (seThetaStar n ω))
    (hbound : ∀ᶠ n in atTop, ∀ ω ωs, |TthetaStar n ω ωs| ≤ C)
    (hseStar :
      TendstoInBootstrapProbability μ Pstar seThetaStar (fun _ => seθ))
    (hα_pos : 0 < α) (hα_lt_one : α < 1)
    (hleftLower :
      ∀ ε : ℝ, 0 < ε → cdf (gaussianReal 0 1) (-q - ε) < α / 2)
    (hrightLower :
      ∀ ε : ℝ, 0 < ε → α / 2 < cdf (gaussianReal 0 1) (-q + ε))
    (hleftUpper :
      ∀ ε : ℝ, 0 < ε → cdf (gaussianReal 0 1) (q - ε) < 1 - α / 2)
    (hrightUpper :
      ∀ ε : ℝ, 0 < ε → 1 - α / 2 < cdf (gaussianReal 0 1) (q + ε))
    (hlower_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantile Pstar
            (fun n ω ωs => TthetaStar n ω ωs / seThetaStar n ω ωs)
            (α / 2) n) μ)
    (hupper_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantile Pstar
            (fun n ω ωs => TthetaStar n ω ωs / seThetaStar n ω ωs)
            (1 - α / 2) n) μ)
    (hq_nonneg : 0 ≤ q)
    (hcdfLower : cdf (gaussianReal 0 1) (-q) = α / 2)
    (hcdfUpper : cdf (gaussianReal 0 1) q = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | percentileTCIEvent θ (θhat n ω) (se n ω)
          (bootstrapScalarLowerQuantile Pstar
            (fun n ω ωs => TthetaStar n ω ωs / seThetaStar n ω ωs)
            (α / 2) n ω)
          (bootstrapScalarLowerQuantile Pstar
            (fun n ω ωs => TthetaStar n ω ωs / seThetaStar n ω ωs)
            (1 - α / 2) n ω)})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) := by
  let Tstar : ℕ → Ω → Ωs → ℝ :=
    fun n ω ωs => TthetaStar n ω ωs / seThetaStar n ω ωs
  haveI : NoAtoms (gaussianReal 0 1) :=
    noAtoms_gaussianReal (μ := 0) (v := 1) (by norm_num)
  have hTmeas : ∀ n ω, AEMeasurable (Tstar n ω) (Pstar n ω) := by
    intro n ω
    exact ((hTthetaStar n ω).div (hseThetaStar n ω)).aemeasurable
  have hTstar :
      TendstoInBootstrapDistribution μ Pstar
        (fun n ω ωs (_ : Unit) => Tstar n ω ωs)
        (gaussianReal 0 1) (fun x : ℝ => fun _ : Unit => x) := by
    simpa [Tstar] using
      chapter10_bootstrap_regression_tstat_distribution_of_eventually_bound
        (μ := μ) (Pstar := Pstar) (TthetaStar := TthetaStar)
        (seThetaStar := seThetaStar) (seθ := seθ) (C := C)
        hseθ hT hPstar hTthetaStar hseThetaStar hbound hseStar
  have hlower_meas' :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantile Pstar Tstar (α / 2) n) μ := by
    intro n
    simpa [Tstar] using hlower_meas n
  have hupper_meas' :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantile Pstar Tstar (1 - α / 2) n) μ := by
    intro n
    simpa [Tstar] using hupper_meas n
  have hξ : HasLaw (fun x : ℝ => x) (gaussianReal 0 1) (gaussianReal 0 1) := by
    simpa [id] using (HasLaw.id (μ := gaussianReal 0 1))
  have hcoverage :=
    chapter10_percentileTCI_coverage_tendsto_one_sub_alpha_quantile_prob_brackets
      (μ := μ) (ν := gaussianReal 0 1) (η := gaussianReal 0 1)
      (Pstar := Pstar) (Tstar := Tstar) (θ := θ) (θhat := θhat)
      (se := se) (ξ := fun x : ℝ => x) (q := q) (α := α)
      hsampleSe htstat hPstar hTmeas hα_pos hα_lt_one
      hleftLower hrightLower hleftUpper hrightUpper hTstar (fun x => continuousAt_cdf_standardNormal x)
      hlower_meas' hupper_meas' hξ hq_nonneg hcdfLower hcdfUpper
  simpa [Tstar] using hcoverage

/-- Strict-CDF counterpart of
`chapter10_percentileTCI_coverage_tendsto_one_sub_alpha_of_bootstrap_regression_tstat_eventually_bound_brackets`. -/
theorem
chapter10_percentileTCI_coverage_tendsto_one_sub_alpha_of_bootstrap_regression_tstat_eventually_bound
    [IsProbabilityMeasure μ]
    {Pstar : ℕ → Ω → Measure Ωs}
    {TthetaStar seThetaStar : ℕ → Ω → Ωs → ℝ}
    {θ : ℝ} {θhat se : ℕ → Ω → ℝ} {seθ C q α : ℝ}
    (hsampleSe : ∀ n ω, 0 < se n ω)
    (htstat :
      TendstoInDistribution
        (fun n ω => percentileTStatistic θ (θhat n ω) (se n ω))
        atTop (fun x : ℝ => x) (fun _ => μ) (gaussianReal 0 1))
    (hseθ : 0 < seθ)
    (hT :
      TendstoInBootstrapWeakDistribution μ Pstar TthetaStar
        (gaussianReal 0 1) (fun z : ℝ => seθ * z))
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hTthetaStar : ∀ n ω, Measurable (TthetaStar n ω))
    (hseThetaStar : ∀ n ω, Measurable (seThetaStar n ω))
    (hbound : ∀ᶠ n in atTop, ∀ ω ωs, |TthetaStar n ω ωs| ≤ C)
    (hseStar :
      TendstoInBootstrapProbability μ Pstar seThetaStar (fun _ => seθ))
    (hα_pos : 0 < α) (hα_lt_one : α < 1)
    (hstrict : StrictMono (fun x => cdf (gaussianReal 0 1) x))
    (hlower_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantile Pstar
            (fun n ω ωs => TthetaStar n ω ωs / seThetaStar n ω ωs)
            (α / 2) n) μ)
    (hupper_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantile Pstar
            (fun n ω ωs => TthetaStar n ω ωs / seThetaStar n ω ωs)
            (1 - α / 2) n) μ)
    (hq_nonneg : 0 ≤ q)
    (hcdfLower : cdf (gaussianReal 0 1) (-q) = α / 2)
    (hcdfUpper : cdf (gaussianReal 0 1) q = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | percentileTCIEvent θ (θhat n ω) (se n ω)
          (bootstrapScalarLowerQuantile Pstar
            (fun n ω ωs => TthetaStar n ω ωs / seThetaStar n ω ωs)
            (α / 2) n ω)
          (bootstrapScalarLowerQuantile Pstar
            (fun n ω ωs => TthetaStar n ω ωs / seThetaStar n ω ωs)
            (1 - α / 2) n ω)})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) := by
  obtain ⟨hleftLower, hrightLower⟩ :=
    strictMono_cdf_brackets hstrict hcdfLower
  obtain ⟨hleftUpper, hrightUpper⟩ :=
    strictMono_cdf_brackets hstrict hcdfUpper
  exact
    chapter10_percentileTCI_coverage_tendsto_one_sub_alpha_of_bootstrap_regression_tstat_eventually_bound_brackets
      (μ := μ) (Pstar := Pstar) (TthetaStar := TthetaStar)
      (seThetaStar := seThetaStar) (θ := θ) (θhat := θhat)
      (se := se) (seθ := seθ) (C := C) (q := q) (α := α)
      hsampleSe htstat hseθ hT hPstar hTthetaStar hseThetaStar hbound
      hseStar hα_pos hα_lt_one hleftLower hrightLower hleftUpper
      hrightUpper hlower_meas hupper_meas hq_nonneg hcdfLower hcdfUpper

/-- Indexed regression-facing percentile-`t` coverage from an eventually
bounded bootstrap numerator, using local standard-normal CDF bracketing. -/
theorem
chapter10_percentileTCI_coverage_tendsto_one_sub_alpha_indexed_of_bootstrap_regression_tstat_eventually_bound_brackets
    [IsProbabilityMeasure μ]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {TthetaStar seThetaStar : ∀ n, Ω → Ωboot n → ℝ}
    {θ : ℝ} {θhat se : ℕ → Ω → ℝ} {seθ C q α : ℝ}
    (hsampleSe : ∀ n ω, 0 < se n ω)
    (htstat :
      TendstoInDistribution
        (fun n ω => percentileTStatistic θ (θhat n ω) (se n ω))
        atTop (fun x : ℝ => x) (fun _ => μ) (gaussianReal 0 1))
    (hseθ : 0 < seθ)
    (hT :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar TthetaStar
        (gaussianReal 0 1) (fun z : ℝ => seθ * z))
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hTthetaStar : ∀ n ω, Measurable (TthetaStar n ω))
    (hseThetaStar : ∀ n ω, Measurable (seThetaStar n ω))
    (hbound : ∀ᶠ n in atTop, ∀ ω ωs, |TthetaStar n ω ωs| ≤ C)
    (hseStar :
      TendstoInBootstrapProbabilityIndexed μ Pstar seThetaStar (fun _ => seθ))
    (hα_pos : 0 < α) (hα_lt_one : α < 1)
    (hleftLower :
      ∀ ε : ℝ, 0 < ε → cdf (gaussianReal 0 1) (-q - ε) < α / 2)
    (hrightLower :
      ∀ ε : ℝ, 0 < ε → α / 2 < cdf (gaussianReal 0 1) (-q + ε))
    (hleftUpper :
      ∀ ε : ℝ, 0 < ε → cdf (gaussianReal 0 1) (q - ε) < 1 - α / 2)
    (hrightUpper :
      ∀ ε : ℝ, 0 < ε → 1 - α / 2 < cdf (gaussianReal 0 1) (q + ε))
    (hlower_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed Pstar
            (fun n ω ωs => TthetaStar n ω ωs / seThetaStar n ω ωs)
            (α / 2) n) μ)
    (hupper_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed Pstar
            (fun n ω ωs => TthetaStar n ω ωs / seThetaStar n ω ωs)
            (1 - α / 2) n) μ)
    (hq_nonneg : 0 ≤ q)
    (hcdfLower : cdf (gaussianReal 0 1) (-q) = α / 2)
    (hcdfUpper : cdf (gaussianReal 0 1) q = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | percentileTCIEvent θ (θhat n ω) (se n ω)
          (bootstrapScalarLowerQuantileIndexed Pstar
            (fun n ω ωs => TthetaStar n ω ωs / seThetaStar n ω ωs)
            (α / 2) n ω)
          (bootstrapScalarLowerQuantileIndexed Pstar
            (fun n ω ωs => TthetaStar n ω ωs / seThetaStar n ω ωs)
            (1 - α / 2) n ω)})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) := by
  let Tstar : ∀ n, Ω → Ωboot n → ℝ :=
    fun n ω ωs => TthetaStar n ω ωs / seThetaStar n ω ωs
  haveI : NoAtoms (gaussianReal 0 1) :=
    noAtoms_gaussianReal (μ := 0) (v := 1) (by norm_num)
  have hTmeas : ∀ n ω, AEMeasurable (Tstar n ω) (Pstar n ω) := by
    intro n ω
    exact ((hTthetaStar n ω).div (hseThetaStar n ω)).aemeasurable
  have hTstar :
      TendstoInBootstrapDistributionIndexed μ Pstar
        (fun n ω ωs (_ : Unit) => Tstar n ω ωs)
        (gaussianReal 0 1) (fun x : ℝ => fun _ : Unit => x) := by
    simpa [Tstar] using
      chapter10_indexed_bootstrap_regression_tstat_distribution_of_eventually_bound
        (μ := μ) (Pstar := Pstar) (TthetaStar := TthetaStar)
        (seThetaStar := seThetaStar) (seθ := seθ) (C := C)
        hseθ hT hPstar hTthetaStar hseThetaStar hbound hseStar
  have hlower_meas' :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed Pstar Tstar (α / 2) n) μ := by
    intro n
    simpa [Tstar] using hlower_meas n
  have hupper_meas' :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed Pstar Tstar (1 - α / 2) n) μ := by
    intro n
    simpa [Tstar] using hupper_meas n
  have hξ : HasLaw (fun x : ℝ => x) (gaussianReal 0 1) (gaussianReal 0 1) := by
    simpa [id] using (HasLaw.id (μ := gaussianReal 0 1))
  have hcoverage :=
    chapter10_percentileTCI_coverage_tendsto_one_sub_alpha_indexed_quantile_prob_brackets
      (μ := μ) (ν := gaussianReal 0 1) (η := gaussianReal 0 1)
      (Pstar := Pstar) (Tstar := Tstar) (θ := θ) (θhat := θhat)
      (se := se) (ξ := fun x : ℝ => x) (q := q) (α := α)
      hsampleSe htstat hPstar hTmeas hα_pos hα_lt_one
      hleftLower hrightLower hleftUpper hrightUpper hTstar (fun x => continuousAt_cdf_standardNormal x)
      hlower_meas' hupper_meas' hξ hq_nonneg hcdfLower hcdfUpper
  simpa [Tstar] using hcoverage

/-- Strict-CDF counterpart of
`chapter10_percentileTCI_coverage_tendsto_one_sub_alpha_indexed_of_bootstrap_regression_tstat_eventually_bound_brackets`. -/
theorem
chapter10_percentileTCI_coverage_tendsto_one_sub_alpha_indexed_of_bootstrap_regression_tstat_eventually_bound
    [IsProbabilityMeasure μ]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {TthetaStar seThetaStar : ∀ n, Ω → Ωboot n → ℝ}
    {θ : ℝ} {θhat se : ℕ → Ω → ℝ} {seθ C q α : ℝ}
    (hsampleSe : ∀ n ω, 0 < se n ω)
    (htstat :
      TendstoInDistribution
        (fun n ω => percentileTStatistic θ (θhat n ω) (se n ω))
        atTop (fun x : ℝ => x) (fun _ => μ) (gaussianReal 0 1))
    (hseθ : 0 < seθ)
    (hT :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar TthetaStar
        (gaussianReal 0 1) (fun z : ℝ => seθ * z))
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hTthetaStar : ∀ n ω, Measurable (TthetaStar n ω))
    (hseThetaStar : ∀ n ω, Measurable (seThetaStar n ω))
    (hbound : ∀ᶠ n in atTop, ∀ ω ωs, |TthetaStar n ω ωs| ≤ C)
    (hseStar :
      TendstoInBootstrapProbabilityIndexed μ Pstar seThetaStar (fun _ => seθ))
    (hα_pos : 0 < α) (hα_lt_one : α < 1)
    (hstrict : StrictMono (fun x => cdf (gaussianReal 0 1) x))
    (hlower_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed Pstar
            (fun n ω ωs => TthetaStar n ω ωs / seThetaStar n ω ωs)
            (α / 2) n) μ)
    (hupper_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed Pstar
            (fun n ω ωs => TthetaStar n ω ωs / seThetaStar n ω ωs)
            (1 - α / 2) n) μ)
    (hq_nonneg : 0 ≤ q)
    (hcdfLower : cdf (gaussianReal 0 1) (-q) = α / 2)
    (hcdfUpper : cdf (gaussianReal 0 1) q = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | percentileTCIEvent θ (θhat n ω) (se n ω)
          (bootstrapScalarLowerQuantileIndexed Pstar
            (fun n ω ωs => TthetaStar n ω ωs / seThetaStar n ω ωs)
            (α / 2) n ω)
          (bootstrapScalarLowerQuantileIndexed Pstar
            (fun n ω ωs => TthetaStar n ω ωs / seThetaStar n ω ωs)
            (1 - α / 2) n ω)})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) := by
  obtain ⟨hleftLower, hrightLower⟩ :=
    strictMono_cdf_brackets hstrict hcdfLower
  obtain ⟨hleftUpper, hrightUpper⟩ :=
    strictMono_cdf_brackets hstrict hcdfUpper
  exact
    chapter10_percentileTCI_coverage_tendsto_one_sub_alpha_indexed_of_bootstrap_regression_tstat_eventually_bound_brackets
      (μ := μ) (Pstar := Pstar) (TthetaStar := TthetaStar)
      (seThetaStar := seThetaStar) (θ := θ) (θhat := θhat)
      (se := se) (seθ := seθ) (C := C) (q := q) (α := α)
      hsampleSe htstat hseθ hT hPstar hTthetaStar hseThetaStar hbound
      hseStar hα_pos hα_lt_one hleftLower hrightLower hleftUpper
      hrightUpper hlower_meas hupper_meas hq_nonneg hcdfLower hcdfUpper

set_option linter.style.longLine false in
/-- Local-CDF bracketing face of indexed percentile-`t` coverage with the
bootstrap statistic specialized to the concrete bounded finite
ordinary-bootstrap OLS linear-restriction numerator. -/
theorem
    chapter10_percentileTCI_coverage_tendsto_one_sub_alpha_indexed_of_bootstrap_regression_tstat_finSucc_olsBetaOrZero_gapEnvelope_bounds_brackets
    [IsProbabilityMeasure μ]
    {k : Type*} [Fintype k] [DecidableEq k]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    {seThetaStar : ∀ n, Ω → (Fin (n + 1) → Fin (n + 1)) → ℝ}
    {θ : ℝ} {θhat se : ℕ → Ω → ℝ} {Clin Cbeta Cnum q α : ℝ}
    (β : k → ℝ) (R : Matrix Unit k ℝ)
    (hsampleSe : ∀ n ω, 0 < se n ω)
    (htstat :
      TendstoInDistribution
        (fun n ω => percentileTStatistic θ (θhat n ω) (se n ω))
        atTop (fun x : ℝ => x) (fun _ => μ) (gaussianReal 0 1))
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
    (hseStar :
      TendstoInBootstrapProbabilityIndexed μ
        (fun n _ =>
          (ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
              Measure (Fin (n + 1) → Fin (n + 1))))
        seThetaStar
        (fun _ => linearRestrictionStdError R (heteroAsymCov μ X e)))
    (hα_pos : 0 < α) (hα_lt_one : α < 1)
    (hleftLower :
      ∀ ε : ℝ, 0 < ε → cdf (gaussianReal 0 1) (-q - ε) < α / 2)
    (hrightLower :
      ∀ ε : ℝ, 0 < ε → α / 2 < cdf (gaussianReal 0 1) (-q + ε))
    (hleftUpper :
      ∀ ε : ℝ, 0 < ε → cdf (gaussianReal 0 1) (q - ε) < 1 - α / 2)
    (hrightUpper :
      ∀ ε : ℝ, 0 < ε → 1 - α / 2 < cdf (gaussianReal 0 1) (q + ε))
    (hlower_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed
            (fun n _ =>
              (ProbabilityTheory.uniformOn
                (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                  Measure (Fin (n + 1) → Fin (n + 1))))
            (fun n ω ωs =>
              regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs /
                seThetaStar n ω ωs)
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
              regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs /
                seThetaStar n ω ωs)
            (1 - α / 2) n) μ)
    (hq_nonneg : 0 ≤ q)
    (hcdfLower : cdf (gaussianReal 0 1) (-q) = α / 2)
    (hcdfUpper : cdf (gaussianReal 0 1) q = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | percentileTCIEvent θ (θhat n ω) (se n ω)
          (bootstrapScalarLowerQuantileIndexed
            (fun n _ =>
              (ProbabilityTheory.uniformOn
                (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                  Measure (Fin (n + 1) → Fin (n + 1))))
            (fun n ω ωs =>
              regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs /
                seThetaStar n ω ωs)
            (α / 2) n ω)
          (bootstrapScalarLowerQuantileIndexed
            (fun n _ =>
              (ProbabilityTheory.uniformOn
                (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                  Measure (Fin (n + 1) → Fin (n + 1))))
            (fun n ω ωs =>
              regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs /
                seThetaStar n ω ωs)
            (1 - α / 2) n ω)})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) :=
  chapter10_percentileTCI_coverage_tendsto_one_sub_alpha_indexed_of_bootstrap_regression_tstat_eventually_bound_brackets
    (μ := μ)
    (Pstar := fun n _ =>
      (ProbabilityTheory.uniformOn
        (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
          Measure (Fin (n + 1) → Fin (n + 1))))
    (TthetaStar := fun n ω ωs =>
      regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs)
    (seThetaStar := seThetaStar)
    (θ := θ) (θhat := θhat) (se := se)
    (seθ := linearRestrictionStdError R (heteroAsymCov μ X e))
    (C := Cnum) (q := q) (α := α)
    hsampleSe htstat hseθ
    (chapter10_indexed_bootstrap_regression_linearRestriction_standardNormal_finSucc_olsBetaOrZero_of_gapEnvelope_bounds
      (μ := μ) (X := X) (e := e) (y := y)
      β R hmodel h hΩ hLinBound hBetaBound hGapTail)
    (fun _ _ => inferInstance) (fun _ _ => measurable_of_finite _)
    hseThetaStar hNumBound hseStar hα_pos hα_lt_one hleftLower
      hrightLower hleftUpper hrightUpper hlower_meas hupper_meas
    hq_nonneg hcdfLower hcdfUpper

set_option linter.style.longLine false in
/-- Robust-feasible HC specialization of the indexed bounded concrete finite
OLS local-CDF percentile-`t` coverage wrapper. -/
theorem
    chapter10_percentileTCI_coverage_tendsto_one_sub_alpha_indexed_of_bootstrap_regression_tstat_finSucc_olsBetaOrZero_gapEnvelope_bounds_brackets_of_robustFeasibleHCMomentConditions
    [IsProbabilityMeasure μ]
    {k : Type*} [Fintype k] [DecidableEq k]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    {seThetaStar : ∀ n, Ω → (Fin (n + 1) → Fin (n + 1)) → ℝ}
    {θ : ℝ} {θhat se : ℕ → Ω → ℝ} {Clin Cbeta Cnum q α : ℝ}
    (β : k → ℝ) (R : Matrix Unit k ℝ)
    (hsampleSe : ∀ n ω, 0 < se n ω)
    (htstat :
      TendstoInDistribution
        (fun n ω => percentileTStatistic θ (θhat n ω) (se n ω))
        atTop (fun x : ℝ => x) (fun _ => μ) (gaussianReal 0 1))
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
    (hseStar :
      TendstoInBootstrapProbabilityIndexed μ
        (fun n _ =>
          (ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
              Measure (Fin (n + 1) → Fin (n + 1))))
        seThetaStar
        (fun _ => linearRestrictionStdError R (heteroAsymCov μ X e)))
    (hα_pos : 0 < α) (hα_lt_one : α < 1)
    (hleftLower :
      ∀ ε : ℝ, 0 < ε → cdf (gaussianReal 0 1) (-q - ε) < α / 2)
    (hrightLower :
      ∀ ε : ℝ, 0 < ε → α / 2 < cdf (gaussianReal 0 1) (-q + ε))
    (hleftUpper :
      ∀ ε : ℝ, 0 < ε → cdf (gaussianReal 0 1) (q - ε) < 1 - α / 2)
    (hrightUpper :
      ∀ ε : ℝ, 0 < ε → 1 - α / 2 < cdf (gaussianReal 0 1) (q + ε))
    (hlower_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed
            (fun n _ =>
              (ProbabilityTheory.uniformOn
                (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                  Measure (Fin (n + 1) → Fin (n + 1))))
            (fun n ω ωs =>
              regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs /
                seThetaStar n ω ωs)
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
              regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs /
                seThetaStar n ω ωs)
            (1 - α / 2) n) μ)
    (hq_nonneg : 0 ≤ q)
    (hcdfLower : cdf (gaussianReal 0 1) (-q) = α / 2)
    (hcdfUpper : cdf (gaussianReal 0 1) q = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | percentileTCIEvent θ (θhat n ω) (se n ω)
          (bootstrapScalarLowerQuantileIndexed
            (fun n _ =>
              (ProbabilityTheory.uniformOn
                (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                  Measure (Fin (n + 1) → Fin (n + 1))))
            (fun n ω ωs =>
              regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs /
                seThetaStar n ω ωs)
            (α / 2) n ω)
          (bootstrapScalarLowerQuantileIndexed
            (fun n _ =>
              (ProbabilityTheory.uniformOn
                (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                  Measure (Fin (n + 1) → Fin (n + 1))))
            (fun n ω ωs =>
              regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs /
                seThetaStar n ω ωs)
            (1 - α / 2) n ω)})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) :=
  chapter10_percentileTCI_coverage_tendsto_one_sub_alpha_indexed_of_bootstrap_regression_tstat_finSucc_olsBetaOrZero_gapEnvelope_bounds_brackets
    (μ := μ) (X := X) (e := e) (y := y)
    β R hsampleSe htstat hseθ hm.model hm.toScoreCLTConditions hΩ
    hLinBound hBetaBound hGapTail hseThetaStar hNumBound hseStar
    hα_pos hα_lt_one hleftLower hrightLower hleftUpper hrightUpper
    hlower_meas hupper_meas hq_nonneg hcdfLower hcdfUpper

set_option linter.style.longLine false in
/-- Indexed percentile-`t` coverage with the bootstrap statistic specialized
to the concrete bounded finite ordinary-bootstrap OLS linear-restriction
numerator.

The sample-side statistic is left explicit; this wrapper discharges the
bootstrap-side Theorem 10.18 bounded-numerator route from the finite OLS
gap-envelope numerator CLT, eventual deterministic numerator bound, and
feasible bootstrap standard-error consistency. -/
theorem
    chapter10_percentileTCI_coverage_tendsto_one_sub_alpha_indexed_of_bootstrap_regression_tstat_finSucc_olsBetaOrZero_gapEnvelope_bounds
    [IsProbabilityMeasure μ]
    {k : Type*} [Fintype k] [DecidableEq k]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    {seThetaStar : ∀ n, Ω → (Fin (n + 1) → Fin (n + 1)) → ℝ}
    {θ : ℝ} {θhat se : ℕ → Ω → ℝ} {Clin Cbeta Cnum q α : ℝ}
    (β : k → ℝ) (R : Matrix Unit k ℝ)
    (hsampleSe : ∀ n ω, 0 < se n ω)
    (htstat :
      TendstoInDistribution
        (fun n ω => percentileTStatistic θ (θhat n ω) (se n ω))
        atTop (fun x : ℝ => x) (fun _ => μ) (gaussianReal 0 1))
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
    (hseStar :
      TendstoInBootstrapProbabilityIndexed μ
        (fun n _ =>
          (ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
              Measure (Fin (n + 1) → Fin (n + 1))))
        seThetaStar
        (fun _ => linearRestrictionStdError R (heteroAsymCov μ X e)))
    (hα_pos : 0 < α) (hα_lt_one : α < 1)
    (hstrict : StrictMono (fun x => cdf (gaussianReal 0 1) x))
    (hlower_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed
            (fun n _ =>
              (ProbabilityTheory.uniformOn
                (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                  Measure (Fin (n + 1) → Fin (n + 1))))
            (fun n ω ωs =>
              regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs /
                seThetaStar n ω ωs)
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
              regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs /
                seThetaStar n ω ωs)
            (1 - α / 2) n) μ)
    (hq_nonneg : 0 ≤ q)
    (hcdfLower : cdf (gaussianReal 0 1) (-q) = α / 2)
    (hcdfUpper : cdf (gaussianReal 0 1) q = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | percentileTCIEvent θ (θhat n ω) (se n ω)
          (bootstrapScalarLowerQuantileIndexed
            (fun n _ =>
              (ProbabilityTheory.uniformOn
                (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                  Measure (Fin (n + 1) → Fin (n + 1))))
            (fun n ω ωs =>
              regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs /
                seThetaStar n ω ωs)
            (α / 2) n ω)
          (bootstrapScalarLowerQuantileIndexed
            (fun n _ =>
              (ProbabilityTheory.uniformOn
                (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                  Measure (Fin (n + 1) → Fin (n + 1))))
            (fun n ω ωs =>
              regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs /
                seThetaStar n ω ωs)
            (1 - α / 2) n ω)})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) :=
  chapter10_percentileTCI_coverage_tendsto_one_sub_alpha_indexed_of_bootstrap_regression_tstat_eventually_bound
    (μ := μ)
    (Pstar := fun n _ =>
      (ProbabilityTheory.uniformOn
        (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
          Measure (Fin (n + 1) → Fin (n + 1))))
    (TthetaStar := fun n ω ωs =>
      regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs)
    (seThetaStar := seThetaStar)
    (θ := θ) (θhat := θhat) (se := se)
    (seθ := linearRestrictionStdError R (heteroAsymCov μ X e))
    (C := Cnum) (q := q) (α := α)
    hsampleSe htstat hseθ
    (chapter10_indexed_bootstrap_regression_linearRestriction_standardNormal_finSucc_olsBetaOrZero_of_gapEnvelope_bounds
      (μ := μ) (X := X) (e := e) (y := y)
      β R hmodel h hΩ hLinBound hBetaBound hGapTail)
    (fun _ _ => inferInstance) (fun _ _ => measurable_of_finite _)
    hseThetaStar hNumBound hseStar hα_pos hα_lt_one hstrict
    hlower_meas hupper_meas hq_nonneg hcdfLower hcdfUpper

set_option linter.style.longLine false in
/-- Robust-feasible HC specialization of the indexed bounded concrete finite
OLS percentile-`t` coverage wrapper. -/
theorem
    chapter10_percentileTCI_coverage_tendsto_one_sub_alpha_indexed_of_bootstrap_regression_tstat_finSucc_olsBetaOrZero_gapEnvelope_bounds_of_robustFeasibleHCMomentConditions
    [IsProbabilityMeasure μ]
    {k : Type*} [Fintype k] [DecidableEq k]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    {seThetaStar : ∀ n, Ω → (Fin (n + 1) → Fin (n + 1)) → ℝ}
    {θ : ℝ} {θhat se : ℕ → Ω → ℝ} {Clin Cbeta Cnum q α : ℝ}
    (β : k → ℝ) (R : Matrix Unit k ℝ)
    (hsampleSe : ∀ n ω, 0 < se n ω)
    (htstat :
      TendstoInDistribution
        (fun n ω => percentileTStatistic θ (θhat n ω) (se n ω))
        atTop (fun x : ℝ => x) (fun _ => μ) (gaussianReal 0 1))
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
    (hseStar :
      TendstoInBootstrapProbabilityIndexed μ
        (fun n _ =>
          (ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
              Measure (Fin (n + 1) → Fin (n + 1))))
        seThetaStar
        (fun _ => linearRestrictionStdError R (heteroAsymCov μ X e)))
    (hα_pos : 0 < α) (hα_lt_one : α < 1)
    (hstrict : StrictMono (fun x => cdf (gaussianReal 0 1) x))
    (hlower_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed
            (fun n _ =>
              (ProbabilityTheory.uniformOn
                (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                  Measure (Fin (n + 1) → Fin (n + 1))))
            (fun n ω ωs =>
              regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs /
                seThetaStar n ω ωs)
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
              regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs /
                seThetaStar n ω ωs)
            (1 - α / 2) n) μ)
    (hq_nonneg : 0 ≤ q)
    (hcdfLower : cdf (gaussianReal 0 1) (-q) = α / 2)
    (hcdfUpper : cdf (gaussianReal 0 1) q = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | percentileTCIEvent θ (θhat n ω) (se n ω)
          (bootstrapScalarLowerQuantileIndexed
            (fun n _ =>
              (ProbabilityTheory.uniformOn
                (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                  Measure (Fin (n + 1) → Fin (n + 1))))
            (fun n ω ωs =>
              regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs /
                seThetaStar n ω ωs)
            (α / 2) n ω)
          (bootstrapScalarLowerQuantileIndexed
            (fun n _ =>
              (ProbabilityTheory.uniformOn
                (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                  Measure (Fin (n + 1) → Fin (n + 1))))
            (fun n ω ωs =>
              regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs /
                seThetaStar n ω ωs)
            (1 - α / 2) n ω)})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) :=
  chapter10_percentileTCI_coverage_tendsto_one_sub_alpha_indexed_of_bootstrap_regression_tstat_finSucc_olsBetaOrZero_gapEnvelope_bounds
    (μ := μ) (X := X) (e := e) (y := y)
    β R hsampleSe htstat hseθ hm.model hm.toScoreCLTConditions hΩ
    hLinBound hBetaBound hGapTail hseThetaStar hNumBound hseStar
      hα_pos hα_lt_one hstrict hlower_meas hupper_meas hq_nonneg
    hcdfLower hcdfUpper

set_option linter.style.longLine false in
/-- Local-CDF bracketing face of the indexed beta-bound concrete finite OLS
percentile-`t` coverage wrapper. -/
theorem
    chapter10_percentileTCI_coverage_tendsto_one_sub_alpha_indexed_of_bootstrap_regression_tstat_finSucc_olsBetaOrZero_gapEnvelope_beta_bound_brackets
    [IsProbabilityMeasure μ]
    {k : Type*} [Fintype k] [DecidableEq k]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    {seThetaStar : ∀ n, Ω → (Fin (n + 1) → Fin (n + 1)) → ℝ}
    {θ : ℝ} {θhat se : ℕ → Ω → ℝ} {Clin Cbeta q α : ℝ}
    (β : k → ℝ) (R : Matrix Unit k ℝ)
    (hsampleSe : ∀ n ω, 0 < se n ω)
    (htstat :
      TendstoInDistribution
        (fun n ω => percentileTStatistic θ (θhat n ω) (se n ω))
        atTop (fun x : ℝ => x) (fun _ => μ) (gaussianReal 0 1))
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
    (hseStar :
      TendstoInBootstrapProbabilityIndexed μ
        (fun n _ =>
          (ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
              Measure (Fin (n + 1) → Fin (n + 1))))
        seThetaStar
        (fun _ => linearRestrictionStdError R (heteroAsymCov μ X e)))
    (hα_pos : 0 < α) (hα_lt_one : α < 1)
    (hleftLower :
      ∀ ε : ℝ, 0 < ε → cdf (gaussianReal 0 1) (-q - ε) < α / 2)
    (hrightLower :
      ∀ ε : ℝ, 0 < ε → α / 2 < cdf (gaussianReal 0 1) (-q + ε))
    (hleftUpper :
      ∀ ε : ℝ, 0 < ε → cdf (gaussianReal 0 1) (q - ε) < 1 - α / 2)
    (hrightUpper :
      ∀ ε : ℝ, 0 < ε → 1 - α / 2 < cdf (gaussianReal 0 1) (q + ε))
    (hlower_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed
            (fun n _ =>
              (ProbabilityTheory.uniformOn
                (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                  Measure (Fin (n + 1) → Fin (n + 1))))
            (fun n ω ωs =>
              regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs /
                seThetaStar n ω ωs)
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
              regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs /
                seThetaStar n ω ωs)
            (1 - α / 2) n) μ)
    (hq_nonneg : 0 ≤ q)
    (hcdfLower : cdf (gaussianReal 0 1) (-q) = α / 2)
    (hcdfUpper : cdf (gaussianReal 0 1) q = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | percentileTCIEvent θ (θhat n ω) (se n ω)
          (bootstrapScalarLowerQuantileIndexed
            (fun n _ =>
              (ProbabilityTheory.uniformOn
                (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                  Measure (Fin (n + 1) → Fin (n + 1))))
            (fun n ω ωs =>
              regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs /
                seThetaStar n ω ωs)
            (α / 2) n ω)
          (bootstrapScalarLowerQuantileIndexed
            (fun n _ =>
              (ProbabilityTheory.uniformOn
                (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                  Measure (Fin (n + 1) → Fin (n + 1))))
            (fun n ω ωs =>
              regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs /
                seThetaStar n ω ωs)
            (1 - α / 2) n ω)})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) :=
  chapter10_percentileTCI_coverage_tendsto_one_sub_alpha_indexed_of_bootstrap_regression_tstat_eventually_bound_brackets
    (μ := μ)
    (Pstar := fun n _ =>
      (ProbabilityTheory.uniformOn
        (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
          Measure (Fin (n + 1) → Fin (n + 1))))
    (TthetaStar := fun n ω ωs =>
      regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs)
    (seThetaStar := seThetaStar)
    (θ := θ) (θhat := θhat) (se := se)
    (seθ := linearRestrictionStdError R (heteroAsymCov μ X e))
    (C := ‖PiLp.proj (p := (2 : ℝ≥0∞)) (𝕜 := ℝ)
        (β := fun _ : Unit => ℝ) ()‖ * (‖matrixContinuousLinearMap R‖ * Cbeta))
    (q := q) (α := α)
    hsampleSe htstat hseθ
    (chapter10_indexed_bootstrap_regression_linearRestriction_standardNormal_finSucc_olsBetaOrZero_of_gapEnvelope_bounds
      (μ := μ) (X := X) (e := e) (y := y)
      β R hmodel h hΩ hLinBound hBetaBound hGapTail)
    (fun _ _ => inferInstance) (fun _ _ => measurable_of_finite _)
    hseThetaStar
    (regressionBootstrapLinearRestrictionStatisticFinSucc_eventually_abs_bound_of_beta_bound
      (R := R) (X := X) (y := y) hBetaBound)
    hseStar hα_pos hα_lt_one hleftLower hrightLower hleftUpper
      hrightUpper hlower_meas hupper_meas hq_nonneg hcdfLower hcdfUpper

set_option linter.style.longLine false in
/-- Robust-feasible HC specialization of the indexed beta-bound local-CDF
concrete finite OLS percentile-`t` coverage wrapper. -/
theorem
    chapter10_percentileTCI_coverage_tendsto_one_sub_alpha_indexed_of_bootstrap_regression_tstat_finSucc_olsBetaOrZero_gapEnvelope_beta_bound_brackets_of_robustFeasibleHCMomentConditions
    [IsProbabilityMeasure μ]
    {k : Type*} [Fintype k] [DecidableEq k]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    {seThetaStar : ∀ n, Ω → (Fin (n + 1) → Fin (n + 1)) → ℝ}
    {θ : ℝ} {θhat se : ℕ → Ω → ℝ} {Clin Cbeta q α : ℝ}
    (β : k → ℝ) (R : Matrix Unit k ℝ)
    (hsampleSe : ∀ n ω, 0 < se n ω)
    (htstat :
      TendstoInDistribution
        (fun n ω => percentileTStatistic θ (θhat n ω) (se n ω))
        atTop (fun x : ℝ => x) (fun _ => μ) (gaussianReal 0 1))
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
    (hseStar :
      TendstoInBootstrapProbabilityIndexed μ
        (fun n _ =>
          (ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
              Measure (Fin (n + 1) → Fin (n + 1))))
        seThetaStar
        (fun _ => linearRestrictionStdError R (heteroAsymCov μ X e)))
    (hα_pos : 0 < α) (hα_lt_one : α < 1)
    (hleftLower :
      ∀ ε : ℝ, 0 < ε → cdf (gaussianReal 0 1) (-q - ε) < α / 2)
    (hrightLower :
      ∀ ε : ℝ, 0 < ε → α / 2 < cdf (gaussianReal 0 1) (-q + ε))
    (hleftUpper :
      ∀ ε : ℝ, 0 < ε → cdf (gaussianReal 0 1) (q - ε) < 1 - α / 2)
    (hrightUpper :
      ∀ ε : ℝ, 0 < ε → 1 - α / 2 < cdf (gaussianReal 0 1) (q + ε))
    (hlower_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed
            (fun n _ =>
              (ProbabilityTheory.uniformOn
                (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                  Measure (Fin (n + 1) → Fin (n + 1))))
            (fun n ω ωs =>
              regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs /
                seThetaStar n ω ωs)
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
              regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs /
                seThetaStar n ω ωs)
            (1 - α / 2) n) μ)
    (hq_nonneg : 0 ≤ q)
    (hcdfLower : cdf (gaussianReal 0 1) (-q) = α / 2)
    (hcdfUpper : cdf (gaussianReal 0 1) q = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | percentileTCIEvent θ (θhat n ω) (se n ω)
          (bootstrapScalarLowerQuantileIndexed
            (fun n _ =>
              (ProbabilityTheory.uniformOn
                (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                  Measure (Fin (n + 1) → Fin (n + 1))))
            (fun n ω ωs =>
              regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs /
                seThetaStar n ω ωs)
            (α / 2) n ω)
          (bootstrapScalarLowerQuantileIndexed
            (fun n _ =>
              (ProbabilityTheory.uniformOn
                (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                  Measure (Fin (n + 1) → Fin (n + 1))))
            (fun n ω ωs =>
              regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs /
                seThetaStar n ω ωs)
            (1 - α / 2) n ω)})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) :=
  chapter10_percentileTCI_coverage_tendsto_one_sub_alpha_indexed_of_bootstrap_regression_tstat_finSucc_olsBetaOrZero_gapEnvelope_beta_bound_brackets
    (μ := μ) (X := X) (e := e) (y := y)
    β R hsampleSe htstat hseθ hm.model hm.toScoreCLTConditions hΩ
    hLinBound hBetaBound hGapTail hseThetaStar hseStar hα_pos
    hα_lt_one hleftLower hrightLower hleftUpper hrightUpper
    hlower_meas hupper_meas hq_nonneg hcdfLower hcdfUpper

set_option linter.style.longLine false in
/-- Indexed percentile-`t` coverage with the bootstrap statistic specialized
to the concrete finite ordinary-bootstrap OLS linear-restriction numerator,
where the scalar numerator bound is discharged by the coefficient-statistic
norm bound. -/
theorem
    chapter10_percentileTCI_coverage_tendsto_one_sub_alpha_indexed_of_bootstrap_regression_tstat_finSucc_olsBetaOrZero_gapEnvelope_beta_bound
    [IsProbabilityMeasure μ]
    {k : Type*} [Fintype k] [DecidableEq k]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    {seThetaStar : ∀ n, Ω → (Fin (n + 1) → Fin (n + 1)) → ℝ}
    {θ : ℝ} {θhat se : ℕ → Ω → ℝ} {Clin Cbeta q α : ℝ}
    (β : k → ℝ) (R : Matrix Unit k ℝ)
    (hsampleSe : ∀ n ω, 0 < se n ω)
    (htstat :
      TendstoInDistribution
        (fun n ω => percentileTStatistic θ (θhat n ω) (se n ω))
        atTop (fun x : ℝ => x) (fun _ => μ) (gaussianReal 0 1))
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
    (hseStar :
      TendstoInBootstrapProbabilityIndexed μ
        (fun n _ =>
          (ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
              Measure (Fin (n + 1) → Fin (n + 1))))
        seThetaStar
        (fun _ => linearRestrictionStdError R (heteroAsymCov μ X e)))
    (hα_pos : 0 < α) (hα_lt_one : α < 1)
    (hstrict : StrictMono (fun x => cdf (gaussianReal 0 1) x))
    (hlower_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed
            (fun n _ =>
              (ProbabilityTheory.uniformOn
                (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                  Measure (Fin (n + 1) → Fin (n + 1))))
            (fun n ω ωs =>
              regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs /
                seThetaStar n ω ωs)
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
              regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs /
                seThetaStar n ω ωs)
            (1 - α / 2) n) μ)
    (hq_nonneg : 0 ≤ q)
    (hcdfLower : cdf (gaussianReal 0 1) (-q) = α / 2)
    (hcdfUpper : cdf (gaussianReal 0 1) q = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | percentileTCIEvent θ (θhat n ω) (se n ω)
          (bootstrapScalarLowerQuantileIndexed
            (fun n _ =>
              (ProbabilityTheory.uniformOn
                (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                  Measure (Fin (n + 1) → Fin (n + 1))))
            (fun n ω ωs =>
              regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs /
                seThetaStar n ω ωs)
            (α / 2) n ω)
          (bootstrapScalarLowerQuantileIndexed
            (fun n _ =>
              (ProbabilityTheory.uniformOn
                (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                  Measure (Fin (n + 1) → Fin (n + 1))))
            (fun n ω ωs =>
              regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs /
                seThetaStar n ω ωs)
            (1 - α / 2) n ω)})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) :=
  chapter10_percentileTCI_coverage_tendsto_one_sub_alpha_indexed_of_bootstrap_regression_tstat_finSucc_olsBetaOrZero_gapEnvelope_bounds
    (μ := μ) (X := X) (e := e) (y := y)
    (Cnum := ‖PiLp.proj (p := (2 : ℝ≥0∞)) (𝕜 := ℝ)
        (β := fun _ : Unit => ℝ) ()‖ * (‖matrixContinuousLinearMap R‖ * Cbeta))
    β R hsampleSe htstat hseθ hmodel h hΩ hLinBound hBetaBound hGapTail
    hseThetaStar
    (regressionBootstrapLinearRestrictionStatisticFinSucc_eventually_abs_bound_of_beta_bound
      (R := R) (X := X) (y := y) hBetaBound)
      hseStar hα_pos hα_lt_one hstrict hlower_meas hupper_meas
    hq_nonneg hcdfLower hcdfUpper

set_option linter.style.longLine false in
/-- Robust-feasible HC specialization of the indexed beta-bound concrete
finite OLS percentile-`t` coverage wrapper. -/
theorem
    chapter10_percentileTCI_coverage_tendsto_one_sub_alpha_indexed_of_bootstrap_regression_tstat_finSucc_olsBetaOrZero_gapEnvelope_beta_bound_of_robustFeasibleHCMomentConditions
    [IsProbabilityMeasure μ]
    {k : Type*} [Fintype k] [DecidableEq k]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    {seThetaStar : ∀ n, Ω → (Fin (n + 1) → Fin (n + 1)) → ℝ}
    {θ : ℝ} {θhat se : ℕ → Ω → ℝ} {Clin Cbeta q α : ℝ}
    (β : k → ℝ) (R : Matrix Unit k ℝ)
    (hsampleSe : ∀ n ω, 0 < se n ω)
    (htstat :
      TendstoInDistribution
        (fun n ω => percentileTStatistic θ (θhat n ω) (se n ω))
        atTop (fun x : ℝ => x) (fun _ => μ) (gaussianReal 0 1))
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
    (hseStar :
      TendstoInBootstrapProbabilityIndexed μ
        (fun n _ =>
          (ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
              Measure (Fin (n + 1) → Fin (n + 1))))
        seThetaStar
        (fun _ => linearRestrictionStdError R (heteroAsymCov μ X e)))
    (hα_pos : 0 < α) (hα_lt_one : α < 1)
    (hstrict : StrictMono (fun x => cdf (gaussianReal 0 1) x))
    (hlower_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed
            (fun n _ =>
              (ProbabilityTheory.uniformOn
                (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                  Measure (Fin (n + 1) → Fin (n + 1))))
            (fun n ω ωs =>
              regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs /
                seThetaStar n ω ωs)
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
              regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs /
                seThetaStar n ω ωs)
            (1 - α / 2) n) μ)
    (hq_nonneg : 0 ≤ q)
    (hcdfLower : cdf (gaussianReal 0 1) (-q) = α / 2)
    (hcdfUpper : cdf (gaussianReal 0 1) q = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | percentileTCIEvent θ (θhat n ω) (se n ω)
          (bootstrapScalarLowerQuantileIndexed
            (fun n _ =>
              (ProbabilityTheory.uniformOn
                (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                  Measure (Fin (n + 1) → Fin (n + 1))))
            (fun n ω ωs =>
              regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs /
                seThetaStar n ω ωs)
            (α / 2) n ω)
          (bootstrapScalarLowerQuantileIndexed
            (fun n _ =>
              (ProbabilityTheory.uniformOn
                (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                  Measure (Fin (n + 1) → Fin (n + 1))))
            (fun n ω ωs =>
              regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs /
                seThetaStar n ω ωs)
            (1 - α / 2) n ω)})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) :=
  chapter10_percentileTCI_coverage_tendsto_one_sub_alpha_indexed_of_bootstrap_regression_tstat_finSucc_olsBetaOrZero_gapEnvelope_beta_bound
    (μ := μ) (X := X) (e := e) (y := y)
    β R hsampleSe htstat hseθ hm.model hm.toScoreCLTConditions hΩ
    hLinBound hBetaBound hGapTail hseThetaStar hseStar hα_pos
      hα_lt_one hstrict hlower_meas hupper_meas hq_nonneg hcdfLower
    hcdfUpper

private theorem percentileTStatistic_linearRestriction_eq_olsLinearTStatOrZero
    {ι k : Type*} [Fintype ι] [Fintype k] [DecidableEq k]
    (R : Matrix Unit k ℝ) (Vhat : Matrix k k ℝ)
    (X : Matrix ι k ℝ) (y : ι → ℝ) (β : k → ℝ) (root : ℝ) :
    percentileTStatistic (linearRestrictionEstimate R β)
      (linearRestrictionEstimate R (olsBetaOrZero X y))
      (linearRestrictionStdError R Vhat / root) =
      olsLinearTStatOrZero R Vhat X y β root := by
  dsimp [percentileTStatistic, olsLinearTStatOrZero,
    olsLinearTNumeratorOrZero, linearRestrictionEstimate]
  rw [linearMapUnit_smul_sub_dot_one]
  by_cases hroot : root = 0
  · simp [hroot]
  · by_cases hse : linearRestrictionStdError R Vhat = 0
    · simp [hse]
    · field_simp [hroot, hse]

private theorem olsPercentileTStdError_pos
    [Fintype k]
    {Vhat : ℕ → Ω → Matrix k k ℝ}
    (R : Matrix Unit k ℝ)
    (hsampleSe_pos :
      ∀ n ω, n ≠ 0 → 0 < linearRestrictionStdError R (Vhat n ω)) :
    ∀ n ω,
      0 <
        if n = 0 then 1
        else linearRestrictionStdError R (Vhat n ω) / Real.sqrt (n : ℝ) := by
  intro n ω
  by_cases hn : n = 0
  · simp [hn]
  · have hnpos_nat : 0 < n := Nat.pos_of_ne_zero hn
    have hnpos_real : (0 : ℝ) < n := by exact_mod_cast hnpos_nat
    have hsqrt_pos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnpos_real
    simp [hn, div_pos (hsampleSe_pos n ω hn) hsqrt_pos]

private theorem olsPercentileTStatistic_tendstoInDistribution_standardNormal
    [IsProbabilityMeasure μ] [Fintype k] [DecidableEq k]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    {Vhat : ℕ → Ω → Matrix k k ℝ}
    (β : k → ℝ) (R : Matrix Unit k ℝ)
    (hm : RobustFeasibleHCMomentConditions μ X e y β)
    (hVhat : ∀ n, AEStronglyMeasurable (Vhat n) μ)
    (htstat :
      TendstoInDistribution
        (fun n ω =>
          olsLinearTStatOrZero R (Vhat n ω)
            (stackRegressors X n ω) (stackOutcomes y n ω) β
            (Real.sqrt (n : ℝ)))
        atTop (fun x : ℝ => x) (fun _ => μ) (gaussianReal 0 1)) :
    TendstoInDistribution
      (fun n ω =>
        percentileTStatistic (linearRestrictionEstimate R β)
          (linearRestrictionEstimate R
            (olsBetaOrZero
              (stackRegressors X n ω) (stackOutcomes y n ω)))
          (if n = 0 then 1
            else linearRestrictionStdError R (Vhat n ω) / Real.sqrt (n : ℝ)))
      atTop (fun x : ℝ => x) (fun _ => μ) (gaussianReal 0 1) := by
  have hmeas :
      ∀ n,
        AEMeasurable
          (fun ω =>
            percentileTStatistic (linearRestrictionEstimate R β)
              (linearRestrictionEstimate R
                (olsBetaOrZero
                  (stackRegressors X n ω) (stackOutcomes y n ω)))
              (if n = 0 then 1
                else linearRestrictionStdError R (Vhat n ω) /
                  Real.sqrt (n : ℝ))) μ := by
    intro n
    have hbeta :
        AEStronglyMeasurable
          (fun ω =>
            olsBetaOrZero
              (stackRegressors X n ω) (stackOutcomes y n ω)) μ :=
      olsBetaOrZero_stack_aestronglyMeasurable
        (μ := μ) (X := X) (e := e) (y := y) β
        hm.toLeastSquaresConsistencyConditions hm.model n
    have hθhat :
        AEMeasurable
          (fun ω =>
            linearRestrictionEstimate R
              (olsBetaOrZero
                (stackRegressors X n ω) (stackOutcomes y n ω))) μ := by
      have  :
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
      exact this.measurable.comp_aemeasurable hbeta.aemeasurable
    have hseBase :
        AEMeasurable
          (fun ω => linearRestrictionStdError R (Vhat n ω)) μ := by
      simpa [linearRestrictionStdError] using
        linearCovarianceStdError_aemeasurable (μ := μ) R (hVhat n)
    have hse :
        AEMeasurable
          (fun ω =>
            if n = 0 then 1
            else linearRestrictionStdError R (Vhat n ω) /
              Real.sqrt (n : ℝ)) μ := by
      by_cases hn : n = 0
      · simp [hn]
      · simpa [hn] using hseBase.div_const (Real.sqrt (n : ℝ))
    simpa [percentileTStatistic] using
      (hθhat.sub (aemeasurable_const :
        AEMeasurable (fun _ : Ω => linearRestrictionEstimate R β) μ)).div hse
  have hcongr :
      ∀ᶠ n in atTop,
        (fun ω =>
          olsLinearTStatOrZero R (Vhat n ω)
            (stackRegressors X n ω) (stackOutcomes y n ω) β
            (Real.sqrt (n : ℝ))) =ᵐ[μ]
        fun ω =>
          percentileTStatistic (linearRestrictionEstimate R β)
            (linearRestrictionEstimate R
              (olsBetaOrZero
                (stackRegressors X n ω) (stackOutcomes y n ω)))
            (if n = 0 then 1
              else linearRestrictionStdError R (Vhat n ω) /
                Real.sqrt (n : ℝ)) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact ae_of_all μ fun ω => by
      have hnpos_nat : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hn
      have hn_ne : n ≠ 0 := Nat.ne_of_gt hnpos_nat
      simpa only [hn_ne, if_false] using
        (percentileTStatistic_linearRestriction_eq_olsLinearTStatOrZero
          (R := R) (Vhat := Vhat n ω)
          (X := stackRegressors X n ω)
          (y := stackOutcomes y n ω) (β := β)
          (root := Real.sqrt (n : ℝ))).symm
  exact tendstoInDistribution_congr_eventually hmeas hcongr htstat

private theorem
chapter10_ols_percentileTCI_coverage_tendsto_one_sub_alpha_of_bootstrap_regression_tstat
    [IsProbabilityMeasure μ] [Fintype k] [DecidableEq k]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    {Vhat : ℕ → Ω → Matrix k k ℝ}
    {Pstar : ℕ → Ω → Measure Ωs}
    {TthetaStar seThetaStar : ℕ → Ω → Ωs → ℝ}
    {seθ q α : ℝ}
    (β : k → ℝ) (R : Matrix Unit k ℝ)
    (hm : RobustFeasibleHCMomentConditions μ X e y β)
    (hVhat : ∀ n, AEStronglyMeasurable (Vhat n) μ)
    (hsampleSe_pos :
      ∀ n ω, n ≠ 0 → 0 < linearRestrictionStdError R (Vhat n ω))
    (htstat :
      TendstoInDistribution
        (fun n ω =>
          olsLinearTStatOrZero R (Vhat n ω)
            (stackRegressors X n ω) (stackOutcomes y n ω) β
            (Real.sqrt (n : ℝ)))
        atTop (fun x : ℝ => x) (fun _ => μ) (gaussianReal 0 1))
    (hseθ : 0 < seθ)
    (hjoint :
      TendstoInBootstrapWeakDistribution μ Pstar
        (fun n ω ωs => (TthetaStar n ω ωs, seThetaStar n ω ωs))
        (gaussianReal 0 1) (fun z : ℝ => (seθ * z, seθ)))
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hTthetaStar : ∀ n ω, Measurable (TthetaStar n ω))
    (hseThetaStar : ∀ n ω, Measurable (seThetaStar n ω))
    (hseStar :
      TendstoInBootstrapProbability μ Pstar seThetaStar (fun _ => seθ))
    (hα_pos : 0 < α) (hα_lt_one : α < 1)
    (hstrict : StrictMono (fun x => cdf (gaussianReal 0 1) x))
    (hlower_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantile Pstar
            (fun n ω ωs => TthetaStar n ω ωs / seThetaStar n ω ωs)
            (α / 2) n) μ)
    (hupper_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantile Pstar
            (fun n ω ωs => TthetaStar n ω ωs / seThetaStar n ω ωs)
            (1 - α / 2) n) μ)
    (hq_nonneg : 0 ≤ q)
    (hcdfLower : cdf (gaussianReal 0 1) (-q) = α / 2)
    (hcdfUpper : cdf (gaussianReal 0 1) q = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | percentileTCIEvent (linearRestrictionEstimate R β)
          (linearRestrictionEstimate R
            (olsBetaOrZero
              (stackRegressors X n ω) (stackOutcomes y n ω)))
          (if n = 0 then 1
            else linearRestrictionStdError R (Vhat n ω) /
              Real.sqrt (n : ℝ))
          (bootstrapScalarLowerQuantile Pstar
            (fun n ω ωs => TthetaStar n ω ωs / seThetaStar n ω ωs)
            (α / 2) n ω)
          (bootstrapScalarLowerQuantile Pstar
            (fun n ω ωs => TthetaStar n ω ωs / seThetaStar n ω ωs)
            (1 - α / 2) n ω)})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) := by
  exact
    chapter10_percentileTCI_coverage_tendsto_one_sub_alpha_of_bootstrap_regression_tstat
      (μ := μ) (Pstar := Pstar) (TthetaStar := TthetaStar)
      (seThetaStar := seThetaStar)
      (θ := linearRestrictionEstimate R β)
      (θhat := fun n ω =>
        linearRestrictionEstimate R
          (olsBetaOrZero
            (stackRegressors X n ω) (stackOutcomes y n ω)))
      (se := fun n ω =>
        if n = 0 then 1
        else linearRestrictionStdError R (Vhat n ω) / Real.sqrt (n : ℝ))
      (seθ := seθ) (q := q) (α := α)
      (olsPercentileTStdError_pos R hsampleSe_pos)
      (olsPercentileTStatistic_tendstoInDistribution_standardNormal
        β R hm hVhat htstat)
      hseθ hjoint hPstar hTthetaStar hseThetaStar hseStar hα_pos
      hα_lt_one hstrict hlower_meas hupper_meas hq_nonneg
      hcdfLower hcdfUpper

private theorem
chapter10_indexed_ols_percentileTCI_coverage_tendsto_one_sub_alpha_of_bootstrap_regression_tstat
    [IsProbabilityMeasure μ] [Fintype k] [DecidableEq k]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    {Vhat : ℕ → Ω → Matrix k k ℝ}
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {TthetaStar seThetaStar : ∀ n, Ω → Ωboot n → ℝ}
    {seθ q α : ℝ}
    (β : k → ℝ) (R : Matrix Unit k ℝ)
    (hm : RobustFeasibleHCMomentConditions μ X e y β)
    (hVhat : ∀ n, AEStronglyMeasurable (Vhat n) μ)
    (hsampleSe_pos :
      ∀ n ω, n ≠ 0 → 0 < linearRestrictionStdError R (Vhat n ω))
    (htstat :
      TendstoInDistribution
        (fun n ω =>
          olsLinearTStatOrZero R (Vhat n ω)
            (stackRegressors X n ω) (stackOutcomes y n ω) β
            (Real.sqrt (n : ℝ)))
        atTop (fun x : ℝ => x) (fun _ => μ) (gaussianReal 0 1))
    (hseθ : 0 < seθ)
    (hjoint :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar
        (fun n ω ωs => (TthetaStar n ω ωs, seThetaStar n ω ωs))
        (gaussianReal 0 1) (fun z : ℝ => (seθ * z, seθ)))
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hTthetaStar : ∀ n ω, Measurable (TthetaStar n ω))
    (hseThetaStar : ∀ n ω, Measurable (seThetaStar n ω))
    (hseStar :
      TendstoInBootstrapProbabilityIndexed μ Pstar seThetaStar (fun _ => seθ))
    (hα_pos : 0 < α) (hα_lt_one : α < 1)
    (hstrict : StrictMono (fun x => cdf (gaussianReal 0 1) x))
    (hlower_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed Pstar
            (fun n ω ωs => TthetaStar n ω ωs / seThetaStar n ω ωs)
            (α / 2) n) μ)
    (hupper_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed Pstar
            (fun n ω ωs => TthetaStar n ω ωs / seThetaStar n ω ωs)
            (1 - α / 2) n) μ)
    (hq_nonneg : 0 ≤ q)
    (hcdfLower : cdf (gaussianReal 0 1) (-q) = α / 2)
    (hcdfUpper : cdf (gaussianReal 0 1) q = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | percentileTCIEvent (linearRestrictionEstimate R β)
          (linearRestrictionEstimate R
            (olsBetaOrZero
              (stackRegressors X n ω) (stackOutcomes y n ω)))
          (if n = 0 then 1
            else linearRestrictionStdError R (Vhat n ω) /
              Real.sqrt (n : ℝ))
          (bootstrapScalarLowerQuantileIndexed Pstar
            (fun n ω ωs => TthetaStar n ω ωs / seThetaStar n ω ωs)
            (α / 2) n ω)
          (bootstrapScalarLowerQuantileIndexed Pstar
            (fun n ω ωs => TthetaStar n ω ωs / seThetaStar n ω ωs)
            (1 - α / 2) n ω)})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) := by
  exact
    chapter10_percentileTCI_coverage_tendsto_one_sub_alpha_indexed_of_bootstrap_regression_tstat
      (μ := μ) (Pstar := Pstar) (TthetaStar := TthetaStar)
      (seThetaStar := seThetaStar)
      (θ := linearRestrictionEstimate R β)
      (θhat := fun n ω =>
        linearRestrictionEstimate R
          (olsBetaOrZero
            (stackRegressors X n ω) (stackOutcomes y n ω)))
      (se := fun n ω =>
        if n = 0 then 1
        else linearRestrictionStdError R (Vhat n ω) / Real.sqrt (n : ℝ))
      (seθ := seθ) (q := q) (α := α)
      (olsPercentileTStdError_pos R hsampleSe_pos)
      (olsPercentileTStatistic_tendstoInDistribution_standardNormal
        β R hm hVhat htstat)
      hseθ hjoint hPstar hTthetaStar hseThetaStar hseStar hα_pos
      hα_lt_one hstrict hlower_meas hupper_meas hq_nonneg
      hcdfLower hcdfUpper

private theorem
chapter10_ols_percentileTCI_coverage_tendsto_one_sub_alpha_of_bootstrap_regression_tstat_brackets
    [IsProbabilityMeasure μ] [Fintype k] [DecidableEq k]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    {Vhat : ℕ → Ω → Matrix k k ℝ}
    {Pstar : ℕ → Ω → Measure Ωs}
    {TthetaStar seThetaStar : ℕ → Ω → Ωs → ℝ}
    {seθ q α : ℝ}
    (β : k → ℝ) (R : Matrix Unit k ℝ)
    (hm : RobustFeasibleHCMomentConditions μ X e y β)
    (hVhat : ∀ n, AEStronglyMeasurable (Vhat n) μ)
    (hsampleSe_pos :
      ∀ n ω, n ≠ 0 → 0 < linearRestrictionStdError R (Vhat n ω))
    (htstat :
      TendstoInDistribution
        (fun n ω =>
          olsLinearTStatOrZero R (Vhat n ω)
            (stackRegressors X n ω) (stackOutcomes y n ω) β
            (Real.sqrt (n : ℝ)))
        atTop (fun x : ℝ => x) (fun _ => μ) (gaussianReal 0 1))
    (hseθ : 0 < seθ)
    (hjoint :
      TendstoInBootstrapWeakDistribution μ Pstar
        (fun n ω ωs => (TthetaStar n ω ωs, seThetaStar n ω ωs))
        (gaussianReal 0 1) (fun z : ℝ => (seθ * z, seθ)))
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hTthetaStar : ∀ n ω, Measurable (TthetaStar n ω))
    (hseThetaStar : ∀ n ω, Measurable (seThetaStar n ω))
    (hseStar :
      TendstoInBootstrapProbability μ Pstar seThetaStar (fun _ => seθ))
    (hα_pos : 0 < α) (hα_lt_one : α < 1)
    (hleftLower :
      ∀ ε : ℝ, 0 < ε → cdf (gaussianReal 0 1) (-q - ε) < α / 2)
    (hrightLower :
      ∀ ε : ℝ, 0 < ε → α / 2 < cdf (gaussianReal 0 1) (-q + ε))
    (hleftUpper :
      ∀ ε : ℝ, 0 < ε → cdf (gaussianReal 0 1) (q - ε) < 1 - α / 2)
    (hrightUpper :
      ∀ ε : ℝ, 0 < ε → 1 - α / 2 < cdf (gaussianReal 0 1) (q + ε))
    (hlower_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantile Pstar
            (fun n ω ωs => TthetaStar n ω ωs / seThetaStar n ω ωs)
            (α / 2) n) μ)
    (hupper_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantile Pstar
            (fun n ω ωs => TthetaStar n ω ωs / seThetaStar n ω ωs)
            (1 - α / 2) n) μ)
    (hq_nonneg : 0 ≤ q)
    (hcdfLower : cdf (gaussianReal 0 1) (-q) = α / 2)
    (hcdfUpper : cdf (gaussianReal 0 1) q = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | percentileTCIEvent (linearRestrictionEstimate R β)
          (linearRestrictionEstimate R
            (olsBetaOrZero
              (stackRegressors X n ω) (stackOutcomes y n ω)))
          (if n = 0 then 1
            else linearRestrictionStdError R (Vhat n ω) /
              Real.sqrt (n : ℝ))
          (bootstrapScalarLowerQuantile Pstar
            (fun n ω ωs => TthetaStar n ω ωs / seThetaStar n ω ωs)
            (α / 2) n ω)
          (bootstrapScalarLowerQuantile Pstar
            (fun n ω ωs => TthetaStar n ω ωs / seThetaStar n ω ωs)
            (1 - α / 2) n ω)})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) := by
  exact
    chapter10_percentileTCI_coverage_tendsto_one_sub_alpha_of_bootstrap_regression_tstat_brackets
      (μ := μ) (Pstar := Pstar) (TthetaStar := TthetaStar)
      (seThetaStar := seThetaStar)
      (θ := linearRestrictionEstimate R β)
      (θhat := fun n ω =>
        linearRestrictionEstimate R
          (olsBetaOrZero
            (stackRegressors X n ω) (stackOutcomes y n ω)))
      (se := fun n ω =>
        if n = 0 then 1
        else linearRestrictionStdError R (Vhat n ω) / Real.sqrt (n : ℝ))
      (seθ := seθ) (q := q) (α := α)
      (olsPercentileTStdError_pos R hsampleSe_pos)
      (olsPercentileTStatistic_tendstoInDistribution_standardNormal
        β R hm hVhat htstat)
      hseθ hjoint hPstar hTthetaStar hseThetaStar hseStar hα_pos
      hα_lt_one hleftLower hrightLower hleftUpper hrightUpper
      hlower_meas hupper_meas hq_nonneg hcdfLower hcdfUpper

private theorem
chapter10_indexed_ols_percentileTCI_coverage_tendsto_one_sub_alpha_of_bootstrap_regression_tstat_brackets
    [IsProbabilityMeasure μ] [Fintype k] [DecidableEq k]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    {Vhat : ℕ → Ω → Matrix k k ℝ}
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {TthetaStar seThetaStar : ∀ n, Ω → Ωboot n → ℝ}
    {seθ q α : ℝ}
    (β : k → ℝ) (R : Matrix Unit k ℝ)
    (hm : RobustFeasibleHCMomentConditions μ X e y β)
    (hVhat : ∀ n, AEStronglyMeasurable (Vhat n) μ)
    (hsampleSe_pos :
      ∀ n ω, n ≠ 0 → 0 < linearRestrictionStdError R (Vhat n ω))
    (htstat :
      TendstoInDistribution
        (fun n ω =>
          olsLinearTStatOrZero R (Vhat n ω)
            (stackRegressors X n ω) (stackOutcomes y n ω) β
            (Real.sqrt (n : ℝ)))
        atTop (fun x : ℝ => x) (fun _ => μ) (gaussianReal 0 1))
    (hseθ : 0 < seθ)
    (hjoint :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar
        (fun n ω ωs => (TthetaStar n ω ωs, seThetaStar n ω ωs))
        (gaussianReal 0 1) (fun z : ℝ => (seθ * z, seθ)))
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hTthetaStar : ∀ n ω, Measurable (TthetaStar n ω))
    (hseThetaStar : ∀ n ω, Measurable (seThetaStar n ω))
    (hseStar :
      TendstoInBootstrapProbabilityIndexed μ Pstar seThetaStar (fun _ => seθ))
    (hα_pos : 0 < α) (hα_lt_one : α < 1)
    (hleftLower :
      ∀ ε : ℝ, 0 < ε → cdf (gaussianReal 0 1) (-q - ε) < α / 2)
    (hrightLower :
      ∀ ε : ℝ, 0 < ε → α / 2 < cdf (gaussianReal 0 1) (-q + ε))
    (hleftUpper :
      ∀ ε : ℝ, 0 < ε → cdf (gaussianReal 0 1) (q - ε) < 1 - α / 2)
    (hrightUpper :
      ∀ ε : ℝ, 0 < ε → 1 - α / 2 < cdf (gaussianReal 0 1) (q + ε))
    (hlower_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed Pstar
            (fun n ω ωs => TthetaStar n ω ωs / seThetaStar n ω ωs)
            (α / 2) n) μ)
    (hupper_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed Pstar
            (fun n ω ωs => TthetaStar n ω ωs / seThetaStar n ω ωs)
            (1 - α / 2) n) μ)
    (hq_nonneg : 0 ≤ q)
    (hcdfLower : cdf (gaussianReal 0 1) (-q) = α / 2)
    (hcdfUpper : cdf (gaussianReal 0 1) q = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | percentileTCIEvent (linearRestrictionEstimate R β)
          (linearRestrictionEstimate R
            (olsBetaOrZero
              (stackRegressors X n ω) (stackOutcomes y n ω)))
          (if n = 0 then 1
            else linearRestrictionStdError R (Vhat n ω) /
              Real.sqrt (n : ℝ))
          (bootstrapScalarLowerQuantileIndexed Pstar
            (fun n ω ωs => TthetaStar n ω ωs / seThetaStar n ω ωs)
            (α / 2) n ω)
          (bootstrapScalarLowerQuantileIndexed Pstar
            (fun n ω ωs => TthetaStar n ω ωs / seThetaStar n ω ωs)
            (1 - α / 2) n ω)})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) := by
  exact
    chapter10_percentileTCI_coverage_tendsto_one_sub_alpha_indexed_of_bootstrap_regression_tstat_brackets
      (μ := μ) (Pstar := Pstar) (TthetaStar := TthetaStar)
      (seThetaStar := seThetaStar)
      (θ := linearRestrictionEstimate R β)
      (θhat := fun n ω =>
        linearRestrictionEstimate R
          (olsBetaOrZero
            (stackRegressors X n ω) (stackOutcomes y n ω)))
      (se := fun n ω =>
        if n = 0 then 1
        else linearRestrictionStdError R (Vhat n ω) / Real.sqrt (n : ℝ))
      (seθ := seθ) (q := q) (α := α)
      (olsPercentileTStdError_pos R hsampleSe_pos)
      (olsPercentileTStatistic_tendstoInDistribution_standardNormal
        β R hm hVhat htstat)
      hseθ hjoint hPstar hTthetaStar hseThetaStar hseStar hα_pos
      hα_lt_one hleftLower hrightLower hleftUpper hrightUpper
      hlower_meas hupper_meas hq_nonneg hcdfLower hcdfUpper

/-- Theorem 10.14 with the actual sample statistic specialized to the ordinary
HC0 OLS scalar restriction.

The displayed interval uses the ordinary OLS estimate and HC0 standard error
scaled by `sqrt n`; the harmless `n = 0` branch keeps the totalized standard
error positive while the proof identifies the statistic with the Chapter 7 HC0
t-statistic eventually. -/
theorem
chapter10_olsHC0_percentileTCI_coverage_tendsto_one_sub_alpha_of_bootstrap_regression_tstat
    [IsProbabilityMeasure μ] [Fintype k] [DecidableEq k]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    {Pstar : ℕ → Ω → Measure Ωs}
    {TthetaStar seThetaStar : ℕ → Ω → Ωs → ℝ}
    {seθ q α : ℝ}
    (β : k → ℝ) (R : Matrix Unit k ℝ)
    (hm : RobustFeasibleHCMomentConditions μ X e y β)
    (hse_pos : 0 <
      linearRestrictionStdError R (heteroAsymCov μ X e))
    (hsampleSe_pos :
      ∀ n ω, n ≠ 0 →
        0 < linearRestrictionStdError R
          (olsHetCovStar
            (stackRegressors X n ω) (stackOutcomes y n ω)))
    (hseθ : 0 < seθ)
    (hjoint :
      TendstoInBootstrapWeakDistribution μ Pstar
        (fun n ω ωs => (TthetaStar n ω ωs, seThetaStar n ω ωs))
        (gaussianReal 0 1) (fun z : ℝ => (seθ * z, seθ)))
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hTthetaStar : ∀ n ω, Measurable (TthetaStar n ω))
    (hseThetaStar : ∀ n ω, Measurable (seThetaStar n ω))
    (hseStar :
      TendstoInBootstrapProbability μ Pstar seThetaStar (fun _ => seθ))
    (hα_pos : 0 < α) (hα_lt_one : α < 1)
    (hstrict : StrictMono (fun x => cdf (gaussianReal 0 1) x))
    (hlower_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantile Pstar
            (fun n ω ωs => TthetaStar n ω ωs / seThetaStar n ω ωs)
            (α / 2) n) μ)
    (hupper_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantile Pstar
            (fun n ω ωs => TthetaStar n ω ωs / seThetaStar n ω ωs)
            (1 - α / 2) n) μ)
    (hq_nonneg : 0 ≤ q)
    (hcdfLower : cdf (gaussianReal 0 1) (-q) = α / 2)
    (hcdfUpper : cdf (gaussianReal 0 1) q = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | percentileTCIEvent (linearRestrictionEstimate R β)
          (linearRestrictionEstimate R
            (olsBetaOrZero
              (stackRegressors X n ω) (stackOutcomes y n ω)))
          (if n = 0 then 1
            else linearRestrictionStdError R
              (olsHetCovStar
                (stackRegressors X n ω) (stackOutcomes y n ω)) /
              Real.sqrt (n : ℝ))
          (bootstrapScalarLowerQuantile Pstar
            (fun n ω ωs => TthetaStar n ω ωs / seThetaStar n ω ωs)
            (α / 2) n ω)
          (bootstrapScalarLowerQuantile Pstar
            (fun n ω ωs => TthetaStar n ω ωs / seThetaStar n ω ωs)
            (1 - α / 2) n ω)})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) := by
  exact
    chapter10_ols_percentileTCI_coverage_tendsto_one_sub_alpha_of_bootstrap_regression_tstat
      (μ := μ) (X := X) (e := e) (y := y)
      (Vhat := fun n ω =>
        olsHetCovStar
          (stackRegressors X n ω) (stackOutcomes y n ω))
      (Pstar := Pstar) (TthetaStar := TthetaStar)
      (seThetaStar := seThetaStar) (seθ := seθ) (q := q) (α := α)
      β R hm
      (fun n =>
        olsHetCovStar_stack_aestronglyMeasurable_components
          (μ := μ) (X := X) (e := e) (y := y)
          hm.toSampleMomentAssumption71 β hm.model
          hm.x_aestronglyMeasurable hm.e_aestronglyMeasurable n)
      hsampleSe_pos
      (olsHC0LinTStatOrZero_tendstoInDistribution_standardNormal_of_robustFeasibleHCMomentConditions
        (μ := μ) (X := X) (e := e) (y := y) β R hm hse_pos)
      hseθ hjoint hPstar hTthetaStar hseThetaStar hseStar hα_pos
      hα_lt_one hstrict hlower_meas hupper_meas hq_nonneg
      hcdfLower hcdfUpper

/-- Indexed Theorem 10.14 with the actual sample statistic specialized to the
ordinary HC0 OLS scalar restriction. -/
theorem
chapter10_indexed_olsHC0_percentileTCI_coverage_tendsto_one_sub_alpha_of_bootstrap_regression_tstat
    [IsProbabilityMeasure μ] [Fintype k] [DecidableEq k]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {TthetaStar seThetaStar : ∀ n, Ω → Ωboot n → ℝ}
    {seθ q α : ℝ}
    (β : k → ℝ) (R : Matrix Unit k ℝ)
    (hm : RobustFeasibleHCMomentConditions μ X e y β)
    (hse_pos : 0 <
      linearRestrictionStdError R (heteroAsymCov μ X e))
    (hsampleSe_pos :
      ∀ n ω, n ≠ 0 →
        0 < linearRestrictionStdError R
          (olsHetCovStar
            (stackRegressors X n ω) (stackOutcomes y n ω)))
    (hseθ : 0 < seθ)
    (hjoint :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar
        (fun n ω ωs => (TthetaStar n ω ωs, seThetaStar n ω ωs))
        (gaussianReal 0 1) (fun z : ℝ => (seθ * z, seθ)))
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hTthetaStar : ∀ n ω, Measurable (TthetaStar n ω))
    (hseThetaStar : ∀ n ω, Measurable (seThetaStar n ω))
    (hseStar :
      TendstoInBootstrapProbabilityIndexed μ Pstar seThetaStar (fun _ => seθ))
    (hα_pos : 0 < α) (hα_lt_one : α < 1)
    (hstrict : StrictMono (fun x => cdf (gaussianReal 0 1) x))
    (hlower_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed Pstar
            (fun n ω ωs => TthetaStar n ω ωs / seThetaStar n ω ωs)
            (α / 2) n) μ)
    (hupper_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed Pstar
            (fun n ω ωs => TthetaStar n ω ωs / seThetaStar n ω ωs)
            (1 - α / 2) n) μ)
    (hq_nonneg : 0 ≤ q)
    (hcdfLower : cdf (gaussianReal 0 1) (-q) = α / 2)
    (hcdfUpper : cdf (gaussianReal 0 1) q = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | percentileTCIEvent (linearRestrictionEstimate R β)
          (linearRestrictionEstimate R
            (olsBetaOrZero
              (stackRegressors X n ω) (stackOutcomes y n ω)))
          (if n = 0 then 1
            else linearRestrictionStdError R
              (olsHetCovStar
                (stackRegressors X n ω) (stackOutcomes y n ω)) /
              Real.sqrt (n : ℝ))
          (bootstrapScalarLowerQuantileIndexed Pstar
            (fun n ω ωs => TthetaStar n ω ωs / seThetaStar n ω ωs)
            (α / 2) n ω)
          (bootstrapScalarLowerQuantileIndexed Pstar
            (fun n ω ωs => TthetaStar n ω ωs / seThetaStar n ω ωs)
            (1 - α / 2) n ω)})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) := by
  exact
    chapter10_indexed_ols_percentileTCI_coverage_tendsto_one_sub_alpha_of_bootstrap_regression_tstat
      (μ := μ) (X := X) (e := e) (y := y)
      (Vhat := fun n ω =>
        olsHetCovStar
          (stackRegressors X n ω) (stackOutcomes y n ω))
      (Pstar := Pstar) (TthetaStar := TthetaStar)
      (seThetaStar := seThetaStar) (seθ := seθ) (q := q) (α := α)
      β R hm
      (fun n =>
        olsHetCovStar_stack_aestronglyMeasurable_components
          (μ := μ) (X := X) (e := e) (y := y)
          hm.toSampleMomentAssumption71 β hm.model
          hm.x_aestronglyMeasurable hm.e_aestronglyMeasurable n)
      hsampleSe_pos
      (olsHC0LinTStatOrZero_tendstoInDistribution_standardNormal_of_robustFeasibleHCMomentConditions
        (μ := μ) (X := X) (e := e) (y := y) β R hm hse_pos)
      hseθ hjoint hPstar hTthetaStar hseThetaStar hseStar hα_pos
      hα_lt_one hstrict hlower_meas hupper_meas hq_nonneg
      hcdfLower hcdfUpper

/-- Theorem 10.14 with the actual sample statistic specialized to the ordinary
HC1 OLS scalar restriction. -/
theorem
chapter10_olsHC1_percentileTCI_coverage_tendsto_one_sub_alpha_of_bootstrap_regression_tstat
    [IsProbabilityMeasure μ] [Fintype k] [DecidableEq k]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    {Pstar : ℕ → Ω → Measure Ωs}
    {TthetaStar seThetaStar : ℕ → Ω → Ωs → ℝ}
    {seθ q α : ℝ}
    (β : k → ℝ) (R : Matrix Unit k ℝ)
    (hm : RobustFeasibleHCMomentConditions μ X e y β)
    (hse_pos : 0 <
      linearRestrictionStdError R (heteroAsymCov μ X e))
    (hsampleSe_pos :
      ∀ n ω, n ≠ 0 →
        0 < linearRestrictionStdError R
          (olsHetCovHC1Star
            (stackRegressors X n ω) (stackOutcomes y n ω)))
    (hseθ : 0 < seθ)
    (hjoint :
      TendstoInBootstrapWeakDistribution μ Pstar
        (fun n ω ωs => (TthetaStar n ω ωs, seThetaStar n ω ωs))
        (gaussianReal 0 1) (fun z : ℝ => (seθ * z, seθ)))
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hTthetaStar : ∀ n ω, Measurable (TthetaStar n ω))
    (hseThetaStar : ∀ n ω, Measurable (seThetaStar n ω))
    (hseStar :
      TendstoInBootstrapProbability μ Pstar seThetaStar (fun _ => seθ))
    (hα_pos : 0 < α) (hα_lt_one : α < 1)
    (hstrict : StrictMono (fun x => cdf (gaussianReal 0 1) x))
    (hlower_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantile Pstar
            (fun n ω ωs => TthetaStar n ω ωs / seThetaStar n ω ωs)
            (α / 2) n) μ)
    (hupper_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantile Pstar
            (fun n ω ωs => TthetaStar n ω ωs / seThetaStar n ω ωs)
            (1 - α / 2) n) μ)
    (hq_nonneg : 0 ≤ q)
    (hcdfLower : cdf (gaussianReal 0 1) (-q) = α / 2)
    (hcdfUpper : cdf (gaussianReal 0 1) q = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | percentileTCIEvent (linearRestrictionEstimate R β)
          (linearRestrictionEstimate R
            (olsBetaOrZero
              (stackRegressors X n ω) (stackOutcomes y n ω)))
          (if n = 0 then 1
            else linearRestrictionStdError R
              (olsHetCovHC1Star
                (stackRegressors X n ω) (stackOutcomes y n ω)) /
              Real.sqrt (n : ℝ))
          (bootstrapScalarLowerQuantile Pstar
            (fun n ω ωs => TthetaStar n ω ωs / seThetaStar n ω ωs)
            (α / 2) n ω)
          (bootstrapScalarLowerQuantile Pstar
            (fun n ω ωs => TthetaStar n ω ωs / seThetaStar n ω ωs)
            (1 - α / 2) n ω)})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) := by
  exact
    chapter10_ols_percentileTCI_coverage_tendsto_one_sub_alpha_of_bootstrap_regression_tstat
      (μ := μ) (X := X) (e := e) (y := y)
      (Vhat := fun n ω =>
        olsHetCovHC1Star
          (stackRegressors X n ω) (stackOutcomes y n ω))
      (Pstar := Pstar) (TthetaStar := TthetaStar)
      (seThetaStar := seThetaStar) (seθ := seθ) (q := q) (α := α)
      β R hm
      (fun n =>
        olsHC1CovarianceStar_stack_aestronglyMeasurable_components
          (μ := μ) (X := X) (e := e) (y := y)
          hm.toSampleMomentAssumption71 β hm.model
          hm.x_aestronglyMeasurable hm.e_aestronglyMeasurable n)
      hsampleSe_pos
      (olsHC1LinTStatOrZero_tendstoInDistribution_standardNormal_of_robustFeasibleHCMomentConditions
        (μ := μ) (X := X) (e := e) (y := y) β R hm hse_pos)
      hseθ hjoint hPstar hTthetaStar hseThetaStar hseStar hα_pos
      hα_lt_one hstrict hlower_meas hupper_meas hq_nonneg
      hcdfLower hcdfUpper

/-- Indexed Theorem 10.14 with the actual sample statistic specialized to the
ordinary HC1 OLS scalar restriction. -/
theorem
chapter10_indexed_olsHC1_percentileTCI_coverage_tendsto_one_sub_alpha_of_bootstrap_regression_tstat
    [IsProbabilityMeasure μ] [Fintype k] [DecidableEq k]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {TthetaStar seThetaStar : ∀ n, Ω → Ωboot n → ℝ}
    {seθ q α : ℝ}
    (β : k → ℝ) (R : Matrix Unit k ℝ)
    (hm : RobustFeasibleHCMomentConditions μ X e y β)
    (hse_pos : 0 <
      linearRestrictionStdError R (heteroAsymCov μ X e))
    (hsampleSe_pos :
      ∀ n ω, n ≠ 0 →
        0 < linearRestrictionStdError R
          (olsHetCovHC1Star
            (stackRegressors X n ω) (stackOutcomes y n ω)))
    (hseθ : 0 < seθ)
    (hjoint :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar
        (fun n ω ωs => (TthetaStar n ω ωs, seThetaStar n ω ωs))
        (gaussianReal 0 1) (fun z : ℝ => (seθ * z, seθ)))
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hTthetaStar : ∀ n ω, Measurable (TthetaStar n ω))
    (hseThetaStar : ∀ n ω, Measurable (seThetaStar n ω))
    (hseStar :
      TendstoInBootstrapProbabilityIndexed μ Pstar seThetaStar (fun _ => seθ))
    (hα_pos : 0 < α) (hα_lt_one : α < 1)
    (hstrict : StrictMono (fun x => cdf (gaussianReal 0 1) x))
    (hlower_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed Pstar
            (fun n ω ωs => TthetaStar n ω ωs / seThetaStar n ω ωs)
            (α / 2) n) μ)
    (hupper_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed Pstar
            (fun n ω ωs => TthetaStar n ω ωs / seThetaStar n ω ωs)
            (1 - α / 2) n) μ)
    (hq_nonneg : 0 ≤ q)
    (hcdfLower : cdf (gaussianReal 0 1) (-q) = α / 2)
    (hcdfUpper : cdf (gaussianReal 0 1) q = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | percentileTCIEvent (linearRestrictionEstimate R β)
          (linearRestrictionEstimate R
            (olsBetaOrZero
              (stackRegressors X n ω) (stackOutcomes y n ω)))
          (if n = 0 then 1
            else linearRestrictionStdError R
              (olsHetCovHC1Star
                (stackRegressors X n ω) (stackOutcomes y n ω)) /
              Real.sqrt (n : ℝ))
          (bootstrapScalarLowerQuantileIndexed Pstar
            (fun n ω ωs => TthetaStar n ω ωs / seThetaStar n ω ωs)
            (α / 2) n ω)
          (bootstrapScalarLowerQuantileIndexed Pstar
            (fun n ω ωs => TthetaStar n ω ωs / seThetaStar n ω ωs)
            (1 - α / 2) n ω)})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) := by
  exact
    chapter10_indexed_ols_percentileTCI_coverage_tendsto_one_sub_alpha_of_bootstrap_regression_tstat
      (μ := μ) (X := X) (e := e) (y := y)
      (Vhat := fun n ω =>
        olsHetCovHC1Star
          (stackRegressors X n ω) (stackOutcomes y n ω))
      (Pstar := Pstar) (TthetaStar := TthetaStar)
      (seThetaStar := seThetaStar) (seθ := seθ) (q := q) (α := α)
      β R hm
      (fun n =>
        olsHC1CovarianceStar_stack_aestronglyMeasurable_components
          (μ := μ) (X := X) (e := e) (y := y)
          hm.toSampleMomentAssumption71 β hm.model
          hm.x_aestronglyMeasurable hm.e_aestronglyMeasurable n)
      hsampleSe_pos
      (olsHC1LinTStatOrZero_tendstoInDistribution_standardNormal_of_robustFeasibleHCMomentConditions
        (μ := μ) (X := X) (e := e) (y := y) β R hm hse_pos)
      hseθ hjoint hPstar hTthetaStar hseThetaStar hseStar hα_pos
      hα_lt_one hstrict hlower_meas hupper_meas hq_nonneg
      hcdfLower hcdfUpper

/-- Theorem 10.14 with the actual sample statistic specialized to the ordinary
HC2 OLS scalar restriction. -/
theorem
chapter10_olsHC2_percentileTCI_coverage_tendsto_one_sub_alpha_of_bootstrap_regression_tstat
    [IsProbabilityMeasure μ] [Fintype k] [DecidableEq k]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    {Pstar : ℕ → Ω → Measure Ωs}
    {TthetaStar seThetaStar : ℕ → Ω → Ωs → ℝ}
    {seθ q α : ℝ}
    (β : k → ℝ) (R : Matrix Unit k ℝ)
    (hm : RobustFeasibleHCMomentConditions μ X e y β)
    (hse_pos : 0 <
      linearRestrictionStdError R (heteroAsymCov μ X e))
    (hsampleSe_pos :
      ∀ n ω, n ≠ 0 →
        0 < linearRestrictionStdError R
          (olsHetCovHC2Star
            (stackRegressors X n ω) (stackOutcomes y n ω)))
    (hseθ : 0 < seθ)
    (hjoint :
      TendstoInBootstrapWeakDistribution μ Pstar
        (fun n ω ωs => (TthetaStar n ω ωs, seThetaStar n ω ωs))
        (gaussianReal 0 1) (fun z : ℝ => (seθ * z, seθ)))
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hTthetaStar : ∀ n ω, Measurable (TthetaStar n ω))
    (hseThetaStar : ∀ n ω, Measurable (seThetaStar n ω))
    (hseStar :
      TendstoInBootstrapProbability μ Pstar seThetaStar (fun _ => seθ))
    (hα_pos : 0 < α) (hα_lt_one : α < 1)
    (hstrict : StrictMono (fun x => cdf (gaussianReal 0 1) x))
    (hlower_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantile Pstar
            (fun n ω ωs => TthetaStar n ω ωs / seThetaStar n ω ωs)
            (α / 2) n) μ)
    (hupper_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantile Pstar
            (fun n ω ωs => TthetaStar n ω ωs / seThetaStar n ω ωs)
            (1 - α / 2) n) μ)
    (hq_nonneg : 0 ≤ q)
    (hcdfLower : cdf (gaussianReal 0 1) (-q) = α / 2)
    (hcdfUpper : cdf (gaussianReal 0 1) q = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | percentileTCIEvent (linearRestrictionEstimate R β)
          (linearRestrictionEstimate R
            (olsBetaOrZero
              (stackRegressors X n ω) (stackOutcomes y n ω)))
          (if n = 0 then 1
            else linearRestrictionStdError R
              (olsHetCovHC2Star
                (stackRegressors X n ω) (stackOutcomes y n ω)) /
              Real.sqrt (n : ℝ))
          (bootstrapScalarLowerQuantile Pstar
            (fun n ω ωs => TthetaStar n ω ωs / seThetaStar n ω ωs)
            (α / 2) n ω)
          (bootstrapScalarLowerQuantile Pstar
            (fun n ω ωs => TthetaStar n ω ωs / seThetaStar n ω ωs)
            (1 - α / 2) n ω)})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) := by
  exact
    chapter10_ols_percentileTCI_coverage_tendsto_one_sub_alpha_of_bootstrap_regression_tstat
      (μ := μ) (X := X) (e := e) (y := y)
      (Vhat := fun n ω =>
        olsHetCovHC2Star
          (stackRegressors X n ω) (stackOutcomes y n ω))
      (Pstar := Pstar) (TthetaStar := TthetaStar)
      (seThetaStar := seThetaStar) (seθ := seθ) (q := q) (α := α)
      β R hm
      (fun n =>
        olsHC2CovarianceStar_stack_aestronglyMeasurable_components
          (μ := μ) (X := X) (e := e) (y := y)
          hm.toSampleMomentAssumption71 β hm.model
          hm.x_aestronglyMeasurable hm.e_aestronglyMeasurable n)
      hsampleSe_pos
      (olsHC2LinTStatOrZero_tendstoInDistribution_standardNormal_of_robustFeasibleHCMomentConditions
        (μ := μ) (X := X) (e := e) (y := y) β R hm hse_pos)
      hseθ hjoint hPstar hTthetaStar hseThetaStar hseStar hα_pos
      hα_lt_one hstrict hlower_meas hupper_meas hq_nonneg
      hcdfLower hcdfUpper

/-- Indexed Theorem 10.14 with the actual sample statistic specialized to the
ordinary HC2 OLS scalar restriction. -/
theorem
chapter10_indexed_olsHC2_percentileTCI_coverage_tendsto_one_sub_alpha_of_bootstrap_regression_tstat
    [IsProbabilityMeasure μ] [Fintype k] [DecidableEq k]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {TthetaStar seThetaStar : ∀ n, Ω → Ωboot n → ℝ}
    {seθ q α : ℝ}
    (β : k → ℝ) (R : Matrix Unit k ℝ)
    (hm : RobustFeasibleHCMomentConditions μ X e y β)
    (hse_pos : 0 <
      linearRestrictionStdError R (heteroAsymCov μ X e))
    (hsampleSe_pos :
      ∀ n ω, n ≠ 0 →
        0 < linearRestrictionStdError R
          (olsHetCovHC2Star
            (stackRegressors X n ω) (stackOutcomes y n ω)))
    (hseθ : 0 < seθ)
    (hjoint :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar
        (fun n ω ωs => (TthetaStar n ω ωs, seThetaStar n ω ωs))
        (gaussianReal 0 1) (fun z : ℝ => (seθ * z, seθ)))
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hTthetaStar : ∀ n ω, Measurable (TthetaStar n ω))
    (hseThetaStar : ∀ n ω, Measurable (seThetaStar n ω))
    (hseStar :
      TendstoInBootstrapProbabilityIndexed μ Pstar seThetaStar (fun _ => seθ))
    (hα_pos : 0 < α) (hα_lt_one : α < 1)
    (hstrict : StrictMono (fun x => cdf (gaussianReal 0 1) x))
    (hlower_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed Pstar
            (fun n ω ωs => TthetaStar n ω ωs / seThetaStar n ω ωs)
            (α / 2) n) μ)
    (hupper_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed Pstar
            (fun n ω ωs => TthetaStar n ω ωs / seThetaStar n ω ωs)
            (1 - α / 2) n) μ)
    (hq_nonneg : 0 ≤ q)
    (hcdfLower : cdf (gaussianReal 0 1) (-q) = α / 2)
    (hcdfUpper : cdf (gaussianReal 0 1) q = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | percentileTCIEvent (linearRestrictionEstimate R β)
          (linearRestrictionEstimate R
            (olsBetaOrZero
              (stackRegressors X n ω) (stackOutcomes y n ω)))
          (if n = 0 then 1
            else linearRestrictionStdError R
              (olsHetCovHC2Star
                (stackRegressors X n ω) (stackOutcomes y n ω)) /
              Real.sqrt (n : ℝ))
          (bootstrapScalarLowerQuantileIndexed Pstar
            (fun n ω ωs => TthetaStar n ω ωs / seThetaStar n ω ωs)
            (α / 2) n ω)
          (bootstrapScalarLowerQuantileIndexed Pstar
            (fun n ω ωs => TthetaStar n ω ωs / seThetaStar n ω ωs)
            (1 - α / 2) n ω)})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) := by
  exact
    chapter10_indexed_ols_percentileTCI_coverage_tendsto_one_sub_alpha_of_bootstrap_regression_tstat
      (μ := μ) (X := X) (e := e) (y := y)
      (Vhat := fun n ω =>
        olsHetCovHC2Star
          (stackRegressors X n ω) (stackOutcomes y n ω))
      (Pstar := Pstar) (TthetaStar := TthetaStar)
      (seThetaStar := seThetaStar) (seθ := seθ) (q := q) (α := α)
      β R hm
      (fun n =>
        olsHC2CovarianceStar_stack_aestronglyMeasurable_components
          (μ := μ) (X := X) (e := e) (y := y)
          hm.toSampleMomentAssumption71 β hm.model
          hm.x_aestronglyMeasurable hm.e_aestronglyMeasurable n)
      hsampleSe_pos
      (olsHC2LinTStatOrZero_tendstoInDistribution_standardNormal_of_robustFeasibleHCMomentConditions
        (μ := μ) (X := X) (e := e) (y := y) β R hm hse_pos)
      hseθ hjoint hPstar hTthetaStar hseThetaStar hseStar hα_pos
      hα_lt_one hstrict hlower_meas hupper_meas hq_nonneg
      hcdfLower hcdfUpper

/-- Theorem 10.14 with the actual sample statistic specialized to the ordinary
HC3 OLS scalar restriction. -/
theorem
chapter10_olsHC3_percentileTCI_coverage_tendsto_one_sub_alpha_of_bootstrap_regression_tstat
    [IsProbabilityMeasure μ] [Fintype k] [DecidableEq k]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    {Pstar : ℕ → Ω → Measure Ωs}
    {TthetaStar seThetaStar : ℕ → Ω → Ωs → ℝ}
    {seθ q α : ℝ}
    (β : k → ℝ) (R : Matrix Unit k ℝ)
    (hm : RobustFeasibleHCMomentConditions μ X e y β)
    (hse_pos : 0 <
      linearRestrictionStdError R (heteroAsymCov μ X e))
    (hsampleSe_pos :
      ∀ n ω, n ≠ 0 →
        0 < linearRestrictionStdError R
          (olsHetCovHC3Star
            (stackRegressors X n ω) (stackOutcomes y n ω)))
    (hseθ : 0 < seθ)
    (hjoint :
      TendstoInBootstrapWeakDistribution μ Pstar
        (fun n ω ωs => (TthetaStar n ω ωs, seThetaStar n ω ωs))
        (gaussianReal 0 1) (fun z : ℝ => (seθ * z, seθ)))
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hTthetaStar : ∀ n ω, Measurable (TthetaStar n ω))
    (hseThetaStar : ∀ n ω, Measurable (seThetaStar n ω))
    (hseStar :
      TendstoInBootstrapProbability μ Pstar seThetaStar (fun _ => seθ))
    (hα_pos : 0 < α) (hα_lt_one : α < 1)
    (hstrict : StrictMono (fun x => cdf (gaussianReal 0 1) x))
    (hlower_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantile Pstar
            (fun n ω ωs => TthetaStar n ω ωs / seThetaStar n ω ωs)
            (α / 2) n) μ)
    (hupper_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantile Pstar
            (fun n ω ωs => TthetaStar n ω ωs / seThetaStar n ω ωs)
            (1 - α / 2) n) μ)
    (hq_nonneg : 0 ≤ q)
    (hcdfLower : cdf (gaussianReal 0 1) (-q) = α / 2)
    (hcdfUpper : cdf (gaussianReal 0 1) q = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | percentileTCIEvent (linearRestrictionEstimate R β)
          (linearRestrictionEstimate R
            (olsBetaOrZero
              (stackRegressors X n ω) (stackOutcomes y n ω)))
          (if n = 0 then 1
            else linearRestrictionStdError R
              (olsHetCovHC3Star
                (stackRegressors X n ω) (stackOutcomes y n ω)) /
              Real.sqrt (n : ℝ))
          (bootstrapScalarLowerQuantile Pstar
            (fun n ω ωs => TthetaStar n ω ωs / seThetaStar n ω ωs)
            (α / 2) n ω)
          (bootstrapScalarLowerQuantile Pstar
            (fun n ω ωs => TthetaStar n ω ωs / seThetaStar n ω ωs)
            (1 - α / 2) n ω)})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) := by
  exact
    chapter10_ols_percentileTCI_coverage_tendsto_one_sub_alpha_of_bootstrap_regression_tstat
      (μ := μ) (X := X) (e := e) (y := y)
      (Vhat := fun n ω =>
        olsHetCovHC3Star
          (stackRegressors X n ω) (stackOutcomes y n ω))
      (Pstar := Pstar) (TthetaStar := TthetaStar)
      (seThetaStar := seThetaStar) (seθ := seθ) (q := q) (α := α)
      β R hm
      (fun n =>
        olsHC3CovarianceStar_stack_aestronglyMeasurable_components
          (μ := μ) (X := X) (e := e) (y := y)
          hm.toSampleMomentAssumption71 β hm.model
          hm.x_aestronglyMeasurable hm.e_aestronglyMeasurable n)
      hsampleSe_pos
      (olsHC3LinTStatOrZero_tendstoInDistribution_standardNormal_of_robustFeasibleHCMomentConditions
        (μ := μ) (X := X) (e := e) (y := y) β R hm hse_pos)
      hseθ hjoint hPstar hTthetaStar hseThetaStar hseStar hα_pos
      hα_lt_one hstrict hlower_meas hupper_meas hq_nonneg
      hcdfLower hcdfUpper

/-- Indexed Theorem 10.14 with the actual sample statistic specialized to the
ordinary HC3 OLS scalar restriction. -/
theorem
chapter10_indexed_olsHC3_percentileTCI_coverage_tendsto_one_sub_alpha_of_bootstrap_regression_tstat
    [IsProbabilityMeasure μ] [Fintype k] [DecidableEq k]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {TthetaStar seThetaStar : ∀ n, Ω → Ωboot n → ℝ}
    {seθ q α : ℝ}
    (β : k → ℝ) (R : Matrix Unit k ℝ)
    (hm : RobustFeasibleHCMomentConditions μ X e y β)
    (hse_pos : 0 <
      linearRestrictionStdError R (heteroAsymCov μ X e))
    (hsampleSe_pos :
      ∀ n ω, n ≠ 0 →
        0 < linearRestrictionStdError R
          (olsHetCovHC3Star
            (stackRegressors X n ω) (stackOutcomes y n ω)))
    (hseθ : 0 < seθ)
    (hjoint :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar
        (fun n ω ωs => (TthetaStar n ω ωs, seThetaStar n ω ωs))
        (gaussianReal 0 1) (fun z : ℝ => (seθ * z, seθ)))
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hTthetaStar : ∀ n ω, Measurable (TthetaStar n ω))
    (hseThetaStar : ∀ n ω, Measurable (seThetaStar n ω))
    (hseStar :
      TendstoInBootstrapProbabilityIndexed μ Pstar seThetaStar (fun _ => seθ))
    (hα_pos : 0 < α) (hα_lt_one : α < 1)
    (hstrict : StrictMono (fun x => cdf (gaussianReal 0 1) x))
    (hlower_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed Pstar
            (fun n ω ωs => TthetaStar n ω ωs / seThetaStar n ω ωs)
            (α / 2) n) μ)
    (hupper_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed Pstar
            (fun n ω ωs => TthetaStar n ω ωs / seThetaStar n ω ωs)
            (1 - α / 2) n) μ)
    (hq_nonneg : 0 ≤ q)
    (hcdfLower : cdf (gaussianReal 0 1) (-q) = α / 2)
    (hcdfUpper : cdf (gaussianReal 0 1) q = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | percentileTCIEvent (linearRestrictionEstimate R β)
          (linearRestrictionEstimate R
            (olsBetaOrZero
              (stackRegressors X n ω) (stackOutcomes y n ω)))
          (if n = 0 then 1
            else linearRestrictionStdError R
              (olsHetCovHC3Star
                (stackRegressors X n ω) (stackOutcomes y n ω)) /
              Real.sqrt (n : ℝ))
          (bootstrapScalarLowerQuantileIndexed Pstar
            (fun n ω ωs => TthetaStar n ω ωs / seThetaStar n ω ωs)
            (α / 2) n ω)
          (bootstrapScalarLowerQuantileIndexed Pstar
            (fun n ω ωs => TthetaStar n ω ωs / seThetaStar n ω ωs)
            (1 - α / 2) n ω)})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) := by
  exact
    chapter10_indexed_ols_percentileTCI_coverage_tendsto_one_sub_alpha_of_bootstrap_regression_tstat
      (μ := μ) (X := X) (e := e) (y := y)
      (Vhat := fun n ω =>
        olsHetCovHC3Star
          (stackRegressors X n ω) (stackOutcomes y n ω))
      (Pstar := Pstar) (TthetaStar := TthetaStar)
      (seThetaStar := seThetaStar) (seθ := seθ) (q := q) (α := α)
      β R hm
      (fun n =>
        olsHC3CovarianceStar_stack_aestronglyMeasurable_components
          (μ := μ) (X := X) (e := e) (y := y)
          hm.toSampleMomentAssumption71 β hm.model
          hm.x_aestronglyMeasurable hm.e_aestronglyMeasurable n)
      hsampleSe_pos
      (olsHC3LinTStatOrZero_tendstoInDistribution_standardNormal_of_robustFeasibleHCMomentConditions
        (μ := μ) (X := X) (e := e) (y := y) β R hm hse_pos)
      hseθ hjoint hPstar hTthetaStar hseThetaStar hseStar hα_pos
      hα_lt_one hstrict hlower_meas hupper_meas hq_nonneg
      hcdfLower hcdfUpper

/-- Theorem 10.14 with the actual sample statistic specialized to the ordinary
HC0 OLS scalar restriction, using local standard-normal CDF bracketing. -/
theorem
chapter10_olsHC0_percentileTCI_coverage_tendsto_one_sub_alpha_of_bootstrap_regression_tstat_brackets
    [IsProbabilityMeasure μ] [Fintype k] [DecidableEq k]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    {Pstar : ℕ → Ω → Measure Ωs}
    {TthetaStar seThetaStar : ℕ → Ω → Ωs → ℝ}
    {seθ q α : ℝ}
    (β : k → ℝ) (R : Matrix Unit k ℝ)
    (hm : RobustFeasibleHCMomentConditions μ X e y β)
    (hse_pos : 0 <
      linearRestrictionStdError R (heteroAsymCov μ X e))
    (hsampleSe_pos :
      ∀ n ω, n ≠ 0 →
        0 < linearRestrictionStdError R
          (olsHetCovStar
            (stackRegressors X n ω) (stackOutcomes y n ω)))
    (hseθ : 0 < seθ)
    (hjoint :
      TendstoInBootstrapWeakDistribution μ Pstar
        (fun n ω ωs => (TthetaStar n ω ωs, seThetaStar n ω ωs))
        (gaussianReal 0 1) (fun z : ℝ => (seθ * z, seθ)))
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hTthetaStar : ∀ n ω, Measurable (TthetaStar n ω))
    (hseThetaStar : ∀ n ω, Measurable (seThetaStar n ω))
    (hseStar :
      TendstoInBootstrapProbability μ Pstar seThetaStar (fun _ => seθ))
    (hα_pos : 0 < α) (hα_lt_one : α < 1)
    (hleftLower :
      ∀ ε : ℝ, 0 < ε → cdf (gaussianReal 0 1) (-q - ε) < α / 2)
    (hrightLower :
      ∀ ε : ℝ, 0 < ε → α / 2 < cdf (gaussianReal 0 1) (-q + ε))
    (hleftUpper :
      ∀ ε : ℝ, 0 < ε → cdf (gaussianReal 0 1) (q - ε) < 1 - α / 2)
    (hrightUpper :
      ∀ ε : ℝ, 0 < ε → 1 - α / 2 < cdf (gaussianReal 0 1) (q + ε))
    (hlower_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantile Pstar
            (fun n ω ωs => TthetaStar n ω ωs / seThetaStar n ω ωs)
            (α / 2) n) μ)
    (hupper_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantile Pstar
            (fun n ω ωs => TthetaStar n ω ωs / seThetaStar n ω ωs)
            (1 - α / 2) n) μ)
    (hq_nonneg : 0 ≤ q)
    (hcdfLower : cdf (gaussianReal 0 1) (-q) = α / 2)
    (hcdfUpper : cdf (gaussianReal 0 1) q = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | percentileTCIEvent (linearRestrictionEstimate R β)
          (linearRestrictionEstimate R
            (olsBetaOrZero
              (stackRegressors X n ω) (stackOutcomes y n ω)))
          (if n = 0 then 1
            else linearRestrictionStdError R
              (olsHetCovStar
                (stackRegressors X n ω) (stackOutcomes y n ω)) /
              Real.sqrt (n : ℝ))
          (bootstrapScalarLowerQuantile Pstar
            (fun n ω ωs => TthetaStar n ω ωs / seThetaStar n ω ωs)
            (α / 2) n ω)
          (bootstrapScalarLowerQuantile Pstar
            (fun n ω ωs => TthetaStar n ω ωs / seThetaStar n ω ωs)
            (1 - α / 2) n ω)})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) := by
  exact
    chapter10_ols_percentileTCI_coverage_tendsto_one_sub_alpha_of_bootstrap_regression_tstat_brackets
      (μ := μ) (X := X) (e := e) (y := y)
      (Vhat := fun n ω =>
        olsHetCovStar
          (stackRegressors X n ω) (stackOutcomes y n ω))
      (Pstar := Pstar) (TthetaStar := TthetaStar)
      (seThetaStar := seThetaStar) (seθ := seθ) (q := q) (α := α)
      β R hm
      (fun n =>
        olsHetCovStar_stack_aestronglyMeasurable_components
          (μ := μ) (X := X) (e := e) (y := y)
          hm.toSampleMomentAssumption71 β hm.model
          hm.x_aestronglyMeasurable hm.e_aestronglyMeasurable n)
      hsampleSe_pos
      (olsHC0LinTStatOrZero_tendstoInDistribution_standardNormal_of_robustFeasibleHCMomentConditions
        (μ := μ) (X := X) (e := e) (y := y) β R hm hse_pos)
      hseθ hjoint hPstar hTthetaStar hseThetaStar hseStar hα_pos
      hα_lt_one hleftLower hrightLower hleftUpper hrightUpper
      hlower_meas hupper_meas hq_nonneg hcdfLower hcdfUpper

/-- Indexed Theorem 10.14 with the actual sample statistic specialized to the
ordinary HC0 OLS scalar restriction, using local standard-normal CDF
bracketing. -/
theorem
chapter10_indexed_olsHC0_percentileTCI_coverage_tendsto_one_sub_alpha_of_bootstrap_regression_tstat_brackets
    [IsProbabilityMeasure μ] [Fintype k] [DecidableEq k]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {TthetaStar seThetaStar : ∀ n, Ω → Ωboot n → ℝ}
    {seθ q α : ℝ}
    (β : k → ℝ) (R : Matrix Unit k ℝ)
    (hm : RobustFeasibleHCMomentConditions μ X e y β)
    (hse_pos : 0 <
      linearRestrictionStdError R (heteroAsymCov μ X e))
    (hsampleSe_pos :
      ∀ n ω, n ≠ 0 →
        0 < linearRestrictionStdError R
          (olsHetCovStar
            (stackRegressors X n ω) (stackOutcomes y n ω)))
    (hseθ : 0 < seθ)
    (hjoint :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar
        (fun n ω ωs => (TthetaStar n ω ωs, seThetaStar n ω ωs))
        (gaussianReal 0 1) (fun z : ℝ => (seθ * z, seθ)))
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hTthetaStar : ∀ n ω, Measurable (TthetaStar n ω))
    (hseThetaStar : ∀ n ω, Measurable (seThetaStar n ω))
    (hseStar :
      TendstoInBootstrapProbabilityIndexed μ Pstar seThetaStar (fun _ => seθ))
    (hα_pos : 0 < α) (hα_lt_one : α < 1)
    (hleftLower :
      ∀ ε : ℝ, 0 < ε → cdf (gaussianReal 0 1) (-q - ε) < α / 2)
    (hrightLower :
      ∀ ε : ℝ, 0 < ε → α / 2 < cdf (gaussianReal 0 1) (-q + ε))
    (hleftUpper :
      ∀ ε : ℝ, 0 < ε → cdf (gaussianReal 0 1) (q - ε) < 1 - α / 2)
    (hrightUpper :
      ∀ ε : ℝ, 0 < ε → 1 - α / 2 < cdf (gaussianReal 0 1) (q + ε))
    (hlower_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed Pstar
            (fun n ω ωs => TthetaStar n ω ωs / seThetaStar n ω ωs)
            (α / 2) n) μ)
    (hupper_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed Pstar
            (fun n ω ωs => TthetaStar n ω ωs / seThetaStar n ω ωs)
            (1 - α / 2) n) μ)
    (hq_nonneg : 0 ≤ q)
    (hcdfLower : cdf (gaussianReal 0 1) (-q) = α / 2)
    (hcdfUpper : cdf (gaussianReal 0 1) q = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | percentileTCIEvent (linearRestrictionEstimate R β)
          (linearRestrictionEstimate R
            (olsBetaOrZero
              (stackRegressors X n ω) (stackOutcomes y n ω)))
          (if n = 0 then 1
            else linearRestrictionStdError R
              (olsHetCovStar
                (stackRegressors X n ω) (stackOutcomes y n ω)) /
              Real.sqrt (n : ℝ))
          (bootstrapScalarLowerQuantileIndexed Pstar
            (fun n ω ωs => TthetaStar n ω ωs / seThetaStar n ω ωs)
            (α / 2) n ω)
          (bootstrapScalarLowerQuantileIndexed Pstar
            (fun n ω ωs => TthetaStar n ω ωs / seThetaStar n ω ωs)
            (1 - α / 2) n ω)})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) := by
  exact
    chapter10_indexed_ols_percentileTCI_coverage_tendsto_one_sub_alpha_of_bootstrap_regression_tstat_brackets
      (μ := μ) (X := X) (e := e) (y := y)
      (Vhat := fun n ω =>
        olsHetCovStar
          (stackRegressors X n ω) (stackOutcomes y n ω))
      (Pstar := Pstar) (TthetaStar := TthetaStar)
      (seThetaStar := seThetaStar) (seθ := seθ) (q := q) (α := α)
      β R hm
      (fun n =>
        olsHetCovStar_stack_aestronglyMeasurable_components
          (μ := μ) (X := X) (e := e) (y := y)
          hm.toSampleMomentAssumption71 β hm.model
          hm.x_aestronglyMeasurable hm.e_aestronglyMeasurable n)
      hsampleSe_pos
      (olsHC0LinTStatOrZero_tendstoInDistribution_standardNormal_of_robustFeasibleHCMomentConditions
        (μ := μ) (X := X) (e := e) (y := y) β R hm hse_pos)
      hseθ hjoint hPstar hTthetaStar hseThetaStar hseStar hα_pos
      hα_lt_one hleftLower hrightLower hleftUpper hrightUpper
      hlower_meas hupper_meas hq_nonneg hcdfLower hcdfUpper

/-- Theorem 10.14 with the actual sample statistic specialized to the ordinary
HC1 OLS scalar restriction, using local standard-normal CDF bracketing. -/
theorem
chapter10_olsHC1_percentileTCI_coverage_tendsto_one_sub_alpha_of_bootstrap_regression_tstat_brackets
    [IsProbabilityMeasure μ] [Fintype k] [DecidableEq k]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    {Pstar : ℕ → Ω → Measure Ωs}
    {TthetaStar seThetaStar : ℕ → Ω → Ωs → ℝ}
    {seθ q α : ℝ}
    (β : k → ℝ) (R : Matrix Unit k ℝ)
    (hm : RobustFeasibleHCMomentConditions μ X e y β)
    (hse_pos : 0 <
      linearRestrictionStdError R (heteroAsymCov μ X e))
    (hsampleSe_pos :
      ∀ n ω, n ≠ 0 →
        0 < linearRestrictionStdError R
          (olsHetCovHC1Star
            (stackRegressors X n ω) (stackOutcomes y n ω)))
    (hseθ : 0 < seθ)
    (hjoint :
      TendstoInBootstrapWeakDistribution μ Pstar
        (fun n ω ωs => (TthetaStar n ω ωs, seThetaStar n ω ωs))
        (gaussianReal 0 1) (fun z : ℝ => (seθ * z, seθ)))
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hTthetaStar : ∀ n ω, Measurable (TthetaStar n ω))
    (hseThetaStar : ∀ n ω, Measurable (seThetaStar n ω))
    (hseStar :
      TendstoInBootstrapProbability μ Pstar seThetaStar (fun _ => seθ))
    (hα_pos : 0 < α) (hα_lt_one : α < 1)
    (hleftLower :
      ∀ ε : ℝ, 0 < ε → cdf (gaussianReal 0 1) (-q - ε) < α / 2)
    (hrightLower :
      ∀ ε : ℝ, 0 < ε → α / 2 < cdf (gaussianReal 0 1) (-q + ε))
    (hleftUpper :
      ∀ ε : ℝ, 0 < ε → cdf (gaussianReal 0 1) (q - ε) < 1 - α / 2)
    (hrightUpper :
      ∀ ε : ℝ, 0 < ε → 1 - α / 2 < cdf (gaussianReal 0 1) (q + ε))
    (hlower_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantile Pstar
            (fun n ω ωs => TthetaStar n ω ωs / seThetaStar n ω ωs)
            (α / 2) n) μ)
    (hupper_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantile Pstar
            (fun n ω ωs => TthetaStar n ω ωs / seThetaStar n ω ωs)
            (1 - α / 2) n) μ)
    (hq_nonneg : 0 ≤ q)
    (hcdfLower : cdf (gaussianReal 0 1) (-q) = α / 2)
    (hcdfUpper : cdf (gaussianReal 0 1) q = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | percentileTCIEvent (linearRestrictionEstimate R β)
          (linearRestrictionEstimate R
            (olsBetaOrZero
              (stackRegressors X n ω) (stackOutcomes y n ω)))
          (if n = 0 then 1
            else linearRestrictionStdError R
              (olsHetCovHC1Star
                (stackRegressors X n ω) (stackOutcomes y n ω)) /
              Real.sqrt (n : ℝ))
          (bootstrapScalarLowerQuantile Pstar
            (fun n ω ωs => TthetaStar n ω ωs / seThetaStar n ω ωs)
            (α / 2) n ω)
          (bootstrapScalarLowerQuantile Pstar
            (fun n ω ωs => TthetaStar n ω ωs / seThetaStar n ω ωs)
            (1 - α / 2) n ω)})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) := by
  exact
    chapter10_ols_percentileTCI_coverage_tendsto_one_sub_alpha_of_bootstrap_regression_tstat_brackets
      (μ := μ) (X := X) (e := e) (y := y)
      (Vhat := fun n ω =>
        olsHetCovHC1Star
          (stackRegressors X n ω) (stackOutcomes y n ω))
      (Pstar := Pstar) (TthetaStar := TthetaStar)
      (seThetaStar := seThetaStar) (seθ := seθ) (q := q) (α := α)
      β R hm
      (fun n =>
        olsHC1CovarianceStar_stack_aestronglyMeasurable_components
          (μ := μ) (X := X) (e := e) (y := y)
          hm.toSampleMomentAssumption71 β hm.model
          hm.x_aestronglyMeasurable hm.e_aestronglyMeasurable n)
      hsampleSe_pos
      (olsHC1LinTStatOrZero_tendstoInDistribution_standardNormal_of_robustFeasibleHCMomentConditions
        (μ := μ) (X := X) (e := e) (y := y) β R hm hse_pos)
      hseθ hjoint hPstar hTthetaStar hseThetaStar hseStar hα_pos
      hα_lt_one hleftLower hrightLower hleftUpper hrightUpper
      hlower_meas hupper_meas hq_nonneg hcdfLower hcdfUpper

/-- Indexed Theorem 10.14 with the actual sample statistic specialized to the
ordinary HC1 OLS scalar restriction, using local standard-normal CDF
bracketing. -/
theorem
chapter10_indexed_olsHC1_percentileTCI_coverage_tendsto_one_sub_alpha_of_bootstrap_regression_tstat_brackets
    [IsProbabilityMeasure μ] [Fintype k] [DecidableEq k]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {TthetaStar seThetaStar : ∀ n, Ω → Ωboot n → ℝ}
    {seθ q α : ℝ}
    (β : k → ℝ) (R : Matrix Unit k ℝ)
    (hm : RobustFeasibleHCMomentConditions μ X e y β)
    (hse_pos : 0 <
      linearRestrictionStdError R (heteroAsymCov μ X e))
    (hsampleSe_pos :
      ∀ n ω, n ≠ 0 →
        0 < linearRestrictionStdError R
          (olsHetCovHC1Star
            (stackRegressors X n ω) (stackOutcomes y n ω)))
    (hseθ : 0 < seθ)
    (hjoint :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar
        (fun n ω ωs => (TthetaStar n ω ωs, seThetaStar n ω ωs))
        (gaussianReal 0 1) (fun z : ℝ => (seθ * z, seθ)))
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hTthetaStar : ∀ n ω, Measurable (TthetaStar n ω))
    (hseThetaStar : ∀ n ω, Measurable (seThetaStar n ω))
    (hseStar :
      TendstoInBootstrapProbabilityIndexed μ Pstar seThetaStar (fun _ => seθ))
    (hα_pos : 0 < α) (hα_lt_one : α < 1)
    (hleftLower :
      ∀ ε : ℝ, 0 < ε → cdf (gaussianReal 0 1) (-q - ε) < α / 2)
    (hrightLower :
      ∀ ε : ℝ, 0 < ε → α / 2 < cdf (gaussianReal 0 1) (-q + ε))
    (hleftUpper :
      ∀ ε : ℝ, 0 < ε → cdf (gaussianReal 0 1) (q - ε) < 1 - α / 2)
    (hrightUpper :
      ∀ ε : ℝ, 0 < ε → 1 - α / 2 < cdf (gaussianReal 0 1) (q + ε))
    (hlower_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed Pstar
            (fun n ω ωs => TthetaStar n ω ωs / seThetaStar n ω ωs)
            (α / 2) n) μ)
    (hupper_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed Pstar
            (fun n ω ωs => TthetaStar n ω ωs / seThetaStar n ω ωs)
            (1 - α / 2) n) μ)
    (hq_nonneg : 0 ≤ q)
    (hcdfLower : cdf (gaussianReal 0 1) (-q) = α / 2)
    (hcdfUpper : cdf (gaussianReal 0 1) q = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | percentileTCIEvent (linearRestrictionEstimate R β)
          (linearRestrictionEstimate R
            (olsBetaOrZero
              (stackRegressors X n ω) (stackOutcomes y n ω)))
          (if n = 0 then 1
            else linearRestrictionStdError R
              (olsHetCovHC1Star
                (stackRegressors X n ω) (stackOutcomes y n ω)) /
              Real.sqrt (n : ℝ))
          (bootstrapScalarLowerQuantileIndexed Pstar
            (fun n ω ωs => TthetaStar n ω ωs / seThetaStar n ω ωs)
            (α / 2) n ω)
          (bootstrapScalarLowerQuantileIndexed Pstar
            (fun n ω ωs => TthetaStar n ω ωs / seThetaStar n ω ωs)
            (1 - α / 2) n ω)})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) := by
  exact
    chapter10_indexed_ols_percentileTCI_coverage_tendsto_one_sub_alpha_of_bootstrap_regression_tstat_brackets
      (μ := μ) (X := X) (e := e) (y := y)
      (Vhat := fun n ω =>
        olsHetCovHC1Star
          (stackRegressors X n ω) (stackOutcomes y n ω))
      (Pstar := Pstar) (TthetaStar := TthetaStar)
      (seThetaStar := seThetaStar) (seθ := seθ) (q := q) (α := α)
      β R hm
      (fun n =>
        olsHC1CovarianceStar_stack_aestronglyMeasurable_components
          (μ := μ) (X := X) (e := e) (y := y)
          hm.toSampleMomentAssumption71 β hm.model
          hm.x_aestronglyMeasurable hm.e_aestronglyMeasurable n)
      hsampleSe_pos
      (olsHC1LinTStatOrZero_tendstoInDistribution_standardNormal_of_robustFeasibleHCMomentConditions
        (μ := μ) (X := X) (e := e) (y := y) β R hm hse_pos)
      hseθ hjoint hPstar hTthetaStar hseThetaStar hseStar hα_pos
      hα_lt_one hleftLower hrightLower hleftUpper hrightUpper
      hlower_meas hupper_meas hq_nonneg hcdfLower hcdfUpper

/-- Theorem 10.14 with the actual sample statistic specialized to the ordinary
HC2 OLS scalar restriction, using local standard-normal CDF bracketing. -/
theorem
chapter10_olsHC2_percentileTCI_coverage_tendsto_one_sub_alpha_of_bootstrap_regression_tstat_brackets
    [IsProbabilityMeasure μ] [Fintype k] [DecidableEq k]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    {Pstar : ℕ → Ω → Measure Ωs}
    {TthetaStar seThetaStar : ℕ → Ω → Ωs → ℝ}
    {seθ q α : ℝ}
    (β : k → ℝ) (R : Matrix Unit k ℝ)
    (hm : RobustFeasibleHCMomentConditions μ X e y β)
    (hse_pos : 0 <
      linearRestrictionStdError R (heteroAsymCov μ X e))
    (hsampleSe_pos :
      ∀ n ω, n ≠ 0 →
        0 < linearRestrictionStdError R
          (olsHetCovHC2Star
            (stackRegressors X n ω) (stackOutcomes y n ω)))
    (hseθ : 0 < seθ)
    (hjoint :
      TendstoInBootstrapWeakDistribution μ Pstar
        (fun n ω ωs => (TthetaStar n ω ωs, seThetaStar n ω ωs))
        (gaussianReal 0 1) (fun z : ℝ => (seθ * z, seθ)))
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hTthetaStar : ∀ n ω, Measurable (TthetaStar n ω))
    (hseThetaStar : ∀ n ω, Measurable (seThetaStar n ω))
    (hseStar :
      TendstoInBootstrapProbability μ Pstar seThetaStar (fun _ => seθ))
    (hα_pos : 0 < α) (hα_lt_one : α < 1)
    (hleftLower :
      ∀ ε : ℝ, 0 < ε → cdf (gaussianReal 0 1) (-q - ε) < α / 2)
    (hrightLower :
      ∀ ε : ℝ, 0 < ε → α / 2 < cdf (gaussianReal 0 1) (-q + ε))
    (hleftUpper :
      ∀ ε : ℝ, 0 < ε → cdf (gaussianReal 0 1) (q - ε) < 1 - α / 2)
    (hrightUpper :
      ∀ ε : ℝ, 0 < ε → 1 - α / 2 < cdf (gaussianReal 0 1) (q + ε))
    (hlower_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantile Pstar
            (fun n ω ωs => TthetaStar n ω ωs / seThetaStar n ω ωs)
            (α / 2) n) μ)
    (hupper_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantile Pstar
            (fun n ω ωs => TthetaStar n ω ωs / seThetaStar n ω ωs)
            (1 - α / 2) n) μ)
    (hq_nonneg : 0 ≤ q)
    (hcdfLower : cdf (gaussianReal 0 1) (-q) = α / 2)
    (hcdfUpper : cdf (gaussianReal 0 1) q = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | percentileTCIEvent (linearRestrictionEstimate R β)
          (linearRestrictionEstimate R
            (olsBetaOrZero
              (stackRegressors X n ω) (stackOutcomes y n ω)))
          (if n = 0 then 1
            else linearRestrictionStdError R
              (olsHetCovHC2Star
                (stackRegressors X n ω) (stackOutcomes y n ω)) /
              Real.sqrt (n : ℝ))
          (bootstrapScalarLowerQuantile Pstar
            (fun n ω ωs => TthetaStar n ω ωs / seThetaStar n ω ωs)
            (α / 2) n ω)
          (bootstrapScalarLowerQuantile Pstar
            (fun n ω ωs => TthetaStar n ω ωs / seThetaStar n ω ωs)
            (1 - α / 2) n ω)})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) := by
  exact
    chapter10_ols_percentileTCI_coverage_tendsto_one_sub_alpha_of_bootstrap_regression_tstat_brackets
      (μ := μ) (X := X) (e := e) (y := y)
      (Vhat := fun n ω =>
        olsHetCovHC2Star
          (stackRegressors X n ω) (stackOutcomes y n ω))
      (Pstar := Pstar) (TthetaStar := TthetaStar)
      (seThetaStar := seThetaStar) (seθ := seθ) (q := q) (α := α)
      β R hm
      (fun n =>
        olsHC2CovarianceStar_stack_aestronglyMeasurable_components
          (μ := μ) (X := X) (e := e) (y := y)
          hm.toSampleMomentAssumption71 β hm.model
          hm.x_aestronglyMeasurable hm.e_aestronglyMeasurable n)
      hsampleSe_pos
      (olsHC2LinTStatOrZero_tendstoInDistribution_standardNormal_of_robustFeasibleHCMomentConditions
        (μ := μ) (X := X) (e := e) (y := y) β R hm hse_pos)
      hseθ hjoint hPstar hTthetaStar hseThetaStar hseStar hα_pos
      hα_lt_one hleftLower hrightLower hleftUpper hrightUpper
      hlower_meas hupper_meas hq_nonneg hcdfLower hcdfUpper

/-- Indexed Theorem 10.14 with the actual sample statistic specialized to the
ordinary HC2 OLS scalar restriction, using local standard-normal CDF
bracketing. -/
theorem
chapter10_indexed_olsHC2_percentileTCI_coverage_tendsto_one_sub_alpha_of_bootstrap_regression_tstat_brackets
    [IsProbabilityMeasure μ] [Fintype k] [DecidableEq k]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {TthetaStar seThetaStar : ∀ n, Ω → Ωboot n → ℝ}
    {seθ q α : ℝ}
    (β : k → ℝ) (R : Matrix Unit k ℝ)
    (hm : RobustFeasibleHCMomentConditions μ X e y β)
    (hse_pos : 0 <
      linearRestrictionStdError R (heteroAsymCov μ X e))
    (hsampleSe_pos :
      ∀ n ω, n ≠ 0 →
        0 < linearRestrictionStdError R
          (olsHetCovHC2Star
            (stackRegressors X n ω) (stackOutcomes y n ω)))
    (hseθ : 0 < seθ)
    (hjoint :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar
        (fun n ω ωs => (TthetaStar n ω ωs, seThetaStar n ω ωs))
        (gaussianReal 0 1) (fun z : ℝ => (seθ * z, seθ)))
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hTthetaStar : ∀ n ω, Measurable (TthetaStar n ω))
    (hseThetaStar : ∀ n ω, Measurable (seThetaStar n ω))
    (hseStar :
      TendstoInBootstrapProbabilityIndexed μ Pstar seThetaStar (fun _ => seθ))
    (hα_pos : 0 < α) (hα_lt_one : α < 1)
    (hleftLower :
      ∀ ε : ℝ, 0 < ε → cdf (gaussianReal 0 1) (-q - ε) < α / 2)
    (hrightLower :
      ∀ ε : ℝ, 0 < ε → α / 2 < cdf (gaussianReal 0 1) (-q + ε))
    (hleftUpper :
      ∀ ε : ℝ, 0 < ε → cdf (gaussianReal 0 1) (q - ε) < 1 - α / 2)
    (hrightUpper :
      ∀ ε : ℝ, 0 < ε → 1 - α / 2 < cdf (gaussianReal 0 1) (q + ε))
    (hlower_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed Pstar
            (fun n ω ωs => TthetaStar n ω ωs / seThetaStar n ω ωs)
            (α / 2) n) μ)
    (hupper_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed Pstar
            (fun n ω ωs => TthetaStar n ω ωs / seThetaStar n ω ωs)
            (1 - α / 2) n) μ)
    (hq_nonneg : 0 ≤ q)
    (hcdfLower : cdf (gaussianReal 0 1) (-q) = α / 2)
    (hcdfUpper : cdf (gaussianReal 0 1) q = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | percentileTCIEvent (linearRestrictionEstimate R β)
          (linearRestrictionEstimate R
            (olsBetaOrZero
              (stackRegressors X n ω) (stackOutcomes y n ω)))
          (if n = 0 then 1
            else linearRestrictionStdError R
              (olsHetCovHC2Star
                (stackRegressors X n ω) (stackOutcomes y n ω)) /
              Real.sqrt (n : ℝ))
          (bootstrapScalarLowerQuantileIndexed Pstar
            (fun n ω ωs => TthetaStar n ω ωs / seThetaStar n ω ωs)
            (α / 2) n ω)
          (bootstrapScalarLowerQuantileIndexed Pstar
            (fun n ω ωs => TthetaStar n ω ωs / seThetaStar n ω ωs)
            (1 - α / 2) n ω)})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) := by
  exact
    chapter10_indexed_ols_percentileTCI_coverage_tendsto_one_sub_alpha_of_bootstrap_regression_tstat_brackets
      (μ := μ) (X := X) (e := e) (y := y)
      (Vhat := fun n ω =>
        olsHetCovHC2Star
          (stackRegressors X n ω) (stackOutcomes y n ω))
      (Pstar := Pstar) (TthetaStar := TthetaStar)
      (seThetaStar := seThetaStar) (seθ := seθ) (q := q) (α := α)
      β R hm
      (fun n =>
        olsHC2CovarianceStar_stack_aestronglyMeasurable_components
          (μ := μ) (X := X) (e := e) (y := y)
          hm.toSampleMomentAssumption71 β hm.model
          hm.x_aestronglyMeasurable hm.e_aestronglyMeasurable n)
      hsampleSe_pos
      (olsHC2LinTStatOrZero_tendstoInDistribution_standardNormal_of_robustFeasibleHCMomentConditions
        (μ := μ) (X := X) (e := e) (y := y) β R hm hse_pos)
      hseθ hjoint hPstar hTthetaStar hseThetaStar hseStar hα_pos
      hα_lt_one hleftLower hrightLower hleftUpper hrightUpper
      hlower_meas hupper_meas hq_nonneg hcdfLower hcdfUpper

/-- Theorem 10.14 with the actual sample statistic specialized to the ordinary
HC3 OLS scalar restriction, using local standard-normal CDF bracketing. -/
theorem
chapter10_olsHC3_percentileTCI_coverage_tendsto_one_sub_alpha_of_bootstrap_regression_tstat_brackets
    [IsProbabilityMeasure μ] [Fintype k] [DecidableEq k]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    {Pstar : ℕ → Ω → Measure Ωs}
    {TthetaStar seThetaStar : ℕ → Ω → Ωs → ℝ}
    {seθ q α : ℝ}
    (β : k → ℝ) (R : Matrix Unit k ℝ)
    (hm : RobustFeasibleHCMomentConditions μ X e y β)
    (hse_pos : 0 <
      linearRestrictionStdError R (heteroAsymCov μ X e))
    (hsampleSe_pos :
      ∀ n ω, n ≠ 0 →
        0 < linearRestrictionStdError R
          (olsHetCovHC3Star
            (stackRegressors X n ω) (stackOutcomes y n ω)))
    (hseθ : 0 < seθ)
    (hjoint :
      TendstoInBootstrapWeakDistribution μ Pstar
        (fun n ω ωs => (TthetaStar n ω ωs, seThetaStar n ω ωs))
        (gaussianReal 0 1) (fun z : ℝ => (seθ * z, seθ)))
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hTthetaStar : ∀ n ω, Measurable (TthetaStar n ω))
    (hseThetaStar : ∀ n ω, Measurable (seThetaStar n ω))
    (hseStar :
      TendstoInBootstrapProbability μ Pstar seThetaStar (fun _ => seθ))
    (hα_pos : 0 < α) (hα_lt_one : α < 1)
    (hleftLower :
      ∀ ε : ℝ, 0 < ε → cdf (gaussianReal 0 1) (-q - ε) < α / 2)
    (hrightLower :
      ∀ ε : ℝ, 0 < ε → α / 2 < cdf (gaussianReal 0 1) (-q + ε))
    (hleftUpper :
      ∀ ε : ℝ, 0 < ε → cdf (gaussianReal 0 1) (q - ε) < 1 - α / 2)
    (hrightUpper :
      ∀ ε : ℝ, 0 < ε → 1 - α / 2 < cdf (gaussianReal 0 1) (q + ε))
    (hlower_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantile Pstar
            (fun n ω ωs => TthetaStar n ω ωs / seThetaStar n ω ωs)
            (α / 2) n) μ)
    (hupper_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantile Pstar
            (fun n ω ωs => TthetaStar n ω ωs / seThetaStar n ω ωs)
            (1 - α / 2) n) μ)
    (hq_nonneg : 0 ≤ q)
    (hcdfLower : cdf (gaussianReal 0 1) (-q) = α / 2)
    (hcdfUpper : cdf (gaussianReal 0 1) q = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | percentileTCIEvent (linearRestrictionEstimate R β)
          (linearRestrictionEstimate R
            (olsBetaOrZero
              (stackRegressors X n ω) (stackOutcomes y n ω)))
          (if n = 0 then 1
            else linearRestrictionStdError R
              (olsHetCovHC3Star
                (stackRegressors X n ω) (stackOutcomes y n ω)) /
              Real.sqrt (n : ℝ))
          (bootstrapScalarLowerQuantile Pstar
            (fun n ω ωs => TthetaStar n ω ωs / seThetaStar n ω ωs)
            (α / 2) n ω)
          (bootstrapScalarLowerQuantile Pstar
            (fun n ω ωs => TthetaStar n ω ωs / seThetaStar n ω ωs)
            (1 - α / 2) n ω)})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) := by
  exact
    chapter10_ols_percentileTCI_coverage_tendsto_one_sub_alpha_of_bootstrap_regression_tstat_brackets
      (μ := μ) (X := X) (e := e) (y := y)
      (Vhat := fun n ω =>
        olsHetCovHC3Star
          (stackRegressors X n ω) (stackOutcomes y n ω))
      (Pstar := Pstar) (TthetaStar := TthetaStar)
      (seThetaStar := seThetaStar) (seθ := seθ) (q := q) (α := α)
      β R hm
      (fun n =>
        olsHC3CovarianceStar_stack_aestronglyMeasurable_components
          (μ := μ) (X := X) (e := e) (y := y)
          hm.toSampleMomentAssumption71 β hm.model
          hm.x_aestronglyMeasurable hm.e_aestronglyMeasurable n)
      hsampleSe_pos
      (olsHC3LinTStatOrZero_tendstoInDistribution_standardNormal_of_robustFeasibleHCMomentConditions
        (μ := μ) (X := X) (e := e) (y := y) β R hm hse_pos)
      hseθ hjoint hPstar hTthetaStar hseThetaStar hseStar hα_pos
      hα_lt_one hleftLower hrightLower hleftUpper hrightUpper
      hlower_meas hupper_meas hq_nonneg hcdfLower hcdfUpper

/-- Indexed Theorem 10.14 with the actual sample statistic specialized to the
ordinary HC3 OLS scalar restriction, using local standard-normal CDF
bracketing. -/
theorem
chapter10_indexed_olsHC3_percentileTCI_coverage_tendsto_one_sub_alpha_of_bootstrap_regression_tstat_brackets
    [IsProbabilityMeasure μ] [Fintype k] [DecidableEq k]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {TthetaStar seThetaStar : ∀ n, Ω → Ωboot n → ℝ}
    {seθ q α : ℝ}
    (β : k → ℝ) (R : Matrix Unit k ℝ)
    (hm : RobustFeasibleHCMomentConditions μ X e y β)
    (hse_pos : 0 <
      linearRestrictionStdError R (heteroAsymCov μ X e))
    (hsampleSe_pos :
      ∀ n ω, n ≠ 0 →
        0 < linearRestrictionStdError R
          (olsHetCovHC3Star
            (stackRegressors X n ω) (stackOutcomes y n ω)))
    (hseθ : 0 < seθ)
    (hjoint :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar
        (fun n ω ωs => (TthetaStar n ω ωs, seThetaStar n ω ωs))
        (gaussianReal 0 1) (fun z : ℝ => (seθ * z, seθ)))
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hTthetaStar : ∀ n ω, Measurable (TthetaStar n ω))
    (hseThetaStar : ∀ n ω, Measurable (seThetaStar n ω))
    (hseStar :
      TendstoInBootstrapProbabilityIndexed μ Pstar seThetaStar (fun _ => seθ))
    (hα_pos : 0 < α) (hα_lt_one : α < 1)
    (hleftLower :
      ∀ ε : ℝ, 0 < ε → cdf (gaussianReal 0 1) (-q - ε) < α / 2)
    (hrightLower :
      ∀ ε : ℝ, 0 < ε → α / 2 < cdf (gaussianReal 0 1) (-q + ε))
    (hleftUpper :
      ∀ ε : ℝ, 0 < ε → cdf (gaussianReal 0 1) (q - ε) < 1 - α / 2)
    (hrightUpper :
      ∀ ε : ℝ, 0 < ε → 1 - α / 2 < cdf (gaussianReal 0 1) (q + ε))
    (hlower_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed Pstar
            (fun n ω ωs => TthetaStar n ω ωs / seThetaStar n ω ωs)
            (α / 2) n) μ)
    (hupper_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed Pstar
            (fun n ω ωs => TthetaStar n ω ωs / seThetaStar n ω ωs)
            (1 - α / 2) n) μ)
    (hq_nonneg : 0 ≤ q)
    (hcdfLower : cdf (gaussianReal 0 1) (-q) = α / 2)
    (hcdfUpper : cdf (gaussianReal 0 1) q = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | percentileTCIEvent (linearRestrictionEstimate R β)
          (linearRestrictionEstimate R
            (olsBetaOrZero
              (stackRegressors X n ω) (stackOutcomes y n ω)))
          (if n = 0 then 1
            else linearRestrictionStdError R
              (olsHetCovHC3Star
                (stackRegressors X n ω) (stackOutcomes y n ω)) /
              Real.sqrt (n : ℝ))
          (bootstrapScalarLowerQuantileIndexed Pstar
            (fun n ω ωs => TthetaStar n ω ωs / seThetaStar n ω ωs)
            (α / 2) n ω)
          (bootstrapScalarLowerQuantileIndexed Pstar
            (fun n ω ωs => TthetaStar n ω ωs / seThetaStar n ω ωs)
            (1 - α / 2) n ω)})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) := by
  exact
    chapter10_indexed_ols_percentileTCI_coverage_tendsto_one_sub_alpha_of_bootstrap_regression_tstat_brackets
      (μ := μ) (X := X) (e := e) (y := y)
      (Vhat := fun n ω =>
        olsHetCovHC3Star
          (stackRegressors X n ω) (stackOutcomes y n ω))
      (Pstar := Pstar) (TthetaStar := TthetaStar)
      (seThetaStar := seThetaStar) (seθ := seθ) (q := q) (α := α)
      β R hm
      (fun n =>
        olsHC3CovarianceStar_stack_aestronglyMeasurable_components
          (μ := μ) (X := X) (e := e) (y := y)
          hm.toSampleMomentAssumption71 β hm.model
          hm.x_aestronglyMeasurable hm.e_aestronglyMeasurable n)
      hsampleSe_pos
      (olsHC3LinTStatOrZero_tendstoInDistribution_standardNormal_of_robustFeasibleHCMomentConditions
        (μ := μ) (X := X) (e := e) (y := y) β R hm hse_pos)
      hseθ hjoint hPstar hTthetaStar hseThetaStar hseStar hα_pos
      hα_lt_one hleftLower hrightLower hleftUpper hrightUpper
      hlower_meas hupper_meas hq_nonneg hcdfLower hcdfUpper

set_option linter.style.longLine false in
private theorem
    chapter10_indexed_ols_percentileTCI_coverage_tendsto_one_sub_alpha_finSucc_olsBetaOrZero_gapEnvelope_beta_bound
    [IsProbabilityMeasure μ] [Fintype k] [DecidableEq k]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    {Vhat : ℕ → Ω → Matrix k k ℝ}
    {seThetaStar : ∀ n, Ω → (Fin (n + 1) → Fin (n + 1)) → ℝ}
    {Clin Cbeta q α : ℝ}
    (β : k → ℝ) (R : Matrix Unit k ℝ)
    (hm : RobustFeasibleHCMomentConditions μ X e y β)
    (hVhat : ∀ n, AEStronglyMeasurable (Vhat n) μ)
    (hsampleSe_pos :
      ∀ n ω, n ≠ 0 → 0 < linearRestrictionStdError R (Vhat n ω))
    (htstat :
      TendstoInDistribution
        (fun n ω =>
          olsLinearTStatOrZero R (Vhat n ω)
            (stackRegressors X n ω) (stackOutcomes y n ω) β
            (Real.sqrt (n : ℝ)))
        atTop (fun x : ℝ => x) (fun _ => μ) (gaussianReal 0 1))
    (hseθ : 0 < linearRestrictionStdError R (heteroAsymCov μ X e))
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
    (hseStar :
      TendstoInBootstrapProbabilityIndexed μ
        (fun n _ =>
          (ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
              Measure (Fin (n + 1) → Fin (n + 1))))
        seThetaStar
        (fun _ => linearRestrictionStdError R (heteroAsymCov μ X e)))
    (hα_pos : 0 < α) (hα_lt_one : α < 1)
    (hstrict : StrictMono (fun x => cdf (gaussianReal 0 1) x))
    (hlower_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed
            (fun n _ =>
              (ProbabilityTheory.uniformOn
                (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                  Measure (Fin (n + 1) → Fin (n + 1))))
            (fun n ω ωs =>
              regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs /
                seThetaStar n ω ωs)
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
              regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs /
                seThetaStar n ω ωs)
            (1 - α / 2) n) μ)
    (hq_nonneg : 0 ≤ q)
    (hcdfLower : cdf (gaussianReal 0 1) (-q) = α / 2)
    (hcdfUpper : cdf (gaussianReal 0 1) q = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | percentileTCIEvent (linearRestrictionEstimate R β)
          (linearRestrictionEstimate R
            (olsBetaOrZero
              (stackRegressors X n ω) (stackOutcomes y n ω)))
          (if n = 0 then 1
            else linearRestrictionStdError R (Vhat n ω) / Real.sqrt (n : ℝ))
          (bootstrapScalarLowerQuantileIndexed
            (fun n _ =>
              (ProbabilityTheory.uniformOn
                (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                  Measure (Fin (n + 1) → Fin (n + 1))))
            (fun n ω ωs =>
              regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs /
                seThetaStar n ω ωs)
            (α / 2) n ω)
          (bootstrapScalarLowerQuantileIndexed
            (fun n _ =>
              (ProbabilityTheory.uniformOn
                (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                  Measure (Fin (n + 1) → Fin (n + 1))))
            (fun n ω ωs =>
              regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs /
                seThetaStar n ω ωs)
            (1 - α / 2) n ω)})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) :=
  chapter10_percentileTCI_coverage_tendsto_one_sub_alpha_indexed_of_bootstrap_regression_tstat_finSucc_olsBetaOrZero_gapEnvelope_beta_bound_of_robustFeasibleHCMomentConditions
    (μ := μ) (X := X) (e := e) (y := y)
    (θ := linearRestrictionEstimate R β)
    (θhat := fun n ω =>
      linearRestrictionEstimate R
        (olsBetaOrZero
          (stackRegressors X n ω) (stackOutcomes y n ω)))
    (se := fun n ω =>
      if n = 0 then 1
      else linearRestrictionStdError R (Vhat n ω) / Real.sqrt (n : ℝ))
    β R
    (olsPercentileTStdError_pos R hsampleSe_pos)
    (olsPercentileTStatistic_tendstoInDistribution_standardNormal
      β R hm hVhat htstat)
    hseθ hm hΩ hLinBound hBetaBound hGapTail hseThetaStar hseStar
      hα_pos hα_lt_one hstrict hlower_meas hupper_meas hq_nonneg
    hcdfLower hcdfUpper

set_option linter.style.longLine false in
private theorem
    chapter10_indexed_ols_percentileTCI_coverage_tendsto_one_sub_alpha_finSucc_olsBetaOrZero_gapEnvelope_beta_bound_brackets
    [IsProbabilityMeasure μ] [Fintype k] [DecidableEq k]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    {Vhat : ℕ → Ω → Matrix k k ℝ}
    {seThetaStar : ∀ n, Ω → (Fin (n + 1) → Fin (n + 1)) → ℝ}
    {Clin Cbeta q α : ℝ}
    (β : k → ℝ) (R : Matrix Unit k ℝ)
    (hm : RobustFeasibleHCMomentConditions μ X e y β)
    (hVhat : ∀ n, AEStronglyMeasurable (Vhat n) μ)
    (hsampleSe_pos :
      ∀ n ω, n ≠ 0 → 0 < linearRestrictionStdError R (Vhat n ω))
    (htstat :
      TendstoInDistribution
        (fun n ω =>
          olsLinearTStatOrZero R (Vhat n ω)
            (stackRegressors X n ω) (stackOutcomes y n ω) β
            (Real.sqrt (n : ℝ)))
        atTop (fun x : ℝ => x) (fun _ => μ) (gaussianReal 0 1))
    (hseθ : 0 < linearRestrictionStdError R (heteroAsymCov μ X e))
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
    (hseStar :
      TendstoInBootstrapProbabilityIndexed μ
        (fun n _ =>
          (ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
              Measure (Fin (n + 1) → Fin (n + 1))))
        seThetaStar
        (fun _ => linearRestrictionStdError R (heteroAsymCov μ X e)))
    (hα_pos : 0 < α) (hα_lt_one : α < 1)
    (hleftLower :
      ∀ ε : ℝ, 0 < ε → cdf (gaussianReal 0 1) (-q - ε) < α / 2)
    (hrightLower :
      ∀ ε : ℝ, 0 < ε → α / 2 < cdf (gaussianReal 0 1) (-q + ε))
    (hleftUpper :
      ∀ ε : ℝ, 0 < ε → cdf (gaussianReal 0 1) (q - ε) < 1 - α / 2)
    (hrightUpper :
      ∀ ε : ℝ, 0 < ε → 1 - α / 2 < cdf (gaussianReal 0 1) (q + ε))
    (hlower_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed
            (fun n _ =>
              (ProbabilityTheory.uniformOn
                (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                  Measure (Fin (n + 1) → Fin (n + 1))))
            (fun n ω ωs =>
              regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs /
                seThetaStar n ω ωs)
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
              regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs /
                seThetaStar n ω ωs)
            (1 - α / 2) n) μ)
    (hq_nonneg : 0 ≤ q)
    (hcdfLower : cdf (gaussianReal 0 1) (-q) = α / 2)
    (hcdfUpper : cdf (gaussianReal 0 1) q = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | percentileTCIEvent (linearRestrictionEstimate R β)
          (linearRestrictionEstimate R
            (olsBetaOrZero
              (stackRegressors X n ω) (stackOutcomes y n ω)))
          (if n = 0 then 1
            else linearRestrictionStdError R (Vhat n ω) / Real.sqrt (n : ℝ))
          (bootstrapScalarLowerQuantileIndexed
            (fun n _ =>
              (ProbabilityTheory.uniformOn
                (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                  Measure (Fin (n + 1) → Fin (n + 1))))
            (fun n ω ωs =>
              regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs /
                seThetaStar n ω ωs)
            (α / 2) n ω)
          (bootstrapScalarLowerQuantileIndexed
            (fun n _ =>
              (ProbabilityTheory.uniformOn
                (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                  Measure (Fin (n + 1) → Fin (n + 1))))
            (fun n ω ωs =>
              regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs /
                seThetaStar n ω ωs)
            (1 - α / 2) n ω)})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) :=
  chapter10_percentileTCI_coverage_tendsto_one_sub_alpha_indexed_of_bootstrap_regression_tstat_finSucc_olsBetaOrZero_gapEnvelope_beta_bound_brackets_of_robustFeasibleHCMomentConditions
    (μ := μ) (X := X) (e := e) (y := y)
    (θ := linearRestrictionEstimate R β)
    (θhat := fun n ω =>
      linearRestrictionEstimate R
        (olsBetaOrZero
          (stackRegressors X n ω) (stackOutcomes y n ω)))
    (se := fun n ω =>
      if n = 0 then 1
      else linearRestrictionStdError R (Vhat n ω) / Real.sqrt (n : ℝ))
    β R
    (olsPercentileTStdError_pos R hsampleSe_pos)
    (olsPercentileTStatistic_tendstoInDistribution_standardNormal
      β R hm hVhat htstat)
    hseθ hm hΩ hLinBound hBetaBound hGapTail hseThetaStar hseStar
    hα_pos hα_lt_one hleftLower hrightLower hleftUpper hrightUpper
    hlower_meas hupper_meas hq_nonneg hcdfLower hcdfUpper

set_option linter.style.longLine false in
/-- Indexed percentile-`t` coverage with the actual sample statistic
specialized to ordinary HC0 OLS and the bootstrap quantiles specialized to
the concrete finite ordinary-bootstrap OLS t-statistic. -/
theorem
    chapter10_indexed_olsHC0_percentileTCI_coverage_tendsto_one_sub_alpha_finSucc_olsBetaOrZero_gapEnvelope_beta_bound
    [IsProbabilityMeasure μ] [Fintype k] [DecidableEq k]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    {seThetaStar : ∀ n, Ω → (Fin (n + 1) → Fin (n + 1)) → ℝ}
    {Clin Cbeta q α : ℝ}
    (β : k → ℝ) (R : Matrix Unit k ℝ)
    (hm : RobustFeasibleHCMomentConditions μ X e y β)
    (hse_pos : 0 <
      linearRestrictionStdError R (heteroAsymCov μ X e))
    (hsampleSe_pos :
      ∀ n ω, n ≠ 0 →
        0 < linearRestrictionStdError R
          (olsHetCovStar
            (stackRegressors X n ω) (stackOutcomes y n ω)))
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
    (hseStar :
      TendstoInBootstrapProbabilityIndexed μ
        (fun n _ =>
          (ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
              Measure (Fin (n + 1) → Fin (n + 1))))
        seThetaStar
        (fun _ => linearRestrictionStdError R (heteroAsymCov μ X e)))
    (hα_pos : 0 < α) (hα_lt_one : α < 1)
    (hstrict : StrictMono (fun x => cdf (gaussianReal 0 1) x))
    (hlower_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed
            (fun n _ =>
              (ProbabilityTheory.uniformOn
                (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                  Measure (Fin (n + 1) → Fin (n + 1))))
            (fun n ω ωs =>
              regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs /
                seThetaStar n ω ωs)
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
              regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs /
                seThetaStar n ω ωs)
            (1 - α / 2) n) μ)
    (hq_nonneg : 0 ≤ q)
    (hcdfLower : cdf (gaussianReal 0 1) (-q) = α / 2)
    (hcdfUpper : cdf (gaussianReal 0 1) q = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | percentileTCIEvent (linearRestrictionEstimate R β)
          (linearRestrictionEstimate R
            (olsBetaOrZero
              (stackRegressors X n ω) (stackOutcomes y n ω)))
          (if n = 0 then 1
            else linearRestrictionStdError R
              (olsHetCovStar
                (stackRegressors X n ω) (stackOutcomes y n ω)) /
              Real.sqrt (n : ℝ))
          (bootstrapScalarLowerQuantileIndexed
            (fun n _ =>
              (ProbabilityTheory.uniformOn
                (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                  Measure (Fin (n + 1) → Fin (n + 1))))
            (fun n ω ωs =>
              regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs /
                seThetaStar n ω ωs)
            (α / 2) n ω)
          (bootstrapScalarLowerQuantileIndexed
            (fun n _ =>
              (ProbabilityTheory.uniformOn
                (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                  Measure (Fin (n + 1) → Fin (n + 1))))
            (fun n ω ωs =>
              regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs /
                seThetaStar n ω ωs)
            (1 - α / 2) n ω)})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) :=
  chapter10_indexed_ols_percentileTCI_coverage_tendsto_one_sub_alpha_finSucc_olsBetaOrZero_gapEnvelope_beta_bound
    (μ := μ) (X := X) (e := e) (y := y)
    (Vhat := fun n ω =>
      olsHetCovStar
        (stackRegressors X n ω) (stackOutcomes y n ω))
    β R hm
    (fun n =>
      olsHetCovStar_stack_aestronglyMeasurable_components
        (μ := μ) (X := X) (e := e) (y := y)
        hm.toSampleMomentAssumption71 β hm.model
        hm.x_aestronglyMeasurable hm.e_aestronglyMeasurable n)
    hsampleSe_pos
    (olsHC0LinTStatOrZero_tendstoInDistribution_standardNormal_of_robustFeasibleHCMomentConditions
      (μ := μ) (X := X) (e := e) (y := y) β R hm hse_pos)
    hse_pos hΩ hLinBound hBetaBound hGapTail hseThetaStar hseStar
      hα_pos hα_lt_one hstrict hlower_meas hupper_meas hq_nonneg
    hcdfLower hcdfUpper

set_option linter.style.longLine false in
/-- Local-CDF bracketing counterpart of
`chapter10_indexed_olsHC0_percentileTCI_coverage_tendsto_one_sub_alpha_finSucc_olsBetaOrZero_gapEnvelope_beta_bound`. -/
theorem
    chapter10_indexed_olsHC0_percentileTCI_coverage_tendsto_one_sub_alpha_finSucc_olsBetaOrZero_gapEnvelope_beta_bound_brackets
    [IsProbabilityMeasure μ] [Fintype k] [DecidableEq k]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    {seThetaStar : ∀ n, Ω → (Fin (n + 1) → Fin (n + 1)) → ℝ}
    {Clin Cbeta q α : ℝ}
    (β : k → ℝ) (R : Matrix Unit k ℝ)
    (hm : RobustFeasibleHCMomentConditions μ X e y β)
    (hse_pos : 0 <
      linearRestrictionStdError R (heteroAsymCov μ X e))
    (hsampleSe_pos :
      ∀ n ω, n ≠ 0 →
        0 < linearRestrictionStdError R
          (olsHetCovStar
            (stackRegressors X n ω) (stackOutcomes y n ω)))
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
    (hseStar :
      TendstoInBootstrapProbabilityIndexed μ
        (fun n _ =>
          (ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
              Measure (Fin (n + 1) → Fin (n + 1))))
        seThetaStar
        (fun _ => linearRestrictionStdError R (heteroAsymCov μ X e)))
    (hα_pos : 0 < α) (hα_lt_one : α < 1)
    (hleftLower :
      ∀ ε : ℝ, 0 < ε → cdf (gaussianReal 0 1) (-q - ε) < α / 2)
    (hrightLower :
      ∀ ε : ℝ, 0 < ε → α / 2 < cdf (gaussianReal 0 1) (-q + ε))
    (hleftUpper :
      ∀ ε : ℝ, 0 < ε → cdf (gaussianReal 0 1) (q - ε) < 1 - α / 2)
    (hrightUpper :
      ∀ ε : ℝ, 0 < ε → 1 - α / 2 < cdf (gaussianReal 0 1) (q + ε))
    (hlower_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed
            (fun n _ =>
              (ProbabilityTheory.uniformOn
                (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                  Measure (Fin (n + 1) → Fin (n + 1))))
            (fun n ω ωs =>
              regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs /
                seThetaStar n ω ωs)
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
              regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs /
                seThetaStar n ω ωs)
            (1 - α / 2) n) μ)
    (hq_nonneg : 0 ≤ q)
    (hcdfLower : cdf (gaussianReal 0 1) (-q) = α / 2)
    (hcdfUpper : cdf (gaussianReal 0 1) q = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | percentileTCIEvent (linearRestrictionEstimate R β)
          (linearRestrictionEstimate R
            (olsBetaOrZero
              (stackRegressors X n ω) (stackOutcomes y n ω)))
          (if n = 0 then 1
            else linearRestrictionStdError R
              (olsHetCovStar
                (stackRegressors X n ω) (stackOutcomes y n ω)) /
              Real.sqrt (n : ℝ))
          (bootstrapScalarLowerQuantileIndexed
            (fun n _ =>
              (ProbabilityTheory.uniformOn
                (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                  Measure (Fin (n + 1) → Fin (n + 1))))
            (fun n ω ωs =>
              regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs /
                seThetaStar n ω ωs)
            (α / 2) n ω)
          (bootstrapScalarLowerQuantileIndexed
            (fun n _ =>
              (ProbabilityTheory.uniformOn
                (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                  Measure (Fin (n + 1) → Fin (n + 1))))
            (fun n ω ωs =>
              regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs /
                seThetaStar n ω ωs)
            (1 - α / 2) n ω)})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) :=
  chapter10_indexed_ols_percentileTCI_coverage_tendsto_one_sub_alpha_finSucc_olsBetaOrZero_gapEnvelope_beta_bound_brackets
    (μ := μ) (X := X) (e := e) (y := y)
    (Vhat := fun n ω =>
      olsHetCovStar
        (stackRegressors X n ω) (stackOutcomes y n ω))
    β R hm
    (fun n =>
      olsHetCovStar_stack_aestronglyMeasurable_components
        (μ := μ) (X := X) (e := e) (y := y)
        hm.toSampleMomentAssumption71 β hm.model
        hm.x_aestronglyMeasurable hm.e_aestronglyMeasurable n)
    hsampleSe_pos
    (olsHC0LinTStatOrZero_tendstoInDistribution_standardNormal_of_robustFeasibleHCMomentConditions
      (μ := μ) (X := X) (e := e) (y := y) β R hm hse_pos)
    hse_pos hΩ hLinBound hBetaBound hGapTail hseThetaStar hseStar
    hα_pos hα_lt_one hleftLower hrightLower hleftUpper hrightUpper
    hlower_meas hupper_meas hq_nonneg hcdfLower hcdfUpper

set_option linter.style.longLine false in
/-- Indexed percentile-`t` coverage with the actual sample statistic
specialized to ordinary HC1 OLS and the bootstrap quantiles specialized to
the concrete finite ordinary-bootstrap OLS t-statistic. -/
theorem
    chapter10_indexed_olsHC1_percentileTCI_coverage_tendsto_one_sub_alpha_finSucc_olsBetaOrZero_gapEnvelope_beta_bound
    [IsProbabilityMeasure μ] [Fintype k] [DecidableEq k]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    {seThetaStar : ∀ n, Ω → (Fin (n + 1) → Fin (n + 1)) → ℝ}
    {Clin Cbeta q α : ℝ}
    (β : k → ℝ) (R : Matrix Unit k ℝ)
    (hm : RobustFeasibleHCMomentConditions μ X e y β)
    (hse_pos : 0 <
      linearRestrictionStdError R (heteroAsymCov μ X e))
    (hsampleSe_pos :
      ∀ n ω, n ≠ 0 →
        0 < linearRestrictionStdError R
          (olsHetCovHC1Star
            (stackRegressors X n ω) (stackOutcomes y n ω)))
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
    (hseStar :
      TendstoInBootstrapProbabilityIndexed μ
        (fun n _ =>
          (ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
              Measure (Fin (n + 1) → Fin (n + 1))))
        seThetaStar
        (fun _ => linearRestrictionStdError R (heteroAsymCov μ X e)))
    (hα_pos : 0 < α) (hα_lt_one : α < 1)
    (hstrict : StrictMono (fun x => cdf (gaussianReal 0 1) x))
    (hlower_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed
            (fun n _ =>
              (ProbabilityTheory.uniformOn
                (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                  Measure (Fin (n + 1) → Fin (n + 1))))
            (fun n ω ωs =>
              regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs /
                seThetaStar n ω ωs)
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
              regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs /
                seThetaStar n ω ωs)
            (1 - α / 2) n) μ)
    (hq_nonneg : 0 ≤ q)
    (hcdfLower : cdf (gaussianReal 0 1) (-q) = α / 2)
    (hcdfUpper : cdf (gaussianReal 0 1) q = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | percentileTCIEvent (linearRestrictionEstimate R β)
          (linearRestrictionEstimate R
            (olsBetaOrZero
              (stackRegressors X n ω) (stackOutcomes y n ω)))
          (if n = 0 then 1
            else linearRestrictionStdError R
              (olsHetCovHC1Star
                (stackRegressors X n ω) (stackOutcomes y n ω)) /
              Real.sqrt (n : ℝ))
          (bootstrapScalarLowerQuantileIndexed
            (fun n _ =>
              (ProbabilityTheory.uniformOn
                (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                  Measure (Fin (n + 1) → Fin (n + 1))))
            (fun n ω ωs =>
              regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs /
                seThetaStar n ω ωs)
            (α / 2) n ω)
          (bootstrapScalarLowerQuantileIndexed
            (fun n _ =>
              (ProbabilityTheory.uniformOn
                (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                  Measure (Fin (n + 1) → Fin (n + 1))))
            (fun n ω ωs =>
              regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs /
                seThetaStar n ω ωs)
            (1 - α / 2) n ω)})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) :=
  chapter10_indexed_ols_percentileTCI_coverage_tendsto_one_sub_alpha_finSucc_olsBetaOrZero_gapEnvelope_beta_bound
    (μ := μ) (X := X) (e := e) (y := y)
    (Vhat := fun n ω =>
      olsHetCovHC1Star
        (stackRegressors X n ω) (stackOutcomes y n ω))
    β R hm
    (fun n =>
      olsHC1CovarianceStar_stack_aestronglyMeasurable_components
        (μ := μ) (X := X) (e := e) (y := y)
        hm.toSampleMomentAssumption71 β hm.model
        hm.x_aestronglyMeasurable hm.e_aestronglyMeasurable n)
    hsampleSe_pos
    (olsHC1LinTStatOrZero_tendstoInDistribution_standardNormal_of_robustFeasibleHCMomentConditions
      (μ := μ) (X := X) (e := e) (y := y) β R hm hse_pos)
    hse_pos hΩ hLinBound hBetaBound hGapTail hseThetaStar hseStar
      hα_pos hα_lt_one hstrict hlower_meas hupper_meas hq_nonneg
    hcdfLower hcdfUpper

set_option linter.style.longLine false in
/-- Local-CDF bracketing counterpart of
`chapter10_indexed_olsHC1_percentileTCI_coverage_tendsto_one_sub_alpha_finSucc_olsBetaOrZero_gapEnvelope_beta_bound`. -/
theorem
    chapter10_indexed_olsHC1_percentileTCI_coverage_tendsto_one_sub_alpha_finSucc_olsBetaOrZero_gapEnvelope_beta_bound_brackets
    [IsProbabilityMeasure μ] [Fintype k] [DecidableEq k]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    {seThetaStar : ∀ n, Ω → (Fin (n + 1) → Fin (n + 1)) → ℝ}
    {Clin Cbeta q α : ℝ}
    (β : k → ℝ) (R : Matrix Unit k ℝ)
    (hm : RobustFeasibleHCMomentConditions μ X e y β)
    (hse_pos : 0 <
      linearRestrictionStdError R (heteroAsymCov μ X e))
    (hsampleSe_pos :
      ∀ n ω, n ≠ 0 →
        0 < linearRestrictionStdError R
          (olsHetCovHC1Star
            (stackRegressors X n ω) (stackOutcomes y n ω)))
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
    (hseStar :
      TendstoInBootstrapProbabilityIndexed μ
        (fun n _ =>
          (ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
              Measure (Fin (n + 1) → Fin (n + 1))))
        seThetaStar
        (fun _ => linearRestrictionStdError R (heteroAsymCov μ X e)))
    (hα_pos : 0 < α) (hα_lt_one : α < 1)
    (hleftLower :
      ∀ ε : ℝ, 0 < ε → cdf (gaussianReal 0 1) (-q - ε) < α / 2)
    (hrightLower :
      ∀ ε : ℝ, 0 < ε → α / 2 < cdf (gaussianReal 0 1) (-q + ε))
    (hleftUpper :
      ∀ ε : ℝ, 0 < ε → cdf (gaussianReal 0 1) (q - ε) < 1 - α / 2)
    (hrightUpper :
      ∀ ε : ℝ, 0 < ε → 1 - α / 2 < cdf (gaussianReal 0 1) (q + ε))
    (hlower_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed
            (fun n _ =>
              (ProbabilityTheory.uniformOn
                (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                  Measure (Fin (n + 1) → Fin (n + 1))))
            (fun n ω ωs =>
              regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs /
                seThetaStar n ω ωs)
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
              regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs /
                seThetaStar n ω ωs)
            (1 - α / 2) n) μ)
    (hq_nonneg : 0 ≤ q)
    (hcdfLower : cdf (gaussianReal 0 1) (-q) = α / 2)
    (hcdfUpper : cdf (gaussianReal 0 1) q = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | percentileTCIEvent (linearRestrictionEstimate R β)
          (linearRestrictionEstimate R
            (olsBetaOrZero
              (stackRegressors X n ω) (stackOutcomes y n ω)))
          (if n = 0 then 1
            else linearRestrictionStdError R
              (olsHetCovHC1Star
                (stackRegressors X n ω) (stackOutcomes y n ω)) /
              Real.sqrt (n : ℝ))
          (bootstrapScalarLowerQuantileIndexed
            (fun n _ =>
              (ProbabilityTheory.uniformOn
                (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                  Measure (Fin (n + 1) → Fin (n + 1))))
            (fun n ω ωs =>
              regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs /
                seThetaStar n ω ωs)
            (α / 2) n ω)
          (bootstrapScalarLowerQuantileIndexed
            (fun n _ =>
              (ProbabilityTheory.uniformOn
                (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                  Measure (Fin (n + 1) → Fin (n + 1))))
            (fun n ω ωs =>
              regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs /
                seThetaStar n ω ωs)
            (1 - α / 2) n ω)})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) :=
  chapter10_indexed_ols_percentileTCI_coverage_tendsto_one_sub_alpha_finSucc_olsBetaOrZero_gapEnvelope_beta_bound_brackets
    (μ := μ) (X := X) (e := e) (y := y)
    (Vhat := fun n ω =>
      olsHetCovHC1Star
        (stackRegressors X n ω) (stackOutcomes y n ω))
    β R hm
    (fun n =>
      olsHC1CovarianceStar_stack_aestronglyMeasurable_components
        (μ := μ) (X := X) (e := e) (y := y)
        hm.toSampleMomentAssumption71 β hm.model
        hm.x_aestronglyMeasurable hm.e_aestronglyMeasurable n)
    hsampleSe_pos
    (olsHC1LinTStatOrZero_tendstoInDistribution_standardNormal_of_robustFeasibleHCMomentConditions
      (μ := μ) (X := X) (e := e) (y := y) β R hm hse_pos)
    hse_pos hΩ hLinBound hBetaBound hGapTail hseThetaStar hseStar
    hα_pos hα_lt_one hleftLower hrightLower hleftUpper hrightUpper
    hlower_meas hupper_meas hq_nonneg hcdfLower hcdfUpper

set_option linter.style.longLine false in
/-- Indexed percentile-`t` coverage with the actual sample statistic
specialized to ordinary HC2 OLS and the bootstrap quantiles specialized to
the concrete finite ordinary-bootstrap OLS t-statistic. -/
theorem
    chapter10_indexed_olsHC2_percentileTCI_coverage_tendsto_one_sub_alpha_finSucc_olsBetaOrZero_gapEnvelope_beta_bound
    [IsProbabilityMeasure μ] [Fintype k] [DecidableEq k]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    {seThetaStar : ∀ n, Ω → (Fin (n + 1) → Fin (n + 1)) → ℝ}
    {Clin Cbeta q α : ℝ}
    (β : k → ℝ) (R : Matrix Unit k ℝ)
    (hm : RobustFeasibleHCMomentConditions μ X e y β)
    (hse_pos : 0 <
      linearRestrictionStdError R (heteroAsymCov μ X e))
    (hsampleSe_pos :
      ∀ n ω, n ≠ 0 →
        0 < linearRestrictionStdError R
          (olsHetCovHC2Star
            (stackRegressors X n ω) (stackOutcomes y n ω)))
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
    (hseStar :
      TendstoInBootstrapProbabilityIndexed μ
        (fun n _ =>
          (ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
              Measure (Fin (n + 1) → Fin (n + 1))))
        seThetaStar
        (fun _ => linearRestrictionStdError R (heteroAsymCov μ X e)))
    (hα_pos : 0 < α) (hα_lt_one : α < 1)
    (hstrict : StrictMono (fun x => cdf (gaussianReal 0 1) x))
    (hlower_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed
            (fun n _ =>
              (ProbabilityTheory.uniformOn
                (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                  Measure (Fin (n + 1) → Fin (n + 1))))
            (fun n ω ωs =>
              regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs /
                seThetaStar n ω ωs)
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
              regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs /
                seThetaStar n ω ωs)
            (1 - α / 2) n) μ)
    (hq_nonneg : 0 ≤ q)
    (hcdfLower : cdf (gaussianReal 0 1) (-q) = α / 2)
    (hcdfUpper : cdf (gaussianReal 0 1) q = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | percentileTCIEvent (linearRestrictionEstimate R β)
          (linearRestrictionEstimate R
            (olsBetaOrZero
              (stackRegressors X n ω) (stackOutcomes y n ω)))
          (if n = 0 then 1
            else linearRestrictionStdError R
              (olsHetCovHC2Star
                (stackRegressors X n ω) (stackOutcomes y n ω)) /
              Real.sqrt (n : ℝ))
          (bootstrapScalarLowerQuantileIndexed
            (fun n _ =>
              (ProbabilityTheory.uniformOn
                (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                  Measure (Fin (n + 1) → Fin (n + 1))))
            (fun n ω ωs =>
              regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs /
                seThetaStar n ω ωs)
            (α / 2) n ω)
          (bootstrapScalarLowerQuantileIndexed
            (fun n _ =>
              (ProbabilityTheory.uniformOn
                (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                  Measure (Fin (n + 1) → Fin (n + 1))))
            (fun n ω ωs =>
              regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs /
                seThetaStar n ω ωs)
            (1 - α / 2) n ω)})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) :=
  chapter10_indexed_ols_percentileTCI_coverage_tendsto_one_sub_alpha_finSucc_olsBetaOrZero_gapEnvelope_beta_bound
    (μ := μ) (X := X) (e := e) (y := y)
    (Vhat := fun n ω =>
      olsHetCovHC2Star
        (stackRegressors X n ω) (stackOutcomes y n ω))
    β R hm
    (fun n =>
      olsHC2CovarianceStar_stack_aestronglyMeasurable_components
        (μ := μ) (X := X) (e := e) (y := y)
        hm.toSampleMomentAssumption71 β hm.model
        hm.x_aestronglyMeasurable hm.e_aestronglyMeasurable n)
    hsampleSe_pos
    (olsHC2LinTStatOrZero_tendstoInDistribution_standardNormal_of_robustFeasibleHCMomentConditions
      (μ := μ) (X := X) (e := e) (y := y) β R hm hse_pos)
    hse_pos hΩ hLinBound hBetaBound hGapTail hseThetaStar hseStar
      hα_pos hα_lt_one hstrict hlower_meas hupper_meas hq_nonneg
    hcdfLower hcdfUpper

set_option linter.style.longLine false in
/-- Local-CDF bracketing counterpart of
`chapter10_indexed_olsHC2_percentileTCI_coverage_tendsto_one_sub_alpha_finSucc_olsBetaOrZero_gapEnvelope_beta_bound`. -/
theorem
    chapter10_indexed_olsHC2_percentileTCI_coverage_tendsto_one_sub_alpha_finSucc_olsBetaOrZero_gapEnvelope_beta_bound_brackets
    [IsProbabilityMeasure μ] [Fintype k] [DecidableEq k]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    {seThetaStar : ∀ n, Ω → (Fin (n + 1) → Fin (n + 1)) → ℝ}
    {Clin Cbeta q α : ℝ}
    (β : k → ℝ) (R : Matrix Unit k ℝ)
    (hm : RobustFeasibleHCMomentConditions μ X e y β)
    (hse_pos : 0 <
      linearRestrictionStdError R (heteroAsymCov μ X e))
    (hsampleSe_pos :
      ∀ n ω, n ≠ 0 →
        0 < linearRestrictionStdError R
          (olsHetCovHC2Star
            (stackRegressors X n ω) (stackOutcomes y n ω)))
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
    (hseStar :
      TendstoInBootstrapProbabilityIndexed μ
        (fun n _ =>
          (ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
              Measure (Fin (n + 1) → Fin (n + 1))))
        seThetaStar
        (fun _ => linearRestrictionStdError R (heteroAsymCov μ X e)))
    (hα_pos : 0 < α) (hα_lt_one : α < 1)
    (hleftLower :
      ∀ ε : ℝ, 0 < ε → cdf (gaussianReal 0 1) (-q - ε) < α / 2)
    (hrightLower :
      ∀ ε : ℝ, 0 < ε → α / 2 < cdf (gaussianReal 0 1) (-q + ε))
    (hleftUpper :
      ∀ ε : ℝ, 0 < ε → cdf (gaussianReal 0 1) (q - ε) < 1 - α / 2)
    (hrightUpper :
      ∀ ε : ℝ, 0 < ε → 1 - α / 2 < cdf (gaussianReal 0 1) (q + ε))
    (hlower_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed
            (fun n _ =>
              (ProbabilityTheory.uniformOn
                (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                  Measure (Fin (n + 1) → Fin (n + 1))))
            (fun n ω ωs =>
              regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs /
                seThetaStar n ω ωs)
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
              regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs /
                seThetaStar n ω ωs)
            (1 - α / 2) n) μ)
    (hq_nonneg : 0 ≤ q)
    (hcdfLower : cdf (gaussianReal 0 1) (-q) = α / 2)
    (hcdfUpper : cdf (gaussianReal 0 1) q = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | percentileTCIEvent (linearRestrictionEstimate R β)
          (linearRestrictionEstimate R
            (olsBetaOrZero
              (stackRegressors X n ω) (stackOutcomes y n ω)))
          (if n = 0 then 1
            else linearRestrictionStdError R
              (olsHetCovHC2Star
                (stackRegressors X n ω) (stackOutcomes y n ω)) /
              Real.sqrt (n : ℝ))
          (bootstrapScalarLowerQuantileIndexed
            (fun n _ =>
              (ProbabilityTheory.uniformOn
                (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                  Measure (Fin (n + 1) → Fin (n + 1))))
            (fun n ω ωs =>
              regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs /
                seThetaStar n ω ωs)
            (α / 2) n ω)
          (bootstrapScalarLowerQuantileIndexed
            (fun n _ =>
              (ProbabilityTheory.uniformOn
                (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                  Measure (Fin (n + 1) → Fin (n + 1))))
            (fun n ω ωs =>
              regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs /
                seThetaStar n ω ωs)
            (1 - α / 2) n ω)})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) :=
  chapter10_indexed_ols_percentileTCI_coverage_tendsto_one_sub_alpha_finSucc_olsBetaOrZero_gapEnvelope_beta_bound_brackets
    (μ := μ) (X := X) (e := e) (y := y)
    (Vhat := fun n ω =>
      olsHetCovHC2Star
        (stackRegressors X n ω) (stackOutcomes y n ω))
    β R hm
    (fun n =>
      olsHC2CovarianceStar_stack_aestronglyMeasurable_components
        (μ := μ) (X := X) (e := e) (y := y)
        hm.toSampleMomentAssumption71 β hm.model
        hm.x_aestronglyMeasurable hm.e_aestronglyMeasurable n)
    hsampleSe_pos
    (olsHC2LinTStatOrZero_tendstoInDistribution_standardNormal_of_robustFeasibleHCMomentConditions
      (μ := μ) (X := X) (e := e) (y := y) β R hm hse_pos)
    hse_pos hΩ hLinBound hBetaBound hGapTail hseThetaStar hseStar
    hα_pos hα_lt_one hleftLower hrightLower hleftUpper hrightUpper
    hlower_meas hupper_meas hq_nonneg hcdfLower hcdfUpper

set_option linter.style.longLine false in
/-- Indexed percentile-`t` coverage with the actual sample statistic
specialized to ordinary HC3 OLS and the bootstrap quantiles specialized to
the concrete finite ordinary-bootstrap OLS t-statistic. -/
theorem
    chapter10_indexed_olsHC3_percentileTCI_coverage_tendsto_one_sub_alpha_finSucc_olsBetaOrZero_gapEnvelope_beta_bound
    [IsProbabilityMeasure μ] [Fintype k] [DecidableEq k]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    {seThetaStar : ∀ n, Ω → (Fin (n + 1) → Fin (n + 1)) → ℝ}
    {Clin Cbeta q α : ℝ}
    (β : k → ℝ) (R : Matrix Unit k ℝ)
    (hm : RobustFeasibleHCMomentConditions μ X e y β)
    (hse_pos : 0 <
      linearRestrictionStdError R (heteroAsymCov μ X e))
    (hsampleSe_pos :
      ∀ n ω, n ≠ 0 →
        0 < linearRestrictionStdError R
          (olsHetCovHC3Star
            (stackRegressors X n ω) (stackOutcomes y n ω)))
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
    (hseStar :
      TendstoInBootstrapProbabilityIndexed μ
        (fun n _ =>
          (ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
              Measure (Fin (n + 1) → Fin (n + 1))))
        seThetaStar
        (fun _ => linearRestrictionStdError R (heteroAsymCov μ X e)))
    (hα_pos : 0 < α) (hα_lt_one : α < 1)
    (hstrict : StrictMono (fun x => cdf (gaussianReal 0 1) x))
    (hlower_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed
            (fun n _ =>
              (ProbabilityTheory.uniformOn
                (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                  Measure (Fin (n + 1) → Fin (n + 1))))
            (fun n ω ωs =>
              regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs /
                seThetaStar n ω ωs)
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
              regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs /
                seThetaStar n ω ωs)
            (1 - α / 2) n) μ)
    (hq_nonneg : 0 ≤ q)
    (hcdfLower : cdf (gaussianReal 0 1) (-q) = α / 2)
    (hcdfUpper : cdf (gaussianReal 0 1) q = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | percentileTCIEvent (linearRestrictionEstimate R β)
          (linearRestrictionEstimate R
            (olsBetaOrZero
              (stackRegressors X n ω) (stackOutcomes y n ω)))
          (if n = 0 then 1
            else linearRestrictionStdError R
              (olsHetCovHC3Star
                (stackRegressors X n ω) (stackOutcomes y n ω)) /
              Real.sqrt (n : ℝ))
          (bootstrapScalarLowerQuantileIndexed
            (fun n _ =>
              (ProbabilityTheory.uniformOn
                (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                  Measure (Fin (n + 1) → Fin (n + 1))))
            (fun n ω ωs =>
              regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs /
                seThetaStar n ω ωs)
            (α / 2) n ω)
          (bootstrapScalarLowerQuantileIndexed
            (fun n _ =>
              (ProbabilityTheory.uniformOn
                (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                  Measure (Fin (n + 1) → Fin (n + 1))))
            (fun n ω ωs =>
              regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs /
                seThetaStar n ω ωs)
            (1 - α / 2) n ω)})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) :=
  chapter10_indexed_ols_percentileTCI_coverage_tendsto_one_sub_alpha_finSucc_olsBetaOrZero_gapEnvelope_beta_bound
    (μ := μ) (X := X) (e := e) (y := y)
    (Vhat := fun n ω =>
      olsHetCovHC3Star
        (stackRegressors X n ω) (stackOutcomes y n ω))
    β R hm
    (fun n =>
      olsHC3CovarianceStar_stack_aestronglyMeasurable_components
        (μ := μ) (X := X) (e := e) (y := y)
        hm.toSampleMomentAssumption71 β hm.model
        hm.x_aestronglyMeasurable hm.e_aestronglyMeasurable n)
    hsampleSe_pos
    (olsHC3LinTStatOrZero_tendstoInDistribution_standardNormal_of_robustFeasibleHCMomentConditions
      (μ := μ) (X := X) (e := e) (y := y) β R hm hse_pos)
    hse_pos hΩ hLinBound hBetaBound hGapTail hseThetaStar hseStar
      hα_pos hα_lt_one hstrict hlower_meas hupper_meas hq_nonneg
    hcdfLower hcdfUpper

set_option linter.style.longLine false in
/-- Local-CDF bracketing counterpart of
`chapter10_indexed_olsHC3_percentileTCI_coverage_tendsto_one_sub_alpha_finSucc_olsBetaOrZero_gapEnvelope_beta_bound`. -/
theorem
    chapter10_indexed_olsHC3_percentileTCI_coverage_tendsto_one_sub_alpha_finSucc_olsBetaOrZero_gapEnvelope_beta_bound_brackets
    [IsProbabilityMeasure μ] [Fintype k] [DecidableEq k]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    {seThetaStar : ∀ n, Ω → (Fin (n + 1) → Fin (n + 1)) → ℝ}
    {Clin Cbeta q α : ℝ}
    (β : k → ℝ) (R : Matrix Unit k ℝ)
    (hm : RobustFeasibleHCMomentConditions μ X e y β)
    (hse_pos : 0 <
      linearRestrictionStdError R (heteroAsymCov μ X e))
    (hsampleSe_pos :
      ∀ n ω, n ≠ 0 →
        0 < linearRestrictionStdError R
          (olsHetCovHC3Star
            (stackRegressors X n ω) (stackOutcomes y n ω)))
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
    (hseStar :
      TendstoInBootstrapProbabilityIndexed μ
        (fun n _ =>
          (ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
              Measure (Fin (n + 1) → Fin (n + 1))))
        seThetaStar
        (fun _ => linearRestrictionStdError R (heteroAsymCov μ X e)))
    (hα_pos : 0 < α) (hα_lt_one : α < 1)
    (hleftLower :
      ∀ ε : ℝ, 0 < ε → cdf (gaussianReal 0 1) (-q - ε) < α / 2)
    (hrightLower :
      ∀ ε : ℝ, 0 < ε → α / 2 < cdf (gaussianReal 0 1) (-q + ε))
    (hleftUpper :
      ∀ ε : ℝ, 0 < ε → cdf (gaussianReal 0 1) (q - ε) < 1 - α / 2)
    (hrightUpper :
      ∀ ε : ℝ, 0 < ε → 1 - α / 2 < cdf (gaussianReal 0 1) (q + ε))
    (hlower_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed
            (fun n _ =>
              (ProbabilityTheory.uniformOn
                (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                  Measure (Fin (n + 1) → Fin (n + 1))))
            (fun n ω ωs =>
              regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs /
                seThetaStar n ω ωs)
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
              regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs /
                seThetaStar n ω ωs)
            (1 - α / 2) n) μ)
    (hq_nonneg : 0 ≤ q)
    (hcdfLower : cdf (gaussianReal 0 1) (-q) = α / 2)
    (hcdfUpper : cdf (gaussianReal 0 1) q = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | percentileTCIEvent (linearRestrictionEstimate R β)
          (linearRestrictionEstimate R
            (olsBetaOrZero
              (stackRegressors X n ω) (stackOutcomes y n ω)))
          (if n = 0 then 1
            else linearRestrictionStdError R
              (olsHetCovHC3Star
                (stackRegressors X n ω) (stackOutcomes y n ω)) /
              Real.sqrt (n : ℝ))
          (bootstrapScalarLowerQuantileIndexed
            (fun n _ =>
              (ProbabilityTheory.uniformOn
                (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                  Measure (Fin (n + 1) → Fin (n + 1))))
            (fun n ω ωs =>
              regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs /
                seThetaStar n ω ωs)
            (α / 2) n ω)
          (bootstrapScalarLowerQuantileIndexed
            (fun n _ =>
              (ProbabilityTheory.uniformOn
                (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                  Measure (Fin (n + 1) → Fin (n + 1))))
            (fun n ω ωs =>
              regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs /
                seThetaStar n ω ωs)
            (1 - α / 2) n ω)})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) :=
  chapter10_indexed_ols_percentileTCI_coverage_tendsto_one_sub_alpha_finSucc_olsBetaOrZero_gapEnvelope_beta_bound_brackets
    (μ := μ) (X := X) (e := e) (y := y)
    (Vhat := fun n ω =>
      olsHetCovHC3Star
        (stackRegressors X n ω) (stackOutcomes y n ω))
    β R hm
    (fun n =>
      olsHC3CovarianceStar_stack_aestronglyMeasurable_components
        (μ := μ) (X := X) (e := e) (y := y)
        hm.toSampleMomentAssumption71 β hm.model
        hm.x_aestronglyMeasurable hm.e_aestronglyMeasurable n)
    hsampleSe_pos
    (olsHC3LinTStatOrZero_tendstoInDistribution_standardNormal_of_robustFeasibleHCMomentConditions
      (μ := μ) (X := X) (e := e) (y := y) β R hm hse_pos)
    hse_pos hΩ hLinBound hBetaBound hGapTail hseThetaStar hseStar
    hα_pos hα_lt_one hleftLower hrightLower hleftUpper hrightUpper
    hlower_meas hupper_meas hq_nonneg hcdfLower hcdfUpper

set_option linter.style.longLine true

end PercentileTIntervals

end HansenEconometrics
