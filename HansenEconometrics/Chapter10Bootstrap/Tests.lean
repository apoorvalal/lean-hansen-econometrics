import HansenEconometrics.Chapter10Bootstrap.Quantiles
import HansenEconometrics.Chapter10Bootstrap.Regression

/-!
# Chapter 10 — Bootstrap tests

Bootstrap hypothesis tests: rejection-set characterizations, CDF bracketing
under almost-everywhere nonnegativity, and the bootstrap test coverage results.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology MeasureTheory ProbabilityTheory Matrix
open scoped Matrix.Norms.Elementwise Function

namespace HansenEconometrics

variable {Ω Ωs Ωlim E F k : Type*}
variable {mΩ : MeasurableSpace Ω} {mΩs : MeasurableSpace Ωs}
variable {mΩlim : MeasurableSpace Ωlim}
variable {μ : Measure Ω} {ν : Measure Ωlim}

section BootstrapTests

/-- Two-sided bootstrap-test rejection event: reject when `crit < |T|`. -/
def bootstrapAbsTestReject (T crit : ℝ) : Prop :=
  crit < |T|

/-- Two-coordinate statistic for a two-sided bootstrap critical-value test:
coordinate `0` is the test statistic and coordinate `1` is the bootstrap
critical value. -/
noncomputable def bootstrapAbsTestVector
    (T crit : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : Fin 2 → ℝ :=
  fun i => if i = 0 then T n ω else crit n ω

/-- Limit vector for the two-sided bootstrap critical-value test. -/
noncomputable def bootstrapAbsTestLimitVector
    (ξ : Ωlim → ℝ) (crit : ℝ) (ω : Ωlim) : Fin 2 → ℝ :=
  fun i => if i = 0 then ξ ω else crit

/-- Componentwise Slutsky constructor for the two-sided bootstrap-test joint
vector.

This assembles the joint convergence premise in
`chapter10_bootstrap_abs_test_rejectionProb_tendsto_of_joint_critical_value_limit`
from statistic convergence and critical-value convergence in probability. -/
theorem bootstrapAbsTestVector_tendstoInDistribution_of_components
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {T crit : ℕ → Ω → ℝ} {ξ : Ωlim → ℝ} {critLim : ℝ}
    (hT : TendstoInDistribution T atTop ξ (fun _ => μ) ν)
    (hcrit : TendstoInMeasure μ crit atTop (fun _ => critLim))
    (hcrit_meas : ∀ n, AEMeasurable (crit n) μ) :
    TendstoInDistribution
      (bootstrapAbsTestVector T crit)
      atTop
      (bootstrapAbsTestLimitVector ξ critLim)
      (fun _ => μ) ν := by
  classical
  let pack : ℝ × ℝ → Fin 2 → ℝ :=
    fun p i => if i = 0 then p.1 else p.2
  have hpack_cont : Continuous pack := by
    refine continuous_pi ?_
    intro i
    by_cases hi0 : i = 0
    · simpa [pack, hi0] using
        (continuous_fst : Continuous (fun p : ℝ × ℝ => p.1))
    · simpa [pack, hi0] using
        (continuous_snd : Continuous (fun p : ℝ × ℝ => p.2))
  have hpacked :
      TendstoInDistribution
        (fun n ω => pack (T n ω, crit n ω))
        atTop (fun ω => pack (ξ ω, critLim)) (fun _ => μ) ν := by
    have hraw := hT.continuous_comp_prodMk_of_tendstoInMeasure_const
      (g := pack) hpack_cont hcrit hcrit_meas
    simpa [Function.comp_def] using hraw
  refine TendstoInDistribution.congr ?_ ?_ hpacked
  · intro n
    exact ae_of_all μ fun ω => by
      ext i
      by_cases hi0 : i = 0 <;> simp [bootstrapAbsTestVector, pack, hi0]
  · exact ae_of_all ν fun ω => by
      ext i
      by_cases hi0 : i = 0 <;> simp [bootstrapAbsTestLimitVector, pack, hi0]

/-- Rejection region for the two-sided bootstrap critical-value test. -/
def bootstrapAbsRejectionSet : Set (Fin 2 → ℝ) :=
  {z | z 1 < |z 0|}

private theorem isOpen_bootstrapAbsRejectionSet : IsOpen bootstrapAbsRejectionSet := by
  simpa [bootstrapAbsRejectionSet] using
    isOpen_lt (continuous_apply 1) ((continuous_apply 0).abs)

private theorem bootstrapAbsTestVector_mem_rejectionSet_iff
    {T crit : ℕ → Ω → ℝ} {n : ℕ} {ω : Ω} :
    bootstrapAbsTestVector T crit n ω ∈ bootstrapAbsRejectionSet ↔
      bootstrapAbsTestReject (T n ω) (crit n ω) := by
  change crit n ω < |T n ω| ↔ crit n ω < |T n ω|
  rfl

/-- The bootstrap-test limit vector belongs to the rejection set exactly when
the scalar limit statistic rejects against the limiting critical value. -/
theorem bootstrapAbsTestLimitVector_mem_rejectionSet_iff
    {ξ : Ωlim → ℝ} {critLim : ℝ} {ω : Ωlim} :
    bootstrapAbsTestLimitVector ξ critLim ω ∈ bootstrapAbsRejectionSet ↔
      bootstrapAbsTestReject (ξ ω) critLim := by
  change critLim < |ξ ω| ↔ critLim < |ξ ω|
  rfl

/-- A scalar a.e.-measurable limit statistic yields an a.e.-measurable
bootstrap-test limit vector. -/
private theorem aemeasurable_bootstrapAbsTestLimitVector
    {ξ : Ωlim → ℝ} (hξ : AEMeasurable ξ ν) (critLim : ℝ) :
    AEMeasurable (bootstrapAbsTestLimitVector ξ critLim) ν := by
  refine aemeasurable_pi_lambda _ ?_
  intro i
  by_cases hi0 : i = 0
  · subst i
    simpa [bootstrapAbsTestLimitVector] using hξ
  · simp [bootstrapAbsTestLimitVector, hi0]

/-- The vector-law probability of the bootstrap-test rejection set is the
scalar event probability `P[q < |ξ|]`. -/
theorem bootstrapAbsTestLimit_measure_rejectionSet_eq
    {ξ : Ωlim → ℝ} {critLim : ℝ}
    (hξ : AEMeasurable ξ ν) :
    (ν.map (bootstrapAbsTestLimitVector ξ critLim))
        bootstrapAbsRejectionSet =
      ν {ω | bootstrapAbsTestReject (ξ ω) critLim} := by
  rw [Measure.map_apply_of_aemeasurable
    (aemeasurable_bootstrapAbsTestLimitVector (ν := ν) hξ critLim)
    isOpen_bootstrapAbsRejectionSet.measurableSet]
  apply congrArg ν
  ext ω
  exact bootstrapAbsTestLimitVector_mem_rejectionSet_iff

/-- The frontier of the two-sided rejection set is contained in the binding
critical-value hyperplane. -/
theorem frontier_bootstrapAbsRejectionSet_subset :
    frontier bootstrapAbsRejectionSet ⊆
      {z : Fin 2 → ℝ | z 1 = |z 0|} :=
  frontier_lt_subset_eq (continuous_apply 1) ((continuous_apply 0).abs)

/-- Scalar critical-value boundary null mass implies the vector-law
null-frontier premise for the two-sided bootstrap rejection set. -/
theorem bootstrapAbsTest_frontier_null_of_boundary_null
    {ξ : Ωlim → ℝ} {critLim : ℝ}
    (hξ : AEMeasurable ξ ν)
    (hboundary : ν {ω | critLim = |ξ ω|} = 0) :
    (ν.map (bootstrapAbsTestLimitVector ξ critLim))
      (frontier bootstrapAbsRejectionSet) = 0 := by
  let boundary : Set (Fin 2 → ℝ) := {z | z 1 = |z 0|}
  have hboundary_meas : MeasurableSet boundary :=
    (isClosed_eq (continuous_apply 1) ((continuous_apply 0).abs)).measurableSet
  have hboundary_zero :
      (ν.map (bootstrapAbsTestLimitVector ξ critLim)) boundary = 0 := by
    rw [Measure.map_apply_of_aemeasurable
      (aemeasurable_bootstrapAbsTestLimitVector (ν := ν) hξ critLim)
      hboundary_meas]
    have hpre :
        (bootstrapAbsTestLimitVector ξ critLim) ⁻¹' boundary =
          {ω | critLim = |ξ ω|} := by
      ext ω
      simp [boundary, bootstrapAbsTestLimitVector]
    simpa [hpre] using hboundary
  exact measure_mono_null (μ := ν.map (bootstrapAbsTestLimitVector ξ critLim))
    frontier_bootstrapAbsRejectionSet_subset hboundary_zero

/-- The scalar two-sided rejection event can be read from the law of the
limit statistic. -/
theorem bootstrapAbsTest_scalar_rejection_eq_law
    {ξ : Ωlim → ℝ} {η : Measure ℝ} (hξ : HasLaw ξ η ν)
    (critLim : ℝ) :
    ν {ω | bootstrapAbsTestReject (ξ ω) critLim} =
      η {x | bootstrapAbsTestReject x critLim} := by
  have hpre :
      {ω | bootstrapAbsTestReject (ξ ω) critLim} =
        ξ ⁻¹' {x | bootstrapAbsTestReject x critLim} := by
    rfl
  rw [hpre]
  exact HasLaw.preimage_eq hξ
    ((isOpen_lt continuous_const continuous_abs).measurableSet)

/-- For a non-atomic real probability law, the two-sided rejection event
`q < |x|` has mass `1 - (F(q) - F(-q))`. -/
theorem bootstrapAbsTest_rejection_law_eq_ofReal_one_sub_cdf
    {η : Measure ℝ} [IsProbabilityMeasure η] [NoAtoms η]
    {critLim : ℝ} (hcrit : 0 ≤ critLim) :
    η {x | bootstrapAbsTestReject x critLim} =
      ENNReal.ofReal (1 - (cdf η critLim - cdf η (-critLim))) := by
  have hset :
      {x : ℝ | bootstrapAbsTestReject x critLim} =
        (Set.Icc (-critLim) critLim)ᶜ := by
    ext x
    constructor
    · intro hx hxI
      exact not_le_of_gt hx ((abs_le).2 hxI)
    · intro hx
      exact lt_of_not_ge fun hle => hx ((abs_le).1 hle)
  have hinc_nonneg : 0 ≤ cdf η critLim - cdf η (-critLim) := by
    exact sub_nonneg.2 ((ProbabilityTheory.monotone_cdf η) (by linarith))
  rw [hset, measure_compl measurableSet_Icc (measure_ne_top η (Set.Icc (-critLim) critLim)),
    measure_univ,
    measure_Icc_eq_ofReal_cdf_sub_of_noAtoms
      (ν := η) (a := -critLim) (b := critLim) (by linarith),
    ← ENNReal.ofReal_one, ← ENNReal.ofReal_sub (1 : ℝ) hinc_nonneg]

/-- If the scalar limit law has no atoms, then the two-sided rejection
frontier has zero mass under the limit vector law. -/
theorem bootstrapAbsTest_frontier_null_of_hasLaw_noAtoms
    {ξ : Ωlim → ℝ} {η : Measure ℝ} [NoAtoms η] (hξ : HasLaw ξ η ν)
    (critLim : ℝ) :
    (ν.map (bootstrapAbsTestLimitVector ξ critLim))
      (frontier bootstrapAbsRejectionSet) = 0 := by
  refine bootstrapAbsTest_frontier_null_of_boundary_null
    (ν := ν) (critLim := critLim) hξ.aemeasurable ?_
  have hpre_subset :
      {ω | critLim = |ξ ω|} ⊆
        ξ ⁻¹' ({critLim} ∪ {-critLim} : Set ℝ) := by
    intro ω hω
    simp only [Set.mem_preimage, Set.mem_union, Set.mem_singleton_iff]
    by_cases hnonneg : 0 ≤ ξ ω
    · left
      simpa [abs_of_nonneg hnonneg, eq_comm] using hω
    · right
      have hneg : ξ ω < 0 := lt_of_not_ge hnonneg
      have hcrit : critLim = -(ξ ω) := by
        simpa [abs_of_neg hneg] using hω
      linarith
  refine measure_mono_null hpre_subset ?_
  rw [HasLaw.preimage_eq hξ
    ((measurableSet_singleton critLim).union
      (measurableSet_singleton (-critLim)))]
  exact measure_union_null (measure_singleton critLim) (measure_singleton (-critLim))

/-- Hansen Theorem 10.16, bootstrap critical-value rejection-probability bridge.

If the test statistic and bootstrap critical value jointly converge to
`(ξ, q)`, and the rejection boundary has zero limit mass, then the rejection
probability converges to `P[q < |ξ|]`. -/
theorem chapter10_bootstrap_abs_test_rejectionProb_tendsto_of_joint_critical_value_limit
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {T crit : ℕ → Ω → ℝ} {ξ : Ωlim → ℝ} {critLim : ℝ}
    (hjoint :
      TendstoInDistribution
        (bootstrapAbsTestVector T crit)
        atTop
        (bootstrapAbsTestLimitVector ξ critLim)
        (fun _ => μ) ν)
    (hfrontier :
      (ν.map (bootstrapAbsTestLimitVector ξ critLim))
        (frontier bootstrapAbsRejectionSet) = 0) :
    Tendsto
      (fun n => μ {ω | bootstrapAbsTestReject (T n ω) (crit n ω)})
      atTop
      (𝓝 ((ν.map (bootstrapAbsTestLimitVector ξ critLim)) bootstrapAbsRejectionSet)) := by
  have hset_meas : MeasurableSet bootstrapAbsRejectionSet :=
    isOpen_bootstrapAbsRejectionSet.measurableSet
  have hrejection :=
    TendstoInDistribution.tendsto_measure_preimage_of_null_frontier
      (h := hjoint) hset_meas hfrontier
  have hseq_eq :
      (fun n =>
        μ {ω | bootstrapAbsTestVector T crit n ω ∈ bootstrapAbsRejectionSet}) =
        fun n => μ {ω | bootstrapAbsTestReject (T n ω) (crit n ω)} := by
    funext n
    rfl
  simpa [hseq_eq] using hrejection

/-- Calibrated form of the bootstrap critical-value bridge.

When the limiting rejection probability equals `α`, the bootstrap critical
value test has asymptotic size `α`. -/
theorem chapter10_bootstrap_abs_test_rejectionProb_tendsto_alpha
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {T crit : ℕ → Ω → ℝ} {ξ : Ωlim → ℝ} {critLim : ℝ} {α : ℝ≥0∞}
    (hjoint :
      TendstoInDistribution
        (bootstrapAbsTestVector T crit)
        atTop
        (bootstrapAbsTestLimitVector ξ critLim)
        (fun _ => μ) ν)
    (hfrontier :
      (ν.map (bootstrapAbsTestLimitVector ξ critLim))
        (frontier bootstrapAbsRejectionSet) = 0)
    (halpha :
      (ν.map (bootstrapAbsTestLimitVector ξ critLim)) bootstrapAbsRejectionSet = α) :
    Tendsto
      (fun n => μ {ω | bootstrapAbsTestReject (T n ω) (crit n ω)})
      atTop (𝓝 α) := by
  simpa [halpha] using
    chapter10_bootstrap_abs_test_rejectionProb_tendsto_of_joint_critical_value_limit
      (μ := μ) (ν := ν) (T := T) (crit := crit) (ξ := ξ) (critLim := critLim)
      hjoint hfrontier

/-- Calibrated bootstrap critical-value bridge with the limiting rejection
probability stated as the scalar event probability `P[q < |ξ|]`. -/
theorem chapter10_bootstrap_abs_test_rejectionProb_tendsto_alpha_of_scalar_limit_rejection
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {T crit : ℕ → Ω → ℝ} {ξ : Ωlim → ℝ} {critLim : ℝ} {α : ℝ≥0∞}
    (hjoint :
      TendstoInDistribution
        (bootstrapAbsTestVector T crit)
        atTop
        (bootstrapAbsTestLimitVector ξ critLim)
        (fun _ => μ) ν)
    (hfrontier :
      (ν.map (bootstrapAbsTestLimitVector ξ critLim))
        (frontier bootstrapAbsRejectionSet) = 0)
    (halpha :
      ν {ω | bootstrapAbsTestReject (ξ ω) critLim} = α) :
    Tendsto
      (fun n => μ {ω | bootstrapAbsTestReject (T n ω) (crit n ω)})
      atTop (𝓝 α) := by
  have halpha_map :
      (ν.map (bootstrapAbsTestLimitVector ξ critLim)) bootstrapAbsRejectionSet =
        α := by
    rw [Measure.map_apply_of_aemeasurable hjoint.aemeasurable_limit
      isOpen_bootstrapAbsRejectionSet.measurableSet]
    have hpre :
        {ω | bootstrapAbsTestLimitVector ξ critLim ω ∈
            bootstrapAbsRejectionSet} =
          {ω | bootstrapAbsTestReject (ξ ω) critLim} := by
      ext ω
      exact bootstrapAbsTestLimitVector_mem_rejectionSet_iff
    simpa [hpre] using halpha
  exact
    chapter10_bootstrap_abs_test_rejectionProb_tendsto_alpha
      (μ := μ) (ν := ν) (T := T) (crit := crit) (ξ := ξ) (critLim := critLim)
      hjoint hfrontier halpha_map

/-- Calibrated bootstrap critical-value bridge with scalar boundary-null and
scalar limiting rejection-probability assumptions. -/
theorem chapter10_bootstrap_abs_test_rejectionProb_tendsto_alpha_of_scalar_limit
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {T crit : ℕ → Ω → ℝ} {ξ : Ωlim → ℝ} {critLim : ℝ} {α : ℝ≥0∞}
    (hjoint :
      TendstoInDistribution
        (bootstrapAbsTestVector T crit)
        atTop
        (bootstrapAbsTestLimitVector ξ critLim)
        (fun _ => μ) ν)
    (hξ : AEMeasurable ξ ν)
    (hboundary : ν {ω | critLim = |ξ ω|} = 0)
    (halpha : ν {ω | bootstrapAbsTestReject (ξ ω) critLim} = α) :
    Tendsto
      (fun n => μ {ω | bootstrapAbsTestReject (T n ω) (crit n ω)})
      atTop (𝓝 α) := by
  exact
    chapter10_bootstrap_abs_test_rejectionProb_tendsto_alpha_of_scalar_limit_rejection
      (μ := μ) (ν := ν) (T := T) (crit := crit) (ξ := ξ) (critLim := critLim)
      hjoint
      (bootstrapAbsTest_frontier_null_of_boundary_null
        (ν := ν) (critLim := critLim) hξ hboundary)
      halpha

/-- Calibrated bootstrap critical-value bridge with calibration stated under
the scalar law of the limit statistic.  A non-atomic limit law supplies the
required null-frontier premise. -/
theorem chapter10_bootstrap_abs_test_rejectionProb_tendsto_alpha_of_limit_law
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {η : Measure ℝ} [NoAtoms η]
    {T crit : ℕ → Ω → ℝ} {ξ : Ωlim → ℝ} {critLim : ℝ} {α : ℝ≥0∞}
    (hjoint :
      TendstoInDistribution
        (bootstrapAbsTestVector T crit)
        atTop
        (bootstrapAbsTestLimitVector ξ critLim)
        (fun _ => μ) ν)
    (hξ : HasLaw ξ η ν)
    (halpha : η {x | bootstrapAbsTestReject x critLim} = α) :
    Tendsto
      (fun n => μ {ω | bootstrapAbsTestReject (T n ω) (crit n ω)})
      atTop (𝓝 α) := by
  have hfrontier :=
    bootstrapAbsTest_frontier_null_of_hasLaw_noAtoms
      (ν := ν) (η := η) hξ critLim
  have halphaν :
      ν {ω | bootstrapAbsTestReject (ξ ω) critLim} = α := by
    rw [bootstrapAbsTest_scalar_rejection_eq_law hξ critLim]
    exact halpha
  exact
    chapter10_bootstrap_abs_test_rejectionProb_tendsto_alpha_of_scalar_limit_rejection
      (μ := μ) (ν := ν) (T := T) (crit := crit) (ξ := ξ) (critLim := critLim)
      hjoint hfrontier halphaν

/-- CDF-calibrated two-sided bootstrap-test bridge.

For a non-atomic scalar limit law and nonnegative critical value, the limiting
rejection probability can be supplied as
`1 - (F(q) - F(-q))`. -/
theorem chapter10_bootstrap_abs_test_rejectionProb_tendsto_alpha_of_limit_law_cdf
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {η : Measure ℝ} [IsProbabilityMeasure η] [NoAtoms η]
    {T crit : ℕ → Ω → ℝ} {ξ : Ωlim → ℝ} {critLim alpha : ℝ}
    (hjoint :
      TendstoInDistribution
        (bootstrapAbsTestVector T crit)
        atTop
        (bootstrapAbsTestLimitVector ξ critLim)
        (fun _ => μ) ν)
    (hξ : HasLaw ξ η ν)
    (hcrit : 0 ≤ critLim)
    (halpha : 1 - (cdf η critLim - cdf η (-critLim)) = alpha) :
    Tendsto
      (fun n => μ {ω | bootstrapAbsTestReject (T n ω) (crit n ω)})
      atTop (𝓝 (ENNReal.ofReal alpha)) := by
  refine
    chapter10_bootstrap_abs_test_rejectionProb_tendsto_alpha_of_limit_law
      (μ := μ) (ν := ν) (η := η) (T := T) (crit := crit)
      (ξ := ξ) (critLim := critLim) (α := ENNReal.ofReal alpha)
      hjoint hξ ?_
  rw [bootstrapAbsTest_rejection_law_eq_ofReal_one_sub_cdf
    (η := η) (critLim := critLim) hcrit, halpha]

/-- Endpoint-CDF two-sided bootstrap-test calibration with limiting size
`α`.  The endpoint premises encode the central interval mass
`F(q) - F(-q) = 1 - α`. -/
theorem chapter10_bootstrap_abs_test_rejectionProb_tendsto_alpha_of_limit_law_cdf_endpoints
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {η : Measure ℝ} [IsProbabilityMeasure η] [NoAtoms η]
    {T crit : ℕ → Ω → ℝ} {ξ : Ωlim → ℝ} {critLim α : ℝ}
    (hjoint :
      TendstoInDistribution
        (bootstrapAbsTestVector T crit)
        atTop
        (bootstrapAbsTestLimitVector ξ critLim)
        (fun _ => μ) ν)
    (hξ : HasLaw ξ η ν)
    (hcrit : 0 ≤ critLim)
    (hlower : cdf η (-critLim) = α / 2)
    (hupper : cdf η critLim = 1 - α / 2) :
    Tendsto
      (fun n => μ {ω | bootstrapAbsTestReject (T n ω) (crit n ω)})
      atTop (𝓝 (ENNReal.ofReal α)) := by
  refine
    chapter10_bootstrap_abs_test_rejectionProb_tendsto_alpha_of_limit_law_cdf
      (μ := μ) (ν := ν) (η := η) (T := T) (crit := crit)
      (ξ := ξ) (critLim := critLim) (alpha := α) hjoint hξ hcrit ?_
  rw [hlower, hupper]
  ring

/-- Componentwise endpoint-CDF two-sided bootstrap-test calibration with
limiting size `α`.

This is the Theorem 10.16 rejection bridge stated directly from statistic
convergence and bootstrap critical-value convergence in probability. -/
theorem chapter10_bootstrap_abs_test_rejectionProb_tendsto_alpha_of_components_law_cdf_endpoints
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {η : Measure ℝ} [IsProbabilityMeasure η] [NoAtoms η]
    {T crit : ℕ → Ω → ℝ} {ξ : Ωlim → ℝ} {critLim α : ℝ}
    (hT : TendstoInDistribution T atTop ξ (fun _ => μ) ν)
    (hcrit : TendstoInMeasure μ crit atTop (fun _ => critLim))
    (hcrit_meas : ∀ n, AEMeasurable (crit n) μ)
    (hξ : HasLaw ξ η ν)
    (hcrit_nonneg : 0 ≤ critLim)
    (hcdfLower : cdf η (-critLim) = α / 2)
    (hcdfUpper : cdf η critLim = 1 - α / 2) :
    Tendsto
      (fun n => μ {ω | bootstrapAbsTestReject (T n ω) (crit n ω)})
      atTop (𝓝 (ENNReal.ofReal α)) := by
  exact
    chapter10_bootstrap_abs_test_rejectionProb_tendsto_alpha_of_limit_law_cdf_endpoints
      (μ := μ) (ν := ν) (η := η) (T := T) (crit := crit)
      (ξ := ξ) (critLim := critLim) (α := α)
      (bootstrapAbsTestVector_tendstoInDistribution_of_components
        (μ := μ) (ν := ν) (T := T) (crit := crit)
        (ξ := ξ) (critLim := critLim)
      hT hcrit hcrit_meas)
      hξ hcrit_nonneg hcdfLower hcdfUpper

/-- Two-sided bootstrap-test calibration from a bootstrap lower critical
quantile, using local limit-CDF bracketing.

This is the non-strict-CDF version of the lower-generalized-inverse route for
Hansen Theorem 10.16.  It requires only that the limiting absolute-statistic
CDF lies below `1 - α` immediately to the left of `critLim` and above it
immediately to the right. -/
theorem
chapter10_bootstrap_abs_test_rejectionProb_tendsto_alpha_of_bootstrap_lowerQuantile_brackets
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {η : Measure ℝ} [IsProbabilityMeasure η] [NoAtoms η]
    {Pstar : ℕ → Ω → Measure Ωs} {Astar : ℕ → Ω → Ωs → ℝ}
    {T : ℕ → Ω → ℝ} {ξ : Ωlim → ℝ} {Gabs : ℝ → ℝ}
    {critLim α : ℝ}
    (hT : TendstoInDistribution T atTop ξ (fun _ => μ) ν)
    (hmono :
      ∀ n ω, Monotone (fun x => bootstrapScalarCDF Pstar Astar x n ω))
    (hne :
      ∀ n ω,
        ({x : ℝ | 1 - α ≤ bootstrapScalarCDF Pstar Astar x n ω} :
          Set ℝ).Nonempty)
    (hbdd :
      ∀ n ω, BddBelow
        {x : ℝ | 1 - α ≤ bootstrapScalarCDF Pstar Astar x n ω})
    (hlocal :
      ∀ n ω x, bootstrapScalarCDF Pstar Astar x n ω < 1 - α →
        ∃ δ : ℝ, 0 < δ ∧ bootstrapScalarCDF Pstar Astar (x + δ) n ω <
          1 - α)
    (hleft : ∀ ε : ℝ, 0 < ε → Gabs (critLim - ε) < 1 - α)
    (hright : ∀ ε : ℝ, 0 < ε → 1 - α < Gabs (critLim + ε))
    (hG :
      ∀ x : ℝ,
        TendstoInMeasure μ
          (fun n ω => bootstrapScalarCDF Pstar Astar x n ω)
          atTop (fun _ => Gabs x))
    (hcrit_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantile Pstar Astar (1 - α) n) μ)
    (hξ : HasLaw ξ η ν)
    (hcrit_nonneg : 0 ≤ critLim)
    (hcdfLower : cdf η (-critLim) = α / 2)
    (hcdfUpper : cdf η critLim = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | bootstrapAbsTestReject (T n ω)
          (bootstrapScalarLowerQuantile Pstar Astar (1 - α) n ω)})
      atTop (𝓝 (ENNReal.ofReal α)) := by
  have hcrit :
      TendstoInMeasure μ
        (bootstrapScalarLowerQuantile Pstar Astar (1 - α))
        atTop (fun _ => critLim) :=
    bootstrapScalarLowerQuantile_tendsto_of_cdf_brackets
      (μ := μ) (Pstar := Pstar) (Zstar := Astar)
      (G := Gabs) (p := 1 - α) (q := critLim)
      hmono hne hbdd hlocal hleft hright hG
  exact
    chapter10_bootstrap_abs_test_rejectionProb_tendsto_alpha_of_components_law_cdf_endpoints
      (μ := μ) (ν := ν) (η := η)
      (T := T) (crit := bootstrapScalarLowerQuantile Pstar Astar (1 - α))
      (ξ := ξ) (critLim := critLim) (α := α)
      hT hcrit hcrit_meas hξ hcrit_nonneg hcdfLower hcdfUpper

/-- If a probability law is supported on `[0, ∞)`, its CDF is zero at every
negative argument. -/
private theorem cdf_eq_zero_of_ae_nonneg
    {η : Measure ℝ} [IsProbabilityMeasure η]
    (hsupport : ∀ᵐ x ∂η, 0 ≤ x) {x : ℝ} (hx : x < 0) :
    cdf η x = 0 := by
  rw [ProbabilityTheory.cdf_eq_real]
  have hnot : ∀ᵐ y ∂η, y ∉ Set.Iic x := by
    filter_upwards [hsupport] with y hy hmem
    exact not_le_of_gt hx (le_trans hy hmem)
  have hnull : η (Set.Iic x) = 0 := by
    exact compl_mem_ae_iff.mp hnot
  rw [Measure.real, hnull]
  simp

/-- Local lower-quantile bracketing for a nonnegative-support law from
strictness on its nonnegative support. -/
private theorem cdf_brackets_of_ae_nonneg_strict
    {η : Measure ℝ} [IsProbabilityMeasure η]
    (hsupport : ∀ᵐ x ∂η, 0 ≤ x)
    {critLim α : ℝ}
    (hstrict_nonneg :
      ∀ {x y : ℝ}, 0 ≤ x → x < y → cdf η x < cdf η y)
    (hα_lt_one : α < 1)
    (hcrit_nonneg : 0 ≤ critLim)
    (hcritLevel : cdf η critLim = 1 - α) :
    (∀ ε : ℝ, 0 < ε → cdf η (critLim - ε) < 1 - α) ∧
      (∀ ε : ℝ, 0 < ε → 1 - α < cdf η (critLim + ε)) := by
  constructor
  · intro ε hε
    by_cases hq_nonneg : 0 ≤ critLim - ε
    · rw [← hcritLevel]
      exact hstrict_nonneg hq_nonneg (by linarith)
    · have hq_neg : critLim - ε < 0 := lt_of_not_ge hq_nonneg
      rw [cdf_eq_zero_of_ae_nonneg hsupport hq_neg]
      linarith
  · intro ε hε
    rw [← hcritLevel]
    exact hstrict_nonneg hcrit_nonneg (by linarith)

/-- Local lower-quantile bracketing for a law identified by a nonnegative
random variable on an auxiliary probability space. -/
private theorem cdf_brackets_of_hasLaw_ae_nonneg_strict
    {Ωstar : Type*} [MeasurableSpace Ωstar]
    {νstar : Measure Ωstar} {η : Measure ℝ} [IsProbabilityMeasure η]
    {Alim : Ωstar → ℝ}
    (hAlaw : HasLaw Alim η νstar)
    (hAlim_nonneg : ∀ᵐ ω ∂νstar, 0 ≤ Alim ω)
    {critLim α : ℝ}
    (hstrict_nonneg :
      ∀ {x y : ℝ}, 0 ≤ x → x < y → cdf η x < cdf η y)
    (hα_lt_one : α < 1)
    (hcrit_nonneg : 0 ≤ critLim)
    (hcritLevel : cdf η critLim = 1 - α) :
    (∀ ε : ℝ, 0 < ε → cdf η (critLim - ε) < 1 - α) ∧
      (∀ ε : ℝ, 0 < ε → 1 - α < cdf η (critLim + ε)) := by
  have hsupport : ∀ᵐ x ∂η, 0 ≤ x :=
    (hAlaw.ae_iff (p := fun x : ℝ => 0 ≤ x) (by fun_prop)).1 hAlim_nonneg
  exact
    cdf_brackets_of_ae_nonneg_strict hsupport hstrict_nonneg hα_lt_one
      hcrit_nonneg hcritLevel

/-- Two-sided bootstrap-test calibration from a bootstrap lower critical
quantile.

This is the theorem-facing quantile-identification route for Hansen Theorem
10.16.  A lower generalized inverse of a conditional bootstrap CDF at level
`1 - α` converges to the limiting critical value, and the existing
componentwise rejection bridge turns that into asymptotic size `α`. -/
theorem chapter10_bootstrap_abs_test_rejectionProb_tendsto_alpha_of_bootstrap_lowerQuantile
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {η : Measure ℝ} [IsProbabilityMeasure η] [NoAtoms η]
    {Pstar : ℕ → Ω → Measure Ωs} {Astar : ℕ → Ω → Ωs → ℝ}
    {T : ℕ → Ω → ℝ} {ξ : Ωlim → ℝ} {Gabs : ℝ → ℝ}
    {critLim α : ℝ}
    (hT : TendstoInDistribution T atTop ξ (fun _ => μ) ν)
    (hmono :
      ∀ n ω, Monotone (fun x => bootstrapScalarCDF Pstar Astar x n ω))
    (hne :
      ∀ n ω,
        ({x : ℝ | 1 - α ≤ bootstrapScalarCDF Pstar Astar x n ω} :
          Set ℝ).Nonempty)
    (hbdd :
      ∀ n ω, BddBelow
        {x : ℝ | 1 - α ≤ bootstrapScalarCDF Pstar Astar x n ω})
    (hlocal :
      ∀ n ω x, bootstrapScalarCDF Pstar Astar x n ω < 1 - α →
        ∃ δ : ℝ, 0 < δ ∧ bootstrapScalarCDF Pstar Astar (x + δ) n ω <
          1 - α)
    (hstrict : StrictMono Gabs)
    (hcritLevel : Gabs critLim = 1 - α)
    (hG :
      ∀ x : ℝ,
        TendstoInMeasure μ
          (fun n ω => bootstrapScalarCDF Pstar Astar x n ω)
          atTop (fun _ => Gabs x))
    (hcrit_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantile Pstar Astar (1 - α) n) μ)
    (hξ : HasLaw ξ η ν)
    (hcrit_nonneg : 0 ≤ critLim)
    (hcdfLower : cdf η (-critLim) = α / 2)
    (hcdfUpper : cdf η critLim = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | bootstrapAbsTestReject (T n ω)
          (bootstrapScalarLowerQuantile Pstar Astar (1 - α) n ω)})
      atTop (𝓝 (ENNReal.ofReal α)) := by
  have hcrit :
      TendstoInMeasure μ
        (bootstrapScalarLowerQuantile Pstar Astar (1 - α))
        atTop (fun _ => critLim) :=
    bootstrapScalarLowerQuantile_tendsto_of_strictMono_cdf
      (μ := μ) (Pstar := Pstar) (Zstar := Astar)
      (G := Gabs) (p := 1 - α) (q := critLim)
      hmono hne hbdd hlocal hstrict hcritLevel hG
  exact
    chapter10_bootstrap_abs_test_rejectionProb_tendsto_alpha_of_components_law_cdf_endpoints
      (μ := μ) (ν := ν) (η := η)
      (T := T) (crit := bootstrapScalarLowerQuantile Pstar Astar (1 - α))
      (ξ := ξ) (critLim := critLim) (α := α)
      hT hcrit hcrit_meas hξ hcrit_nonneg hcdfLower hcdfUpper

/-- Two-sided bootstrap-test calibration from bootstrap-distribution
convergence of the absolute bootstrap statistic.

The bootstrap critical value is a lower generalized inverse of the conditional
CDF of `Astar`.  The limiting CDF for that critical value is supplied by a
separate scalar law `ηAbs`, while the final rejection-size calibration still
uses the sample statistic law `η`. -/
theorem
    chapter10_bootstrap_abs_test_rejectionProb_tendsto_alpha_of_bootstrapDistribution_lowerQuantile
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {η ηAbs : Measure ℝ} [IsProbabilityMeasure η] [NoAtoms η]
    [IsProbabilityMeasure ηAbs]
    {Pstar : ℕ → Ω → Measure Ωs} {Astar : ℕ → Ω → Ωs → ℝ}
    {T : ℕ → Ω → ℝ} {ξ : Ωlim → ℝ} {critLim α : ℝ}
    (hT : TendstoInDistribution T atTop ξ (fun _ => μ) ν)
    (hPstar : ∀ n ω, IsFiniteMeasure (Pstar n ω))
    (hne :
      ∀ n ω,
        ({x : ℝ | 1 - α ≤ bootstrapScalarCDF Pstar Astar x n ω} :
          Set ℝ).Nonempty)
    (hbdd :
      ∀ n ω, BddBelow
        {x : ℝ | 1 - α ≤ bootstrapScalarCDF Pstar Astar x n ω})
    (hlocal :
      ∀ n ω x, bootstrapScalarCDF Pstar Astar x n ω < 1 - α →
        ∃ δ : ℝ, 0 < δ ∧ bootstrapScalarCDF Pstar Astar (x + δ) n ω <
          1 - α)
    (hstrictAbs : StrictMono (fun x => cdf ηAbs x))
    (hcritLevel : cdf ηAbs critLim = 1 - α)
    (hAstar :
      TendstoInBootstrapDistribution μ Pstar
        (fun n ω ωs (_ : Unit) => Astar n ω ωs) ηAbs
        (fun x (_ : Unit) => x))
    (hcontAbs : ∀ x : ℝ, ContinuousAt (fun y => cdf ηAbs y) x)
    (hcrit_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantile Pstar Astar (1 - α) n) μ)
    (hξ : HasLaw ξ η ν)
    (hcrit_nonneg : 0 ≤ critLim)
    (hcdfLower : cdf η (-critLim) = α / 2)
    (hcdfUpper : cdf η critLim = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | bootstrapAbsTestReject (T n ω)
          (bootstrapScalarLowerQuantile Pstar Astar (1 - α) n ω)})
      atTop (𝓝 (ENNReal.ofReal α)) := by
  have hmono :
      ∀ n ω, Monotone (fun x => bootstrapScalarCDF Pstar Astar x n ω) := by
    intro n ω
    haveI : IsFiniteMeasure (Pstar n ω) := hPstar n ω
    exact bootstrapScalarCDF_mono (Pstar := Pstar) (Zstar := Astar)
      (n := n) (ω := ω)
  have hG :
      ∀ x : ℝ,
        TendstoInMeasure μ
          (fun n ω => bootstrapScalarCDF Pstar Astar x n ω)
          atTop (fun _ => cdf ηAbs x) :=
    fun x =>
      hAstar.bootstrapScalarCDF_tendsto_unit_id_cdf
        (Pstar := Pstar) (Zstar := Astar) (x := x) (hcontAbs x)
  exact
    chapter10_bootstrap_abs_test_rejectionProb_tendsto_alpha_of_bootstrap_lowerQuantile
      (μ := μ) (ν := ν) (η := η) (Pstar := Pstar) (Astar := Astar)
      (T := T) (ξ := ξ) (Gabs := fun x => cdf ηAbs x)
      (critLim := critLim) (α := α)
      hT hmono hne hbdd hlocal hstrictAbs hcritLevel hG hcrit_meas hξ
      hcrit_nonneg hcdfLower hcdfUpper

/-- Two-sided bootstrap-test calibration from bootstrap-distribution
convergence of the absolute bootstrap statistic, using local limit-CDF
bracketing at the critical value.

This variant avoids a global strict-monotonicity requirement on the limiting
absolute-statistic CDF; it only needs the local lower-quantile bracketing
premises around `critLim`. -/
theorem
chapter10_bootstrap_abs_test_rejectionProb_tendsto_alpha_of_bootstrapDistribution_brackets
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {η ηAbs : Measure ℝ} [IsProbabilityMeasure η] [NoAtoms η]
    [IsProbabilityMeasure ηAbs]
    {Pstar : ℕ → Ω → Measure Ωs} {Astar : ℕ → Ω → Ωs → ℝ}
    {T : ℕ → Ω → ℝ} {ξ : Ωlim → ℝ} {critLim α : ℝ}
    (hT : TendstoInDistribution T atTop ξ (fun _ => μ) ν)
    (hPstar : ∀ n ω, IsFiniteMeasure (Pstar n ω))
    (hne :
      ∀ n ω,
        ({x : ℝ | 1 - α ≤ bootstrapScalarCDF Pstar Astar x n ω} :
          Set ℝ).Nonempty)
    (hbdd :
      ∀ n ω, BddBelow
        {x : ℝ | 1 - α ≤ bootstrapScalarCDF Pstar Astar x n ω})
    (hlocal :
      ∀ n ω x, bootstrapScalarCDF Pstar Astar x n ω < 1 - α →
        ∃ δ : ℝ, 0 < δ ∧ bootstrapScalarCDF Pstar Astar (x + δ) n ω <
          1 - α)
    (hleft :
      ∀ ε : ℝ, 0 < ε → cdf ηAbs (critLim - ε) < 1 - α)
    (hright :
      ∀ ε : ℝ, 0 < ε → 1 - α < cdf ηAbs (critLim + ε))
    (hAstar :
      TendstoInBootstrapDistribution μ Pstar
        (fun n ω ωs (_ : Unit) => Astar n ω ωs) ηAbs
        (fun x (_ : Unit) => x))
    (hcontAbs : ∀ x : ℝ, ContinuousAt (fun y => cdf ηAbs y) x)
    (hcrit_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantile Pstar Astar (1 - α) n) μ)
    (hξ : HasLaw ξ η ν)
    (hcrit_nonneg : 0 ≤ critLim)
    (hcdfLower : cdf η (-critLim) = α / 2)
    (hcdfUpper : cdf η critLim = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | bootstrapAbsTestReject (T n ω)
          (bootstrapScalarLowerQuantile Pstar Astar (1 - α) n ω)})
      atTop (𝓝 (ENNReal.ofReal α)) := by
  have hmono :
      ∀ n ω, Monotone (fun x => bootstrapScalarCDF Pstar Astar x n ω) := by
    intro n ω
    haveI : IsFiniteMeasure (Pstar n ω) := hPstar n ω
    exact bootstrapScalarCDF_mono (Pstar := Pstar) (Zstar := Astar)
      (n := n) (ω := ω)
  have hG :
      ∀ x : ℝ,
        TendstoInMeasure μ
          (fun n ω => bootstrapScalarCDF Pstar Astar x n ω)
          atTop (fun _ => cdf ηAbs x) :=
    fun x =>
      hAstar.bootstrapScalarCDF_tendsto_unit_id_cdf
        (Pstar := Pstar) (Zstar := Astar) (x := x) (hcontAbs x)
  exact
    chapter10_bootstrap_abs_test_rejectionProb_tendsto_alpha_of_bootstrap_lowerQuantile_brackets
      (μ := μ) (ν := ν) (η := η) (Pstar := Pstar) (Astar := Astar)
      (T := T) (ξ := ξ) (Gabs := fun x => cdf ηAbs x)
      (critLim := critLim) (α := α)
      hT hmono hne hbdd hlocal hleft hright hG hcrit_meas hξ
      hcrit_nonneg hcdfLower hcdfUpper

/-- Two-sided bootstrap-test calibration from bootstrap-distribution
convergence of the absolute bootstrap statistic, with probability-CDF
bracketing discharged at level `1 - α`.

For `0 < α < 1`, probability conditional bootstrap laws and pointwise
a.e.-measurability of `Astar` supply the lower generalized-inverse bracketing
premises. -/
theorem
chapter10_bootstrap_abs_test_rejectionProb_tendsto_alpha_of_bootstrapDistribution_quantile_prob
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {η ηAbs : Measure ℝ} [IsProbabilityMeasure η] [NoAtoms η]
    [IsProbabilityMeasure ηAbs]
    {Pstar : ℕ → Ω → Measure Ωs} {Astar : ℕ → Ω → Ωs → ℝ}
    {T : ℕ → Ω → ℝ} {ξ : Ωlim → ℝ} {critLim α : ℝ}
    (hT : TendstoInDistribution T atTop ξ (fun _ => μ) ν)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hAmeas : ∀ n ω, AEMeasurable (Astar n ω) (Pstar n ω))
    (hα_pos : 0 < α) (hα_lt_one : α < 1)
    (hstrictAbs : StrictMono (fun x => cdf ηAbs x))
    (hcritLevel : cdf ηAbs critLim = 1 - α)
    (hAstar :
      TendstoInBootstrapDistribution μ Pstar
        (fun n ω ωs (_ : Unit) => Astar n ω ωs) ηAbs
        (fun x (_ : Unit) => x))
    (hcontAbs : ∀ x : ℝ, ContinuousAt (fun y => cdf ηAbs y) x)
    (hcrit_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantile Pstar Astar (1 - α) n) μ)
    (hξ : HasLaw ξ η ν)
    (hcrit_nonneg : 0 ≤ critLim)
    (hcdfLower : cdf η (-critLim) = α / 2)
    (hcdfUpper : cdf η critLim = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | bootstrapAbsTestReject (T n ω)
          (bootstrapScalarLowerQuantile Pstar Astar (1 - α) n ω)})
      atTop (𝓝 (ENNReal.ofReal α)) := by
  have hPstarFinite : ∀ n ω, IsFiniteMeasure (Pstar n ω) := by
    intro n ω
    haveI : IsProbabilityMeasure (Pstar n ω) := hPstar n ω
    infer_instance
  exact
    chapter10_bootstrap_abs_test_rejectionProb_tendsto_alpha_of_bootstrapDistribution_lowerQuantile
      (μ := μ) (ν := ν) (η := η) (ηAbs := ηAbs) (Pstar := Pstar)
      (Astar := Astar) (T := T) (ξ := ξ) (critLim := critLim)
      (α := α) hT hPstarFinite
      (bootstrapScalarCDF_level_nonempty_of_aemeasurable
        (Pstar := Pstar) (Zstar := Astar) hPstar hAmeas
        (by linarith : 1 - α < 1))
      (bootstrapScalarCDF_level_bddBelow_of_aemeasurable
        (Pstar := Pstar) (Zstar := Astar) hPstar hAmeas
        (by linarith : 0 < 1 - α))
      (bootstrapScalarCDF_local_right_lt_of_aemeasurable
        (Pstar := Pstar) (Zstar := Astar) hPstar hAmeas)
      hstrictAbs hcritLevel hAstar hcontAbs hcrit_meas hξ hcrit_nonneg
      hcdfLower hcdfUpper

/-- Two-sided bootstrap-test calibration from a bootstrap distribution whose
absolute-statistic scalar limit has law `ηAbs`.

The absolute bootstrap statistic may converge on an auxiliary probability
space; `HasLaw` identifies its scalar CDF for the lower critical-value
quantile route. -/
theorem
chapter10_bootstrap_abs_test_rejectionProb_law_quantile_prob
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {Ωstar : Type*} [MeasurableSpace Ωstar]
    {η ηAbs : Measure ℝ} [IsProbabilityMeasure η] [NoAtoms η]
    [IsProbabilityMeasure ηAbs]
    {νstar : Measure Ωstar} {Alim : Ωstar → ℝ}
    {Pstar : ℕ → Ω → Measure Ωs} {Astar : ℕ → Ω → Ωs → ℝ}
    {T : ℕ → Ω → ℝ} {ξ : Ωlim → ℝ} {critLim α : ℝ}
    (hT : TendstoInDistribution T atTop ξ (fun _ => μ) ν)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hAmeas : ∀ n ω, AEMeasurable (Astar n ω) (Pstar n ω))
    (hα_pos : 0 < α) (hα_lt_one : α < 1)
    (hstrictAbs : StrictMono (fun x => cdf ηAbs x))
    (hcritLevel : cdf ηAbs critLim = 1 - α)
    (hAstar :
      TendstoInBootstrapDistribution μ Pstar
        (fun n ω ωs (_ : Unit) => Astar n ω ωs) νstar
        (fun ωstar (_ : Unit) => Alim ωstar))
    (hAlaw : HasLaw Alim ηAbs νstar)
    (hcontAbs : ∀ x : ℝ, ContinuousAt (fun y => cdf ηAbs y) x)
    (hcrit_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantile Pstar Astar (1 - α) n) μ)
    (hξ : HasLaw ξ η ν)
    (hcrit_nonneg : 0 ≤ critLim)
    (hcdfLower : cdf η (-critLim) = α / 2)
    (hcdfUpper : cdf η critLim = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | bootstrapAbsTestReject (T n ω)
          (bootstrapScalarLowerQuantile Pstar Astar (1 - α) n ω)})
      atTop (𝓝 (ENNReal.ofReal α)) := by
  obtain ⟨hleft, hright⟩ :=
    strictMono_cdf_brackets hstrictAbs hcritLevel
  let crit : ℕ → Ω → ℝ :=
    bootstrapScalarLowerQuantile Pstar Astar (1 - α)
  have hcrit :
      TendstoInMeasure μ crit atTop (fun _ => critLim) := by
    simpa [crit] using
      bootstrapScalarLowerQuantile_tendsto_of_bootstrapDistribution_unit_law_cdf_probability
        (μ := μ) (Pstar := Pstar) (Zstar := Astar)
        (ν := νstar) (Z := Alim) (η := ηAbs)
        (p := 1 - α) (q := critLim)
        hPstar hAmeas (by linarith : 0 < 1 - α)
        (by linarith : 1 - α < 1)
        hleft hright hAstar hAlaw hcontAbs
  have hcrit_meas' : ∀ n, AEMeasurable (crit n) μ := by
    intro n
    simpa [crit] using hcrit_meas n
  have hreject :=
    chapter10_bootstrap_abs_test_rejectionProb_tendsto_alpha_of_components_law_cdf_endpoints
      (μ := μ) (ν := ν) (η := η) (T := T) (crit := crit)
      (ξ := ξ) (critLim := critLim) (α := α)
      hT hcrit hcrit_meas' hξ hcrit_nonneg hcdfLower hcdfUpper
  simpa [crit] using hreject

/-- Two-sided bootstrap-test calibration from an auxiliary
absolute-statistic limit, retaining local CDF bracketing at the lower
critical-value endpoint.

This law-facing variant is the local-bracketing counterpart of
`chapter10_bootstrap_abs_test_rejectionProb_law_quantile_prob`: `HasLaw`
identifies the auxiliary absolute-statistic limit's scalar CDF with `cdf ηAbs`
without requiring global strict monotonicity of that CDF. -/
theorem
chapter10_bootstrap_abs_test_rejectionProb_law_quantile_prob_brackets
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {Ωstar : Type*} [MeasurableSpace Ωstar]
    {η ηAbs : Measure ℝ} [IsProbabilityMeasure η] [NoAtoms η]
    [IsProbabilityMeasure ηAbs]
    {νstar : Measure Ωstar} {Alim : Ωstar → ℝ}
    {Pstar : ℕ → Ω → Measure Ωs} {Astar : ℕ → Ω → Ωs → ℝ}
    {T : ℕ → Ω → ℝ} {ξ : Ωlim → ℝ} {critLim α : ℝ}
    (hT : TendstoInDistribution T atTop ξ (fun _ => μ) ν)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hAmeas : ∀ n ω, AEMeasurable (Astar n ω) (Pstar n ω))
    (hα_pos : 0 < α) (hα_lt_one : α < 1)
    (hleft :
      ∀ ε : ℝ, 0 < ε → cdf ηAbs (critLim - ε) < 1 - α)
    (hright :
      ∀ ε : ℝ, 0 < ε → 1 - α < cdf ηAbs (critLim + ε))
    (hAstar :
      TendstoInBootstrapDistribution μ Pstar
        (fun n ω ωs (_ : Unit) => Astar n ω ωs) νstar
        (fun ωstar (_ : Unit) => Alim ωstar))
    (hAlaw : HasLaw Alim ηAbs νstar)
    (hcontAbs : ∀ x : ℝ, ContinuousAt (fun y => cdf ηAbs y) x)
    (hcrit_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantile Pstar Astar (1 - α) n) μ)
    (hξ : HasLaw ξ η ν)
    (hcrit_nonneg : 0 ≤ critLim)
    (hcdfLower : cdf η (-critLim) = α / 2)
    (hcdfUpper : cdf η critLim = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | bootstrapAbsTestReject (T n ω)
          (bootstrapScalarLowerQuantile Pstar Astar (1 - α) n ω)})
      atTop (𝓝 (ENNReal.ofReal α)) := by
  let crit : ℕ → Ω → ℝ :=
    bootstrapScalarLowerQuantile Pstar Astar (1 - α)
  have hcrit :
      TendstoInMeasure μ crit atTop (fun _ => critLim) := by
    simpa [crit] using
      bootstrapScalarLowerQuantile_tendsto_of_bootstrapDistribution_unit_law_cdf_probability
        (μ := μ) (Pstar := Pstar) (Zstar := Astar)
        (ν := νstar) (Z := Alim) (η := ηAbs)
        (p := 1 - α) (q := critLim)
        hPstar hAmeas (by linarith : 0 < 1 - α)
        (by linarith : 1 - α < 1)
        hleft hright hAstar hAlaw hcontAbs
  have hcrit_meas' : ∀ n, AEMeasurable (crit n) μ := by
    intro n
    simpa [crit] using hcrit_meas n
  have hreject :=
    chapter10_bootstrap_abs_test_rejectionProb_tendsto_alpha_of_components_law_cdf_endpoints
      (μ := μ) (ν := ν) (η := η) (T := T) (crit := crit)
      (ξ := ξ) (critLim := critLim) (α := α)
      hT hcrit hcrit_meas' hξ hcrit_nonneg hcdfLower hcdfUpper
  simpa [crit] using hreject

/-- Fixed-space law-facing two-sided bootstrap-test calibration for an
absolute-statistic limit that is nonnegative almost surely.

This is the support-aware strict-CDF counterpart of
`chapter10_bootstrap_abs_test_rejectionProb_law_quantile_prob_brackets`.
It uses `HasLaw` to transport nonnegative support from the auxiliary limit
variable to `ηAbs`, then only requires strictness of `cdf ηAbs` on that support. -/
theorem
chapter10_bootstrap_abs_test_rejectionProb_law_quantile_prob_nonneg_strict
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {Ωstar : Type*} [MeasurableSpace Ωstar]
    {η ηAbs : Measure ℝ} [IsProbabilityMeasure η] [NoAtoms η]
    [IsProbabilityMeasure ηAbs]
    {νstar : Measure Ωstar} {Alim : Ωstar → ℝ}
    {Pstar : ℕ → Ω → Measure Ωs} {Astar : ℕ → Ω → Ωs → ℝ}
    {T : ℕ → Ω → ℝ} {ξ : Ωlim → ℝ} {critLim α : ℝ}
    (hT : TendstoInDistribution T atTop ξ (fun _ => μ) ν)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hAmeas : ∀ n ω, AEMeasurable (Astar n ω) (Pstar n ω))
    (hα_pos : 0 < α) (hα_lt_one : α < 1)
    (hstrictAbs_nonneg :
      ∀ {x y : ℝ}, 0 ≤ x → x < y → cdf ηAbs x < cdf ηAbs y)
    (hcritLevel : cdf ηAbs critLim = 1 - α)
    (hAstar :
      TendstoInBootstrapDistribution μ Pstar
        (fun n ω ωs (_ : Unit) => Astar n ω ωs) νstar
        (fun ωstar (_ : Unit) => Alim ωstar))
    (hAlaw : HasLaw Alim ηAbs νstar)
    (hAlim_nonneg : ∀ᵐ ωstar ∂νstar, 0 ≤ Alim ωstar)
    (hcontAbs : ∀ x : ℝ, ContinuousAt (fun y => cdf ηAbs y) x)
    (hcrit_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantile Pstar Astar (1 - α) n) μ)
    (hξ : HasLaw ξ η ν)
    (hcrit_nonneg : 0 ≤ critLim)
    (hcdfLower : cdf η (-critLim) = α / 2)
    (hcdfUpper : cdf η critLim = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | bootstrapAbsTestReject (T n ω)
          (bootstrapScalarLowerQuantile Pstar Astar (1 - α) n ω)})
      atTop (𝓝 (ENNReal.ofReal α)) := by
  obtain ⟨hleft, hright⟩ :=
    cdf_brackets_of_hasLaw_ae_nonneg_strict hAlaw hAlim_nonneg
      hstrictAbs_nonneg hα_lt_one hcrit_nonneg hcritLevel
  exact
    chapter10_bootstrap_abs_test_rejectionProb_law_quantile_prob_brackets
      (μ := μ) (ν := ν) (η := η) (ηAbs := ηAbs)
      (νstar := νstar) (Alim := Alim) (Pstar := Pstar)
      (Astar := Astar) (T := T) (ξ := ξ) (critLim := critLim)
      (α := α) hT hPstar hAmeas hα_pos hα_lt_one hleft hright
      hAstar hAlaw hcontAbs hcrit_meas hξ hcrit_nonneg hcdfLower
      hcdfUpper

/-- Two-sided bootstrap-test calibration from bootstrap-distribution
convergence of the absolute bootstrap statistic, with bootstrap-side
probability-CDF bracketing discharged and local limit-CDF bracketing retained.

This is the probability-level version of
`chapter10_bootstrap_abs_test_rejectionProb_tendsto_alpha_of_bootstrapDistribution_brackets`.
It avoids the global strict-CDF assumption on the limiting absolute-statistic
law. -/
theorem
chapter10_bootstrap_abs_test_quantile_prob_brackets
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {η ηAbs : Measure ℝ} [IsProbabilityMeasure η] [NoAtoms η]
    [IsProbabilityMeasure ηAbs]
    {Pstar : ℕ → Ω → Measure Ωs} {Astar : ℕ → Ω → Ωs → ℝ}
    {T : ℕ → Ω → ℝ} {ξ : Ωlim → ℝ} {critLim α : ℝ}
    (hT : TendstoInDistribution T atTop ξ (fun _ => μ) ν)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hAmeas : ∀ n ω, AEMeasurable (Astar n ω) (Pstar n ω))
    (hα_pos : 0 < α) (hα_lt_one : α < 1)
    (hleft :
      ∀ ε : ℝ, 0 < ε → cdf ηAbs (critLim - ε) < 1 - α)
    (hright :
      ∀ ε : ℝ, 0 < ε → 1 - α < cdf ηAbs (critLim + ε))
    (hAstar :
      TendstoInBootstrapDistribution μ Pstar
        (fun n ω ωs (_ : Unit) => Astar n ω ωs) ηAbs
        (fun x (_ : Unit) => x))
    (hcontAbs : ∀ x : ℝ, ContinuousAt (fun y => cdf ηAbs y) x)
    (hcrit_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantile Pstar Astar (1 - α) n) μ)
    (hξ : HasLaw ξ η ν)
    (hcrit_nonneg : 0 ≤ critLim)
    (hcdfLower : cdf η (-critLim) = α / 2)
    (hcdfUpper : cdf η critLim = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | bootstrapAbsTestReject (T n ω)
          (bootstrapScalarLowerQuantile Pstar Astar (1 - α) n ω)})
      atTop (𝓝 (ENNReal.ofReal α)) := by
  have hPstarFinite : ∀ n ω, IsFiniteMeasure (Pstar n ω) := by
    intro n ω
    haveI : IsProbabilityMeasure (Pstar n ω) := hPstar n ω
    infer_instance
  exact
    chapter10_bootstrap_abs_test_rejectionProb_tendsto_alpha_of_bootstrapDistribution_brackets
      (μ := μ) (ν := ν) (η := η) (ηAbs := ηAbs) (Pstar := Pstar)
      (Astar := Astar) (T := T) (ξ := ξ) (critLim := critLim)
      (α := α) hT hPstarFinite
      (bootstrapScalarCDF_level_nonempty_of_aemeasurable
        (Pstar := Pstar) (Zstar := Astar) hPstar hAmeas
        (by linarith : 1 - α < 1))
      (bootstrapScalarCDF_level_bddBelow_of_aemeasurable
        (Pstar := Pstar) (Zstar := Astar) hPstar hAmeas
        (by linarith : 0 < 1 - α))
      (bootstrapScalarCDF_local_right_lt_of_aemeasurable
        (Pstar := Pstar) (Zstar := Astar) hPstar hAmeas)
      hleft hright hAstar hcontAbs hcrit_meas hξ hcrit_nonneg
      hcdfLower hcdfUpper

/-- Fixed-space two-sided bootstrap-test calibration for a limiting absolute
bootstrap statistic whose law is supported on `[0, ∞)`.

This support-aware strict-CDF route is the absolute-statistic counterpart of
`chapter10_bootstrap_abs_test_quantile_prob_brackets`: it replaces global
strict monotonicity of `cdf ηAbs` by strictness on the nonnegative support and
the critical-value level equation. -/
theorem
chapter10_bootstrap_abs_test_quantile_prob_nonneg_strict
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {η ηAbs : Measure ℝ} [IsProbabilityMeasure η] [NoAtoms η]
    [IsProbabilityMeasure ηAbs]
    {Pstar : ℕ → Ω → Measure Ωs} {Astar : ℕ → Ω → Ωs → ℝ}
    {T : ℕ → Ω → ℝ} {ξ : Ωlim → ℝ} {critLim α : ℝ}
    (hT : TendstoInDistribution T atTop ξ (fun _ => μ) ν)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hAmeas : ∀ n ω, AEMeasurable (Astar n ω) (Pstar n ω))
    (hα_pos : 0 < α) (hα_lt_one : α < 1)
    (hsupportAbs : ∀ᵐ x ∂ηAbs, 0 ≤ x)
    (hstrictAbs_nonneg :
      ∀ {x y : ℝ}, 0 ≤ x → x < y → cdf ηAbs x < cdf ηAbs y)
    (hcritLevel : cdf ηAbs critLim = 1 - α)
    (hAstar :
      TendstoInBootstrapDistribution μ Pstar
        (fun n ω ωs (_ : Unit) => Astar n ω ωs) ηAbs
        (fun x (_ : Unit) => x))
    (hcontAbs : ∀ x : ℝ, ContinuousAt (fun y => cdf ηAbs y) x)
    (hcrit_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantile Pstar Astar (1 - α) n) μ)
    (hξ : HasLaw ξ η ν)
    (hcrit_nonneg : 0 ≤ critLim)
    (hcdfLower : cdf η (-critLim) = α / 2)
    (hcdfUpper : cdf η critLim = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | bootstrapAbsTestReject (T n ω)
          (bootstrapScalarLowerQuantile Pstar Astar (1 - α) n ω)})
      atTop (𝓝 (ENNReal.ofReal α)) := by
  obtain ⟨hleft, hright⟩ :=
    cdf_brackets_of_ae_nonneg_strict hsupportAbs hstrictAbs_nonneg
      hα_lt_one hcrit_nonneg hcritLevel
  exact
    chapter10_bootstrap_abs_test_quantile_prob_brackets
      (μ := μ) (ν := ν) (η := η) (ηAbs := ηAbs) (Pstar := Pstar)
      (Astar := Astar) (T := T) (ξ := ξ) (critLim := critLim)
      (α := α) hT hPstar hAmeas hα_pos hα_lt_one hleft hright
      hAstar hcontAbs hcrit_meas hξ hcrit_nonneg hcdfLower hcdfUpper

variable {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]

/-- Indexed two-sided bootstrap-test calibration from bootstrap-distribution
convergence of the absolute bootstrap statistic, with bootstrap-side
probability-CDF bracketing discharged and local limit-CDF bracketing retained.

This is the sample-size-indexed counterpart of
`chapter10_bootstrap_abs_test_quantile_prob_brackets`, for ordinary
nonparametric bootstrap laws whose resampling spaces vary with `n`. -/
theorem
chapter10_bootstrap_abs_test_rejectionProb_tendsto_alpha_indexed_quantile_prob_brackets
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {η ηAbs : Measure ℝ} [IsProbabilityMeasure η] [NoAtoms η]
    [IsProbabilityMeasure ηAbs]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Astar : ∀ n, Ω → Ωboot n → ℝ}
    {T : ℕ → Ω → ℝ} {ξ : Ωlim → ℝ} {critLim α : ℝ}
    (hT : TendstoInDistribution T atTop ξ (fun _ => μ) ν)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hAmeas : ∀ n ω, AEMeasurable (Astar n ω) (Pstar n ω))
    (hα_pos : 0 < α) (hα_lt_one : α < 1)
    (hleft :
      ∀ ε : ℝ, 0 < ε → cdf ηAbs (critLim - ε) < 1 - α)
    (hright :
      ∀ ε : ℝ, 0 < ε → 1 - α < cdf ηAbs (critLim + ε))
    (hAstar :
      TendstoInBootstrapDistributionIndexed μ Pstar
        (fun n ω ωs (_ : Unit) => Astar n ω ωs) ηAbs
        (fun x (_ : Unit) => x))
    (hcontAbs : ∀ x : ℝ, ContinuousAt (fun y => cdf ηAbs y) x)
    (hcrit_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed Pstar Astar (1 - α) n) μ)
    (hξ : HasLaw ξ η ν)
    (hcrit_nonneg : 0 ≤ critLim)
    (hcdfLower : cdf η (-critLim) = α / 2)
    (hcdfUpper : cdf η critLim = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | bootstrapAbsTestReject (T n ω)
          (bootstrapScalarLowerQuantileIndexed Pstar Astar (1 - α) n ω)})
      atTop (𝓝 (ENNReal.ofReal α)) := by
  let crit : ℕ → Ω → ℝ :=
    bootstrapScalarLowerQuantileIndexed Pstar Astar (1 - α)
  have hcrit :
      TendstoInMeasure μ crit atTop (fun _ => critLim) :=
    bootstrapScalarLowerQuantileIndexed_tendsto_of_bootstrapDistribution_unit_id_cdf_probability
      (μ := μ) (Pstar := Pstar) (Zstar := Astar) (η := ηAbs)
      (p := 1 - α) (q := critLim)
      hPstar hAmeas (by linarith : 0 < 1 - α)
      (by linarith : 1 - α < 1)
      hleft hright hAstar hcontAbs
  have hcrit_meas' : ∀ n, AEMeasurable (crit n) μ := by
    intro n
    simpa [crit] using hcrit_meas n
  have hreject :=
    chapter10_bootstrap_abs_test_rejectionProb_tendsto_alpha_of_components_law_cdf_endpoints
      (μ := μ) (ν := ν) (η := η) (T := T) (crit := crit)
      (ξ := ξ) (critLim := critLim) (α := α)
      hT hcrit hcrit_meas' hξ hcrit_nonneg hcdfLower hcdfUpper
  simpa [crit] using hreject

/-- Indexed two-sided bootstrap-test calibration for a limiting absolute
bootstrap statistic whose law is supported on `[0, ∞)`.

This support-aware strict-CDF route replaces global strict monotonicity of
`cdf ηAbs` by strictness on the nonnegative support and the critical-value
level equation. -/
theorem
chapter10_bootstrap_abs_test_rejectionProb_tendsto_alpha_indexed_quantile_prob_nonneg_strict
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {η ηAbs : Measure ℝ} [IsProbabilityMeasure η] [NoAtoms η]
    [IsProbabilityMeasure ηAbs]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Astar : ∀ n, Ω → Ωboot n → ℝ}
    {T : ℕ → Ω → ℝ} {ξ : Ωlim → ℝ} {critLim α : ℝ}
    (hT : TendstoInDistribution T atTop ξ (fun _ => μ) ν)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hAmeas : ∀ n ω, AEMeasurable (Astar n ω) (Pstar n ω))
    (hα_pos : 0 < α) (hα_lt_one : α < 1)
    (hsupportAbs : ∀ᵐ x ∂ηAbs, 0 ≤ x)
    (hstrictAbs_nonneg :
      ∀ {x y : ℝ}, 0 ≤ x → x < y → cdf ηAbs x < cdf ηAbs y)
    (hcritLevel : cdf ηAbs critLim = 1 - α)
    (hAstar :
      TendstoInBootstrapDistributionIndexed μ Pstar
        (fun n ω ωs (_ : Unit) => Astar n ω ωs) ηAbs
        (fun x (_ : Unit) => x))
    (hcontAbs : ∀ x : ℝ, ContinuousAt (fun y => cdf ηAbs y) x)
    (hcrit_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed Pstar Astar (1 - α) n) μ)
    (hξ : HasLaw ξ η ν)
    (hcrit_nonneg : 0 ≤ critLim)
    (hcdfLower : cdf η (-critLim) = α / 2)
    (hcdfUpper : cdf η critLim = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | bootstrapAbsTestReject (T n ω)
          (bootstrapScalarLowerQuantileIndexed Pstar Astar (1 - α) n ω)})
      atTop (𝓝 (ENNReal.ofReal α)) := by
  obtain ⟨hleft, hright⟩ :=
    cdf_brackets_of_ae_nonneg_strict hsupportAbs hstrictAbs_nonneg
      hα_lt_one hcrit_nonneg hcritLevel
  exact
    chapter10_bootstrap_abs_test_rejectionProb_tendsto_alpha_indexed_quantile_prob_brackets
      (μ := μ) (ν := ν) (η := η) (ηAbs := ηAbs) (Pstar := Pstar)
      (Astar := Astar) (T := T) (ξ := ξ) (critLim := critLim)
      (α := α) hT hPstar hAmeas hα_pos hα_lt_one hleft hright
      hAstar hcontAbs hcrit_meas hξ hcrit_nonneg hcdfLower hcdfUpper

/-- Indexed two-sided bootstrap-test calibration from bootstrap-distribution
convergence of the absolute bootstrap statistic, with probability-CDF
bracketing discharged at level `1 - α`.

This is the strict-CDF counterpart of
`chapter10_bootstrap_abs_test_rejectionProb_tendsto_alpha_indexed_quantile_prob_brackets`. -/
theorem
chapter10_bootstrap_abs_test_rejectionProb_tendsto_alpha_indexed_bootstrapDistribution_quantile_prob
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {η ηAbs : Measure ℝ} [IsProbabilityMeasure η] [NoAtoms η]
    [IsProbabilityMeasure ηAbs]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Astar : ∀ n, Ω → Ωboot n → ℝ}
    {T : ℕ → Ω → ℝ} {ξ : Ωlim → ℝ} {critLim α : ℝ}
    (hT : TendstoInDistribution T atTop ξ (fun _ => μ) ν)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hAmeas : ∀ n ω, AEMeasurable (Astar n ω) (Pstar n ω))
    (hα_pos : 0 < α) (hα_lt_one : α < 1)
    (hstrictAbs : StrictMono (fun x => cdf ηAbs x))
    (hcritLevel : cdf ηAbs critLim = 1 - α)
    (hAstar :
      TendstoInBootstrapDistributionIndexed μ Pstar
        (fun n ω ωs (_ : Unit) => Astar n ω ωs) ηAbs
        (fun x (_ : Unit) => x))
    (hcontAbs : ∀ x : ℝ, ContinuousAt (fun y => cdf ηAbs y) x)
    (hcrit_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed Pstar Astar (1 - α) n) μ)
    (hξ : HasLaw ξ η ν)
    (hcrit_nonneg : 0 ≤ critLim)
    (hcdfLower : cdf η (-critLim) = α / 2)
    (hcdfUpper : cdf η critLim = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | bootstrapAbsTestReject (T n ω)
          (bootstrapScalarLowerQuantileIndexed Pstar Astar (1 - α) n ω)})
      atTop (𝓝 (ENNReal.ofReal α)) := by
  obtain ⟨hleft, hright⟩ :=
    strictMono_cdf_brackets hstrictAbs hcritLevel
  exact
    chapter10_bootstrap_abs_test_rejectionProb_tendsto_alpha_indexed_quantile_prob_brackets
      (μ := μ) (ν := ν) (η := η) (ηAbs := ηAbs) (Pstar := Pstar)
      (Astar := Astar) (T := T) (ξ := ξ) (critLim := critLim)
      (α := α) hT hPstar hAmeas hα_pos hα_lt_one hleft hright
      hAstar hcontAbs hcrit_meas hξ hcrit_nonneg hcdfLower hcdfUpper

/-- Indexed two-sided bootstrap-test calibration from a bootstrap distribution
whose absolute-statistic scalar limit has law `ηAbs`.

This sample-size-dependent law-facing wrapper lets the absolute bootstrap
statistic converge on an auxiliary probability space while `HasLaw` supplies
the scalar CDF used by the lower critical-value quantile route. -/
theorem
chapter10_indexed_abs_test_rejectionProb_law_quantile_prob
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {Ωstar : Type*} [MeasurableSpace Ωstar]
    {η ηAbs : Measure ℝ} [IsProbabilityMeasure η] [NoAtoms η]
    [IsProbabilityMeasure ηAbs]
    {νstar : Measure Ωstar} {Alim : Ωstar → ℝ}
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Astar : ∀ n, Ω → Ωboot n → ℝ}
    {T : ℕ → Ω → ℝ} {ξ : Ωlim → ℝ} {critLim α : ℝ}
    (hT : TendstoInDistribution T atTop ξ (fun _ => μ) ν)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hAmeas : ∀ n ω, AEMeasurable (Astar n ω) (Pstar n ω))
    (hα_pos : 0 < α) (hα_lt_one : α < 1)
    (hstrictAbs : StrictMono (fun x => cdf ηAbs x))
    (hcritLevel : cdf ηAbs critLim = 1 - α)
    (hAstar :
      TendstoInBootstrapDistributionIndexed μ Pstar
        (fun n ω ωs (_ : Unit) => Astar n ω ωs) νstar
        (fun ωstar (_ : Unit) => Alim ωstar))
    (hAlaw : HasLaw Alim ηAbs νstar)
    (hcontAbs : ∀ x : ℝ, ContinuousAt (fun y => cdf ηAbs y) x)
    (hcrit_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed Pstar Astar (1 - α) n) μ)
    (hξ : HasLaw ξ η ν)
    (hcrit_nonneg : 0 ≤ critLim)
    (hcdfLower : cdf η (-critLim) = α / 2)
    (hcdfUpper : cdf η critLim = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | bootstrapAbsTestReject (T n ω)
          (bootstrapScalarLowerQuantileIndexed Pstar Astar (1 - α) n ω)})
      atTop (𝓝 (ENNReal.ofReal α)) := by
  obtain ⟨hleft, hright⟩ :=
    strictMono_cdf_brackets hstrictAbs hcritLevel
  let crit : ℕ → Ω → ℝ :=
    bootstrapScalarLowerQuantileIndexed Pstar Astar (1 - α)
  have hcrit :
      TendstoInMeasure μ crit atTop (fun _ => critLim) := by
    simpa [crit] using
      bootstrapScalarLowerQuantileIndexed_tendsto_of_bootstrapDistribution_unit_law_cdf_probability
        (μ := μ) (Pstar := Pstar) (Zstar := Astar)
        (ν := νstar) (Z := Alim) (η := ηAbs)
        (p := 1 - α) (q := critLim)
        hPstar hAmeas (by linarith : 0 < 1 - α)
        (by linarith : 1 - α < 1)
        hleft hright hAstar hAlaw hcontAbs
  have hcrit_meas' : ∀ n, AEMeasurable (crit n) μ := by
    intro n
    simpa [crit] using hcrit_meas n
  have hreject :=
    chapter10_bootstrap_abs_test_rejectionProb_tendsto_alpha_of_components_law_cdf_endpoints
      (μ := μ) (ν := ν) (η := η) (T := T) (crit := crit)
      (ξ := ξ) (critLim := critLim) (α := α)
      hT hcrit hcrit_meas' hξ hcrit_nonneg hcdfLower hcdfUpper
  simpa [crit] using hreject

/-- Indexed two-sided bootstrap-test calibration from an auxiliary
absolute-statistic limit, retaining local CDF bracketing at the lower
critical-value endpoint.

This sample-size-dependent law-facing wrapper is the indexed counterpart of
`chapter10_bootstrap_abs_test_rejectionProb_law_quantile_prob_brackets`. -/
theorem
chapter10_indexed_abs_test_rejectionProb_law_quantile_prob_brackets
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {Ωstar : Type*} [MeasurableSpace Ωstar]
    {η ηAbs : Measure ℝ} [IsProbabilityMeasure η] [NoAtoms η]
    [IsProbabilityMeasure ηAbs]
    {νstar : Measure Ωstar} {Alim : Ωstar → ℝ}
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Astar : ∀ n, Ω → Ωboot n → ℝ}
    {T : ℕ → Ω → ℝ} {ξ : Ωlim → ℝ} {critLim α : ℝ}
    (hT : TendstoInDistribution T atTop ξ (fun _ => μ) ν)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hAmeas : ∀ n ω, AEMeasurable (Astar n ω) (Pstar n ω))
    (hα_pos : 0 < α) (hα_lt_one : α < 1)
    (hleft :
      ∀ ε : ℝ, 0 < ε → cdf ηAbs (critLim - ε) < 1 - α)
    (hright :
      ∀ ε : ℝ, 0 < ε → 1 - α < cdf ηAbs (critLim + ε))
    (hAstar :
      TendstoInBootstrapDistributionIndexed μ Pstar
        (fun n ω ωs (_ : Unit) => Astar n ω ωs) νstar
        (fun ωstar (_ : Unit) => Alim ωstar))
    (hAlaw : HasLaw Alim ηAbs νstar)
    (hcontAbs : ∀ x : ℝ, ContinuousAt (fun y => cdf ηAbs y) x)
    (hcrit_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed Pstar Astar (1 - α) n) μ)
    (hξ : HasLaw ξ η ν)
    (hcrit_nonneg : 0 ≤ critLim)
    (hcdfLower : cdf η (-critLim) = α / 2)
    (hcdfUpper : cdf η critLim = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | bootstrapAbsTestReject (T n ω)
          (bootstrapScalarLowerQuantileIndexed Pstar Astar (1 - α) n ω)})
      atTop (𝓝 (ENNReal.ofReal α)) := by
  let crit : ℕ → Ω → ℝ :=
    bootstrapScalarLowerQuantileIndexed Pstar Astar (1 - α)
  have hcrit :
      TendstoInMeasure μ crit atTop (fun _ => critLim) := by
    simpa [crit] using
      bootstrapScalarLowerQuantileIndexed_tendsto_of_bootstrapDistribution_unit_law_cdf_probability
        (μ := μ) (Pstar := Pstar) (Zstar := Astar)
        (ν := νstar) (Z := Alim) (η := ηAbs)
        (p := 1 - α) (q := critLim)
        hPstar hAmeas (by linarith : 0 < 1 - α)
        (by linarith : 1 - α < 1)
        hleft hright hAstar hAlaw hcontAbs
  have hcrit_meas' : ∀ n, AEMeasurable (crit n) μ := by
    intro n
    simpa [crit] using hcrit_meas n
  have hreject :=
    chapter10_bootstrap_abs_test_rejectionProb_tendsto_alpha_of_components_law_cdf_endpoints
      (μ := μ) (ν := ν) (η := η) (T := T) (crit := crit)
      (ξ := ξ) (critLim := critLim) (α := α)
      hT hcrit hcrit_meas' hξ hcrit_nonneg hcdfLower hcdfUpper
  simpa [crit] using hreject

/-- Indexed law-facing two-sided bootstrap-test calibration for an
absolute-statistic limit that is nonnegative almost surely.

This is the support-aware strict-CDF counterpart of
`chapter10_indexed_abs_test_rejectionProb_law_quantile_prob_brackets`.
It uses `HasLaw` to transport nonnegative support from the auxiliary limit
variable to `ηAbs`, then only requires strictness of `cdf ηAbs` on that support. -/
theorem
chapter10_indexed_abs_test_rejectionProb_law_quantile_prob_nonneg_strict
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {Ωstar : Type*} [MeasurableSpace Ωstar]
    {η ηAbs : Measure ℝ} [IsProbabilityMeasure η] [NoAtoms η]
    [IsProbabilityMeasure ηAbs]
    {νstar : Measure Ωstar} {Alim : Ωstar → ℝ}
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Astar : ∀ n, Ω → Ωboot n → ℝ}
    {T : ℕ → Ω → ℝ} {ξ : Ωlim → ℝ} {critLim α : ℝ}
    (hT : TendstoInDistribution T atTop ξ (fun _ => μ) ν)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hAmeas : ∀ n ω, AEMeasurable (Astar n ω) (Pstar n ω))
    (hα_pos : 0 < α) (hα_lt_one : α < 1)
    (hstrictAbs_nonneg :
      ∀ {x y : ℝ}, 0 ≤ x → x < y → cdf ηAbs x < cdf ηAbs y)
    (hcritLevel : cdf ηAbs critLim = 1 - α)
    (hAstar :
      TendstoInBootstrapDistributionIndexed μ Pstar
        (fun n ω ωs (_ : Unit) => Astar n ω ωs) νstar
        (fun ωstar (_ : Unit) => Alim ωstar))
    (hAlaw : HasLaw Alim ηAbs νstar)
    (hAlim_nonneg : ∀ᵐ ωstar ∂νstar, 0 ≤ Alim ωstar)
    (hcontAbs : ∀ x : ℝ, ContinuousAt (fun y => cdf ηAbs y) x)
    (hcrit_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed Pstar Astar (1 - α) n) μ)
    (hξ : HasLaw ξ η ν)
    (hcrit_nonneg : 0 ≤ critLim)
    (hcdfLower : cdf η (-critLim) = α / 2)
    (hcdfUpper : cdf η critLim = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | bootstrapAbsTestReject (T n ω)
          (bootstrapScalarLowerQuantileIndexed Pstar Astar (1 - α) n ω)})
      atTop (𝓝 (ENNReal.ofReal α)) := by
  obtain ⟨hleft, hright⟩ :=
    cdf_brackets_of_hasLaw_ae_nonneg_strict hAlaw hAlim_nonneg
      hstrictAbs_nonneg hα_lt_one hcrit_nonneg hcritLevel
  exact
    chapter10_indexed_abs_test_rejectionProb_law_quantile_prob_brackets
      (μ := μ) (ν := ν) (η := η) (ηAbs := ηAbs)
      (νstar := νstar) (Alim := Alim) (Pstar := Pstar)
      (Astar := Astar) (T := T) (ξ := ξ) (critLim := critLim)
      (α := α) hT hPstar hAmeas hα_pos hα_lt_one hleft hright
      hAstar hAlaw hcontAbs hcrit_meas hξ hcrit_nonneg hcdfLower
      hcdfUpper

/-- Indexed ordinary nonparametric-bootstrap two-sided critical-value test from
the concrete normalized scalar `Fin (n+1)` resample-mean CLT.

The bootstrap critical value is the lower generalized inverse of the
conditional CDF of `|sqrt(n+1) (Ybar*_n - Ybar_n)|` under the finite ordinary
resampling law.  The sample-side statistic convergence and endpoint
calibration are kept explicit, matching Hansen Theorem 10.16. -/
theorem
chapter10_indexed_abs_test_resampleMean_of_iIndep_tail_posDef_brackets
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {η ηAbs : Measure ℝ} [IsProbabilityMeasure η] [NoAtoms η]
    [IsProbabilityMeasure ηAbs] [NoAtoms ηAbs]
    (Y : ℕ → Ω → ℝ)
    (hYmem : MemLp (Y 0) 2 μ)
    (hindep : iIndepFun Y μ)
    (hident : ∀ i, IdentDistrib (Y i) (Y 0) μ μ)
    (hS : (covMat μ (fun ω (_ : Unit) => Y 0 ω)).PosDef)
    {T : ℕ → Ω → ℝ} {ξ : Ωlim → ℝ} {critLim α : ℝ}
    (hT : TendstoInDistribution T atTop ξ (fun _ => μ) ν)
    (hα_pos : 0 < α) (hα_lt_one : α < 1)
    (hleft :
      ∀ ε : ℝ, 0 < ε → cdf ηAbs (critLim - ε) < 1 - α)
    (hright :
      ∀ ε : ℝ, 0 < ε → 1 - α < cdf ηAbs (critLim + ε))
    (hcontAbs : ∀ x : ℝ, ContinuousAt (fun y => cdf ηAbs y) x)
    (hcrit_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed
            (fun n _ =>
              (ProbabilityTheory.uniformOn
                (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                  Measure (Fin (n + 1) → Fin (n + 1))))
            (fun n ω ωs =>
              |Real.sqrt (n + 1 : ℝ) *
                (empiricalBootstrapResampleMean
                    (fun i : Fin (n + 1) => Y i.val ω)
                    (fun ωs t => ωs t) ωs -
                  empiricalMean (fun i : Fin (n + 1) => Y i.val ω))|)
            (1 - α) n) μ)
    (hξ : HasLaw ξ η ν)
    (hAlaw :
      HasLaw
        (fun z : EuclideanSpace ℝ Unit => |(z : Unit → ℝ) ()|)
        ηAbs
        (multivariateGaussian (0 : EuclideanSpace ℝ Unit)
          (covMat μ (fun ω (_ : Unit) => Y 0 ω))))
    (hcrit_nonneg : 0 ≤ critLim)
    (hcdfLower : cdf η (-critLim) = α / 2)
    (hcdfUpper : cdf η critLim = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | bootstrapAbsTestReject (T n ω)
          (bootstrapScalarLowerQuantileIndexed
            (fun n _ =>
              (ProbabilityTheory.uniformOn
                (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                  Measure (Fin (n + 1) → Fin (n + 1))))
            (fun n ω ωs =>
              |Real.sqrt (n + 1 : ℝ) *
                (empiricalBootstrapResampleMean
                    (fun i : Fin (n + 1) => Y i.val ω)
                    (fun ωs t => ωs t) ωs -
                  empiricalMean (fun i : Fin (n + 1) => Y i.val ω))|)
            (1 - α) n ω)})
      atTop (𝓝 (ENNReal.ofReal α)) := by
  let Pstar : ∀ n, Ω → Measure (Fin (n + 1) → Fin (n + 1)) :=
    fun n _ =>
      (ProbabilityTheory.uniformOn
        (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
          Measure (Fin (n + 1) → Fin (n + 1)))
  let scalarStat : ∀ n, Ω → (Fin (n + 1) → Fin (n + 1)) → ℝ :=
    fun n ω ωs =>
      Real.sqrt (n + 1 : ℝ) *
        (empiricalBootstrapResampleMean
            (fun i : Fin (n + 1) => Y i.val ω)
            (fun ωs t => ωs t) ωs -
          empiricalMean (fun i : Fin (n + 1) => Y i.val ω))
  let Astar : ∀ n, Ω → (Fin (n + 1) → Fin (n + 1)) → ℝ :=
    fun n ω ωs => |scalarStat n ω ωs|
  let νstar : Measure (EuclideanSpace ℝ Unit) :=
    multivariateGaussian (0 : EuclideanSpace ℝ Unit)
      (covMat μ (fun ω (_ : Unit) => Y 0 ω))
  let Alim : EuclideanSpace ℝ Unit → ℝ :=
    fun z => |(z : Unit → ℝ) ()|
  have hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω) := by
    intro n ω
    dsimp [Pstar]
    infer_instance
  have hAmeas : ∀ n ω, AEMeasurable (Astar n ω) (Pstar n ω) := by
    intro n ω
    exact (measurable_of_finite _).aemeasurable
  have hweakScalar :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar scalarStat νstar
        (fun z : EuclideanSpace ℝ Unit => (z : Unit → ℝ) ()) := by
    simpa [Pstar, scalarStat, νstar] using
      chapter10_indexed_bootstrap_weak_clt_scalar_finSucc_resampleMean_of_iIndep_tail_posDef
        (μ := μ) Y hYmem hindep hident hS
  have hweakAbsScalar :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar Astar νstar Alim := by
    have hmap :=
      chapter10_indexed_bootstrap_continuous_mapping_distribution
        (μ := μ) (Pstar := Pstar) (Zstar := scalarStat) (ν := νstar)
        (Z := fun z : EuclideanSpace ℝ Unit => (z : Unit → ℝ) ())
        (g := fun x : ℝ => |x|) hweakScalar continuous_abs
    simpa [Astar, Alim] using hmap
  have hunitCont : Continuous (fun x : ℝ => fun _ : Unit => x) := by
    refine continuous_pi ?_
    intro _
    exact continuous_id
  have hweakUnit :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar
        (fun n ω ωs => fun _ : Unit => Astar n ω ωs)
        νstar
        (fun z : EuclideanSpace ℝ Unit => fun _ : Unit => Alim z) := by
    exact
      chapter10_indexed_bootstrap_continuous_mapping_distribution
        (μ := μ) (Pstar := Pstar) (Zstar := Astar) (ν := νstar)
        (Z := Alim) (g := fun x : ℝ => fun _ : Unit => x)
        hweakAbsScalar hunitCont
  have hPfinite : ∀ n ω, IsFiniteMeasure (Pstar n ω) := by
    intro n ω
    haveI : IsProbabilityMeasure (Pstar n ω) := hPstar n ω
    infer_instance
  have hZstar :
      ∀ n ω, Measurable (fun ωs => fun _ : Unit => Astar n ω ωs) := by
    intro n ω
    exact measurable_of_finite _
  have hZlim :
      AEMeasurable
        (fun z : EuclideanSpace ℝ Unit => fun _ : Unit => Alim z)
        νstar := by
    refine aemeasurable_pi_lambda _ ?_
    intro _
    simpa [νstar, Alim] using hAlaw.aemeasurable
  have hfrontier :
      ∀ x : Unit → ℝ,
        ContinuousAt
          (fun y =>
            vectorCDF νstar
              (fun z : EuclideanSpace ℝ Unit => fun _ : Unit => Alim z) y) x →
        (νstar.map
          (fun z : EuclideanSpace ℝ Unit => fun _ : Unit => Alim z))
          (frontier {z : Unit → ℝ | coordinateLE z x}) = 0 := by
    intro x _hx
    refine map_measure_frontier_coordinateLE_eq_zero_of_coord_singletons
      (ν := νstar)
      (Z := fun z : EuclideanSpace ℝ Unit => fun _ : Unit => Alim z)
      hZlim x ?_
    intro i
    have hpre :
        {z : EuclideanSpace ℝ Unit |
          (fun z : EuclideanSpace ℝ Unit => fun _ : Unit => Alim z) z i =
            x i} =
          Alim ⁻¹' {x i} := by
      ext z
      simp
    rw [hpre, HasLaw.preimage_eq hAlaw (measurableSet_singleton (x i))]
    exact measure_singleton (x i)
  have hAstarDist :
      TendstoInBootstrapDistributionIndexed μ Pstar
        (fun n ω ωs (_ : Unit) => Astar n ω ωs)
        νstar
        (fun z : EuclideanSpace ℝ Unit => fun _ : Unit => Alim z) := by
    exact
      TendstoInBootstrapDistributionIndexed.of_weakDistribution_null_frontiers
        (μ := μ) (Pstar := Pstar)
        (Zstar := fun n ω ωs (_ : Unit) => Astar n ω ωs)
        (ν := νstar)
        (Z := fun z : EuclideanSpace ℝ Unit => fun _ : Unit => Alim z)
        hweakUnit hPfinite hZstar hZlim hfrontier
  have hcrit_meas' :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed Pstar Astar (1 - α) n) μ := by
    intro n
    simpa [Pstar, Astar, scalarStat] using hcrit_meas n
  have hreject :=
    chapter10_indexed_abs_test_rejectionProb_law_quantile_prob_brackets
      (μ := μ) (ν := ν)
      (Ωstar := EuclideanSpace ℝ Unit)
      (η := η) (ηAbs := ηAbs) (νstar := νstar) (Alim := Alim)
      (Pstar := Pstar) (Astar := Astar) (T := T) (ξ := ξ)
      (critLim := critLim) (α := α)
      hT hPstar hAmeas hα_pos hα_lt_one hleft hright
      hAstarDist hAlaw hcontAbs hcrit_meas' hξ hcrit_nonneg
      hcdfLower hcdfUpper
  simpa [Pstar, Astar, scalarStat] using hreject

/-- Strict-CDF counterpart of
`chapter10_indexed_abs_test_resampleMean_of_iIndep_tail_posDef_brackets`.

Strict monotonicity on the nonnegative support of the absolute-statistic limit
CDF supplies the local critical-value bracketing needed by the concrete
ordinary-bootstrap two-sided test constructor. -/
theorem
chapter10_indexed_abs_test_resampleMean_of_iIndep_tail_posDef
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {η ηAbs : Measure ℝ} [IsProbabilityMeasure η] [NoAtoms η]
    [IsProbabilityMeasure ηAbs] [NoAtoms ηAbs]
    (Y : ℕ → Ω → ℝ)
    (hYmem : MemLp (Y 0) 2 μ)
    (hindep : iIndepFun Y μ)
    (hident : ∀ i, IdentDistrib (Y i) (Y 0) μ μ)
    (hS : (covMat μ (fun ω (_ : Unit) => Y 0 ω)).PosDef)
    {T : ℕ → Ω → ℝ} {ξ : Ωlim → ℝ} {critLim α : ℝ}
    (hT : TendstoInDistribution T atTop ξ (fun _ => μ) ν)
    (hα_pos : 0 < α) (hα_lt_one : α < 1)
    (hstrictAbs_nonneg :
      ∀ {x y : ℝ}, 0 ≤ x → x < y → cdf ηAbs x < cdf ηAbs y)
    (hcritLevel : cdf ηAbs critLim = 1 - α)
    (hcontAbs : ∀ x : ℝ, ContinuousAt (fun y => cdf ηAbs y) x)
    (hcrit_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed
            (fun n _ =>
              (ProbabilityTheory.uniformOn
                (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                  Measure (Fin (n + 1) → Fin (n + 1))))
            (fun n ω ωs =>
              |Real.sqrt (n + 1 : ℝ) *
                (empiricalBootstrapResampleMean
                    (fun i : Fin (n + 1) => Y i.val ω)
                    (fun ωs t => ωs t) ωs -
                  empiricalMean (fun i : Fin (n + 1) => Y i.val ω))|)
            (1 - α) n) μ)
    (hξ : HasLaw ξ η ν)
    (hAlaw :
      HasLaw
        (fun z : EuclideanSpace ℝ Unit => |(z : Unit → ℝ) ()|)
        ηAbs
        (multivariateGaussian (0 : EuclideanSpace ℝ Unit)
          (covMat μ (fun ω (_ : Unit) => Y 0 ω))))
    (hcrit_nonneg : 0 ≤ critLim)
    (hcdfLower : cdf η (-critLim) = α / 2)
    (hcdfUpper : cdf η critLim = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | bootstrapAbsTestReject (T n ω)
          (bootstrapScalarLowerQuantileIndexed
            (fun n _ =>
              (ProbabilityTheory.uniformOn
                (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                  Measure (Fin (n + 1) → Fin (n + 1))))
            (fun n ω ωs =>
              |Real.sqrt (n + 1 : ℝ) *
                (empiricalBootstrapResampleMean
                    (fun i : Fin (n + 1) => Y i.val ω)
                    (fun ωs t => ωs t) ωs -
                  empiricalMean (fun i : Fin (n + 1) => Y i.val ω))|)
            (1 - α) n ω)})
      atTop (𝓝 (ENNReal.ofReal α)) := by
  obtain ⟨hleft, hright⟩ :=
    cdf_brackets_of_hasLaw_ae_nonneg_strict hAlaw
      (ae_of_all _ fun z => abs_nonneg ((z : Unit → ℝ) ()))
      hstrictAbs_nonneg hα_lt_one hcrit_nonneg hcritLevel
  exact
    chapter10_indexed_abs_test_resampleMean_of_iIndep_tail_posDef_brackets
      (μ := μ) (ν := ν) (η := η) (ηAbs := ηAbs)
      Y hYmem hindep hident hS
      (T := T) (ξ := ξ) (critLim := critLim) (α := α)
      hT hα_pos hα_lt_one hleft hright hcontAbs hcrit_meas hξ hAlaw
      hcrit_nonneg hcdfLower hcdfUpper

/-- Regression-facing two-sided bootstrap-test calibration from the Theorem
10.18 t-statistic route.

The bootstrap critical value is the lower generalized inverse of the
conditional law of `|TthetaStar / seThetaStar|`.  The joint
numerator/standard-error bootstrap weak limit and scale consistency give the
absolute-standard-normal bootstrap CDF limit, and the existing Theorem 10.16
quantile route then gives rejection probability `α`. -/
theorem
chapter10_bootstrap_abs_test_rejectionProb_tendsto_alpha_of_bootstrap_regression_tstat
    [IsProbabilityMeasure μ]
    {Pstar : ℕ → Ω → Measure Ωs}
    {TthetaStar seThetaStar : ℕ → Ω → Ωs → ℝ}
    {T : ℕ → Ω → ℝ} {seθ critLim α : ℝ}
    (hT :
      TendstoInDistribution T atTop (fun x : ℝ => x) (fun _ => μ)
        (gaussianReal 0 1))
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
    (hleft :
      ∀ ε : ℝ, 0 < ε →
        cdf ((gaussianReal 0 1).map (fun z : ℝ => |z|)) (critLim - ε) <
          1 - α)
    (hright :
      ∀ ε : ℝ, 0 < ε →
        1 - α <
          cdf ((gaussianReal 0 1).map (fun z : ℝ => |z|)) (critLim + ε))
    (hcrit_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantile Pstar
            (fun n ω ωs => |TthetaStar n ω ωs / seThetaStar n ω ωs|)
            (1 - α) n) μ)
    (hcrit_nonneg : 0 ≤ critLim)
    (hcdfLower : cdf (gaussianReal 0 1) (-critLim) = α / 2)
    (hcdfUpper : cdf (gaussianReal 0 1) critLim = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | bootstrapAbsTestReject (T n ω)
          (bootstrapScalarLowerQuantile Pstar
            (fun n ω ωs => |TthetaStar n ω ωs / seThetaStar n ω ωs|)
            (1 - α) n ω)})
      atTop (𝓝 (ENNReal.ofReal α)) := by
  let Astar : ℕ → Ω → Ωs → ℝ :=
    fun n ω ωs => |TthetaStar n ω ωs / seThetaStar n ω ωs|
  haveI : NoAtoms (gaussianReal 0 1) :=
    noAtoms_gaussianReal (μ := 0) (v := 1) (by norm_num)
  letI :
      IsProbabilityMeasure ((gaussianReal 0 1).map (fun z : ℝ => |z|)) :=
    Measure.isProbabilityMeasure_map continuous_abs.aemeasurable
  have hAmeas : ∀ n ω, AEMeasurable (Astar n ω) (Pstar n ω) := by
    intro n ω
    exact
      (continuous_abs.measurable.comp
        ((hTthetaStar n ω).div (hseThetaStar n ω))).aemeasurable
  have hAstar :
      TendstoInBootstrapDistribution μ Pstar
        (fun n ω ωs (_ : Unit) => Astar n ω ωs)
        ((gaussianReal 0 1).map (fun z : ℝ => |z|))
        (fun x : ℝ => fun _ : Unit => x) := by
    simpa [Astar] using
      chapter10_bootstrap_regression_abs_tstat_distribution_standardNormalAbs
        (μ := μ) (Pstar := Pstar) (TthetaStar := TthetaStar)
        (seThetaStar := seThetaStar) (seθ := seθ)
        hseθ hjoint hPstar hTthetaStar hseThetaStar hseStar
  have hcrit_meas' :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantile Pstar Astar (1 - α) n) μ := by
    intro n
    simpa [Astar] using hcrit_meas n
  have hξ : HasLaw (fun x : ℝ => x) (gaussianReal 0 1) (gaussianReal 0 1) := by
    simpa [id] using (HasLaw.id (μ := gaussianReal 0 1))
  have hreject :=
    chapter10_bootstrap_abs_test_quantile_prob_brackets
      (μ := μ) (ν := gaussianReal 0 1) (η := gaussianReal 0 1)
      (ηAbs := (gaussianReal 0 1).map (fun z : ℝ => |z|))
      (Pstar := Pstar) (Astar := Astar) (T := T)
      (ξ := fun x : ℝ => x) (critLim := critLim) (α := α)
      hT hPstar hAmeas hα_pos hα_lt_one hleft hright hAstar
      (fun x => continuousAt_cdf_standardNormalAbs x) hcrit_meas' hξ
      hcrit_nonneg hcdfLower hcdfUpper
  simpa [Astar] using hreject

/-- Indexed regression-facing two-sided bootstrap-test calibration from the
Theorem 10.18 t-statistic route for sample-size-dependent bootstrap spaces. -/
theorem
chapter10_bootstrap_abs_test_rejectionProb_tendsto_alpha_indexed_of_bootstrap_regression_tstat
    [IsProbabilityMeasure μ]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {TthetaStar seThetaStar : ∀ n, Ω → Ωboot n → ℝ}
    {T : ℕ → Ω → ℝ} {seθ critLim α : ℝ}
    (hT :
      TendstoInDistribution T atTop (fun x : ℝ => x) (fun _ => μ)
        (gaussianReal 0 1))
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
    (hleft :
      ∀ ε : ℝ, 0 < ε →
        cdf ((gaussianReal 0 1).map (fun z : ℝ => |z|)) (critLim - ε) <
          1 - α)
    (hright :
      ∀ ε : ℝ, 0 < ε →
        1 - α <
          cdf ((gaussianReal 0 1).map (fun z : ℝ => |z|)) (critLim + ε))
    (hcrit_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed Pstar
            (fun n ω ωs => |TthetaStar n ω ωs / seThetaStar n ω ωs|)
            (1 - α) n) μ)
    (hcrit_nonneg : 0 ≤ critLim)
    (hcdfLower : cdf (gaussianReal 0 1) (-critLim) = α / 2)
    (hcdfUpper : cdf (gaussianReal 0 1) critLim = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | bootstrapAbsTestReject (T n ω)
          (bootstrapScalarLowerQuantileIndexed Pstar
            (fun n ω ωs => |TthetaStar n ω ωs / seThetaStar n ω ωs|)
            (1 - α) n ω)})
      atTop (𝓝 (ENNReal.ofReal α)) := by
  let Astar : ∀ n, Ω → Ωboot n → ℝ :=
    fun n ω ωs => |TthetaStar n ω ωs / seThetaStar n ω ωs|
  haveI : NoAtoms (gaussianReal 0 1) :=
    noAtoms_gaussianReal (μ := 0) (v := 1) (by norm_num)
  letI :
      IsProbabilityMeasure ((gaussianReal 0 1).map (fun z : ℝ => |z|)) :=
    Measure.isProbabilityMeasure_map continuous_abs.aemeasurable
  have hAmeas : ∀ n ω, AEMeasurable (Astar n ω) (Pstar n ω) := by
    intro n ω
    exact
      (continuous_abs.measurable.comp
        ((hTthetaStar n ω).div (hseThetaStar n ω))).aemeasurable
  have hAstar :
      TendstoInBootstrapDistributionIndexed μ Pstar
        (fun n ω ωs (_ : Unit) => Astar n ω ωs)
        ((gaussianReal 0 1).map (fun z : ℝ => |z|))
        (fun x : ℝ => fun _ : Unit => x) := by
    simpa [Astar] using
      chapter10_indexed_bootstrap_regression_abs_tstat_distribution_standardNormalAbs
        (μ := μ) (Pstar := Pstar) (TthetaStar := TthetaStar)
        (seThetaStar := seThetaStar) (seθ := seθ)
        hseθ hjoint hPstar hTthetaStar hseThetaStar hseStar
  have hcrit_meas' :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed Pstar Astar (1 - α) n) μ := by
    intro n
    simpa [Astar] using hcrit_meas n
  have hξ : HasLaw (fun x : ℝ => x) (gaussianReal 0 1) (gaussianReal 0 1) := by
    simpa [id] using (HasLaw.id (μ := gaussianReal 0 1))
  have hreject :=
    chapter10_bootstrap_abs_test_rejectionProb_tendsto_alpha_indexed_quantile_prob_brackets
      (μ := μ) (ν := gaussianReal 0 1) (η := gaussianReal 0 1)
      (ηAbs := (gaussianReal 0 1).map (fun z : ℝ => |z|))
      (Pstar := Pstar) (Astar := Astar) (T := T)
      (ξ := fun x : ℝ => x) (critLim := critLim) (α := α)
      hT hPstar hAmeas hα_pos hα_lt_one hleft hright hAstar
      (fun x => continuousAt_cdf_standardNormalAbs x) hcrit_meas' hξ
      hcrit_nonneg hcdfLower hcdfUpper
  simpa [Astar] using hreject

/-- Regression-facing two-sided bootstrap-test calibration from a marginal
numerator CLT plus explicit numerator/standard-error compact-tail control.

The `*_of_numerator_tight` studentized absolute-t CDF route from Theorem 10.18
supplies the bootstrap critical-value convergence required by the Theorem 10.16
test-size theorem. -/
theorem
chapter10_bootstrap_abs_test_rejectionProb_of_regression_tstat_numerator_tight
    [IsProbabilityMeasure μ]
    {Pstar : ℕ → Ω → Measure Ωs}
    {TthetaStar seThetaStar : ℕ → Ω → Ωs → ℝ}
    {T : ℕ → Ω → ℝ} {seθ critLim α : ℝ}
    (hTsample :
      TendstoInDistribution T atTop (fun x : ℝ => x) (fun _ => μ)
        (gaussianReal 0 1))
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
    (hleft :
      ∀ ε : ℝ, 0 < ε →
        cdf ((gaussianReal 0 1).map (fun z : ℝ => |z|)) (critLim - ε) <
          1 - α)
    (hright :
      ∀ ε : ℝ, 0 < ε →
        1 - α <
          cdf ((gaussianReal 0 1).map (fun z : ℝ => |z|)) (critLim + ε))
    (hcrit_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantile Pstar
            (fun n ω ωs => |TthetaStar n ω ωs / seThetaStar n ω ωs|)
            (1 - α) n) μ)
    (hcrit_nonneg : 0 ≤ critLim)
    (hcdfLower : cdf (gaussianReal 0 1) (-critLim) = α / 2)
    (hcdfUpper : cdf (gaussianReal 0 1) critLim = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | bootstrapAbsTestReject (T n ω)
          (bootstrapScalarLowerQuantile Pstar
            (fun n ω ωs => |TthetaStar n ω ωs / seThetaStar n ω ωs|)
            (1 - α) n ω)})
      atTop (𝓝 (ENNReal.ofReal α)) := by
  let Astar : ℕ → Ω → Ωs → ℝ :=
    fun n ω ωs => |TthetaStar n ω ωs / seThetaStar n ω ωs|
  haveI : NoAtoms (gaussianReal 0 1) :=
    noAtoms_gaussianReal (μ := 0) (v := 1) (by norm_num)
  letI :
      IsProbabilityMeasure ((gaussianReal 0 1).map (fun z : ℝ => |z|)) :=
    Measure.isProbabilityMeasure_map continuous_abs.aemeasurable
  have hAmeas : ∀ n ω, AEMeasurable (Astar n ω) (Pstar n ω) := by
    intro n ω
    exact
      (continuous_abs.measurable.comp
        ((hTthetaStar n ω).div (hseThetaStar n ω))).aemeasurable
  have hAstar :
      TendstoInBootstrapDistribution μ Pstar
        (fun n ω ωs (_ : Unit) => Astar n ω ωs)
        ((gaussianReal 0 1).map (fun z : ℝ => |z|))
        (fun x : ℝ => fun _ : Unit => x) := by
    simpa [Astar] using
      chapter10_bootstrap_regression_abs_tstat_distribution_standardNormalAbs_of_numerator_tight
        (μ := μ) (Pstar := Pstar) (TthetaStar := TthetaStar)
        (seThetaStar := seThetaStar) (seθ := seθ)
        hseθ hT hPstar hTthetaStar hseThetaStar hTail hseStar
  have hcrit_meas' :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantile Pstar Astar (1 - α) n) μ := by
    intro n
    simpa [Astar] using hcrit_meas n
  have hξ : HasLaw (fun x : ℝ => x) (gaussianReal 0 1) (gaussianReal 0 1) := by
    simpa [id] using (HasLaw.id (μ := gaussianReal 0 1))
  have hreject :=
    chapter10_bootstrap_abs_test_quantile_prob_brackets
      (μ := μ) (ν := gaussianReal 0 1) (η := gaussianReal 0 1)
      (ηAbs := (gaussianReal 0 1).map (fun z : ℝ => |z|))
      (Pstar := Pstar) (Astar := Astar) (T := T)
      (ξ := fun x : ℝ => x) (critLim := critLim) (α := α)
      hTsample hPstar hAmeas hα_pos hα_lt_one hleft hright hAstar
      (fun x => continuousAt_cdf_standardNormalAbs x) hcrit_meas' hξ
      hcrit_nonneg hcdfLower hcdfUpper
  simpa [Astar] using hreject

set_option linter.style.longLine false in
/-- Indexed regression-facing two-sided bootstrap-test calibration from a
marginal numerator CLT plus explicit numerator/standard-error compact-tail
control. -/
theorem
chapter10_indexed_abs_test_rejectionProb_of_regression_tstat_numerator_tight
    [IsProbabilityMeasure μ]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {TthetaStar seThetaStar : ∀ n, Ω → Ωboot n → ℝ}
    {T : ℕ → Ω → ℝ} {seθ critLim α : ℝ}
    (hTsample :
      TendstoInDistribution T atTop (fun x : ℝ => x) (fun _ => μ)
        (gaussianReal 0 1))
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
    (hleft :
      ∀ ε : ℝ, 0 < ε →
        cdf ((gaussianReal 0 1).map (fun z : ℝ => |z|)) (critLim - ε) <
          1 - α)
    (hright :
      ∀ ε : ℝ, 0 < ε →
        1 - α <
          cdf ((gaussianReal 0 1).map (fun z : ℝ => |z|)) (critLim + ε))
    (hcrit_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed Pstar
            (fun n ω ωs => |TthetaStar n ω ωs / seThetaStar n ω ωs|)
            (1 - α) n) μ)
    (hcrit_nonneg : 0 ≤ critLim)
    (hcdfLower : cdf (gaussianReal 0 1) (-critLim) = α / 2)
    (hcdfUpper : cdf (gaussianReal 0 1) critLim = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | bootstrapAbsTestReject (T n ω)
          (bootstrapScalarLowerQuantileIndexed Pstar
            (fun n ω ωs => |TthetaStar n ω ωs / seThetaStar n ω ωs|)
            (1 - α) n ω)})
      atTop (𝓝 (ENNReal.ofReal α)) := by
  let Astar : ∀ n, Ω → Ωboot n → ℝ :=
    fun n ω ωs => |TthetaStar n ω ωs / seThetaStar n ω ωs|
  haveI : NoAtoms (gaussianReal 0 1) :=
    noAtoms_gaussianReal (μ := 0) (v := 1) (by norm_num)
  letI :
      IsProbabilityMeasure ((gaussianReal 0 1).map (fun z : ℝ => |z|)) :=
    Measure.isProbabilityMeasure_map continuous_abs.aemeasurable
  have hAmeas : ∀ n ω, AEMeasurable (Astar n ω) (Pstar n ω) := by
    intro n ω
    exact
      (continuous_abs.measurable.comp
        ((hTthetaStar n ω).div (hseThetaStar n ω))).aemeasurable
  have hAstar :
      TendstoInBootstrapDistributionIndexed μ Pstar
        (fun n ω ωs (_ : Unit) => Astar n ω ωs)
        ((gaussianReal 0 1).map (fun z : ℝ => |z|))
        (fun x : ℝ => fun _ : Unit => x) := by
    simpa [Astar] using
      chapter10_indexed_bootstrap_regression_abs_tstat_distribution_standardNormalAbs_of_numerator_tight
        (μ := μ) (Pstar := Pstar) (TthetaStar := TthetaStar)
        (seThetaStar := seThetaStar) (seθ := seθ)
        hseθ hT hPstar hTthetaStar hseThetaStar hTail hseStar
  have hcrit_meas' :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed Pstar Astar (1 - α) n) μ := by
    intro n
    simpa [Astar] using hcrit_meas n
  have hξ : HasLaw (fun x : ℝ => x) (gaussianReal 0 1) (gaussianReal 0 1) := by
    simpa [id] using (HasLaw.id (μ := gaussianReal 0 1))
  have hreject :=
    chapter10_bootstrap_abs_test_rejectionProb_tendsto_alpha_indexed_quantile_prob_brackets
      (μ := μ) (ν := gaussianReal 0 1) (η := gaussianReal 0 1)
      (ηAbs := (gaussianReal 0 1).map (fun z : ℝ => |z|))
      (Pstar := Pstar) (Astar := Astar) (T := T)
      (ξ := fun x : ℝ => x) (critLim := critLim) (α := α)
      hTsample hPstar hAmeas hα_pos hα_lt_one hleft hright hAstar
      (fun x => continuousAt_cdf_standardNormalAbs x) hcrit_meas' hξ
      hcrit_nonneg hcdfLower hcdfUpper
  simpa [Astar] using hreject

/-- Regression-facing two-sided bootstrap-test calibration from scalar
compact-tail control for the bootstrap numerator.

The scalar-tail studentized absolute-t CDF route from Theorem 10.18 supplies
the bootstrap critical-value convergence required by the Theorem 10.16
test-size theorem. -/
theorem
chapter10_bootstrap_abs_test_rejectionProb_of_regression_tstat_scalarTail
    [IsProbabilityMeasure μ]
    {Pstar : ℕ → Ω → Measure Ωs}
    {TthetaStar seThetaStar : ℕ → Ω → Ωs → ℝ}
    {T : ℕ → Ω → ℝ} {seθ critLim α : ℝ}
    (hTsample :
      TendstoInDistribution T atTop (fun x : ℝ => x) (fun _ => μ)
        (gaussianReal 0 1))
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
    (hleft :
      ∀ ε : ℝ, 0 < ε →
        cdf ((gaussianReal 0 1).map (fun z : ℝ => |z|)) (critLim - ε) <
          1 - α)
    (hright :
      ∀ ε : ℝ, 0 < ε →
        1 - α <
          cdf ((gaussianReal 0 1).map (fun z : ℝ => |z|)) (critLim + ε))
    (hcrit_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantile Pstar
            (fun n ω ωs => |TthetaStar n ω ωs / seThetaStar n ω ωs|)
            (1 - α) n) μ)
    (hcrit_nonneg : 0 ≤ critLim)
    (hcdfLower : cdf (gaussianReal 0 1) (-critLim) = α / 2)
    (hcdfUpper : cdf (gaussianReal 0 1) critLim = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | bootstrapAbsTestReject (T n ω)
          (bootstrapScalarLowerQuantile Pstar
            (fun n ω ωs => |TthetaStar n ω ωs / seThetaStar n ω ωs|)
            (1 - α) n ω)})
      atTop (𝓝 (ENNReal.ofReal α)) := by
  let Astar : ℕ → Ω → Ωs → ℝ :=
    fun n ω ωs => |TthetaStar n ω ωs / seThetaStar n ω ωs|
  haveI : NoAtoms (gaussianReal 0 1) :=
    noAtoms_gaussianReal (μ := 0) (v := 1) (by norm_num)
  letI :
      IsProbabilityMeasure ((gaussianReal 0 1).map (fun z : ℝ => |z|)) :=
    Measure.isProbabilityMeasure_map continuous_abs.aemeasurable
  have hAmeas : ∀ n ω, AEMeasurable (Astar n ω) (Pstar n ω) := by
    intro n ω
    exact
      (continuous_abs.measurable.comp
        ((hTthetaStar n ω).div (hseThetaStar n ω))).aemeasurable
  have hAstar :
      TendstoInBootstrapDistribution μ Pstar
        (fun n ω ωs (_ : Unit) => Astar n ω ωs)
        ((gaussianReal 0 1).map (fun z : ℝ => |z|))
        (fun x : ℝ => fun _ : Unit => x) := by
    simpa [Astar] using
      chapter10_bootstrap_regression_abs_tstat_distribution_of_scalarTail
        (μ := μ) (Pstar := Pstar) (TthetaStar := TthetaStar)
        (seThetaStar := seThetaStar) (seθ := seθ)
        hseθ hT hPstar hTthetaStar hseThetaStar hTtail hseStar
  have hcrit_meas' :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantile Pstar Astar (1 - α) n) μ := by
    intro n
    simpa [Astar] using hcrit_meas n
  have hξ : HasLaw (fun x : ℝ => x) (gaussianReal 0 1) (gaussianReal 0 1) := by
    simpa [id] using (HasLaw.id (μ := gaussianReal 0 1))
  have hreject :=
    chapter10_bootstrap_abs_test_quantile_prob_brackets
      (μ := μ) (ν := gaussianReal 0 1) (η := gaussianReal 0 1)
      (ηAbs := (gaussianReal 0 1).map (fun z : ℝ => |z|))
      (Pstar := Pstar) (Astar := Astar) (T := T)
      (ξ := fun x : ℝ => x) (critLim := critLim) (α := α)
      hTsample hPstar hAmeas hα_pos hα_lt_one hleft hright hAstar
      (fun x => continuousAt_cdf_standardNormalAbs x) hcrit_meas' hξ
      hcrit_nonneg hcdfLower hcdfUpper
  simpa [Astar] using hreject

/-- Indexed regression-facing two-sided bootstrap-test calibration from scalar
compact-tail control for the bootstrap numerator. -/
theorem
chapter10_indexed_abs_test_rejectionProb_of_regression_tstat_scalarTail
    [IsProbabilityMeasure μ]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {TthetaStar seThetaStar : ∀ n, Ω → Ωboot n → ℝ}
    {T : ℕ → Ω → ℝ} {seθ critLim α : ℝ}
    (hTsample :
      TendstoInDistribution T atTop (fun x : ℝ => x) (fun _ => μ)
        (gaussianReal 0 1))
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
    (hleft :
      ∀ ε : ℝ, 0 < ε →
        cdf ((gaussianReal 0 1).map (fun z : ℝ => |z|)) (critLim - ε) <
          1 - α)
    (hright :
      ∀ ε : ℝ, 0 < ε →
        1 - α <
          cdf ((gaussianReal 0 1).map (fun z : ℝ => |z|)) (critLim + ε))
    (hcrit_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed Pstar
            (fun n ω ωs => |TthetaStar n ω ωs / seThetaStar n ω ωs|)
            (1 - α) n) μ)
    (hcrit_nonneg : 0 ≤ critLim)
    (hcdfLower : cdf (gaussianReal 0 1) (-critLim) = α / 2)
    (hcdfUpper : cdf (gaussianReal 0 1) critLim = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | bootstrapAbsTestReject (T n ω)
          (bootstrapScalarLowerQuantileIndexed Pstar
            (fun n ω ωs => |TthetaStar n ω ωs / seThetaStar n ω ωs|)
            (1 - α) n ω)})
      atTop (𝓝 (ENNReal.ofReal α)) := by
  let Astar : ∀ n, Ω → Ωboot n → ℝ :=
    fun n ω ωs => |TthetaStar n ω ωs / seThetaStar n ω ωs|
  haveI : NoAtoms (gaussianReal 0 1) :=
    noAtoms_gaussianReal (μ := 0) (v := 1) (by norm_num)
  letI :
      IsProbabilityMeasure ((gaussianReal 0 1).map (fun z : ℝ => |z|)) :=
    Measure.isProbabilityMeasure_map continuous_abs.aemeasurable
  have hAmeas : ∀ n ω, AEMeasurable (Astar n ω) (Pstar n ω) := by
    intro n ω
    exact
      (continuous_abs.measurable.comp
        ((hTthetaStar n ω).div (hseThetaStar n ω))).aemeasurable
  have hAstar :
      TendstoInBootstrapDistributionIndexed μ Pstar
        (fun n ω ωs (_ : Unit) => Astar n ω ωs)
        ((gaussianReal 0 1).map (fun z : ℝ => |z|))
        (fun x : ℝ => fun _ : Unit => x) := by
    simpa [Astar] using
      chapter10_indexed_bootstrap_regression_abs_tstat_distribution_of_scalarTail
        (μ := μ) (Pstar := Pstar) (TthetaStar := TthetaStar)
        (seThetaStar := seThetaStar) (seθ := seθ)
        hseθ hT hPstar hTthetaStar hseThetaStar hTtail hseStar
  have hcrit_meas' :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed Pstar Astar (1 - α) n) μ := by
    intro n
    simpa [Astar] using hcrit_meas n
  have hξ : HasLaw (fun x : ℝ => x) (gaussianReal 0 1) (gaussianReal 0 1) := by
    simpa [id] using (HasLaw.id (μ := gaussianReal 0 1))
  have hreject :=
    chapter10_bootstrap_abs_test_rejectionProb_tendsto_alpha_indexed_quantile_prob_brackets
      (μ := μ) (ν := gaussianReal 0 1) (η := gaussianReal 0 1)
      (ηAbs := (gaussianReal 0 1).map (fun z : ℝ => |z|))
      (Pstar := Pstar) (Astar := Astar) (T := T)
      (ξ := fun x : ℝ => x) (critLim := critLim) (α := α)
      hTsample hPstar hAmeas hα_pos hα_lt_one hleft hright hAstar
      (fun x => continuousAt_cdf_standardNormalAbs x) hcrit_meas' hξ
      hcrit_nonneg hcdfLower hcdfUpper
  simpa [Astar] using hreject

/-- Regression-facing two-sided bootstrap-test calibration from an eventually
bounded bootstrap numerator.

The bounded numerator supplies Theorem 10.18's scalar-tail studentized
absolute-t CDF route, and the existing Theorem 10.16 lower-critical-value
constructor gives rejection probability `α`. -/
theorem
chapter10_bootstrap_abs_test_rejectionProb_of_regression_tstat_eventually_bound
    [IsProbabilityMeasure μ]
    {Pstar : ℕ → Ω → Measure Ωs}
    {TthetaStar seThetaStar : ℕ → Ω → Ωs → ℝ}
    {T : ℕ → Ω → ℝ} {seθ C critLim α : ℝ}
    (hTsample :
      TendstoInDistribution T atTop (fun x : ℝ => x) (fun _ => μ)
        (gaussianReal 0 1))
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
    (hleft :
      ∀ ε : ℝ, 0 < ε →
        cdf ((gaussianReal 0 1).map (fun z : ℝ => |z|)) (critLim - ε) <
          1 - α)
    (hright :
      ∀ ε : ℝ, 0 < ε →
        1 - α <
          cdf ((gaussianReal 0 1).map (fun z : ℝ => |z|)) (critLim + ε))
    (hcrit_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantile Pstar
            (fun n ω ωs => |TthetaStar n ω ωs / seThetaStar n ω ωs|)
            (1 - α) n) μ)
    (hcrit_nonneg : 0 ≤ critLim)
    (hcdfLower : cdf (gaussianReal 0 1) (-critLim) = α / 2)
    (hcdfUpper : cdf (gaussianReal 0 1) critLim = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | bootstrapAbsTestReject (T n ω)
          (bootstrapScalarLowerQuantile Pstar
            (fun n ω ωs => |TthetaStar n ω ωs / seThetaStar n ω ωs|)
            (1 - α) n ω)})
      atTop (𝓝 (ENNReal.ofReal α)) := by
  let Astar : ℕ → Ω → Ωs → ℝ :=
    fun n ω ωs => |TthetaStar n ω ωs / seThetaStar n ω ωs|
  haveI : NoAtoms (gaussianReal 0 1) :=
    noAtoms_gaussianReal (μ := 0) (v := 1) (by norm_num)
  letI :
      IsProbabilityMeasure ((gaussianReal 0 1).map (fun z : ℝ => |z|)) :=
    Measure.isProbabilityMeasure_map continuous_abs.aemeasurable
  have hAmeas : ∀ n ω, AEMeasurable (Astar n ω) (Pstar n ω) := by
    intro n ω
    exact
      (continuous_abs.measurable.comp
        ((hTthetaStar n ω).div (hseThetaStar n ω))).aemeasurable
  have hAstar :
      TendstoInBootstrapDistribution μ Pstar
        (fun n ω ωs (_ : Unit) => Astar n ω ωs)
        ((gaussianReal 0 1).map (fun z : ℝ => |z|))
        (fun x : ℝ => fun _ : Unit => x) := by
    simpa [Astar] using
      chapter10_bootstrap_regression_abs_tstat_distribution_of_eventually_bound
        (μ := μ) (Pstar := Pstar) (TthetaStar := TthetaStar)
        (seThetaStar := seThetaStar) (seθ := seθ) (C := C)
        hseθ hT hPstar hTthetaStar hseThetaStar hbound hseStar
  have hcrit_meas' :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantile Pstar Astar (1 - α) n) μ := by
    intro n
    simpa [Astar] using hcrit_meas n
  have hξ : HasLaw (fun x : ℝ => x) (gaussianReal 0 1) (gaussianReal 0 1) := by
    simpa [id] using (HasLaw.id (μ := gaussianReal 0 1))
  have hreject :=
    chapter10_bootstrap_abs_test_quantile_prob_brackets
      (μ := μ) (ν := gaussianReal 0 1) (η := gaussianReal 0 1)
      (ηAbs := (gaussianReal 0 1).map (fun z : ℝ => |z|))
      (Pstar := Pstar) (Astar := Astar) (T := T)
      (ξ := fun x : ℝ => x) (critLim := critLim) (α := α)
      hTsample hPstar hAmeas hα_pos hα_lt_one hleft hright hAstar
      (fun x => continuousAt_cdf_standardNormalAbs x) hcrit_meas' hξ
      hcrit_nonneg hcdfLower hcdfUpper
  simpa [Astar] using hreject

/-- Indexed regression-facing two-sided bootstrap-test calibration from an
eventually bounded bootstrap numerator. -/
theorem
chapter10_indexed_abs_test_rejectionProb_of_regression_tstat_eventually_bound
    [IsProbabilityMeasure μ]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {TthetaStar seThetaStar : ∀ n, Ω → Ωboot n → ℝ}
    {T : ℕ → Ω → ℝ} {seθ C critLim α : ℝ}
    (hTsample :
      TendstoInDistribution T atTop (fun x : ℝ => x) (fun _ => μ)
        (gaussianReal 0 1))
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
    (hleft :
      ∀ ε : ℝ, 0 < ε →
        cdf ((gaussianReal 0 1).map (fun z : ℝ => |z|)) (critLim - ε) <
          1 - α)
    (hright :
      ∀ ε : ℝ, 0 < ε →
        1 - α <
          cdf ((gaussianReal 0 1).map (fun z : ℝ => |z|)) (critLim + ε))
    (hcrit_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed Pstar
            (fun n ω ωs => |TthetaStar n ω ωs / seThetaStar n ω ωs|)
            (1 - α) n) μ)
    (hcrit_nonneg : 0 ≤ critLim)
    (hcdfLower : cdf (gaussianReal 0 1) (-critLim) = α / 2)
    (hcdfUpper : cdf (gaussianReal 0 1) critLim = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | bootstrapAbsTestReject (T n ω)
          (bootstrapScalarLowerQuantileIndexed Pstar
            (fun n ω ωs => |TthetaStar n ω ωs / seThetaStar n ω ωs|)
            (1 - α) n ω)})
      atTop (𝓝 (ENNReal.ofReal α)) := by
  let Astar : ∀ n, Ω → Ωboot n → ℝ :=
    fun n ω ωs => |TthetaStar n ω ωs / seThetaStar n ω ωs|
  haveI : NoAtoms (gaussianReal 0 1) :=
    noAtoms_gaussianReal (μ := 0) (v := 1) (by norm_num)
  letI :
      IsProbabilityMeasure ((gaussianReal 0 1).map (fun z : ℝ => |z|)) :=
    Measure.isProbabilityMeasure_map continuous_abs.aemeasurable
  have hAmeas : ∀ n ω, AEMeasurable (Astar n ω) (Pstar n ω) := by
    intro n ω
    exact
      (continuous_abs.measurable.comp
        ((hTthetaStar n ω).div (hseThetaStar n ω))).aemeasurable
  have hAstar :
      TendstoInBootstrapDistributionIndexed μ Pstar
        (fun n ω ωs (_ : Unit) => Astar n ω ωs)
        ((gaussianReal 0 1).map (fun z : ℝ => |z|))
        (fun x : ℝ => fun _ : Unit => x) := by
    simpa [Astar] using
      chapter10_indexed_bootstrap_regression_abs_tstat_distribution_of_eventually_bound
        (μ := μ) (Pstar := Pstar) (TthetaStar := TthetaStar)
        (seThetaStar := seThetaStar) (seθ := seθ) (C := C)
        hseθ hT hPstar hTthetaStar hseThetaStar hbound hseStar
  have hcrit_meas' :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed Pstar Astar (1 - α) n) μ := by
    intro n
    simpa [Astar] using hcrit_meas n
  have hξ : HasLaw (fun x : ℝ => x) (gaussianReal 0 1) (gaussianReal 0 1) := by
    simpa [id] using (HasLaw.id (μ := gaussianReal 0 1))
  have hreject :=
    chapter10_bootstrap_abs_test_rejectionProb_tendsto_alpha_indexed_quantile_prob_brackets
      (μ := μ) (ν := gaussianReal 0 1) (η := gaussianReal 0 1)
      (ηAbs := (gaussianReal 0 1).map (fun z : ℝ => |z|))
      (Pstar := Pstar) (Astar := Astar) (T := T)
      (ξ := fun x : ℝ => x) (critLim := critLim) (α := α)
      hTsample hPstar hAmeas hα_pos hα_lt_one hleft hright hAstar
      (fun x => continuousAt_cdf_standardNormalAbs x) hcrit_meas' hξ
      hcrit_nonneg hcdfLower hcdfUpper
  simpa [Astar] using hreject

/-- Strict-CDF counterpart of the regression-facing two-sided bootstrap-test
calibration from the joint Theorem 10.18 t-statistic route. -/
theorem chapter10_bootstrap_abs_test_rejectionProb_strict_of_bootstrap_regression_tstat
    [IsProbabilityMeasure μ]
    {Pstar : ℕ → Ω → Measure Ωs}
    {TthetaStar seThetaStar : ℕ → Ω → Ωs → ℝ}
    {T : ℕ → Ω → ℝ} {seθ critLim α : ℝ}
    (hT :
      TendstoInDistribution T atTop (fun x : ℝ => x) (fun _ => μ)
        (gaussianReal 0 1))
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
    (hstrict :
      StrictMono (fun x => cdf (gaussianReal 0 1) x))
    (hcrit_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantile Pstar
            (fun n ω ωs => |TthetaStar n ω ωs / seThetaStar n ω ωs|)
            (1 - α) n) μ)
    (hcrit_nonneg : 0 ≤ critLim)
    (hcdfLower : cdf (gaussianReal 0 1) (-critLim) = α / 2)
    (hcdfUpper : cdf (gaussianReal 0 1) critLim = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | bootstrapAbsTestReject (T n ω)
          (bootstrapScalarLowerQuantile Pstar
            (fun n ω ωs => |TthetaStar n ω ωs / seThetaStar n ω ωs|)
            (1 - α) n ω)})
      atTop (𝓝 (ENNReal.ofReal α)) := by
  obtain ⟨hleft, hright⟩ :=
    standardNormalAbs_cdf_brackets_of_standardNormal_endpoints
      hstrict hα_lt_one hcrit_nonneg hcdfLower hcdfUpper
  exact
    chapter10_bootstrap_abs_test_rejectionProb_tendsto_alpha_of_bootstrap_regression_tstat
      (μ := μ) (Pstar := Pstar) (TthetaStar := TthetaStar)
      (seThetaStar := seThetaStar) (T := T) (seθ := seθ)
      (critLim := critLim) (α := α)
      hT hseθ hjoint hPstar hTthetaStar hseThetaStar hseStar
      hα_pos hα_lt_one hleft hright hcrit_meas
      hcrit_nonneg hcdfLower hcdfUpper

/-- Indexed strict-CDF counterpart of the regression-facing two-sided
bootstrap-test calibration from the joint Theorem 10.18 t-statistic route. -/
theorem
chapter10_indexed_abs_test_rejectionProb_strict_of_bootstrap_regression_tstat
    [IsProbabilityMeasure μ]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {TthetaStar seThetaStar : ∀ n, Ω → Ωboot n → ℝ}
    {T : ℕ → Ω → ℝ} {seθ critLim α : ℝ}
    (hT :
      TendstoInDistribution T atTop (fun x : ℝ => x) (fun _ => μ)
        (gaussianReal 0 1))
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
    (hstrict :
      StrictMono (fun x => cdf (gaussianReal 0 1) x))
    (hcrit_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed Pstar
            (fun n ω ωs => |TthetaStar n ω ωs / seThetaStar n ω ωs|)
            (1 - α) n) μ)
    (hcrit_nonneg : 0 ≤ critLim)
    (hcdfLower : cdf (gaussianReal 0 1) (-critLim) = α / 2)
    (hcdfUpper : cdf (gaussianReal 0 1) critLim = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | bootstrapAbsTestReject (T n ω)
          (bootstrapScalarLowerQuantileIndexed Pstar
            (fun n ω ωs => |TthetaStar n ω ωs / seThetaStar n ω ωs|)
            (1 - α) n ω)})
      atTop (𝓝 (ENNReal.ofReal α)) := by
  obtain ⟨hleft, hright⟩ :=
    standardNormalAbs_cdf_brackets_of_standardNormal_endpoints
      hstrict hα_lt_one hcrit_nonneg hcdfLower hcdfUpper
  exact
    chapter10_bootstrap_abs_test_rejectionProb_tendsto_alpha_indexed_of_bootstrap_regression_tstat
      (μ := μ) (Pstar := Pstar) (TthetaStar := TthetaStar)
      (seThetaStar := seThetaStar) (T := T) (seθ := seθ)
      (critLim := critLim) (α := α)
      hT hseθ hjoint hPstar hTthetaStar hseThetaStar hseStar
      hα_pos hα_lt_one hleft hright hcrit_meas
      hcrit_nonneg hcdfLower hcdfUpper

/-- Strict-CDF counterpart of the numerator-tight regression absolute-test
route. -/
theorem
chapter10_abs_test_rejectionProb_strict_of_regression_tstat_numerator_tight
    [IsProbabilityMeasure μ]
    {Pstar : ℕ → Ω → Measure Ωs}
    {TthetaStar seThetaStar : ℕ → Ω → Ωs → ℝ}
    {T : ℕ → Ω → ℝ} {seθ critLim α : ℝ}
    (hTsample :
      TendstoInDistribution T atTop (fun x : ℝ => x) (fun _ => μ)
        (gaussianReal 0 1))
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
    (hstrict :
      StrictMono (fun x => cdf (gaussianReal 0 1) x))
    (hcrit_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantile Pstar
            (fun n ω ωs => |TthetaStar n ω ωs / seThetaStar n ω ωs|)
            (1 - α) n) μ)
    (hcrit_nonneg : 0 ≤ critLim)
    (hcdfLower : cdf (gaussianReal 0 1) (-critLim) = α / 2)
    (hcdfUpper : cdf (gaussianReal 0 1) critLim = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | bootstrapAbsTestReject (T n ω)
          (bootstrapScalarLowerQuantile Pstar
            (fun n ω ωs => |TthetaStar n ω ωs / seThetaStar n ω ωs|)
            (1 - α) n ω)})
      atTop (𝓝 (ENNReal.ofReal α)) := by
  obtain ⟨hleft, hright⟩ :=
    standardNormalAbs_cdf_brackets_of_standardNormal_endpoints
      hstrict hα_lt_one hcrit_nonneg hcdfLower hcdfUpper
  exact
    chapter10_bootstrap_abs_test_rejectionProb_of_regression_tstat_numerator_tight
      (μ := μ) (Pstar := Pstar) (TthetaStar := TthetaStar)
      (seThetaStar := seThetaStar) (T := T) (seθ := seθ)
      (critLim := critLim) (α := α)
      hTsample hseθ hT hPstar hTthetaStar hseThetaStar hTail hseStar
      hα_pos hα_lt_one hleft hright hcrit_meas
      hcrit_nonneg hcdfLower hcdfUpper

/-- Indexed strict-CDF counterpart of the numerator-tight regression
absolute-test route. -/
theorem
chapter10_indexed_abs_test_rejectionProb_strict_of_regression_tstat_numerator_tight
    [IsProbabilityMeasure μ]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {TthetaStar seThetaStar : ∀ n, Ω → Ωboot n → ℝ}
    {T : ℕ → Ω → ℝ} {seθ critLim α : ℝ}
    (hTsample :
      TendstoInDistribution T atTop (fun x : ℝ => x) (fun _ => μ)
        (gaussianReal 0 1))
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
    (hstrict :
      StrictMono (fun x => cdf (gaussianReal 0 1) x))
    (hcrit_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed Pstar
            (fun n ω ωs => |TthetaStar n ω ωs / seThetaStar n ω ωs|)
            (1 - α) n) μ)
    (hcrit_nonneg : 0 ≤ critLim)
    (hcdfLower : cdf (gaussianReal 0 1) (-critLim) = α / 2)
    (hcdfUpper : cdf (gaussianReal 0 1) critLim = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | bootstrapAbsTestReject (T n ω)
          (bootstrapScalarLowerQuantileIndexed Pstar
            (fun n ω ωs => |TthetaStar n ω ωs / seThetaStar n ω ωs|)
            (1 - α) n ω)})
      atTop (𝓝 (ENNReal.ofReal α)) := by
  obtain ⟨hleft, hright⟩ :=
    standardNormalAbs_cdf_brackets_of_standardNormal_endpoints
      hstrict hα_lt_one hcrit_nonneg hcdfLower hcdfUpper
  exact
    chapter10_indexed_abs_test_rejectionProb_of_regression_tstat_numerator_tight
      (μ := μ) (Pstar := Pstar) (TthetaStar := TthetaStar)
      (seThetaStar := seThetaStar) (T := T) (seθ := seθ)
      (critLim := critLim) (α := α)
      hTsample hseθ hT hPstar hTthetaStar hseThetaStar hTail hseStar
      hα_pos hα_lt_one hleft hright hcrit_meas
      hcrit_nonneg hcdfLower hcdfUpper

/-- Strict-CDF counterpart of the scalar-tail regression absolute-test route. -/
theorem chapter10_abs_test_rejectionProb_strict_of_regression_tstat_scalarTail
    [IsProbabilityMeasure μ]
    {Pstar : ℕ → Ω → Measure Ωs}
    {TthetaStar seThetaStar : ℕ → Ω → Ωs → ℝ}
    {T : ℕ → Ω → ℝ} {seθ critLim α : ℝ}
    (hTsample :
      TendstoInDistribution T atTop (fun x : ℝ => x) (fun _ => μ)
        (gaussianReal 0 1))
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
    (hstrict :
      StrictMono (fun x => cdf (gaussianReal 0 1) x))
    (hcrit_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantile Pstar
            (fun n ω ωs => |TthetaStar n ω ωs / seThetaStar n ω ωs|)
            (1 - α) n) μ)
    (hcrit_nonneg : 0 ≤ critLim)
    (hcdfLower : cdf (gaussianReal 0 1) (-critLim) = α / 2)
    (hcdfUpper : cdf (gaussianReal 0 1) critLim = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | bootstrapAbsTestReject (T n ω)
          (bootstrapScalarLowerQuantile Pstar
            (fun n ω ωs => |TthetaStar n ω ωs / seThetaStar n ω ωs|)
            (1 - α) n ω)})
      atTop (𝓝 (ENNReal.ofReal α)) := by
  obtain ⟨hleft, hright⟩ :=
    standardNormalAbs_cdf_brackets_of_standardNormal_endpoints
      hstrict hα_lt_one hcrit_nonneg hcdfLower hcdfUpper
  exact
    chapter10_bootstrap_abs_test_rejectionProb_of_regression_tstat_scalarTail
      (μ := μ) (Pstar := Pstar) (TthetaStar := TthetaStar)
      (seThetaStar := seThetaStar) (T := T) (seθ := seθ)
      (critLim := critLim) (α := α)
      hTsample hseθ hT hPstar hTthetaStar hseThetaStar hTtail hseStar
      hα_pos hα_lt_one hleft hright hcrit_meas
      hcrit_nonneg hcdfLower hcdfUpper

/-- Indexed strict-CDF counterpart of the scalar-tail regression absolute-test
route. -/
theorem
chapter10_indexed_abs_test_rejectionProb_strict_of_regression_tstat_scalarTail
    [IsProbabilityMeasure μ]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {TthetaStar seThetaStar : ∀ n, Ω → Ωboot n → ℝ}
    {T : ℕ → Ω → ℝ} {seθ critLim α : ℝ}
    (hTsample :
      TendstoInDistribution T atTop (fun x : ℝ => x) (fun _ => μ)
        (gaussianReal 0 1))
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
    (hstrict :
      StrictMono (fun x => cdf (gaussianReal 0 1) x))
    (hcrit_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed Pstar
            (fun n ω ωs => |TthetaStar n ω ωs / seThetaStar n ω ωs|)
            (1 - α) n) μ)
    (hcrit_nonneg : 0 ≤ critLim)
    (hcdfLower : cdf (gaussianReal 0 1) (-critLim) = α / 2)
    (hcdfUpper : cdf (gaussianReal 0 1) critLim = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | bootstrapAbsTestReject (T n ω)
          (bootstrapScalarLowerQuantileIndexed Pstar
            (fun n ω ωs => |TthetaStar n ω ωs / seThetaStar n ω ωs|)
            (1 - α) n ω)})
      atTop (𝓝 (ENNReal.ofReal α)) := by
  obtain ⟨hleft, hright⟩ :=
    standardNormalAbs_cdf_brackets_of_standardNormal_endpoints
      hstrict hα_lt_one hcrit_nonneg hcdfLower hcdfUpper
  exact
    chapter10_indexed_abs_test_rejectionProb_of_regression_tstat_scalarTail
      (μ := μ) (Pstar := Pstar) (TthetaStar := TthetaStar)
      (seThetaStar := seThetaStar) (T := T) (seθ := seθ)
      (critLim := critLim) (α := α)
      hTsample hseθ hT hPstar hTthetaStar hseThetaStar hTtail hseStar
      hα_pos hα_lt_one hleft hright hcrit_meas
      hcrit_nonneg hcdfLower hcdfUpper

/-- Strict-CDF counterpart of the bounded-numerator regression absolute-test
route. -/
theorem
chapter10_abs_test_rejectionProb_strict_of_regression_tstat_eventually_bound
    [IsProbabilityMeasure μ]
    {Pstar : ℕ → Ω → Measure Ωs}
    {TthetaStar seThetaStar : ℕ → Ω → Ωs → ℝ}
    {T : ℕ → Ω → ℝ} {seθ C critLim α : ℝ}
    (hTsample :
      TendstoInDistribution T atTop (fun x : ℝ => x) (fun _ => μ)
        (gaussianReal 0 1))
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
    (hstrict :
      StrictMono (fun x => cdf (gaussianReal 0 1) x))
    (hcrit_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantile Pstar
            (fun n ω ωs => |TthetaStar n ω ωs / seThetaStar n ω ωs|)
            (1 - α) n) μ)
    (hcrit_nonneg : 0 ≤ critLim)
    (hcdfLower : cdf (gaussianReal 0 1) (-critLim) = α / 2)
    (hcdfUpper : cdf (gaussianReal 0 1) critLim = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | bootstrapAbsTestReject (T n ω)
          (bootstrapScalarLowerQuantile Pstar
            (fun n ω ωs => |TthetaStar n ω ωs / seThetaStar n ω ωs|)
            (1 - α) n ω)})
      atTop (𝓝 (ENNReal.ofReal α)) := by
  obtain ⟨hleft, hright⟩ :=
    standardNormalAbs_cdf_brackets_of_standardNormal_endpoints
      hstrict hα_lt_one hcrit_nonneg hcdfLower hcdfUpper
  exact
    chapter10_bootstrap_abs_test_rejectionProb_of_regression_tstat_eventually_bound
      (μ := μ) (Pstar := Pstar) (TthetaStar := TthetaStar)
      (seThetaStar := seThetaStar) (T := T) (seθ := seθ) (C := C)
      (critLim := critLim) (α := α)
      hTsample hseθ hT hPstar hTthetaStar hseThetaStar hbound hseStar
      hα_pos hα_lt_one hleft hright hcrit_meas
      hcrit_nonneg hcdfLower hcdfUpper

/-- Indexed strict-CDF counterpart of the bounded-numerator regression
absolute-test route. -/
theorem
chapter10_indexed_abs_test_rejectionProb_strict_of_regression_tstat_eventually_bound
    [IsProbabilityMeasure μ]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {TthetaStar seThetaStar : ∀ n, Ω → Ωboot n → ℝ}
    {T : ℕ → Ω → ℝ} {seθ C critLim α : ℝ}
    (hTsample :
      TendstoInDistribution T atTop (fun x : ℝ => x) (fun _ => μ)
        (gaussianReal 0 1))
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
    (hstrict :
      StrictMono (fun x => cdf (gaussianReal 0 1) x))
    (hcrit_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed Pstar
            (fun n ω ωs => |TthetaStar n ω ωs / seThetaStar n ω ωs|)
            (1 - α) n) μ)
    (hcrit_nonneg : 0 ≤ critLim)
    (hcdfLower : cdf (gaussianReal 0 1) (-critLim) = α / 2)
    (hcdfUpper : cdf (gaussianReal 0 1) critLim = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | bootstrapAbsTestReject (T n ω)
          (bootstrapScalarLowerQuantileIndexed Pstar
            (fun n ω ωs => |TthetaStar n ω ωs / seThetaStar n ω ωs|)
            (1 - α) n ω)})
      atTop (𝓝 (ENNReal.ofReal α)) := by
  obtain ⟨hleft, hright⟩ :=
    standardNormalAbs_cdf_brackets_of_standardNormal_endpoints
      hstrict hα_lt_one hcrit_nonneg hcdfLower hcdfUpper
  exact
    chapter10_indexed_abs_test_rejectionProb_of_regression_tstat_eventually_bound
      (μ := μ) (Pstar := Pstar) (TthetaStar := TthetaStar)
      (seThetaStar := seThetaStar) (T := T) (seθ := seθ) (C := C)
      (critLim := critLim) (α := α)
      hTsample hseθ hT hPstar hTthetaStar hseThetaStar hbound hseStar
      hα_pos hα_lt_one hleft hright hcrit_meas
      hcrit_nonneg hcdfLower hcdfUpper

set_option linter.style.longLine false in
/-- Local-CDF two-sided bootstrap-test calibration with the bootstrap critical
value specialized to the concrete finite ordinary-bootstrap OLS
linear-restriction t-statistic.

The sample-side statistic is left explicit; this wrapper discharges the
bootstrap-side Theorem 10.18 absolute-t route from the finite OLS
gap-envelope numerator CLT, scalar compact-tail control, and feasible
bootstrap standard-error consistency. -/
theorem
    chapter10_indexed_abs_test_rejectionProb_of_regression_tstat_finSucc_olsBetaOrZero_gapEnvelope_scalarTail
    [IsProbabilityMeasure μ]
    {k : Type*} [Fintype k] [DecidableEq k]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    {seThetaStar : ∀ n, Ω → (Fin (n + 1) → Fin (n + 1)) → ℝ}
    {T : ℕ → Ω → ℝ} {critLim α : ℝ}
    (β : k → ℝ) (R : Matrix Unit k ℝ)
    (hTsample :
      TendstoInDistribution T atTop (fun x : ℝ => x) (fun _ => μ)
        (gaussianReal 0 1))
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
    (hleft :
      ∀ ε : ℝ, 0 < ε →
        cdf ((gaussianReal 0 1).map (fun z : ℝ => |z|)) (critLim - ε) <
          1 - α)
    (hright :
      ∀ ε : ℝ, 0 < ε →
        1 - α <
          cdf ((gaussianReal 0 1).map (fun z : ℝ => |z|)) (critLim + ε))
    (hcrit_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed
            (fun n _ =>
              (ProbabilityTheory.uniformOn
                (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                  Measure (Fin (n + 1) → Fin (n + 1))))
            (fun n ω ωs =>
              |regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs /
                seThetaStar n ω ωs|)
            (1 - α) n) μ)
    (hcrit_nonneg : 0 ≤ critLim)
    (hcdfLower : cdf (gaussianReal 0 1) (-critLim) = α / 2)
    (hcdfUpper : cdf (gaussianReal 0 1) critLim = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | bootstrapAbsTestReject (T n ω)
          (bootstrapScalarLowerQuantileIndexed
            (fun n _ =>
              (ProbabilityTheory.uniformOn
                (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                  Measure (Fin (n + 1) → Fin (n + 1))))
            (fun n ω ωs =>
              |regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs /
                seThetaStar n ω ωs|)
            (1 - α) n ω)})
      atTop (𝓝 (ENNReal.ofReal α)) :=
  chapter10_indexed_abs_test_rejectionProb_of_regression_tstat_scalarTail
    (μ := μ)
    (Pstar := fun n _ =>
      (ProbabilityTheory.uniformOn
        (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
          Measure (Fin (n + 1) → Fin (n + 1))))
    (TthetaStar := fun n ω ωs =>
      regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs)
    (seThetaStar := seThetaStar) (T := T)
    (seθ := linearRestrictionStdError R (heteroAsymCov μ X e))
    (critLim := critLim) (α := α)
    hTsample hseθ
    (chapter10_indexed_bootstrap_regression_linearRestriction_standardNormal_finSucc_olsBetaOrZero_of_gapEnvelope_tight
      (μ := μ) (X := X) (e := e) (y := y)
      β R hmodel h hΩ hTail hGapTail)
    (fun _ _ => inferInstance) (fun _ _ => measurable_of_finite _)
    hseThetaStar hTtail hseStar hα_pos hα_lt_one hleft hright
     hcrit_meas hcrit_nonneg hcdfLower hcdfUpper

set_option linter.style.longLine false in
/-- Robust-feasible HC specialization of the indexed concrete finite OLS
local-CDF scalar-tail absolute-test wrapper. -/
theorem
    chapter10_indexed_abs_test_rejectionProb_of_regression_tstat_finSucc_olsBetaOrZero_gapEnvelope_scalarTail_of_robustFeasibleHCMomentConditions
    [IsProbabilityMeasure μ]
    {k : Type*} [Fintype k] [DecidableEq k]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    {seThetaStar : ∀ n, Ω → (Fin (n + 1) → Fin (n + 1)) → ℝ}
    {T : ℕ → Ω → ℝ} {critLim α : ℝ}
    (β : k → ℝ) (R : Matrix Unit k ℝ)
    (hTsample :
      TendstoInDistribution T atTop (fun x : ℝ => x) (fun _ => μ)
        (gaussianReal 0 1))
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
    (hleft :
      ∀ ε : ℝ, 0 < ε →
        cdf ((gaussianReal 0 1).map (fun z : ℝ => |z|)) (critLim - ε) <
          1 - α)
    (hright :
      ∀ ε : ℝ, 0 < ε →
        1 - α <
          cdf ((gaussianReal 0 1).map (fun z : ℝ => |z|)) (critLim + ε))
    (hcrit_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed
            (fun n _ =>
              (ProbabilityTheory.uniformOn
                (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                  Measure (Fin (n + 1) → Fin (n + 1))))
            (fun n ω ωs =>
              |regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs /
                seThetaStar n ω ωs|)
            (1 - α) n) μ)
    (hcrit_nonneg : 0 ≤ critLim)
    (hcdfLower : cdf (gaussianReal 0 1) (-critLim) = α / 2)
    (hcdfUpper : cdf (gaussianReal 0 1) critLim = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | bootstrapAbsTestReject (T n ω)
          (bootstrapScalarLowerQuantileIndexed
            (fun n _ =>
              (ProbabilityTheory.uniformOn
                (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                  Measure (Fin (n + 1) → Fin (n + 1))))
            (fun n ω ωs =>
              |regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs /
                seThetaStar n ω ωs|)
            (1 - α) n ω)})
      atTop (𝓝 (ENNReal.ofReal α)) :=
  chapter10_indexed_abs_test_rejectionProb_of_regression_tstat_finSucc_olsBetaOrZero_gapEnvelope_scalarTail
    (μ := μ) (X := X) (e := e) (y := y)
    β R hTsample hseθ hm.model hm.toScoreCLTConditions hΩ hTail
    hGapTail hseThetaStar hTtail hseStar hα_pos hα_lt_one
    hleft hright hcrit_meas hcrit_nonneg hcdfLower hcdfUpper

set_option linter.style.longLine false in
/-- Indexed strict-CDF two-sided bootstrap-test calibration with the bootstrap
critical value specialized to the concrete finite ordinary-bootstrap OLS
linear-restriction t-statistic.

The sample-side statistic is left explicit; this wrapper discharges the
bootstrap-side Theorem 10.18 absolute-t route from the finite OLS
gap-envelope numerator CLT, scalar compact-tail control, and feasible
bootstrap standard-error consistency. -/
theorem
    chapter10_indexed_abs_test_rejectionProb_strict_of_regression_tstat_finSucc_olsBetaOrZero_gapEnvelope_scalarTail
    [IsProbabilityMeasure μ]
    {k : Type*} [Fintype k] [DecidableEq k]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    {seThetaStar : ∀ n, Ω → (Fin (n + 1) → Fin (n + 1)) → ℝ}
    {T : ℕ → Ω → ℝ} {critLim α : ℝ}
    (β : k → ℝ) (R : Matrix Unit k ℝ)
    (hTsample :
      TendstoInDistribution T atTop (fun x : ℝ => x) (fun _ => μ)
        (gaussianReal 0 1))
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
    (hstrict :
      StrictMono (fun x => cdf (gaussianReal 0 1) x))
    (hcrit_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed
            (fun n _ =>
              (ProbabilityTheory.uniformOn
                (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                  Measure (Fin (n + 1) → Fin (n + 1))))
            (fun n ω ωs =>
              |regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs /
                seThetaStar n ω ωs|)
            (1 - α) n) μ)
    (hcrit_nonneg : 0 ≤ critLim)
    (hcdfLower : cdf (gaussianReal 0 1) (-critLim) = α / 2)
    (hcdfUpper : cdf (gaussianReal 0 1) critLim = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | bootstrapAbsTestReject (T n ω)
          (bootstrapScalarLowerQuantileIndexed
            (fun n _ =>
              (ProbabilityTheory.uniformOn
                (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                  Measure (Fin (n + 1) → Fin (n + 1))))
            (fun n ω ωs =>
              |regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs /
                seThetaStar n ω ωs|)
            (1 - α) n ω)})
      atTop (𝓝 (ENNReal.ofReal α)) :=
  chapter10_indexed_abs_test_rejectionProb_strict_of_regression_tstat_scalarTail
    (μ := μ)
    (Pstar := fun n _ =>
      (ProbabilityTheory.uniformOn
        (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
          Measure (Fin (n + 1) → Fin (n + 1))))
    (TthetaStar := fun n ω ωs =>
      regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs)
    (seThetaStar := seThetaStar) (T := T)
    (seθ := linearRestrictionStdError R (heteroAsymCov μ X e))
    (critLim := critLim) (α := α)
    hTsample hseθ
    (chapter10_indexed_bootstrap_regression_linearRestriction_standardNormal_finSucc_olsBetaOrZero_of_gapEnvelope_tight
      (μ := μ) (X := X) (e := e) (y := y)
      β R hmodel h hΩ hTail hGapTail)
    (fun _ _ => inferInstance) (fun _ _ => measurable_of_finite _)
    hseThetaStar hTtail hseStar hα_pos hα_lt_one hstrict
    hcrit_meas hcrit_nonneg hcdfLower hcdfUpper

set_option linter.style.longLine false in
/-- Robust-feasible HC specialization of the indexed concrete finite OLS
strict-CDF scalar-tail absolute-test wrapper. -/
theorem
    chapter10_indexed_abs_test_rejectionProb_strict_of_regression_tstat_finSucc_olsBetaOrZero_gapEnvelope_scalarTail_of_robustFeasibleHCMomentConditions
    [IsProbabilityMeasure μ]
    {k : Type*} [Fintype k] [DecidableEq k]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    {seThetaStar : ∀ n, Ω → (Fin (n + 1) → Fin (n + 1)) → ℝ}
    {T : ℕ → Ω → ℝ} {critLim α : ℝ}
    (β : k → ℝ) (R : Matrix Unit k ℝ)
    (hTsample :
      TendstoInDistribution T atTop (fun x : ℝ => x) (fun _ => μ)
        (gaussianReal 0 1))
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
    (hstrict :
      StrictMono (fun x => cdf (gaussianReal 0 1) x))
    (hcrit_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed
            (fun n _ =>
              (ProbabilityTheory.uniformOn
                (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                  Measure (Fin (n + 1) → Fin (n + 1))))
            (fun n ω ωs =>
              |regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs /
                seThetaStar n ω ωs|)
            (1 - α) n) μ)
    (hcrit_nonneg : 0 ≤ critLim)
    (hcdfLower : cdf (gaussianReal 0 1) (-critLim) = α / 2)
    (hcdfUpper : cdf (gaussianReal 0 1) critLim = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | bootstrapAbsTestReject (T n ω)
          (bootstrapScalarLowerQuantileIndexed
            (fun n _ =>
              (ProbabilityTheory.uniformOn
                (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                  Measure (Fin (n + 1) → Fin (n + 1))))
            (fun n ω ωs =>
              |regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs /
                seThetaStar n ω ωs|)
            (1 - α) n ω)})
      atTop (𝓝 (ENNReal.ofReal α)) :=
  chapter10_indexed_abs_test_rejectionProb_strict_of_regression_tstat_finSucc_olsBetaOrZero_gapEnvelope_scalarTail
    (μ := μ) (X := X) (e := e) (y := y)
    β R hTsample hseθ hm.model hm.toScoreCLTConditions hΩ hTail
    hGapTail hseThetaStar hTtail hseStar hα_pos hα_lt_one
    hstrict hcrit_meas hcrit_nonneg hcdfLower
    hcdfUpper

set_option linter.style.longLine false in
/-- Local-CDF two-sided bootstrap-test calibration with the bootstrap critical
value specialized to the concrete bounded finite ordinary-bootstrap OLS
linear-restriction t-statistic. -/
theorem
    chapter10_indexed_abs_test_rejectionProb_of_regression_tstat_finSucc_olsBetaOrZero_gapEnvelope_bounds
    [IsProbabilityMeasure μ]
    {k : Type*} [Fintype k] [DecidableEq k]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    {seThetaStar : ∀ n, Ω → (Fin (n + 1) → Fin (n + 1)) → ℝ}
    {T : ℕ → Ω → ℝ} {Clin Cbeta Cnum critLim α : ℝ}
    (β : k → ℝ) (R : Matrix Unit k ℝ)
    (hTsample :
      TendstoInDistribution T atTop (fun x : ℝ => x) (fun _ => μ)
        (gaussianReal 0 1))
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
    (hleft :
      ∀ ε : ℝ, 0 < ε →
        cdf ((gaussianReal 0 1).map (fun z : ℝ => |z|)) (critLim - ε) <
          1 - α)
    (hright :
      ∀ ε : ℝ, 0 < ε →
        1 - α <
          cdf ((gaussianReal 0 1).map (fun z : ℝ => |z|)) (critLim + ε))
    (hcrit_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed
            (fun n _ =>
              (ProbabilityTheory.uniformOn
                (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                  Measure (Fin (n + 1) → Fin (n + 1))))
            (fun n ω ωs =>
              |regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs /
                seThetaStar n ω ωs|)
            (1 - α) n) μ)
    (hcrit_nonneg : 0 ≤ critLim)
    (hcdfLower : cdf (gaussianReal 0 1) (-critLim) = α / 2)
    (hcdfUpper : cdf (gaussianReal 0 1) critLim = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | bootstrapAbsTestReject (T n ω)
          (bootstrapScalarLowerQuantileIndexed
            (fun n _ =>
              (ProbabilityTheory.uniformOn
                (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                  Measure (Fin (n + 1) → Fin (n + 1))))
            (fun n ω ωs =>
              |regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs /
                seThetaStar n ω ωs|)
            (1 - α) n ω)})
      atTop (𝓝 (ENNReal.ofReal α)) :=
  chapter10_indexed_abs_test_rejectionProb_of_regression_tstat_eventually_bound
    (μ := μ)
    (Pstar := fun n _ =>
      (ProbabilityTheory.uniformOn
        (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
          Measure (Fin (n + 1) → Fin (n + 1))))
    (TthetaStar := fun n ω ωs =>
      regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs)
    (seThetaStar := seThetaStar) (T := T)
    (seθ := linearRestrictionStdError R (heteroAsymCov μ X e))
    (C := Cnum) (critLim := critLim) (α := α)
    hTsample hseθ
    (chapter10_indexed_bootstrap_regression_linearRestriction_standardNormal_finSucc_olsBetaOrZero_of_gapEnvelope_bounds
      (μ := μ) (X := X) (e := e) (y := y)
      β R hmodel h hΩ hLinBound hBetaBound hGapTail)
    (fun _ _ => inferInstance) (fun _ _ => measurable_of_finite _)
    hseThetaStar hNumBound hseStar hα_pos hα_lt_one hleft hright
     hcrit_meas hcrit_nonneg hcdfLower hcdfUpper

set_option linter.style.longLine false in
/-- Robust-feasible HC specialization of the indexed concrete bounded finite
OLS local-CDF absolute-test wrapper. -/
theorem
    chapter10_indexed_abs_test_rejectionProb_of_regression_tstat_finSucc_olsBetaOrZero_gapEnvelope_bounds_of_robustFeasibleHCMomentConditions
    [IsProbabilityMeasure μ]
    {k : Type*} [Fintype k] [DecidableEq k]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    {seThetaStar : ∀ n, Ω → (Fin (n + 1) → Fin (n + 1)) → ℝ}
    {T : ℕ → Ω → ℝ} {Clin Cbeta Cnum critLim α : ℝ}
    (β : k → ℝ) (R : Matrix Unit k ℝ)
    (hTsample :
      TendstoInDistribution T atTop (fun x : ℝ => x) (fun _ => μ)
        (gaussianReal 0 1))
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
    (hleft :
      ∀ ε : ℝ, 0 < ε →
        cdf ((gaussianReal 0 1).map (fun z : ℝ => |z|)) (critLim - ε) <
          1 - α)
    (hright :
      ∀ ε : ℝ, 0 < ε →
        1 - α <
          cdf ((gaussianReal 0 1).map (fun z : ℝ => |z|)) (critLim + ε))
    (hcrit_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed
            (fun n _ =>
              (ProbabilityTheory.uniformOn
                (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                  Measure (Fin (n + 1) → Fin (n + 1))))
            (fun n ω ωs =>
              |regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs /
                seThetaStar n ω ωs|)
            (1 - α) n) μ)
    (hcrit_nonneg : 0 ≤ critLim)
    (hcdfLower : cdf (gaussianReal 0 1) (-critLim) = α / 2)
    (hcdfUpper : cdf (gaussianReal 0 1) critLim = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | bootstrapAbsTestReject (T n ω)
          (bootstrapScalarLowerQuantileIndexed
            (fun n _ =>
              (ProbabilityTheory.uniformOn
                (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                  Measure (Fin (n + 1) → Fin (n + 1))))
            (fun n ω ωs =>
              |regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs /
                seThetaStar n ω ωs|)
            (1 - α) n ω)})
      atTop (𝓝 (ENNReal.ofReal α)) :=
  chapter10_indexed_abs_test_rejectionProb_of_regression_tstat_finSucc_olsBetaOrZero_gapEnvelope_bounds
    (μ := μ) (X := X) (e := e) (y := y)
    β R hTsample hseθ hm.model hm.toScoreCLTConditions hΩ
    hLinBound hBetaBound hGapTail hseThetaStar hNumBound hseStar
    hα_pos hα_lt_one hleft hright hcrit_meas hcrit_nonneg
    hcdfLower hcdfUpper

set_option linter.style.longLine false in
/-- Indexed strict-CDF two-sided bootstrap-test calibration with the bootstrap
critical value specialized to the concrete bounded finite ordinary-bootstrap
OLS linear-restriction t-statistic. -/
theorem
    chapter10_indexed_abs_test_rejectionProb_strict_of_regression_tstat_finSucc_olsBetaOrZero_gapEnvelope_bounds
    [IsProbabilityMeasure μ]
    {k : Type*} [Fintype k] [DecidableEq k]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    {seThetaStar : ∀ n, Ω → (Fin (n + 1) → Fin (n + 1)) → ℝ}
    {T : ℕ → Ω → ℝ} {Clin Cbeta Cnum critLim α : ℝ}
    (β : k → ℝ) (R : Matrix Unit k ℝ)
    (hTsample :
      TendstoInDistribution T atTop (fun x : ℝ => x) (fun _ => μ)
        (gaussianReal 0 1))
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
    (hstrict :
      StrictMono (fun x => cdf (gaussianReal 0 1) x))
    (hcrit_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed
            (fun n _ =>
              (ProbabilityTheory.uniformOn
                (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                  Measure (Fin (n + 1) → Fin (n + 1))))
            (fun n ω ωs =>
              |regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs /
                seThetaStar n ω ωs|)
            (1 - α) n) μ)
    (hcrit_nonneg : 0 ≤ critLim)
    (hcdfLower : cdf (gaussianReal 0 1) (-critLim) = α / 2)
    (hcdfUpper : cdf (gaussianReal 0 1) critLim = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | bootstrapAbsTestReject (T n ω)
          (bootstrapScalarLowerQuantileIndexed
            (fun n _ =>
              (ProbabilityTheory.uniformOn
                (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                  Measure (Fin (n + 1) → Fin (n + 1))))
            (fun n ω ωs =>
              |regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs /
                seThetaStar n ω ωs|)
            (1 - α) n ω)})
      atTop (𝓝 (ENNReal.ofReal α)) :=
  chapter10_indexed_abs_test_rejectionProb_strict_of_regression_tstat_eventually_bound
    (μ := μ)
    (Pstar := fun n _ =>
      (ProbabilityTheory.uniformOn
        (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
          Measure (Fin (n + 1) → Fin (n + 1))))
    (TthetaStar := fun n ω ωs =>
      regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs)
    (seThetaStar := seThetaStar) (T := T)
    (seθ := linearRestrictionStdError R (heteroAsymCov μ X e))
    (C := Cnum) (critLim := critLim) (α := α)
    hTsample hseθ
    (chapter10_indexed_bootstrap_regression_linearRestriction_standardNormal_finSucc_olsBetaOrZero_of_gapEnvelope_bounds
      (μ := μ) (X := X) (e := e) (y := y)
      β R hmodel h hΩ hLinBound hBetaBound hGapTail)
    (fun _ _ => inferInstance) (fun _ _ => measurable_of_finite _)
    hseThetaStar hNumBound hseStar hα_pos hα_lt_one hstrict
    hcrit_meas hcrit_nonneg hcdfLower hcdfUpper

set_option linter.style.longLine false in
/-- Robust-feasible HC specialization of the indexed concrete bounded finite
OLS strict-CDF absolute-test wrapper. -/
theorem
    chapter10_indexed_abs_test_rejectionProb_strict_of_regression_tstat_finSucc_olsBetaOrZero_gapEnvelope_bounds_of_robustFeasibleHCMomentConditions
    [IsProbabilityMeasure μ]
    {k : Type*} [Fintype k] [DecidableEq k]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    {seThetaStar : ∀ n, Ω → (Fin (n + 1) → Fin (n + 1)) → ℝ}
    {T : ℕ → Ω → ℝ} {Clin Cbeta Cnum critLim α : ℝ}
    (β : k → ℝ) (R : Matrix Unit k ℝ)
    (hTsample :
      TendstoInDistribution T atTop (fun x : ℝ => x) (fun _ => μ)
        (gaussianReal 0 1))
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
    (hstrict :
      StrictMono (fun x => cdf (gaussianReal 0 1) x))
    (hcrit_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed
            (fun n _ =>
              (ProbabilityTheory.uniformOn
                (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                  Measure (Fin (n + 1) → Fin (n + 1))))
            (fun n ω ωs =>
              |regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs /
                seThetaStar n ω ωs|)
            (1 - α) n) μ)
    (hcrit_nonneg : 0 ≤ critLim)
    (hcdfLower : cdf (gaussianReal 0 1) (-critLim) = α / 2)
    (hcdfUpper : cdf (gaussianReal 0 1) critLim = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | bootstrapAbsTestReject (T n ω)
          (bootstrapScalarLowerQuantileIndexed
            (fun n _ =>
              (ProbabilityTheory.uniformOn
                (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                  Measure (Fin (n + 1) → Fin (n + 1))))
            (fun n ω ωs =>
              |regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs /
                seThetaStar n ω ωs|)
            (1 - α) n ω)})
      atTop (𝓝 (ENNReal.ofReal α)) :=
  chapter10_indexed_abs_test_rejectionProb_strict_of_regression_tstat_finSucc_olsBetaOrZero_gapEnvelope_bounds
    (μ := μ) (X := X) (e := e) (y := y)
    β R hTsample hseθ hm.model hm.toScoreCLTConditions hΩ
    hLinBound hBetaBound hGapTail hseThetaStar hNumBound hseStar
    hα_pos hα_lt_one hstrict hcrit_meas
    hcrit_nonneg hcdfLower hcdfUpper

set_option linter.style.longLine false in
/-- Local-CDF two-sided bootstrap-test calibration with the bootstrap critical
value specialized to the concrete finite ordinary-bootstrap OLS
linear-restriction t-statistic, where the scalar numerator bound is discharged
by the coefficient-statistic norm bound. -/
theorem
    chapter10_indexed_abs_test_rejectionProb_of_regression_tstat_finSucc_olsBetaOrZero_gapEnvelope_beta_bound
    [IsProbabilityMeasure μ]
    {k : Type*} [Fintype k] [DecidableEq k]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    {seThetaStar : ∀ n, Ω → (Fin (n + 1) → Fin (n + 1)) → ℝ}
    {T : ℕ → Ω → ℝ} {Clin Cbeta critLim α : ℝ}
    (β : k → ℝ) (R : Matrix Unit k ℝ)
    (hTsample :
      TendstoInDistribution T atTop (fun x : ℝ => x) (fun _ => μ)
        (gaussianReal 0 1))
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
    (hleft :
      ∀ ε : ℝ, 0 < ε →
        cdf ((gaussianReal 0 1).map (fun z : ℝ => |z|)) (critLim - ε) <
          1 - α)
    (hright :
      ∀ ε : ℝ, 0 < ε →
        1 - α <
          cdf ((gaussianReal 0 1).map (fun z : ℝ => |z|)) (critLim + ε))
    (hcrit_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed
            (fun n _ =>
              (ProbabilityTheory.uniformOn
                (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                  Measure (Fin (n + 1) → Fin (n + 1))))
            (fun n ω ωs =>
              |regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs /
                seThetaStar n ω ωs|)
            (1 - α) n) μ)
    (hcrit_nonneg : 0 ≤ critLim)
    (hcdfLower : cdf (gaussianReal 0 1) (-critLim) = α / 2)
    (hcdfUpper : cdf (gaussianReal 0 1) critLim = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | bootstrapAbsTestReject (T n ω)
          (bootstrapScalarLowerQuantileIndexed
            (fun n _ =>
              (ProbabilityTheory.uniformOn
                (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                  Measure (Fin (n + 1) → Fin (n + 1))))
            (fun n ω ωs =>
              |regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs /
                seThetaStar n ω ωs|)
            (1 - α) n ω)})
      atTop (𝓝 (ENNReal.ofReal α)) :=
  chapter10_indexed_abs_test_rejectionProb_of_regression_tstat_eventually_bound
    (μ := μ)
    (Pstar := fun n _ =>
      (ProbabilityTheory.uniformOn
        (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
          Measure (Fin (n + 1) → Fin (n + 1))))
    (TthetaStar := fun n ω ωs =>
      regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs)
    (seThetaStar := seThetaStar) (T := T)
    (seθ := linearRestrictionStdError R (heteroAsymCov μ X e))
    (C := ‖PiLp.proj (p := (2 : ℝ≥0∞)) (𝕜 := ℝ)
        (β := fun _ : Unit => ℝ) ()‖ * (‖matrixContinuousLinearMap R‖ * Cbeta))
    (critLim := critLim) (α := α)
    hTsample hseθ
    (chapter10_indexed_bootstrap_regression_linearRestriction_standardNormal_finSucc_olsBetaOrZero_of_gapEnvelope_bounds
      (μ := μ) (X := X) (e := e) (y := y)
      β R hmodel h hΩ hLinBound hBetaBound hGapTail)
    (fun _ _ => inferInstance) (fun _ _ => measurable_of_finite _)
    hseThetaStar
    (regressionBootstrapLinearRestrictionStatisticFinSucc_eventually_abs_bound_of_beta_bound
      (R := R) (X := X) (y := y) hBetaBound)
    hseStar hα_pos hα_lt_one hleft hright hcrit_meas
    hcrit_nonneg hcdfLower hcdfUpper

set_option linter.style.longLine false in
/-- Robust-feasible HC specialization of the indexed concrete beta-bound
finite OLS local-CDF absolute-test wrapper. -/
theorem
    chapter10_indexed_abs_test_rejectionProb_of_regression_tstat_finSucc_olsBetaOrZero_gapEnvelope_beta_bound_of_robustFeasibleHCMomentConditions
    [IsProbabilityMeasure μ]
    {k : Type*} [Fintype k] [DecidableEq k]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    {seThetaStar : ∀ n, Ω → (Fin (n + 1) → Fin (n + 1)) → ℝ}
    {T : ℕ → Ω → ℝ} {Clin Cbeta critLim α : ℝ}
    (β : k → ℝ) (R : Matrix Unit k ℝ)
    (hTsample :
      TendstoInDistribution T atTop (fun x : ℝ => x) (fun _ => μ)
        (gaussianReal 0 1))
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
    (hleft :
      ∀ ε : ℝ, 0 < ε →
        cdf ((gaussianReal 0 1).map (fun z : ℝ => |z|)) (critLim - ε) <
          1 - α)
    (hright :
      ∀ ε : ℝ, 0 < ε →
        1 - α <
          cdf ((gaussianReal 0 1).map (fun z : ℝ => |z|)) (critLim + ε))
    (hcrit_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed
            (fun n _ =>
              (ProbabilityTheory.uniformOn
                (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                  Measure (Fin (n + 1) → Fin (n + 1))))
            (fun n ω ωs =>
              |regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs /
                seThetaStar n ω ωs|)
            (1 - α) n) μ)
    (hcrit_nonneg : 0 ≤ critLim)
    (hcdfLower : cdf (gaussianReal 0 1) (-critLim) = α / 2)
    (hcdfUpper : cdf (gaussianReal 0 1) critLim = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | bootstrapAbsTestReject (T n ω)
          (bootstrapScalarLowerQuantileIndexed
            (fun n _ =>
              (ProbabilityTheory.uniformOn
                (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                  Measure (Fin (n + 1) → Fin (n + 1))))
            (fun n ω ωs =>
              |regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs /
                seThetaStar n ω ωs|)
            (1 - α) n ω)})
      atTop (𝓝 (ENNReal.ofReal α)) :=
  chapter10_indexed_abs_test_rejectionProb_of_regression_tstat_finSucc_olsBetaOrZero_gapEnvelope_beta_bound
    (μ := μ) (X := X) (e := e) (y := y)
    β R hTsample hseθ hm.model hm.toScoreCLTConditions hΩ hLinBound
    hBetaBound hGapTail hseThetaStar hseStar hα_pos hα_lt_one
    hleft hright hcrit_meas hcrit_nonneg hcdfLower hcdfUpper

set_option linter.style.longLine false in
/-- Indexed strict-CDF two-sided bootstrap-test calibration with the bootstrap
critical value specialized to the concrete finite ordinary-bootstrap OLS
linear-restriction t-statistic, where the scalar numerator bound is discharged
by the coefficient-statistic norm bound. -/
theorem
    chapter10_indexed_abs_test_rejectionProb_strict_of_regression_tstat_finSucc_olsBetaOrZero_gapEnvelope_beta_bound
    [IsProbabilityMeasure μ]
    {k : Type*} [Fintype k] [DecidableEq k]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    {seThetaStar : ∀ n, Ω → (Fin (n + 1) → Fin (n + 1)) → ℝ}
    {T : ℕ → Ω → ℝ} {Clin Cbeta critLim α : ℝ}
    (β : k → ℝ) (R : Matrix Unit k ℝ)
    (hTsample :
      TendstoInDistribution T atTop (fun x : ℝ => x) (fun _ => μ)
        (gaussianReal 0 1))
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
    (hstrict :
      StrictMono (fun x => cdf (gaussianReal 0 1) x))
    (hcrit_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed
            (fun n _ =>
              (ProbabilityTheory.uniformOn
                (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                  Measure (Fin (n + 1) → Fin (n + 1))))
            (fun n ω ωs =>
              |regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs /
                seThetaStar n ω ωs|)
            (1 - α) n) μ)
    (hcrit_nonneg : 0 ≤ critLim)
    (hcdfLower : cdf (gaussianReal 0 1) (-critLim) = α / 2)
    (hcdfUpper : cdf (gaussianReal 0 1) critLim = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | bootstrapAbsTestReject (T n ω)
          (bootstrapScalarLowerQuantileIndexed
            (fun n _ =>
              (ProbabilityTheory.uniformOn
                (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                  Measure (Fin (n + 1) → Fin (n + 1))))
            (fun n ω ωs =>
              |regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs /
                seThetaStar n ω ωs|)
            (1 - α) n ω)})
      atTop (𝓝 (ENNReal.ofReal α)) :=
  chapter10_indexed_abs_test_rejectionProb_strict_of_regression_tstat_finSucc_olsBetaOrZero_gapEnvelope_bounds
    (μ := μ) (X := X) (e := e) (y := y)
    (Cnum := ‖PiLp.proj (p := (2 : ℝ≥0∞)) (𝕜 := ℝ)
        (β := fun _ : Unit => ℝ) ()‖ * (‖matrixContinuousLinearMap R‖ * Cbeta))
    β R hTsample hseθ hmodel h hΩ hLinBound hBetaBound hGapTail
    hseThetaStar
    (regressionBootstrapLinearRestrictionStatisticFinSucc_eventually_abs_bound_of_beta_bound
      (R := R) (X := X) (y := y) hBetaBound)
    hseStar hα_pos hα_lt_one hstrict hcrit_meas hcrit_nonneg hcdfLower hcdfUpper

set_option linter.style.longLine false in
/-- Robust-feasible HC specialization of the indexed concrete beta-bound
finite OLS strict-CDF absolute-test wrapper. -/
theorem
    chapter10_indexed_abs_test_rejectionProb_strict_of_regression_tstat_finSucc_olsBetaOrZero_gapEnvelope_beta_bound_of_robustFeasibleHCMomentConditions
    [IsProbabilityMeasure μ]
    {k : Type*} [Fintype k] [DecidableEq k]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    {seThetaStar : ∀ n, Ω → (Fin (n + 1) → Fin (n + 1)) → ℝ}
    {T : ℕ → Ω → ℝ} {Clin Cbeta critLim α : ℝ}
    (β : k → ℝ) (R : Matrix Unit k ℝ)
    (hTsample :
      TendstoInDistribution T atTop (fun x : ℝ => x) (fun _ => μ)
        (gaussianReal 0 1))
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
    (hstrict :
      StrictMono (fun x => cdf (gaussianReal 0 1) x))
    (hcrit_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed
            (fun n _ =>
              (ProbabilityTheory.uniformOn
                (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                  Measure (Fin (n + 1) → Fin (n + 1))))
            (fun n ω ωs =>
              |regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs /
                seThetaStar n ω ωs|)
            (1 - α) n) μ)
    (hcrit_nonneg : 0 ≤ critLim)
    (hcdfLower : cdf (gaussianReal 0 1) (-critLim) = α / 2)
    (hcdfUpper : cdf (gaussianReal 0 1) critLim = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | bootstrapAbsTestReject (T n ω)
          (bootstrapScalarLowerQuantileIndexed
            (fun n _ =>
              (ProbabilityTheory.uniformOn
                (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                  Measure (Fin (n + 1) → Fin (n + 1))))
            (fun n ω ωs =>
              |regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs /
                seThetaStar n ω ωs|)
            (1 - α) n ω)})
      atTop (𝓝 (ENNReal.ofReal α)) :=
  chapter10_indexed_abs_test_rejectionProb_strict_of_regression_tstat_finSucc_olsBetaOrZero_gapEnvelope_beta_bound
    (μ := μ) (X := X) (e := e) (y := y)
    β R hTsample hseθ hm.model hm.toScoreCLTConditions hΩ hLinBound
    hBetaBound hGapTail hseThetaStar hseStar hα_pos hα_lt_one
    hstrict hcrit_meas hcrit_nonneg hcdfLower
    hcdfUpper

/-- Theorem 10.16 with the actual statistic specialized to the ordinary HC0
OLS scalar t-statistic.

The conditional bootstrap side remains the regression t-statistic route from
Theorem 10.18; this wrapper discharges the ordinary sample-statistic
standard-normal premise using the Chapter 7 HC0 inference theorem. -/
theorem
chapter10_olsHC0_abs_test_rejectionProb_tendsto_alpha_of_bootstrap_regression_tstat
    [IsProbabilityMeasure μ] [Fintype k] [DecidableEq k]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    {Pstar : ℕ → Ω → Measure Ωs}
    {TthetaStar seThetaStar : ℕ → Ω → Ωs → ℝ}
    {seθ critLim α : ℝ}
    (β : k → ℝ) (R : Matrix Unit k ℝ)
    (hm : RobustFeasibleHCMomentConditions μ X e y β)
    (hse_pos : 0 <
      linearRestrictionStdError R (heteroAsymCov μ X e))
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
    (hleft :
      ∀ ε : ℝ, 0 < ε →
        cdf ((gaussianReal 0 1).map (fun z : ℝ => |z|)) (critLim - ε) <
          1 - α)
    (hright :
      ∀ ε : ℝ, 0 < ε →
        1 - α <
          cdf ((gaussianReal 0 1).map (fun z : ℝ => |z|)) (critLim + ε))
    (hcrit_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantile Pstar
            (fun n ω ωs => |TthetaStar n ω ωs / seThetaStar n ω ωs|)
            (1 - α) n) μ)
    (hcrit_nonneg : 0 ≤ critLim)
    (hcdfLower : cdf (gaussianReal 0 1) (-critLim) = α / 2)
    (hcdfUpper : cdf (gaussianReal 0 1) critLim = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | bootstrapAbsTestReject
          (olsLinearTStatOrZero R
            (olsHetCovStar
              (stackRegressors X n ω) (stackOutcomes y n ω))
            (stackRegressors X n ω) (stackOutcomes y n ω) β
            (Real.sqrt (n : ℝ)))
          (bootstrapScalarLowerQuantile Pstar
            (fun n ω ωs => |TthetaStar n ω ωs / seThetaStar n ω ωs|)
            (1 - α) n ω)})
      atTop (𝓝 (ENNReal.ofReal α)) := by
  exact
    chapter10_bootstrap_abs_test_rejectionProb_tendsto_alpha_of_bootstrap_regression_tstat
      (μ := μ) (Pstar := Pstar) (TthetaStar := TthetaStar)
      (seThetaStar := seThetaStar)
      (T := fun n ω =>
        olsLinearTStatOrZero R
          (olsHetCovStar
            (stackRegressors X n ω) (stackOutcomes y n ω))
          (stackRegressors X n ω) (stackOutcomes y n ω) β
          (Real.sqrt (n : ℝ)))
      (seθ := seθ) (critLim := critLim) (α := α)
      (olsHC0LinTStatOrZero_tendstoInDistribution_standardNormal_of_robustFeasibleHCMomentConditions
        (μ := μ) (X := X) (e := e) (y := y) β R hm hse_pos)
      hseθ hjoint hPstar hTthetaStar hseThetaStar hseStar hα_pos
      hα_lt_one hleft hright hcrit_meas hcrit_nonneg
      hcdfLower hcdfUpper

/-- Indexed Theorem 10.16 with the actual statistic specialized to the ordinary
HC0 OLS scalar t-statistic. -/
theorem
chapter10_indexed_olsHC0_abs_test_rejectionProb_tendsto_alpha_of_bootstrap_regression_tstat
    [IsProbabilityMeasure μ] [Fintype k] [DecidableEq k]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {TthetaStar seThetaStar : ∀ n, Ω → Ωboot n → ℝ}
    {seθ critLim α : ℝ}
    (β : k → ℝ) (R : Matrix Unit k ℝ)
    (hm : RobustFeasibleHCMomentConditions μ X e y β)
    (hse_pos : 0 <
      linearRestrictionStdError R (heteroAsymCov μ X e))
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
    (hleft :
      ∀ ε : ℝ, 0 < ε →
        cdf ((gaussianReal 0 1).map (fun z : ℝ => |z|)) (critLim - ε) <
          1 - α)
    (hright :
      ∀ ε : ℝ, 0 < ε →
        1 - α <
          cdf ((gaussianReal 0 1).map (fun z : ℝ => |z|)) (critLim + ε))
    (hcrit_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed Pstar
            (fun n ω ωs => |TthetaStar n ω ωs / seThetaStar n ω ωs|)
            (1 - α) n) μ)
    (hcrit_nonneg : 0 ≤ critLim)
    (hcdfLower : cdf (gaussianReal 0 1) (-critLim) = α / 2)
    (hcdfUpper : cdf (gaussianReal 0 1) critLim = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | bootstrapAbsTestReject
          (olsLinearTStatOrZero R
            (olsHetCovStar
              (stackRegressors X n ω) (stackOutcomes y n ω))
            (stackRegressors X n ω) (stackOutcomes y n ω) β
            (Real.sqrt (n : ℝ)))
          (bootstrapScalarLowerQuantileIndexed Pstar
            (fun n ω ωs => |TthetaStar n ω ωs / seThetaStar n ω ωs|)
            (1 - α) n ω)})
      atTop (𝓝 (ENNReal.ofReal α)) := by
  exact
    chapter10_bootstrap_abs_test_rejectionProb_tendsto_alpha_indexed_of_bootstrap_regression_tstat
      (μ := μ) (Pstar := Pstar) (TthetaStar := TthetaStar)
      (seThetaStar := seThetaStar)
      (T := fun n ω =>
        olsLinearTStatOrZero R
          (olsHetCovStar
            (stackRegressors X n ω) (stackOutcomes y n ω))
          (stackRegressors X n ω) (stackOutcomes y n ω) β
          (Real.sqrt (n : ℝ)))
      (seθ := seθ) (critLim := critLim) (α := α)
      (olsHC0LinTStatOrZero_tendstoInDistribution_standardNormal_of_robustFeasibleHCMomentConditions
        (μ := μ) (X := X) (e := e) (y := y) β R hm hse_pos)
      hseθ hjoint hPstar hTthetaStar hseThetaStar hseStar hα_pos
      hα_lt_one hleft hright hcrit_meas hcrit_nonneg
      hcdfLower hcdfUpper

/-- Theorem 10.16 with the actual statistic specialized to the ordinary HC1
OLS scalar t-statistic.

The conditional bootstrap side remains the regression t-statistic route from
Theorem 10.18; this wrapper discharges the ordinary sample-statistic
standard-normal premise using the Chapter 7 HC1 inference theorem. -/
theorem
chapter10_olsHC1_abs_test_rejectionProb_tendsto_alpha_of_bootstrap_regression_tstat
    [IsProbabilityMeasure μ] [Fintype k] [DecidableEq k]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    {Pstar : ℕ → Ω → Measure Ωs}
    {TthetaStar seThetaStar : ℕ → Ω → Ωs → ℝ}
    {seθ critLim α : ℝ}
    (β : k → ℝ) (R : Matrix Unit k ℝ)
    (hm : RobustFeasibleHCMomentConditions μ X e y β)
    (hse_pos : 0 <
      linearRestrictionStdError R (heteroAsymCov μ X e))
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
    (hleft :
      ∀ ε : ℝ, 0 < ε →
        cdf ((gaussianReal 0 1).map (fun z : ℝ => |z|)) (critLim - ε) <
          1 - α)
    (hright :
      ∀ ε : ℝ, 0 < ε →
        1 - α <
          cdf ((gaussianReal 0 1).map (fun z : ℝ => |z|)) (critLim + ε))
    (hcrit_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantile Pstar
            (fun n ω ωs => |TthetaStar n ω ωs / seThetaStar n ω ωs|)
            (1 - α) n) μ)
    (hcrit_nonneg : 0 ≤ critLim)
    (hcdfLower : cdf (gaussianReal 0 1) (-critLim) = α / 2)
    (hcdfUpper : cdf (gaussianReal 0 1) critLim = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | bootstrapAbsTestReject
          (olsLinearTStatOrZero R
            (olsHetCovHC1Star
              (stackRegressors X n ω) (stackOutcomes y n ω))
            (stackRegressors X n ω) (stackOutcomes y n ω) β
            (Real.sqrt (n : ℝ)))
          (bootstrapScalarLowerQuantile Pstar
            (fun n ω ωs => |TthetaStar n ω ωs / seThetaStar n ω ωs|)
            (1 - α) n ω)})
      atTop (𝓝 (ENNReal.ofReal α)) := by
  exact
    chapter10_bootstrap_abs_test_rejectionProb_tendsto_alpha_of_bootstrap_regression_tstat
      (μ := μ) (Pstar := Pstar) (TthetaStar := TthetaStar)
      (seThetaStar := seThetaStar)
      (T := fun n ω =>
        olsLinearTStatOrZero R
          (olsHetCovHC1Star
            (stackRegressors X n ω) (stackOutcomes y n ω))
          (stackRegressors X n ω) (stackOutcomes y n ω) β
          (Real.sqrt (n : ℝ)))
      (seθ := seθ) (critLim := critLim) (α := α)
      (olsHC1LinTStatOrZero_tendstoInDistribution_standardNormal_of_robustFeasibleHCMomentConditions
        (μ := μ) (X := X) (e := e) (y := y) β R hm hse_pos)
      hseθ hjoint hPstar hTthetaStar hseThetaStar hseStar hα_pos
      hα_lt_one hleft hright hcrit_meas hcrit_nonneg
      hcdfLower hcdfUpper

/-- Indexed Theorem 10.16 with the actual statistic specialized to the ordinary
HC1 OLS scalar t-statistic. -/
theorem
chapter10_indexed_olsHC1_abs_test_rejectionProb_tendsto_alpha_of_bootstrap_regression_tstat
    [IsProbabilityMeasure μ] [Fintype k] [DecidableEq k]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {TthetaStar seThetaStar : ∀ n, Ω → Ωboot n → ℝ}
    {seθ critLim α : ℝ}
    (β : k → ℝ) (R : Matrix Unit k ℝ)
    (hm : RobustFeasibleHCMomentConditions μ X e y β)
    (hse_pos : 0 <
      linearRestrictionStdError R (heteroAsymCov μ X e))
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
    (hleft :
      ∀ ε : ℝ, 0 < ε →
        cdf ((gaussianReal 0 1).map (fun z : ℝ => |z|)) (critLim - ε) <
          1 - α)
    (hright :
      ∀ ε : ℝ, 0 < ε →
        1 - α <
          cdf ((gaussianReal 0 1).map (fun z : ℝ => |z|)) (critLim + ε))
    (hcrit_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed Pstar
            (fun n ω ωs => |TthetaStar n ω ωs / seThetaStar n ω ωs|)
            (1 - α) n) μ)
    (hcrit_nonneg : 0 ≤ critLim)
    (hcdfLower : cdf (gaussianReal 0 1) (-critLim) = α / 2)
    (hcdfUpper : cdf (gaussianReal 0 1) critLim = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | bootstrapAbsTestReject
          (olsLinearTStatOrZero R
            (olsHetCovHC1Star
              (stackRegressors X n ω) (stackOutcomes y n ω))
            (stackRegressors X n ω) (stackOutcomes y n ω) β
            (Real.sqrt (n : ℝ)))
          (bootstrapScalarLowerQuantileIndexed Pstar
            (fun n ω ωs => |TthetaStar n ω ωs / seThetaStar n ω ωs|)
            (1 - α) n ω)})
      atTop (𝓝 (ENNReal.ofReal α)) := by
  exact
    chapter10_bootstrap_abs_test_rejectionProb_tendsto_alpha_indexed_of_bootstrap_regression_tstat
      (μ := μ) (Pstar := Pstar) (TthetaStar := TthetaStar)
      (seThetaStar := seThetaStar)
      (T := fun n ω =>
        olsLinearTStatOrZero R
          (olsHetCovHC1Star
            (stackRegressors X n ω) (stackOutcomes y n ω))
          (stackRegressors X n ω) (stackOutcomes y n ω) β
          (Real.sqrt (n : ℝ)))
      (seθ := seθ) (critLim := critLim) (α := α)
      (olsHC1LinTStatOrZero_tendstoInDistribution_standardNormal_of_robustFeasibleHCMomentConditions
        (μ := μ) (X := X) (e := e) (y := y) β R hm hse_pos)
      hseθ hjoint hPstar hTthetaStar hseThetaStar hseStar hα_pos
      hα_lt_one hleft hright hcrit_meas hcrit_nonneg
      hcdfLower hcdfUpper

/-- Theorem 10.16 with the actual statistic specialized to the ordinary HC2
OLS scalar t-statistic. -/
theorem
chapter10_olsHC2_abs_test_rejectionProb_tendsto_alpha_of_bootstrap_regression_tstat
    [IsProbabilityMeasure μ] [Fintype k] [DecidableEq k]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    {Pstar : ℕ → Ω → Measure Ωs}
    {TthetaStar seThetaStar : ℕ → Ω → Ωs → ℝ}
    {seθ critLim α : ℝ}
    (β : k → ℝ) (R : Matrix Unit k ℝ)
    (hm : RobustFeasibleHCMomentConditions μ X e y β)
    (hse_pos : 0 <
      linearRestrictionStdError R (heteroAsymCov μ X e))
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
    (hleft :
      ∀ ε : ℝ, 0 < ε →
        cdf ((gaussianReal 0 1).map (fun z : ℝ => |z|)) (critLim - ε) <
          1 - α)
    (hright :
      ∀ ε : ℝ, 0 < ε →
        1 - α <
          cdf ((gaussianReal 0 1).map (fun z : ℝ => |z|)) (critLim + ε))
    (hcrit_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantile Pstar
            (fun n ω ωs => |TthetaStar n ω ωs / seThetaStar n ω ωs|)
            (1 - α) n) μ)
    (hcrit_nonneg : 0 ≤ critLim)
    (hcdfLower : cdf (gaussianReal 0 1) (-critLim) = α / 2)
    (hcdfUpper : cdf (gaussianReal 0 1) critLim = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | bootstrapAbsTestReject
          (olsLinearTStatOrZero R
            (olsHetCovHC2Star
              (stackRegressors X n ω) (stackOutcomes y n ω))
            (stackRegressors X n ω) (stackOutcomes y n ω) β
            (Real.sqrt (n : ℝ)))
          (bootstrapScalarLowerQuantile Pstar
            (fun n ω ωs => |TthetaStar n ω ωs / seThetaStar n ω ωs|)
            (1 - α) n ω)})
      atTop (𝓝 (ENNReal.ofReal α)) := by
  exact
    chapter10_bootstrap_abs_test_rejectionProb_tendsto_alpha_of_bootstrap_regression_tstat
      (μ := μ) (Pstar := Pstar) (TthetaStar := TthetaStar)
      (seThetaStar := seThetaStar)
      (T := fun n ω =>
        olsLinearTStatOrZero R
          (olsHetCovHC2Star
            (stackRegressors X n ω) (stackOutcomes y n ω))
          (stackRegressors X n ω) (stackOutcomes y n ω) β
          (Real.sqrt (n : ℝ)))
      (seθ := seθ) (critLim := critLim) (α := α)
      (olsHC2LinTStatOrZero_tendstoInDistribution_standardNormal_of_robustFeasibleHCMomentConditions
        (μ := μ) (X := X) (e := e) (y := y) β R hm hse_pos)
      hseθ hjoint hPstar hTthetaStar hseThetaStar hseStar hα_pos
      hα_lt_one hleft hright hcrit_meas hcrit_nonneg
      hcdfLower hcdfUpper

/-- Indexed Theorem 10.16 with the actual statistic specialized to the ordinary
HC2 OLS scalar t-statistic. -/
theorem
chapter10_indexed_olsHC2_abs_test_rejectionProb_tendsto_alpha_of_bootstrap_regression_tstat
    [IsProbabilityMeasure μ] [Fintype k] [DecidableEq k]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {TthetaStar seThetaStar : ∀ n, Ω → Ωboot n → ℝ}
    {seθ critLim α : ℝ}
    (β : k → ℝ) (R : Matrix Unit k ℝ)
    (hm : RobustFeasibleHCMomentConditions μ X e y β)
    (hse_pos : 0 <
      linearRestrictionStdError R (heteroAsymCov μ X e))
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
    (hleft :
      ∀ ε : ℝ, 0 < ε →
        cdf ((gaussianReal 0 1).map (fun z : ℝ => |z|)) (critLim - ε) <
          1 - α)
    (hright :
      ∀ ε : ℝ, 0 < ε →
        1 - α <
          cdf ((gaussianReal 0 1).map (fun z : ℝ => |z|)) (critLim + ε))
    (hcrit_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed Pstar
            (fun n ω ωs => |TthetaStar n ω ωs / seThetaStar n ω ωs|)
            (1 - α) n) μ)
    (hcrit_nonneg : 0 ≤ critLim)
    (hcdfLower : cdf (gaussianReal 0 1) (-critLim) = α / 2)
    (hcdfUpper : cdf (gaussianReal 0 1) critLim = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | bootstrapAbsTestReject
          (olsLinearTStatOrZero R
            (olsHetCovHC2Star
              (stackRegressors X n ω) (stackOutcomes y n ω))
            (stackRegressors X n ω) (stackOutcomes y n ω) β
            (Real.sqrt (n : ℝ)))
          (bootstrapScalarLowerQuantileIndexed Pstar
            (fun n ω ωs => |TthetaStar n ω ωs / seThetaStar n ω ωs|)
            (1 - α) n ω)})
      atTop (𝓝 (ENNReal.ofReal α)) := by
  exact
    chapter10_bootstrap_abs_test_rejectionProb_tendsto_alpha_indexed_of_bootstrap_regression_tstat
      (μ := μ) (Pstar := Pstar) (TthetaStar := TthetaStar)
      (seThetaStar := seThetaStar)
      (T := fun n ω =>
        olsLinearTStatOrZero R
          (olsHetCovHC2Star
            (stackRegressors X n ω) (stackOutcomes y n ω))
          (stackRegressors X n ω) (stackOutcomes y n ω) β
          (Real.sqrt (n : ℝ)))
      (seθ := seθ) (critLim := critLim) (α := α)
      (olsHC2LinTStatOrZero_tendstoInDistribution_standardNormal_of_robustFeasibleHCMomentConditions
        (μ := μ) (X := X) (e := e) (y := y) β R hm hse_pos)
      hseθ hjoint hPstar hTthetaStar hseThetaStar hseStar hα_pos
      hα_lt_one hleft hright hcrit_meas hcrit_nonneg
      hcdfLower hcdfUpper

/-- Theorem 10.16 with the actual statistic specialized to the ordinary HC3
OLS scalar t-statistic. -/
theorem
chapter10_olsHC3_abs_test_rejectionProb_tendsto_alpha_of_bootstrap_regression_tstat
    [IsProbabilityMeasure μ] [Fintype k] [DecidableEq k]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    {Pstar : ℕ → Ω → Measure Ωs}
    {TthetaStar seThetaStar : ℕ → Ω → Ωs → ℝ}
    {seθ critLim α : ℝ}
    (β : k → ℝ) (R : Matrix Unit k ℝ)
    (hm : RobustFeasibleHCMomentConditions μ X e y β)
    (hse_pos : 0 <
      linearRestrictionStdError R (heteroAsymCov μ X e))
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
    (hleft :
      ∀ ε : ℝ, 0 < ε →
        cdf ((gaussianReal 0 1).map (fun z : ℝ => |z|)) (critLim - ε) <
          1 - α)
    (hright :
      ∀ ε : ℝ, 0 < ε →
        1 - α <
          cdf ((gaussianReal 0 1).map (fun z : ℝ => |z|)) (critLim + ε))
    (hcrit_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantile Pstar
            (fun n ω ωs => |TthetaStar n ω ωs / seThetaStar n ω ωs|)
            (1 - α) n) μ)
    (hcrit_nonneg : 0 ≤ critLim)
    (hcdfLower : cdf (gaussianReal 0 1) (-critLim) = α / 2)
    (hcdfUpper : cdf (gaussianReal 0 1) critLim = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | bootstrapAbsTestReject
          (olsLinearTStatOrZero R
            (olsHetCovHC3Star
              (stackRegressors X n ω) (stackOutcomes y n ω))
            (stackRegressors X n ω) (stackOutcomes y n ω) β
            (Real.sqrt (n : ℝ)))
          (bootstrapScalarLowerQuantile Pstar
            (fun n ω ωs => |TthetaStar n ω ωs / seThetaStar n ω ωs|)
            (1 - α) n ω)})
      atTop (𝓝 (ENNReal.ofReal α)) := by
  exact
    chapter10_bootstrap_abs_test_rejectionProb_tendsto_alpha_of_bootstrap_regression_tstat
      (μ := μ) (Pstar := Pstar) (TthetaStar := TthetaStar)
      (seThetaStar := seThetaStar)
      (T := fun n ω =>
        olsLinearTStatOrZero R
          (olsHetCovHC3Star
            (stackRegressors X n ω) (stackOutcomes y n ω))
          (stackRegressors X n ω) (stackOutcomes y n ω) β
          (Real.sqrt (n : ℝ)))
      (seθ := seθ) (critLim := critLim) (α := α)
      (olsHC3LinTStatOrZero_tendstoInDistribution_standardNormal_of_robustFeasibleHCMomentConditions
        (μ := μ) (X := X) (e := e) (y := y) β R hm hse_pos)
      hseθ hjoint hPstar hTthetaStar hseThetaStar hseStar hα_pos
      hα_lt_one hleft hright hcrit_meas hcrit_nonneg
      hcdfLower hcdfUpper

/-- Indexed Theorem 10.16 with the actual statistic specialized to the ordinary
HC3 OLS scalar t-statistic. -/
theorem
chapter10_indexed_olsHC3_abs_test_rejectionProb_tendsto_alpha_of_bootstrap_regression_tstat
    [IsProbabilityMeasure μ] [Fintype k] [DecidableEq k]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {TthetaStar seThetaStar : ∀ n, Ω → Ωboot n → ℝ}
    {seθ critLim α : ℝ}
    (β : k → ℝ) (R : Matrix Unit k ℝ)
    (hm : RobustFeasibleHCMomentConditions μ X e y β)
    (hse_pos : 0 <
      linearRestrictionStdError R (heteroAsymCov μ X e))
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
    (hleft :
      ∀ ε : ℝ, 0 < ε →
        cdf ((gaussianReal 0 1).map (fun z : ℝ => |z|)) (critLim - ε) <
          1 - α)
    (hright :
      ∀ ε : ℝ, 0 < ε →
        1 - α <
          cdf ((gaussianReal 0 1).map (fun z : ℝ => |z|)) (critLim + ε))
    (hcrit_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed Pstar
            (fun n ω ωs => |TthetaStar n ω ωs / seThetaStar n ω ωs|)
            (1 - α) n) μ)
    (hcrit_nonneg : 0 ≤ critLim)
    (hcdfLower : cdf (gaussianReal 0 1) (-critLim) = α / 2)
    (hcdfUpper : cdf (gaussianReal 0 1) critLim = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | bootstrapAbsTestReject
          (olsLinearTStatOrZero R
            (olsHetCovHC3Star
              (stackRegressors X n ω) (stackOutcomes y n ω))
            (stackRegressors X n ω) (stackOutcomes y n ω) β
            (Real.sqrt (n : ℝ)))
          (bootstrapScalarLowerQuantileIndexed Pstar
            (fun n ω ωs => |TthetaStar n ω ωs / seThetaStar n ω ωs|)
            (1 - α) n ω)})
      atTop (𝓝 (ENNReal.ofReal α)) := by
  exact
    chapter10_bootstrap_abs_test_rejectionProb_tendsto_alpha_indexed_of_bootstrap_regression_tstat
      (μ := μ) (Pstar := Pstar) (TthetaStar := TthetaStar)
      (seThetaStar := seThetaStar)
      (T := fun n ω =>
        olsLinearTStatOrZero R
          (olsHetCovHC3Star
            (stackRegressors X n ω) (stackOutcomes y n ω))
          (stackRegressors X n ω) (stackOutcomes y n ω) β
          (Real.sqrt (n : ℝ)))
      (seθ := seθ) (critLim := critLim) (α := α)
      (olsHC3LinTStatOrZero_tendstoInDistribution_standardNormal_of_robustFeasibleHCMomentConditions
        (μ := μ) (X := X) (e := e) (y := y) β R hm hse_pos)
      hseθ hjoint hPstar hTthetaStar hseThetaStar hseStar hα_pos
      hα_lt_one hleft hright hcrit_meas hcrit_nonneg
      hcdfLower hcdfUpper

/-- Strict-CDF counterpart of Theorem 10.16 with the actual statistic
specialized to the ordinary HC0 OLS scalar t-statistic. -/
theorem
chapter10_olsHC0_abs_test_rejectionProb_strict_of_bootstrap_regression_tstat
    [IsProbabilityMeasure μ] [Fintype k] [DecidableEq k]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    {Pstar : ℕ → Ω → Measure Ωs}
    {TthetaStar seThetaStar : ℕ → Ω → Ωs → ℝ}
    {seθ critLim α : ℝ}
    (β : k → ℝ) (R : Matrix Unit k ℝ)
    (hm : RobustFeasibleHCMomentConditions μ X e y β)
    (hse_pos : 0 <
      linearRestrictionStdError R (heteroAsymCov μ X e))
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
    (hstrict :
      StrictMono (fun x => cdf (gaussianReal 0 1) x))
    (hcrit_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantile Pstar
            (fun n ω ωs => |TthetaStar n ω ωs / seThetaStar n ω ωs|)
            (1 - α) n) μ)
    (hcrit_nonneg : 0 ≤ critLim)
    (hcdfLower : cdf (gaussianReal 0 1) (-critLim) = α / 2)
    (hcdfUpper : cdf (gaussianReal 0 1) critLim = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | bootstrapAbsTestReject
          (olsLinearTStatOrZero R
            (olsHetCovStar
              (stackRegressors X n ω) (stackOutcomes y n ω))
            (stackRegressors X n ω) (stackOutcomes y n ω) β
            (Real.sqrt (n : ℝ)))
          (bootstrapScalarLowerQuantile Pstar
            (fun n ω ωs => |TthetaStar n ω ωs / seThetaStar n ω ωs|)
            (1 - α) n ω)})
      atTop (𝓝 (ENNReal.ofReal α)) := by
  exact
    chapter10_bootstrap_abs_test_rejectionProb_strict_of_bootstrap_regression_tstat
      (μ := μ) (Pstar := Pstar) (TthetaStar := TthetaStar)
      (seThetaStar := seThetaStar)
      (T := fun n ω =>
        olsLinearTStatOrZero R
          (olsHetCovStar
            (stackRegressors X n ω) (stackOutcomes y n ω))
          (stackRegressors X n ω) (stackOutcomes y n ω) β
          (Real.sqrt (n : ℝ)))
      (seθ := seθ) (critLim := critLim) (α := α)
      (olsHC0LinTStatOrZero_tendstoInDistribution_standardNormal_of_robustFeasibleHCMomentConditions
        (μ := μ) (X := X) (e := e) (y := y) β R hm hse_pos)
      hseθ hjoint hPstar hTthetaStar hseThetaStar hseStar hα_pos
      hα_lt_one hstrict hcrit_meas hcrit_nonneg
      hcdfLower hcdfUpper

/-- Indexed strict-CDF counterpart of Theorem 10.16 with the actual statistic
specialized to the ordinary HC0 OLS scalar t-statistic. -/
theorem
chapter10_indexed_olsHC0_abs_test_rejectionProb_strict_of_bootstrap_regression_tstat
    [IsProbabilityMeasure μ] [Fintype k] [DecidableEq k]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {TthetaStar seThetaStar : ∀ n, Ω → Ωboot n → ℝ}
    {seθ critLim α : ℝ}
    (β : k → ℝ) (R : Matrix Unit k ℝ)
    (hm : RobustFeasibleHCMomentConditions μ X e y β)
    (hse_pos : 0 <
      linearRestrictionStdError R (heteroAsymCov μ X e))
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
    (hstrict :
      StrictMono (fun x => cdf (gaussianReal 0 1) x))
    (hcrit_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed Pstar
            (fun n ω ωs => |TthetaStar n ω ωs / seThetaStar n ω ωs|)
            (1 - α) n) μ)
    (hcrit_nonneg : 0 ≤ critLim)
    (hcdfLower : cdf (gaussianReal 0 1) (-critLim) = α / 2)
    (hcdfUpper : cdf (gaussianReal 0 1) critLim = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | bootstrapAbsTestReject
          (olsLinearTStatOrZero R
            (olsHetCovStar
              (stackRegressors X n ω) (stackOutcomes y n ω))
            (stackRegressors X n ω) (stackOutcomes y n ω) β
            (Real.sqrt (n : ℝ)))
          (bootstrapScalarLowerQuantileIndexed Pstar
            (fun n ω ωs => |TthetaStar n ω ωs / seThetaStar n ω ωs|)
            (1 - α) n ω)})
      atTop (𝓝 (ENNReal.ofReal α)) := by
  exact
    chapter10_indexed_abs_test_rejectionProb_strict_of_bootstrap_regression_tstat
      (μ := μ) (Pstar := Pstar) (TthetaStar := TthetaStar)
      (seThetaStar := seThetaStar)
      (T := fun n ω =>
        olsLinearTStatOrZero R
          (olsHetCovStar
            (stackRegressors X n ω) (stackOutcomes y n ω))
          (stackRegressors X n ω) (stackOutcomes y n ω) β
          (Real.sqrt (n : ℝ)))
      (seθ := seθ) (critLim := critLim) (α := α)
      (olsHC0LinTStatOrZero_tendstoInDistribution_standardNormal_of_robustFeasibleHCMomentConditions
        (μ := μ) (X := X) (e := e) (y := y) β R hm hse_pos)
      hseθ hjoint hPstar hTthetaStar hseThetaStar hseStar hα_pos
      hα_lt_one hstrict hcrit_meas hcrit_nonneg
      hcdfLower hcdfUpper

/-- Strict-CDF counterpart of Theorem 10.16 with the actual statistic
specialized to the ordinary HC1 OLS scalar t-statistic. -/
theorem
chapter10_olsHC1_abs_test_rejectionProb_strict_of_bootstrap_regression_tstat
    [IsProbabilityMeasure μ] [Fintype k] [DecidableEq k]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    {Pstar : ℕ → Ω → Measure Ωs}
    {TthetaStar seThetaStar : ℕ → Ω → Ωs → ℝ}
    {seθ critLim α : ℝ}
    (β : k → ℝ) (R : Matrix Unit k ℝ)
    (hm : RobustFeasibleHCMomentConditions μ X e y β)
    (hse_pos : 0 <
      linearRestrictionStdError R (heteroAsymCov μ X e))
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
    (hstrict :
      StrictMono (fun x => cdf (gaussianReal 0 1) x))
    (hcrit_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantile Pstar
            (fun n ω ωs => |TthetaStar n ω ωs / seThetaStar n ω ωs|)
            (1 - α) n) μ)
    (hcrit_nonneg : 0 ≤ critLim)
    (hcdfLower : cdf (gaussianReal 0 1) (-critLim) = α / 2)
    (hcdfUpper : cdf (gaussianReal 0 1) critLim = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | bootstrapAbsTestReject
          (olsLinearTStatOrZero R
            (olsHetCovHC1Star
              (stackRegressors X n ω) (stackOutcomes y n ω))
            (stackRegressors X n ω) (stackOutcomes y n ω) β
            (Real.sqrt (n : ℝ)))
          (bootstrapScalarLowerQuantile Pstar
            (fun n ω ωs => |TthetaStar n ω ωs / seThetaStar n ω ωs|)
            (1 - α) n ω)})
      atTop (𝓝 (ENNReal.ofReal α)) := by
  exact
    chapter10_bootstrap_abs_test_rejectionProb_strict_of_bootstrap_regression_tstat
      (μ := μ) (Pstar := Pstar) (TthetaStar := TthetaStar)
      (seThetaStar := seThetaStar)
      (T := fun n ω =>
        olsLinearTStatOrZero R
          (olsHetCovHC1Star
            (stackRegressors X n ω) (stackOutcomes y n ω))
          (stackRegressors X n ω) (stackOutcomes y n ω) β
          (Real.sqrt (n : ℝ)))
      (seθ := seθ) (critLim := critLim) (α := α)
      (olsHC1LinTStatOrZero_tendstoInDistribution_standardNormal_of_robustFeasibleHCMomentConditions
        (μ := μ) (X := X) (e := e) (y := y) β R hm hse_pos)
      hseθ hjoint hPstar hTthetaStar hseThetaStar hseStar hα_pos
      hα_lt_one hstrict hcrit_meas hcrit_nonneg
      hcdfLower hcdfUpper

/-- Indexed strict-CDF counterpart of Theorem 10.16 with the actual statistic
specialized to the ordinary HC1 OLS scalar t-statistic. -/
theorem
chapter10_indexed_olsHC1_abs_test_rejectionProb_strict_of_bootstrap_regression_tstat
    [IsProbabilityMeasure μ] [Fintype k] [DecidableEq k]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {TthetaStar seThetaStar : ∀ n, Ω → Ωboot n → ℝ}
    {seθ critLim α : ℝ}
    (β : k → ℝ) (R : Matrix Unit k ℝ)
    (hm : RobustFeasibleHCMomentConditions μ X e y β)
    (hse_pos : 0 <
      linearRestrictionStdError R (heteroAsymCov μ X e))
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
    (hstrict :
      StrictMono (fun x => cdf (gaussianReal 0 1) x))
    (hcrit_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed Pstar
            (fun n ω ωs => |TthetaStar n ω ωs / seThetaStar n ω ωs|)
            (1 - α) n) μ)
    (hcrit_nonneg : 0 ≤ critLim)
    (hcdfLower : cdf (gaussianReal 0 1) (-critLim) = α / 2)
    (hcdfUpper : cdf (gaussianReal 0 1) critLim = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | bootstrapAbsTestReject
          (olsLinearTStatOrZero R
            (olsHetCovHC1Star
              (stackRegressors X n ω) (stackOutcomes y n ω))
            (stackRegressors X n ω) (stackOutcomes y n ω) β
            (Real.sqrt (n : ℝ)))
          (bootstrapScalarLowerQuantileIndexed Pstar
            (fun n ω ωs => |TthetaStar n ω ωs / seThetaStar n ω ωs|)
            (1 - α) n ω)})
      atTop (𝓝 (ENNReal.ofReal α)) := by
  exact
    chapter10_indexed_abs_test_rejectionProb_strict_of_bootstrap_regression_tstat
      (μ := μ) (Pstar := Pstar) (TthetaStar := TthetaStar)
      (seThetaStar := seThetaStar)
      (T := fun n ω =>
        olsLinearTStatOrZero R
          (olsHetCovHC1Star
            (stackRegressors X n ω) (stackOutcomes y n ω))
          (stackRegressors X n ω) (stackOutcomes y n ω) β
          (Real.sqrt (n : ℝ)))
      (seθ := seθ) (critLim := critLim) (α := α)
      (olsHC1LinTStatOrZero_tendstoInDistribution_standardNormal_of_robustFeasibleHCMomentConditions
        (μ := μ) (X := X) (e := e) (y := y) β R hm hse_pos)
      hseθ hjoint hPstar hTthetaStar hseThetaStar hseStar hα_pos
      hα_lt_one hstrict hcrit_meas hcrit_nonneg
      hcdfLower hcdfUpper

/-- Strict-CDF counterpart of Theorem 10.16 with the actual statistic
specialized to the ordinary HC2 OLS scalar t-statistic. -/
theorem
chapter10_olsHC2_abs_test_rejectionProb_strict_of_bootstrap_regression_tstat
    [IsProbabilityMeasure μ] [Fintype k] [DecidableEq k]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    {Pstar : ℕ → Ω → Measure Ωs}
    {TthetaStar seThetaStar : ℕ → Ω → Ωs → ℝ}
    {seθ critLim α : ℝ}
    (β : k → ℝ) (R : Matrix Unit k ℝ)
    (hm : RobustFeasibleHCMomentConditions μ X e y β)
    (hse_pos : 0 <
      linearRestrictionStdError R (heteroAsymCov μ X e))
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
    (hstrict :
      StrictMono (fun x => cdf (gaussianReal 0 1) x))
    (hcrit_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantile Pstar
            (fun n ω ωs => |TthetaStar n ω ωs / seThetaStar n ω ωs|)
            (1 - α) n) μ)
    (hcrit_nonneg : 0 ≤ critLim)
    (hcdfLower : cdf (gaussianReal 0 1) (-critLim) = α / 2)
    (hcdfUpper : cdf (gaussianReal 0 1) critLim = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | bootstrapAbsTestReject
          (olsLinearTStatOrZero R
            (olsHetCovHC2Star
              (stackRegressors X n ω) (stackOutcomes y n ω))
            (stackRegressors X n ω) (stackOutcomes y n ω) β
            (Real.sqrt (n : ℝ)))
          (bootstrapScalarLowerQuantile Pstar
            (fun n ω ωs => |TthetaStar n ω ωs / seThetaStar n ω ωs|)
            (1 - α) n ω)})
      atTop (𝓝 (ENNReal.ofReal α)) := by
  exact
    chapter10_bootstrap_abs_test_rejectionProb_strict_of_bootstrap_regression_tstat
      (μ := μ) (Pstar := Pstar) (TthetaStar := TthetaStar)
      (seThetaStar := seThetaStar)
      (T := fun n ω =>
        olsLinearTStatOrZero R
          (olsHetCovHC2Star
            (stackRegressors X n ω) (stackOutcomes y n ω))
          (stackRegressors X n ω) (stackOutcomes y n ω) β
          (Real.sqrt (n : ℝ)))
      (seθ := seθ) (critLim := critLim) (α := α)
      (olsHC2LinTStatOrZero_tendstoInDistribution_standardNormal_of_robustFeasibleHCMomentConditions
        (μ := μ) (X := X) (e := e) (y := y) β R hm hse_pos)
      hseθ hjoint hPstar hTthetaStar hseThetaStar hseStar hα_pos
      hα_lt_one hstrict hcrit_meas hcrit_nonneg
      hcdfLower hcdfUpper

/-- Indexed strict-CDF counterpart of Theorem 10.16 with the actual statistic
specialized to the ordinary HC2 OLS scalar t-statistic. -/
theorem
chapter10_indexed_olsHC2_abs_test_rejectionProb_strict_of_bootstrap_regression_tstat
    [IsProbabilityMeasure μ] [Fintype k] [DecidableEq k]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {TthetaStar seThetaStar : ∀ n, Ω → Ωboot n → ℝ}
    {seθ critLim α : ℝ}
    (β : k → ℝ) (R : Matrix Unit k ℝ)
    (hm : RobustFeasibleHCMomentConditions μ X e y β)
    (hse_pos : 0 <
      linearRestrictionStdError R (heteroAsymCov μ X e))
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
    (hstrict :
      StrictMono (fun x => cdf (gaussianReal 0 1) x))
    (hcrit_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed Pstar
            (fun n ω ωs => |TthetaStar n ω ωs / seThetaStar n ω ωs|)
            (1 - α) n) μ)
    (hcrit_nonneg : 0 ≤ critLim)
    (hcdfLower : cdf (gaussianReal 0 1) (-critLim) = α / 2)
    (hcdfUpper : cdf (gaussianReal 0 1) critLim = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | bootstrapAbsTestReject
          (olsLinearTStatOrZero R
            (olsHetCovHC2Star
              (stackRegressors X n ω) (stackOutcomes y n ω))
            (stackRegressors X n ω) (stackOutcomes y n ω) β
            (Real.sqrt (n : ℝ)))
          (bootstrapScalarLowerQuantileIndexed Pstar
            (fun n ω ωs => |TthetaStar n ω ωs / seThetaStar n ω ωs|)
            (1 - α) n ω)})
      atTop (𝓝 (ENNReal.ofReal α)) := by
  exact
    chapter10_indexed_abs_test_rejectionProb_strict_of_bootstrap_regression_tstat
      (μ := μ) (Pstar := Pstar) (TthetaStar := TthetaStar)
      (seThetaStar := seThetaStar)
      (T := fun n ω =>
        olsLinearTStatOrZero R
          (olsHetCovHC2Star
            (stackRegressors X n ω) (stackOutcomes y n ω))
          (stackRegressors X n ω) (stackOutcomes y n ω) β
          (Real.sqrt (n : ℝ)))
      (seθ := seθ) (critLim := critLim) (α := α)
      (olsHC2LinTStatOrZero_tendstoInDistribution_standardNormal_of_robustFeasibleHCMomentConditions
        (μ := μ) (X := X) (e := e) (y := y) β R hm hse_pos)
      hseθ hjoint hPstar hTthetaStar hseThetaStar hseStar hα_pos
      hα_lt_one hstrict hcrit_meas hcrit_nonneg
      hcdfLower hcdfUpper

/-- Strict-CDF counterpart of Theorem 10.16 with the actual statistic
specialized to the ordinary HC3 OLS scalar t-statistic. -/
theorem
chapter10_olsHC3_abs_test_rejectionProb_strict_of_bootstrap_regression_tstat
    [IsProbabilityMeasure μ] [Fintype k] [DecidableEq k]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    {Pstar : ℕ → Ω → Measure Ωs}
    {TthetaStar seThetaStar : ℕ → Ω → Ωs → ℝ}
    {seθ critLim α : ℝ}
    (β : k → ℝ) (R : Matrix Unit k ℝ)
    (hm : RobustFeasibleHCMomentConditions μ X e y β)
    (hse_pos : 0 <
      linearRestrictionStdError R (heteroAsymCov μ X e))
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
    (hstrict :
      StrictMono (fun x => cdf (gaussianReal 0 1) x))
    (hcrit_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantile Pstar
            (fun n ω ωs => |TthetaStar n ω ωs / seThetaStar n ω ωs|)
            (1 - α) n) μ)
    (hcrit_nonneg : 0 ≤ critLim)
    (hcdfLower : cdf (gaussianReal 0 1) (-critLim) = α / 2)
    (hcdfUpper : cdf (gaussianReal 0 1) critLim = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | bootstrapAbsTestReject
          (olsLinearTStatOrZero R
            (olsHetCovHC3Star
              (stackRegressors X n ω) (stackOutcomes y n ω))
            (stackRegressors X n ω) (stackOutcomes y n ω) β
            (Real.sqrt (n : ℝ)))
          (bootstrapScalarLowerQuantile Pstar
            (fun n ω ωs => |TthetaStar n ω ωs / seThetaStar n ω ωs|)
            (1 - α) n ω)})
      atTop (𝓝 (ENNReal.ofReal α)) := by
  exact
    chapter10_bootstrap_abs_test_rejectionProb_strict_of_bootstrap_regression_tstat
      (μ := μ) (Pstar := Pstar) (TthetaStar := TthetaStar)
      (seThetaStar := seThetaStar)
      (T := fun n ω =>
        olsLinearTStatOrZero R
          (olsHetCovHC3Star
            (stackRegressors X n ω) (stackOutcomes y n ω))
          (stackRegressors X n ω) (stackOutcomes y n ω) β
          (Real.sqrt (n : ℝ)))
      (seθ := seθ) (critLim := critLim) (α := α)
      (olsHC3LinTStatOrZero_tendstoInDistribution_standardNormal_of_robustFeasibleHCMomentConditions
        (μ := μ) (X := X) (e := e) (y := y) β R hm hse_pos)
      hseθ hjoint hPstar hTthetaStar hseThetaStar hseStar hα_pos
      hα_lt_one hstrict hcrit_meas hcrit_nonneg
      hcdfLower hcdfUpper

/-- Indexed strict-CDF counterpart of Theorem 10.16 with the actual statistic
specialized to the ordinary HC3 OLS scalar t-statistic. -/
theorem
chapter10_indexed_olsHC3_abs_test_rejectionProb_strict_of_bootstrap_regression_tstat
    [IsProbabilityMeasure μ] [Fintype k] [DecidableEq k]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {TthetaStar seThetaStar : ∀ n, Ω → Ωboot n → ℝ}
    {seθ critLim α : ℝ}
    (β : k → ℝ) (R : Matrix Unit k ℝ)
    (hm : RobustFeasibleHCMomentConditions μ X e y β)
    (hse_pos : 0 <
      linearRestrictionStdError R (heteroAsymCov μ X e))
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
    (hstrict :
      StrictMono (fun x => cdf (gaussianReal 0 1) x))
    (hcrit_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed Pstar
            (fun n ω ωs => |TthetaStar n ω ωs / seThetaStar n ω ωs|)
            (1 - α) n) μ)
    (hcrit_nonneg : 0 ≤ critLim)
    (hcdfLower : cdf (gaussianReal 0 1) (-critLim) = α / 2)
    (hcdfUpper : cdf (gaussianReal 0 1) critLim = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | bootstrapAbsTestReject
          (olsLinearTStatOrZero R
            (olsHetCovHC3Star
              (stackRegressors X n ω) (stackOutcomes y n ω))
            (stackRegressors X n ω) (stackOutcomes y n ω) β
            (Real.sqrt (n : ℝ)))
          (bootstrapScalarLowerQuantileIndexed Pstar
            (fun n ω ωs => |TthetaStar n ω ωs / seThetaStar n ω ωs|)
            (1 - α) n ω)})
      atTop (𝓝 (ENNReal.ofReal α)) := by
  exact
    chapter10_indexed_abs_test_rejectionProb_strict_of_bootstrap_regression_tstat
      (μ := μ) (Pstar := Pstar) (TthetaStar := TthetaStar)
      (seThetaStar := seThetaStar)
      (T := fun n ω =>
        olsLinearTStatOrZero R
          (olsHetCovHC3Star
            (stackRegressors X n ω) (stackOutcomes y n ω))
          (stackRegressors X n ω) (stackOutcomes y n ω) β
          (Real.sqrt (n : ℝ)))
      (seθ := seθ) (critLim := critLim) (α := α)
      (olsHC3LinTStatOrZero_tendstoInDistribution_standardNormal_of_robustFeasibleHCMomentConditions
        (μ := μ) (X := X) (e := e) (y := y) β R hm hse_pos)
      hseθ hjoint hPstar hTthetaStar hseThetaStar hseStar hα_pos
      hα_lt_one hstrict hcrit_meas hcrit_nonneg
      hcdfLower hcdfUpper

set_option linter.style.longLine false in
/-- Indexed local-CDF two-sided bootstrap-test calibration with the actual
sample statistic specialized to ordinary HC0 OLS and the bootstrap critical
value specialized to the concrete finite ordinary-bootstrap OLS
linear-restriction t-statistic.  The bootstrap numerator bound is discharged
from the coefficient-statistic norm bound. -/
theorem
    chapter10_indexed_olsHC0_abs_test_rejectionProb_tendsto_alpha_finSucc_olsBetaOrZero_gapEnvelope_beta_bound
    [IsProbabilityMeasure μ] [Fintype k] [DecidableEq k]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    {seThetaStar : ∀ n, Ω → (Fin (n + 1) → Fin (n + 1)) → ℝ}
    {Clin Cbeta critLim α : ℝ}
    (β : k → ℝ) (R : Matrix Unit k ℝ)
    (hse_pos : 0 <
      linearRestrictionStdError R (heteroAsymCov μ X e))
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
    (hleft :
      ∀ ε : ℝ, 0 < ε →
        cdf ((gaussianReal 0 1).map (fun z : ℝ => |z|)) (critLim - ε) <
          1 - α)
    (hright :
      ∀ ε : ℝ, 0 < ε →
        1 - α <
          cdf ((gaussianReal 0 1).map (fun z : ℝ => |z|)) (critLim + ε))
    (hcrit_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed
            (fun n _ =>
              (ProbabilityTheory.uniformOn
                (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                  Measure (Fin (n + 1) → Fin (n + 1))))
            (fun n ω ωs =>
              |regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs /
                seThetaStar n ω ωs|)
            (1 - α) n) μ)
    (hcrit_nonneg : 0 ≤ critLim)
    (hcdfLower : cdf (gaussianReal 0 1) (-critLim) = α / 2)
    (hcdfUpper : cdf (gaussianReal 0 1) critLim = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | bootstrapAbsTestReject
          (olsLinearTStatOrZero R
            (olsHetCovStar
              (stackRegressors X n ω) (stackOutcomes y n ω))
            (stackRegressors X n ω) (stackOutcomes y n ω) β
            (Real.sqrt (n : ℝ)))
          (bootstrapScalarLowerQuantileIndexed
            (fun n _ =>
              (ProbabilityTheory.uniformOn
                (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                  Measure (Fin (n + 1) → Fin (n + 1))))
            (fun n ω ωs =>
              |regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs /
                seThetaStar n ω ωs|)
            (1 - α) n ω)})
      atTop (𝓝 (ENNReal.ofReal α)) :=
  chapter10_indexed_abs_test_rejectionProb_of_regression_tstat_finSucc_olsBetaOrZero_gapEnvelope_beta_bound_of_robustFeasibleHCMomentConditions
    (μ := μ) (X := X) (e := e) (y := y)
    β R
    (olsHC0LinTStatOrZero_tendstoInDistribution_standardNormal_of_robustFeasibleHCMomentConditions
      (μ := μ) (X := X) (e := e) (y := y) β R hm hse_pos)
    hse_pos hm hΩ hLinBound hBetaBound hGapTail hseThetaStar
    hseStar hα_pos hα_lt_one hleft hright hcrit_meas
    hcrit_nonneg hcdfLower hcdfUpper

set_option linter.style.longLine false in
/-- Strict-CDF counterpart of
`chapter10_indexed_olsHC0_abs_test_rejectionProb_tendsto_alpha_finSucc_olsBetaOrZero_gapEnvelope_beta_bound`. -/
theorem
    chapter10_indexed_olsHC0_abs_test_rejectionProb_strict_finSucc_olsBetaOrZero_gapEnvelope_beta_bound
    [IsProbabilityMeasure μ] [Fintype k] [DecidableEq k]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    {seThetaStar : ∀ n, Ω → (Fin (n + 1) → Fin (n + 1)) → ℝ}
    {Clin Cbeta critLim α : ℝ}
    (β : k → ℝ) (R : Matrix Unit k ℝ)
    (hse_pos : 0 <
      linearRestrictionStdError R (heteroAsymCov μ X e))
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
    (hstrict :
      StrictMono (fun x => cdf (gaussianReal 0 1) x))
    (hcrit_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed
            (fun n _ =>
              (ProbabilityTheory.uniformOn
                (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                  Measure (Fin (n + 1) → Fin (n + 1))))
            (fun n ω ωs =>
              |regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs /
                seThetaStar n ω ωs|)
            (1 - α) n) μ)
    (hcrit_nonneg : 0 ≤ critLim)
    (hcdfLower : cdf (gaussianReal 0 1) (-critLim) = α / 2)
    (hcdfUpper : cdf (gaussianReal 0 1) critLim = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | bootstrapAbsTestReject
          (olsLinearTStatOrZero R
            (olsHetCovStar
              (stackRegressors X n ω) (stackOutcomes y n ω))
            (stackRegressors X n ω) (stackOutcomes y n ω) β
            (Real.sqrt (n : ℝ)))
          (bootstrapScalarLowerQuantileIndexed
            (fun n _ =>
              (ProbabilityTheory.uniformOn
                (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                  Measure (Fin (n + 1) → Fin (n + 1))))
            (fun n ω ωs =>
              |regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs /
                seThetaStar n ω ωs|)
            (1 - α) n ω)})
      atTop (𝓝 (ENNReal.ofReal α)) :=
  chapter10_indexed_abs_test_rejectionProb_strict_of_regression_tstat_finSucc_olsBetaOrZero_gapEnvelope_beta_bound_of_robustFeasibleHCMomentConditions
    (μ := μ) (X := X) (e := e) (y := y)
    β R
    (olsHC0LinTStatOrZero_tendstoInDistribution_standardNormal_of_robustFeasibleHCMomentConditions
      (μ := μ) (X := X) (e := e) (y := y) β R hm hse_pos)
    hse_pos hm hΩ hLinBound hBetaBound hGapTail hseThetaStar
    hseStar hα_pos hα_lt_one hstrict hcrit_meas hcrit_nonneg hcdfLower hcdfUpper

set_option linter.style.longLine false in
/-- Indexed local-CDF two-sided bootstrap-test calibration with the actual
sample statistic specialized to ordinary HC1 OLS and the bootstrap critical
value specialized to the concrete finite ordinary-bootstrap OLS
linear-restriction t-statistic. -/
theorem
    chapter10_indexed_olsHC1_abs_test_rejectionProb_tendsto_alpha_finSucc_olsBetaOrZero_gapEnvelope_beta_bound
    [IsProbabilityMeasure μ] [Fintype k] [DecidableEq k]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    {seThetaStar : ∀ n, Ω → (Fin (n + 1) → Fin (n + 1)) → ℝ}
    {Clin Cbeta critLim α : ℝ}
    (β : k → ℝ) (R : Matrix Unit k ℝ)
    (hse_pos : 0 <
      linearRestrictionStdError R (heteroAsymCov μ X e))
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
    (hleft :
      ∀ ε : ℝ, 0 < ε →
        cdf ((gaussianReal 0 1).map (fun z : ℝ => |z|)) (critLim - ε) <
          1 - α)
    (hright :
      ∀ ε : ℝ, 0 < ε →
        1 - α <
          cdf ((gaussianReal 0 1).map (fun z : ℝ => |z|)) (critLim + ε))
    (hcrit_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed
            (fun n _ =>
              (ProbabilityTheory.uniformOn
                (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                  Measure (Fin (n + 1) → Fin (n + 1))))
            (fun n ω ωs =>
              |regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs /
                seThetaStar n ω ωs|)
            (1 - α) n) μ)
    (hcrit_nonneg : 0 ≤ critLim)
    (hcdfLower : cdf (gaussianReal 0 1) (-critLim) = α / 2)
    (hcdfUpper : cdf (gaussianReal 0 1) critLim = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | bootstrapAbsTestReject
          (olsLinearTStatOrZero R
            (olsHetCovHC1Star
              (stackRegressors X n ω) (stackOutcomes y n ω))
            (stackRegressors X n ω) (stackOutcomes y n ω) β
            (Real.sqrt (n : ℝ)))
          (bootstrapScalarLowerQuantileIndexed
            (fun n _ =>
              (ProbabilityTheory.uniformOn
                (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                  Measure (Fin (n + 1) → Fin (n + 1))))
            (fun n ω ωs =>
              |regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs /
                seThetaStar n ω ωs|)
            (1 - α) n ω)})
      atTop (𝓝 (ENNReal.ofReal α)) :=
  chapter10_indexed_abs_test_rejectionProb_of_regression_tstat_finSucc_olsBetaOrZero_gapEnvelope_beta_bound_of_robustFeasibleHCMomentConditions
    (μ := μ) (X := X) (e := e) (y := y)
    β R
    (olsHC1LinTStatOrZero_tendstoInDistribution_standardNormal_of_robustFeasibleHCMomentConditions
      (μ := μ) (X := X) (e := e) (y := y) β R hm hse_pos)
    hse_pos hm hΩ hLinBound hBetaBound hGapTail hseThetaStar
    hseStar hα_pos hα_lt_one hleft hright hcrit_meas
    hcrit_nonneg hcdfLower hcdfUpper

set_option linter.style.longLine false in
/-- Strict-CDF counterpart of
`chapter10_indexed_olsHC1_abs_test_rejectionProb_tendsto_alpha_finSucc_olsBetaOrZero_gapEnvelope_beta_bound`. -/
theorem
    chapter10_indexed_olsHC1_abs_test_rejectionProb_strict_finSucc_olsBetaOrZero_gapEnvelope_beta_bound
    [IsProbabilityMeasure μ] [Fintype k] [DecidableEq k]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    {seThetaStar : ∀ n, Ω → (Fin (n + 1) → Fin (n + 1)) → ℝ}
    {Clin Cbeta critLim α : ℝ}
    (β : k → ℝ) (R : Matrix Unit k ℝ)
    (hse_pos : 0 <
      linearRestrictionStdError R (heteroAsymCov μ X e))
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
    (hstrict :
      StrictMono (fun x => cdf (gaussianReal 0 1) x))
    (hcrit_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed
            (fun n _ =>
              (ProbabilityTheory.uniformOn
                (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                  Measure (Fin (n + 1) → Fin (n + 1))))
            (fun n ω ωs =>
              |regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs /
                seThetaStar n ω ωs|)
            (1 - α) n) μ)
    (hcrit_nonneg : 0 ≤ critLim)
    (hcdfLower : cdf (gaussianReal 0 1) (-critLim) = α / 2)
    (hcdfUpper : cdf (gaussianReal 0 1) critLim = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | bootstrapAbsTestReject
          (olsLinearTStatOrZero R
            (olsHetCovHC1Star
              (stackRegressors X n ω) (stackOutcomes y n ω))
            (stackRegressors X n ω) (stackOutcomes y n ω) β
            (Real.sqrt (n : ℝ)))
          (bootstrapScalarLowerQuantileIndexed
            (fun n _ =>
              (ProbabilityTheory.uniformOn
                (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                  Measure (Fin (n + 1) → Fin (n + 1))))
            (fun n ω ωs =>
              |regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs /
                seThetaStar n ω ωs|)
            (1 - α) n ω)})
      atTop (𝓝 (ENNReal.ofReal α)) :=
  chapter10_indexed_abs_test_rejectionProb_strict_of_regression_tstat_finSucc_olsBetaOrZero_gapEnvelope_beta_bound_of_robustFeasibleHCMomentConditions
    (μ := μ) (X := X) (e := e) (y := y)
    β R
    (olsHC1LinTStatOrZero_tendstoInDistribution_standardNormal_of_robustFeasibleHCMomentConditions
      (μ := μ) (X := X) (e := e) (y := y) β R hm hse_pos)
    hse_pos hm hΩ hLinBound hBetaBound hGapTail hseThetaStar
    hseStar hα_pos hα_lt_one hstrict hcrit_meas hcrit_nonneg hcdfLower hcdfUpper

set_option linter.style.longLine false in
/-- Indexed local-CDF two-sided bootstrap-test calibration with the actual
sample statistic specialized to ordinary HC2 OLS and the bootstrap critical
value specialized to the concrete finite ordinary-bootstrap OLS
linear-restriction t-statistic. -/
theorem
    chapter10_indexed_olsHC2_abs_test_rejectionProb_tendsto_alpha_finSucc_olsBetaOrZero_gapEnvelope_beta_bound
    [IsProbabilityMeasure μ] [Fintype k] [DecidableEq k]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    {seThetaStar : ∀ n, Ω → (Fin (n + 1) → Fin (n + 1)) → ℝ}
    {Clin Cbeta critLim α : ℝ}
    (β : k → ℝ) (R : Matrix Unit k ℝ)
    (hse_pos : 0 <
      linearRestrictionStdError R (heteroAsymCov μ X e))
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
    (hleft :
      ∀ ε : ℝ, 0 < ε →
        cdf ((gaussianReal 0 1).map (fun z : ℝ => |z|)) (critLim - ε) <
          1 - α)
    (hright :
      ∀ ε : ℝ, 0 < ε →
        1 - α <
          cdf ((gaussianReal 0 1).map (fun z : ℝ => |z|)) (critLim + ε))
    (hcrit_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed
            (fun n _ =>
              (ProbabilityTheory.uniformOn
                (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                  Measure (Fin (n + 1) → Fin (n + 1))))
            (fun n ω ωs =>
              |regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs /
                seThetaStar n ω ωs|)
            (1 - α) n) μ)
    (hcrit_nonneg : 0 ≤ critLim)
    (hcdfLower : cdf (gaussianReal 0 1) (-critLim) = α / 2)
    (hcdfUpper : cdf (gaussianReal 0 1) critLim = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | bootstrapAbsTestReject
          (olsLinearTStatOrZero R
            (olsHetCovHC2Star
              (stackRegressors X n ω) (stackOutcomes y n ω))
            (stackRegressors X n ω) (stackOutcomes y n ω) β
            (Real.sqrt (n : ℝ)))
          (bootstrapScalarLowerQuantileIndexed
            (fun n _ =>
              (ProbabilityTheory.uniformOn
                (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                  Measure (Fin (n + 1) → Fin (n + 1))))
            (fun n ω ωs =>
              |regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs /
                seThetaStar n ω ωs|)
            (1 - α) n ω)})
      atTop (𝓝 (ENNReal.ofReal α)) :=
  chapter10_indexed_abs_test_rejectionProb_of_regression_tstat_finSucc_olsBetaOrZero_gapEnvelope_beta_bound_of_robustFeasibleHCMomentConditions
    (μ := μ) (X := X) (e := e) (y := y)
    β R
    (olsHC2LinTStatOrZero_tendstoInDistribution_standardNormal_of_robustFeasibleHCMomentConditions
      (μ := μ) (X := X) (e := e) (y := y) β R hm hse_pos)
    hse_pos hm hΩ hLinBound hBetaBound hGapTail hseThetaStar
    hseStar hα_pos hα_lt_one hleft hright hcrit_meas
    hcrit_nonneg hcdfLower hcdfUpper

set_option linter.style.longLine false in
/-- Strict-CDF counterpart of
`chapter10_indexed_olsHC2_abs_test_rejectionProb_tendsto_alpha_finSucc_olsBetaOrZero_gapEnvelope_beta_bound`. -/
theorem
    chapter10_indexed_olsHC2_abs_test_rejectionProb_strict_finSucc_olsBetaOrZero_gapEnvelope_beta_bound
    [IsProbabilityMeasure μ] [Fintype k] [DecidableEq k]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    {seThetaStar : ∀ n, Ω → (Fin (n + 1) → Fin (n + 1)) → ℝ}
    {Clin Cbeta critLim α : ℝ}
    (β : k → ℝ) (R : Matrix Unit k ℝ)
    (hse_pos : 0 <
      linearRestrictionStdError R (heteroAsymCov μ X e))
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
    (hstrict :
      StrictMono (fun x => cdf (gaussianReal 0 1) x))
    (hcrit_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed
            (fun n _ =>
              (ProbabilityTheory.uniformOn
                (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                  Measure (Fin (n + 1) → Fin (n + 1))))
            (fun n ω ωs =>
              |regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs /
                seThetaStar n ω ωs|)
            (1 - α) n) μ)
    (hcrit_nonneg : 0 ≤ critLim)
    (hcdfLower : cdf (gaussianReal 0 1) (-critLim) = α / 2)
    (hcdfUpper : cdf (gaussianReal 0 1) critLim = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | bootstrapAbsTestReject
          (olsLinearTStatOrZero R
            (olsHetCovHC2Star
              (stackRegressors X n ω) (stackOutcomes y n ω))
            (stackRegressors X n ω) (stackOutcomes y n ω) β
            (Real.sqrt (n : ℝ)))
          (bootstrapScalarLowerQuantileIndexed
            (fun n _ =>
              (ProbabilityTheory.uniformOn
                (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                  Measure (Fin (n + 1) → Fin (n + 1))))
            (fun n ω ωs =>
              |regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs /
                seThetaStar n ω ωs|)
            (1 - α) n ω)})
      atTop (𝓝 (ENNReal.ofReal α)) :=
  chapter10_indexed_abs_test_rejectionProb_strict_of_regression_tstat_finSucc_olsBetaOrZero_gapEnvelope_beta_bound_of_robustFeasibleHCMomentConditions
    (μ := μ) (X := X) (e := e) (y := y)
    β R
    (olsHC2LinTStatOrZero_tendstoInDistribution_standardNormal_of_robustFeasibleHCMomentConditions
      (μ := μ) (X := X) (e := e) (y := y) β R hm hse_pos)
    hse_pos hm hΩ hLinBound hBetaBound hGapTail hseThetaStar
    hseStar hα_pos hα_lt_one hstrict hcrit_meas hcrit_nonneg hcdfLower hcdfUpper

set_option linter.style.longLine false in
/-- Indexed local-CDF two-sided bootstrap-test calibration with the actual
sample statistic specialized to ordinary HC3 OLS and the bootstrap critical
value specialized to the concrete finite ordinary-bootstrap OLS
linear-restriction t-statistic. -/
theorem
    chapter10_indexed_olsHC3_abs_test_rejectionProb_tendsto_alpha_finSucc_olsBetaOrZero_gapEnvelope_beta_bound
    [IsProbabilityMeasure μ] [Fintype k] [DecidableEq k]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    {seThetaStar : ∀ n, Ω → (Fin (n + 1) → Fin (n + 1)) → ℝ}
    {Clin Cbeta critLim α : ℝ}
    (β : k → ℝ) (R : Matrix Unit k ℝ)
    (hse_pos : 0 <
      linearRestrictionStdError R (heteroAsymCov μ X e))
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
    (hleft :
      ∀ ε : ℝ, 0 < ε →
        cdf ((gaussianReal 0 1).map (fun z : ℝ => |z|)) (critLim - ε) <
          1 - α)
    (hright :
      ∀ ε : ℝ, 0 < ε →
        1 - α <
          cdf ((gaussianReal 0 1).map (fun z : ℝ => |z|)) (critLim + ε))
    (hcrit_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed
            (fun n _ =>
              (ProbabilityTheory.uniformOn
                (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                  Measure (Fin (n + 1) → Fin (n + 1))))
            (fun n ω ωs =>
              |regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs /
                seThetaStar n ω ωs|)
            (1 - α) n) μ)
    (hcrit_nonneg : 0 ≤ critLim)
    (hcdfLower : cdf (gaussianReal 0 1) (-critLim) = α / 2)
    (hcdfUpper : cdf (gaussianReal 0 1) critLim = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | bootstrapAbsTestReject
          (olsLinearTStatOrZero R
            (olsHetCovHC3Star
              (stackRegressors X n ω) (stackOutcomes y n ω))
            (stackRegressors X n ω) (stackOutcomes y n ω) β
            (Real.sqrt (n : ℝ)))
          (bootstrapScalarLowerQuantileIndexed
            (fun n _ =>
              (ProbabilityTheory.uniformOn
                (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                  Measure (Fin (n + 1) → Fin (n + 1))))
            (fun n ω ωs =>
              |regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs /
                seThetaStar n ω ωs|)
            (1 - α) n ω)})
      atTop (𝓝 (ENNReal.ofReal α)) :=
  chapter10_indexed_abs_test_rejectionProb_of_regression_tstat_finSucc_olsBetaOrZero_gapEnvelope_beta_bound_of_robustFeasibleHCMomentConditions
    (μ := μ) (X := X) (e := e) (y := y)
    β R
    (olsHC3LinTStatOrZero_tendstoInDistribution_standardNormal_of_robustFeasibleHCMomentConditions
      (μ := μ) (X := X) (e := e) (y := y) β R hm hse_pos)
    hse_pos hm hΩ hLinBound hBetaBound hGapTail hseThetaStar
    hseStar hα_pos hα_lt_one hleft hright hcrit_meas
    hcrit_nonneg hcdfLower hcdfUpper

set_option linter.style.longLine false in
/-- Strict-CDF counterpart of
`chapter10_indexed_olsHC3_abs_test_rejectionProb_tendsto_alpha_finSucc_olsBetaOrZero_gapEnvelope_beta_bound`. -/
theorem
    chapter10_indexed_olsHC3_abs_test_rejectionProb_strict_finSucc_olsBetaOrZero_gapEnvelope_beta_bound
    [IsProbabilityMeasure μ] [Fintype k] [DecidableEq k]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    {seThetaStar : ∀ n, Ω → (Fin (n + 1) → Fin (n + 1)) → ℝ}
    {Clin Cbeta critLim α : ℝ}
    (β : k → ℝ) (R : Matrix Unit k ℝ)
    (hse_pos : 0 <
      linearRestrictionStdError R (heteroAsymCov μ X e))
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
    (hstrict :
      StrictMono (fun x => cdf (gaussianReal 0 1) x))
    (hcrit_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed
            (fun n _ =>
              (ProbabilityTheory.uniformOn
                (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                  Measure (Fin (n + 1) → Fin (n + 1))))
            (fun n ω ωs =>
              |regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs /
                seThetaStar n ω ωs|)
            (1 - α) n) μ)
    (hcrit_nonneg : 0 ≤ critLim)
    (hcdfLower : cdf (gaussianReal 0 1) (-critLim) = α / 2)
    (hcdfUpper : cdf (gaussianReal 0 1) critLim = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | bootstrapAbsTestReject
          (olsLinearTStatOrZero R
            (olsHetCovHC3Star
              (stackRegressors X n ω) (stackOutcomes y n ω))
            (stackRegressors X n ω) (stackOutcomes y n ω) β
            (Real.sqrt (n : ℝ)))
          (bootstrapScalarLowerQuantileIndexed
            (fun n _ =>
              (ProbabilityTheory.uniformOn
                (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                  Measure (Fin (n + 1) → Fin (n + 1))))
            (fun n ω ωs =>
              |regressionBootstrapLinearRestrictionStatisticFinSucc R X y n ω ωs /
                seThetaStar n ω ωs|)
            (1 - α) n ω)})
      atTop (𝓝 (ENNReal.ofReal α)) :=
  chapter10_indexed_abs_test_rejectionProb_strict_of_regression_tstat_finSucc_olsBetaOrZero_gapEnvelope_beta_bound_of_robustFeasibleHCMomentConditions
    (μ := μ) (X := X) (e := e) (y := y)
    β R
    (olsHC3LinTStatOrZero_tendstoInDistribution_standardNormal_of_robustFeasibleHCMomentConditions
      (μ := μ) (X := X) (e := e) (y := y) β R hm hse_pos)
    hse_pos hm hΩ hLinBound hBetaBound hGapTail hseThetaStar
    hseStar hα_pos hα_lt_one hstrict hcrit_meas hcrit_nonneg hcdfLower hcdfUpper

end BootstrapTests

end HansenEconometrics
