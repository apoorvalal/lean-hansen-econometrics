import HansenEconometrics.Chapter7Asymptotics.Normality

/-!
# Chapter 7 Asymptotics: Inference

T-statistics, confidence-interval coverage bridges, scalar Wald statistics, and
ordinary-wrapper projection-family consequences.
-/

open scoped Matrix Real

namespace HansenEconometrics

open Matrix

section Assumption72

open MeasureTheory ProbabilityTheory Filter
open scoped Matrix.Norms.Elementwise Function Topology ProbabilityTheory ENNReal symmDiff

variable {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
variable {k : Type*} [Fintype k] [DecidableEq k]

omit [DecidableEq k] in
/-- Borel σ-algebra on `Matrix k k ℝ` inherited from the elementwise-L∞ norm,
reintroduced for Chapter 7 submodules using covariance-matrix random variables. -/
@[reducible]
private noncomputable def matrixBorelMeasurableSpace72 :
    MeasurableSpace (Matrix k k ℝ) := borel _

attribute [local instance] matrixBorelMeasurableSpace72

omit [Fintype k] [DecidableEq k] in
private lemma matrixBorelSpace72 : BorelSpace (Matrix k k ℝ) := ⟨rfl⟩

attribute [local instance] matrixBorelSpace72

/-- The absolute standard-normal law has no atom at the frontier of `(-∞, c]`. -/
theorem standardNormalAbs_frontier_Iic_null (crit : ℝ) :
    ((gaussianReal 0 1).map (fun x : ℝ => |x|)) (frontier (Set.Iic crit)) = 0 := by
  rw [frontier_Iic]
  rw [Measure.map_apply continuous_abs.measurable (measurableSet_singleton crit)]
  have hpre_subset :
      (fun x : ℝ => |x|) ⁻¹' ({crit} : Set ℝ) ⊆
        ({crit} ∪ {-crit} : Set ℝ) := by
    intro x hx
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hx
    simp only [Set.mem_union, Set.mem_singleton_iff]
    by_cases hx_nonneg : 0 ≤ x
    · left
      simpa [abs_of_nonneg hx_nonneg] using hx
    · right
      have hx_neg : x < 0 := lt_of_not_ge hx_nonneg
      have hneg : -x = crit := by
        simpa [abs_of_neg hx_neg] using hx
      linarith
  haveI : NoAtoms (gaussianReal 0 1) :=
    noAtoms_gaussianReal (μ := 0) (v := 1) (by norm_num)
  exact measure_mono_null hpre_subset
    (measure_union_null (measure_singleton crit) (measure_singleton (-crit)))

/-- Squaring a standard-normal distributional limit gives a `χ²(1)` limit. -/
theorem tendstoInDistribution_sq_standardNormal_chiSquared_one
    {P : ℕ → Measure Ω} [∀ n, IsProbabilityMeasure (P n)]
    {T : ℕ → Ω → ℝ}
    (hT : TendstoInDistribution T atTop (fun x : ℝ => x) P (gaussianReal 0 1)) :
    TendstoInDistribution (fun n ω => (T n ω) ^ 2) atTop
      (fun x : ℝ => x) P (chiSquared 1) := by
  have hsquare := hT.continuous_comp (by fun_prop : Continuous (fun x : ℝ => x ^ 2))
  refine ⟨?_, ?_, ?_⟩
  · simpa [Function.comp_def] using hsquare.forall_aemeasurable
  · fun_prop
  · convert hsquare.tendsto using 2
    · ext s hs
      simp [Function.comp_def, gaussianReal_map_sq_eq_chiSquared_one]

omit [DecidableEq k] in
/-- One-row linear maps turn scaled parameter errors into scaled scalar errors.

This is the algebraic bridge between the existing t-statistic numerator
`√n • R(β̂-β)` and the confidence-interval expression `√n(θ̂-θ)`. -/
theorem linearMapUnit_smul_sub_dot_one
    (R : Matrix Unit k ℝ) (b β : k → ℝ) (root : ℝ) :
    (root • (R *ᵥ (b - β))) ⬝ᵥ (fun _ : Unit => 1) =
      root * (((R *ᵥ b) ⬝ᵥ (fun _ : Unit => 1)) -
        ((R *ᵥ β) ⬝ᵥ (fun _ : Unit => 1))) := by
  rw [Matrix.mulVec_sub, smul_dotProduct, sub_dotProduct]
  simp [smul_eq_mul]

/-- Scaling by positive standard-error and root factors preserves absolute-value inequalities. -/
theorem abs_scaled_error_div_le_iff
    {d root se crit : ℝ}
    (hroot : 0 < root) (hse : 0 < se) :
    |root * d / se| ≤ crit ↔ |d| ≤ crit * se / root := by
  rw [abs_div, abs_mul, abs_of_pos hroot, abs_of_pos hse]
  constructor
  · intro h
    have hmul : root * |d| ≤ crit * se := (div_le_iff₀ hse).mp h
    exact (le_div_iff₀ hroot).mpr (by simpa [mul_comm] using hmul)
  · intro h
    have hmul' : |d| * root ≤ crit * se := (le_div_iff₀ hroot).mp h
    have hmul : root * |d| ≤ crit * se := by
      simpa [mul_comm] using hmul'
    exact (div_le_iff₀ hse).mpr hmul

/-- Symmetric confidence-interval membership is equivalent to an absolute t-statistic bound. -/
theorem mem_symmetric_ci_iff_abs_tstat_le
    {θ θhat root se crit : ℝ}
    (hroot : 0 < root) (hse : 0 < se) :
    θ ∈ Set.Icc (θhat - crit * se / root) (θhat + crit * se / root) ↔
      |root * (θhat - θ) / se| ≤ crit := by
  rw [← Set.mem_Icc_iff_abs_le
    (x := θhat) (y := θ) (z := crit * se / root)]
  exact (abs_scaled_error_div_le_iff
    (d := θhat - θ) (root := root) (se := se) (crit := crit) hroot hse).symm

/-- **Hansen Theorem 7.12, generic symmetric confidence-interval coverage bridge.**

If the absolute t-statistic converges to `|N(0,1)|`, then the probability that
the true scalar parameter lies in the usual symmetric interval converges to the
absolute-standard-normal mass below the critical value, at every continuity
critical value. Positivity of the root and standard error is needed only
eventually, so finite initial sample sizes are ignored by the limit. -/
theorem symmetricCI_coverage_tendsto_of_abs_tstat
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {θ crit : ℝ}
    {θhat se : ℕ → Ω → ℝ} {root : ℕ → ℝ}
    (hroot : ∀ᶠ n in atTop, 0 < root n)
    (hse : ∀ᶠ n in atTop, ∀ ω, 0 < se n ω)
    (hT : TendstoInDistribution
      (fun n ω => |root n * (θhat n ω - θ) / se n ω|)
      atTop (fun x : ℝ => |x|) (fun _ => μ) (gaussianReal 0 1))
    (hcrit : ((gaussianReal 0 1).map (fun x : ℝ => |x|))
      (frontier (Set.Iic crit)) = 0) :
    Tendsto
      (fun n => μ {ω | θ ∈ Set.Icc
        (θhat n ω - crit * se n ω / root n)
        (θhat n ω + crit * se n ω / root n)})
      atTop
      (𝓝 (((gaussianReal 0 1).map (fun x : ℝ => |x|)) (Set.Iic crit))) := by
  have hevent :=
    TendstoInDistribution.tendsto_measure_preimage_of_null_frontier_real
      hT
      (E := Set.Iic crit) measurableSet_Iic hcrit
  refine hevent.congr' ?_
  filter_upwards [hroot, hse] with n hnroot hnse
  congr 1
  ext ω
  have hiff := mem_symmetric_ci_iff_abs_tstat_le
    (θ := θ) (θhat := θhat n ω) (root := root n)
    (se := se n ω) (crit := crit) hnroot (hnse ω)
  simpa [Set.mem_Iic] using hiff.symm

/-- Version of `symmetricCI_coverage_tendsto_of_abs_tstat` with the standard-normal
continuity-set side condition already discharged. -/
theorem symmetricCI_coverage_tendsto_of_abs_tstat_standardNormal
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {θ crit : ℝ}
    {θhat se : ℕ → Ω → ℝ} {root : ℕ → ℝ}
    (hroot : ∀ᶠ n in atTop, 0 < root n)
    (hse : ∀ᶠ n in atTop, ∀ ω, 0 < se n ω)
    (hT : TendstoInDistribution
      (fun n ω => |root n * (θhat n ω - θ) / se n ω|)
      atTop (fun x : ℝ => |x|) (fun _ => μ) (gaussianReal 0 1)) :
    Tendsto
      (fun n => μ {ω | θ ∈ Set.Icc
        (θhat n ω - crit * se n ω / root n)
        (θhat n ω + crit * se n ω / root n)})
      atTop
      (𝓝 (((gaussianReal 0 1).map (fun x : ℝ => |x|)) (Set.Iic crit))) :=
  symmetricCI_coverage_tendsto_of_abs_tstat
    (μ := μ) (θ := θ) (crit := crit)
    hroot hse hT (standardNormalAbs_frontier_Iic_null crit)

/-- **Hansen Theorem 7.12, probabilistic symmetric confidence-interval coverage bridge.**

This version removes the pointwise eventual standard-error positivity shortcut:
it is enough that the nonpositive-standard-error event has probability tending
to zero. The interval event and the absolute-t-statistic event can then differ
only on a negligible bad set. -/
theorem symmetricCI_coverage_tendsto_of_abs_tstat_of_nonpos_tendsto_zero
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {θ crit : ℝ}
    {θhat se : ℕ → Ω → ℝ} {root : ℕ → ℝ}
    (hroot : ∀ᶠ n in atTop, 0 < root n)
    (hse_nonpos : Tendsto (fun n => μ {ω | se n ω ≤ 0}) atTop (𝓝 0))
    (hT : TendstoInDistribution
      (fun n ω => |root n * (θhat n ω - θ) / se n ω|)
      atTop (fun x : ℝ => |x|) (fun _ => μ) (gaussianReal 0 1))
    (hcrit : ((gaussianReal 0 1).map (fun x : ℝ => |x|))
      (frontier (Set.Iic crit)) = 0) :
    Tendsto
      (fun n => μ {ω | θ ∈ Set.Icc
        (θhat n ω - crit * se n ω / root n)
        (θhat n ω + crit * se n ω / root n)})
      atTop
      (𝓝 (((gaussianReal 0 1).map (fun x : ℝ => |x|)) (Set.Iic crit))) := by
  let ci : ℕ → Set Ω := fun n => {ω | θ ∈ Set.Icc
    (θhat n ω - crit * se n ω / root n)
    (θhat n ω + crit * se n ω / root n)}
  let stat : ℕ → Set Ω := fun n =>
    {ω | |root n * (θhat n ω - θ) / se n ω| ∈ Set.Iic crit}
  let bad : ℕ → Set Ω := fun n => {ω | se n ω ≤ 0}
  let L : ℝ≥0∞ := ((gaussianReal 0 1).map (fun x : ℝ => |x|)) (Set.Iic crit)
  have hstat : Tendsto (fun n => μ (stat n)) atTop (𝓝 L) := by
    have hevent :=
      TendstoInDistribution.tendsto_measure_preimage_of_null_frontier_real
        hT
        (E := Set.Iic crit) measurableSet_Iic hcrit
    simpa [stat, L] using hevent
  have hsymm_subset : ∀ n, 0 < root n → ci n ∆ stat n ⊆ bad n := by
    intro n hnroot ω hω
    by_cases hnse : 0 < se n ω
    · have hiff := mem_symmetric_ci_iff_abs_tstat_le
        (θ := θ) (θhat := θhat n ω) (root := root n)
        (se := se n ω) (crit := crit) hnroot hnse
      rw [Set.mem_symmDiff] at hω
      rcases hω with hω | hω
      · exact False.elim (hω.2 (hiff.mp hω.1))
      · exact False.elim (hω.2 (hiff.mpr hω.1))
    · exact not_lt.mp hnse
  have hdiff : Tendsto (fun n => μ (ci n ∆ stat n)) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hse_nonpos
      (Eventually.of_forall fun n => zero_le _) ?_
    filter_upwards [hroot] with n hnroot
    exact measure_mono (hsymm_subset n hnroot)
  have hL_ne_top : L ≠ ∞ := by
    simp [L]
  have hlower : Tendsto (fun n => μ (stat n) - μ (ci n ∆ stat n)) atTop (𝓝 L) := by
    simpa [L] using ENNReal.Tendsto.sub hstat hdiff (Or.inl hL_ne_top)
  have hupper : Tendsto (fun n => μ (stat n) + μ (ci n ∆ stat n)) atTop (𝓝 L) := by
    simpa using hstat.add hdiff
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower hupper ?_ ?_
  · exact Eventually.of_forall fun n => by
      have hstat_le : μ (stat n) ≤ μ (ci n) + μ (ci n ∆ stat n) := by
        calc
          μ (stat n) ≤ μ ((ci n ∆ stat n) ∪ ci n) :=
            measure_mono (le_symmDiff_sup_left (ci n) (stat n))
          _ ≤ μ (ci n ∆ stat n) + μ (ci n) := measure_union_le _ _
          _ = μ (ci n) + μ (ci n ∆ stat n) := by rw [add_comm]
      exact tsub_le_iff_right.mpr hstat_le
  · exact Eventually.of_forall fun n => by
      calc
        μ (ci n) ≤ μ ((ci n ∆ stat n) ∪ stat n) :=
          measure_mono (le_symmDiff_sup_right (ci n) (stat n))
        _ ≤ μ (ci n ∆ stat n) + μ (stat n) := measure_union_le _ _
        _ = μ (stat n) + μ (ci n ∆ stat n) := by rw [add_comm]

/-- Standard-normal version of
`symmetricCI_coverage_tendsto_of_abs_tstat_of_nonpos_tendsto_zero`. -/
theorem symmetricCI_coverage_tendsto_of_abs_tstat_standardNormal_of_nonpos_tendsto_zero
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {θ crit : ℝ}
    {θhat se : ℕ → Ω → ℝ} {root : ℕ → ℝ}
    (hroot : ∀ᶠ n in atTop, 0 < root n)
    (hse_nonpos : Tendsto (fun n => μ {ω | se n ω ≤ 0}) atTop (𝓝 0))
    (hT : TendstoInDistribution
      (fun n ω => |root n * (θhat n ω - θ) / se n ω|)
      atTop (fun x : ℝ => |x|) (fun _ => μ) (gaussianReal 0 1)) :
    Tendsto
      (fun n => μ {ω | θ ∈ Set.Icc
        (θhat n ω - crit * se n ω / root n)
        (θhat n ω + crit * se n ω / root n)})
      atTop
      (𝓝 (((gaussianReal 0 1).map (fun x : ℝ => |x|)) (Set.Iic crit))) :=
  symmetricCI_coverage_tendsto_of_abs_tstat_of_nonpos_tendsto_zero
    (μ := μ) (θ := θ) (crit := crit)
    hroot hse_nonpos hT (standardNormalAbs_frontier_Iic_null crit)

/-- Standard-normal confidence-interval coverage from convergence in probability
of the standard error to a positive constant. -/
theorem symmetricCI_coverage_tendsto_of_abs_tstat_standardNormal_of_se_tendsto_pos
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {θ crit c : ℝ}
    {θhat se : ℕ → Ω → ℝ} {root : ℕ → ℝ}
    (hroot : ∀ᶠ n in atTop, 0 < root n)
    (hc : 0 < c)
    (hse : TendstoInMeasure μ se atTop (fun _ => c))
    (hT : TendstoInDistribution
      (fun n ω => |root n * (θhat n ω - θ) / se n ω|)
      atTop (fun x : ℝ => |x|) (fun _ => μ) (gaussianReal 0 1)) :
    Tendsto
      (fun n => μ {ω | θ ∈ Set.Icc
        (θhat n ω - crit * se n ω / root n)
        (θhat n ω + crit * se n ω / root n)})
      atTop
      (𝓝 (((gaussianReal 0 1).map (fun x : ℝ => |x|)) (Set.Iic crit))) :=
  symmetricCI_coverage_tendsto_of_abs_tstat_standardNormal_of_nonpos_tendsto_zero
    (μ := μ) (θ := θ) (crit := crit)
    hroot (tendsto_measure_nonpos_of_tendstoInMeasure_const_pos (μ := μ) hc hse) hT

omit [DecidableEq k] in
/-- Measurability of a scalar standard error induced by any matrix covariance estimator. -/
theorem linearCovarianceStdError_aemeasurable
    {μ : Measure Ω} (R : Matrix Unit k ℝ)
    {Vhat : Ω → Matrix k k ℝ}
    (hVhat : AEStronglyMeasurable Vhat μ) :
    AEMeasurable (fun ω => Real.sqrt ((R * Vhat ω * Rᵀ) () ())) μ := by
  have hcov : AEStronglyMeasurable
      (fun ω => R * Vhat ω * Rᵀ) μ :=
    linearMapCovariance_aestronglyMeasurable
      (μ := μ) (R := R) hVhat
  have hentry_cont : Continuous (fun M : Matrix Unit Unit ℝ => M () ()) :=
    (continuous_apply ()).comp (continuous_apply ())
  have hsqrt_cont : Continuous (fun M : Matrix Unit Unit ℝ => Real.sqrt (M () ())) :=
    Real.continuous_sqrt.comp hentry_cont
  exact (hsqrt_cont.comp_aestronglyMeasurable hcov).aemeasurable

/-- Generic studentization bridge for scalar linear inference.

If a numerator has a distributional limit and the standard error converges in
probability to a positive constant, then the studentized statistic has the
corresponding ratio limit. -/
theorem studentizedLimit_tendstoInDistribution
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ν : Measure Ω'} [IsProbabilityMeasure ν]
    {num se : ℕ → Ω → ℝ} {Z : Ω' → ℝ} {c : ℝ}
    (hc : 0 < c)
    (hnum : TendstoInDistribution num atTop Z (fun _ => μ) ν)
    (hse : TendstoInMeasure μ se atTop (fun _ => c))
    (hse_meas : ∀ n, AEMeasurable (se n) μ) :
    TendstoInDistribution
      (fun n ω => num n ω / se n ω)
      atTop (fun ω => Z ω / c) (fun _ => μ) ν := by
  have hratio_meas : ∀ n, AEMeasurable (fun ω => num n ω / se n ω) μ :=
    fun n => (hnum.forall_aemeasurable n).div (hse_meas n)
  exact tendstoInDistribution_div_of_tendstoInMeasure_const_pos
    (μ := μ) (ν := ν) (X := num) (Y := se) (Z := Z) (c := c)
    hc hnum hse hse_meas hratio_meas

/-- **Hansen §7.17, homoskedastic t-statistic for a scalar linear function.**

For a one-dimensional fixed linear map `R`, the homoskedastic-studentized
totalized OLS linear function converges to the Gaussian linear-function limit
divided by the homoskedastic population standard-error scale. -/
theorem olsHomoskedasticLinearTStatisticStar_tendstoInDistribution
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ν : Measure Ω'} [IsProbabilityMeasure ν]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (hclt : ScoreCLTConditions μ X e)
    (hvar : ErrorVarianceConsistencyConditions μ X e) (β : k → ℝ)
    (R : Matrix Unit k ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (he_meas : ∀ i, AEStronglyMeasurable (e i) μ)
    {Z : Ω' → ℝ}
    (hZ : HasLaw Z
      (gaussianReal 0
        (olsProjectionAsymptoticVariance μ X e (Rᵀ *ᵥ (fun _ : Unit => 1))).toNNReal)
      ν)
    (hse_pos : 0 <
      Real.sqrt ((R * homoskedasticAsymptoticCovariance μ X e * Rᵀ) () ())) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        ((Real.sqrt (n : ℝ) •
          (R *ᵥ
            (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β))) ⬝ᵥ
            (fun _ : Unit => 1)) /
            Real.sqrt ((R * olsHomoskedasticCovarianceStar
              (stackRegressors X n ω) (stackOutcomes y n ω) * Rᵀ) () ()))
      atTop
      (fun ω =>
        Z ω / Real.sqrt ((R * homoskedasticAsymptoticCovariance μ X e * Rᵀ) () ()))
      (fun _ => μ) ν := by
  let c : ℝ := Real.sqrt ((R * homoskedasticAsymptoticCovariance μ X e * Rᵀ) () ())
  let se : ℕ → Ω → ℝ := fun n ω =>
    Real.sqrt ((R * olsHomoskedasticCovarianceStar
      (stackRegressors X n ω) (stackOutcomes y n ω) * Rᵀ) () ())
  let num : ℕ → Ω → ℝ := fun n ω =>
    ((Real.sqrt (n : ℝ) •
      (R *ᵥ (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β))) ⬝ᵥ
        (fun _ : Unit => 1))
  have hnum : TendstoInDistribution num atTop Z (fun _ => μ) ν := by
    simpa [num] using
      scoreProjection_linearMap_olsBetaStar_tendstoInDistribution_gaussian_covariance
        (μ := μ) (ν := ν) (X := X) (e := e) (y := y)
        hclt β R (fun _ : Unit => 1) hmodel hZ
  have hse : TendstoInMeasure μ se atTop (fun _ => c) := by
    simpa [se, c] using
      olsHomoskedasticLinearStdErrorStar_tendstoInMeasure
        (μ := μ) (X := X) (e := e) (y := y)
        hvar β R () hmodel hX_meas he_meas
  have hV_meas :=
    olsHomoskedasticCovarianceStar_stack_aestronglyMeasurable_of_components
      (μ := μ) (X := X) (e := e) (y := y)
      hvar.toSampleMomentAssumption71 β hmodel hX_meas he_meas
  have hse_meas : ∀ n, AEMeasurable (se n) μ := by
    intro n
    exact linearCovarianceStdError_aemeasurable
      (μ := μ) (R := R)
      (Vhat := fun ω =>
        olsHomoskedasticCovarianceStar
          (stackRegressors X n ω) (stackOutcomes y n ω))
      (hV_meas n)
  have hratio := studentizedLimit_tendstoInDistribution
    (μ := μ) (ν := ν) (num := num) (se := se) (Z := Z) (c := c)
    (by simpa [c] using hse_pos) hnum hse hse_meas
  simpa [num, se, c] using hratio

/-- **Hansen Theorem 7.14, scalar homoskedastic t-statistic with standard normal limit.**

If the homoskedastic asymptotic covariance equals the robust sandwich
covariance, the scalar homoskedastic t-statistic has the standard-normal limit.
This is the one-dimensional t-statistic face behind the homoskedastic Wald
statistic. -/
theorem olsHomoskedasticLinearTStatisticStar_tendstoInDistribution_standardNormal
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (hclt : ScoreCLTConditions μ X e)
    (hvar : ErrorVarianceConsistencyConditions μ X e) (β : k → ℝ)
    (R : Matrix Unit k ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (he_meas : ∀ i, AEStronglyMeasurable (e i) μ)
    (hVeq : homoskedasticAsymptoticCovariance μ X e =
      heteroskedasticAsymptoticCovariance μ X e)
    (hse_pos : 0 <
      Real.sqrt ((R * homoskedasticAsymptoticCovariance μ X e * Rᵀ) () ())) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        ((Real.sqrt (n : ℝ) •
          (R *ᵥ
            (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β))) ⬝ᵥ
            (fun _ : Unit => 1)) /
          Real.sqrt ((R * olsHomoskedasticCovarianceStar
            (stackRegressors X n ω) (stackOutcomes y n ω) * Rᵀ) () ()))
      atTop (fun x : ℝ => x) (fun _ => μ) (gaussianReal 0 1) := by
  let c : ℝ := Real.sqrt ((R * homoskedasticAsymptoticCovariance μ X e * Rᵀ) () ())
  have hentry_pos : 0 < (R * homoskedasticAsymptoticCovariance μ X e * Rᵀ) () () := by
    exact Real.sqrt_pos.mp hse_pos
  have hentry_eq :
      (R * homoskedasticAsymptoticCovariance μ X e * Rᵀ) () () =
        olsProjectionAsymptoticVariance μ X e (Rᵀ *ᵥ (fun _ : Unit => 1)) := by
    rw [hVeq]
    exact linearMapCovariance_unit_apply_eq_olsProjectionAsymptoticVariance
      (μ := μ) (X := X) (e := e) hclt.toSampleMomentAssumption71.int_outer R
  have hσ :
      olsProjectionAsymptoticVariance μ X e (Rᵀ *ᵥ (fun _ : Unit => 1)) = c ^ 2 := by
    calc
      olsProjectionAsymptoticVariance μ X e (Rᵀ *ᵥ (fun _ : Unit => 1))
          = (R * homoskedasticAsymptoticCovariance μ X e * Rᵀ) () () :=
            hentry_eq.symm
      _ = c ^ 2 := by
            simpa [c] using (Real.sq_sqrt hentry_pos.le).symm
  have hZ : HasLaw (fun x : ℝ => c * x)
      (gaussianReal 0
        (olsProjectionAsymptoticVariance μ X e (Rᵀ *ᵥ (fun _ : Unit => 1))).toNNReal)
      (gaussianReal 0 1) :=
    hasLaw_const_mul_id_gaussianReal_of_variance_eq hσ
  have hbase := olsHomoskedasticLinearTStatisticStar_tendstoInDistribution
    (μ := μ) (ν := gaussianReal 0 1) (X := X) (e := e) (y := y)
    hclt hvar β R hmodel hX_meas he_meas hZ hse_pos
  convert hbase using 2
  · rename_i x
    dsimp [c]
    exact (mul_div_cancel_left₀ x hse_pos.ne').symm

/-- **Hansen §7.17 for ordinary OLS on nonsingular samples, homoskedastic face.**

The homoskedastic-studentized scalar linear t-statistic transfers from the
totalized estimator to the ordinary-on-nonsingular wrapper `olsBetaOrZero`. -/
theorem olsHomoskedasticLinearTStatisticOrZero_tendstoInDistribution
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ν : Measure Ω'} [IsProbabilityMeasure ν]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (hclt : ScoreCLTConditions μ X e)
    (hvar : ErrorVarianceConsistencyConditions μ X e) (β : k → ℝ)
    (R : Matrix Unit k ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (he_meas : ∀ i, AEStronglyMeasurable (e i) μ)
    {Z : Ω' → ℝ}
    (hZ : HasLaw Z
      (gaussianReal 0
        (olsProjectionAsymptoticVariance μ X e (Rᵀ *ᵥ (fun _ : Unit => 1))).toNNReal)
      ν)
    (hse_pos : 0 <
      Real.sqrt ((R * homoskedasticAsymptoticCovariance μ X e * Rᵀ) () ())) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        ((Real.sqrt (n : ℝ) •
          (R *ᵥ
            (olsBetaOrZero (stackRegressors X n ω) (stackOutcomes y n ω) - β))) ⬝ᵥ
            (fun _ : Unit => 1)) /
          Real.sqrt ((R * olsHomoskedasticCovarianceStar
            (stackRegressors X n ω) (stackOutcomes y n ω) * Rᵀ) () ()))
      atTop
      (fun ω =>
        Z ω / Real.sqrt ((R * homoskedasticAsymptoticCovariance μ X e * Rᵀ) () ()))
      (fun _ => μ) ν := by
  simpa [olsBetaOrZero_eq_olsBetaStar] using
    olsHomoskedasticLinearTStatisticStar_tendstoInDistribution
      (μ := μ) (ν := ν) (X := X) (e := e) (y := y)
      hclt hvar β R hmodel hX_meas he_meas hZ hse_pos

/-- **Hansen Theorem 7.14 for ordinary OLS, homoskedastic standard-normal face.** -/
theorem olsHomoskedasticLinearTStatisticOrZero_tendstoInDistribution_standardNormal
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (hclt : ScoreCLTConditions μ X e)
    (hvar : ErrorVarianceConsistencyConditions μ X e) (β : k → ℝ)
    (R : Matrix Unit k ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (he_meas : ∀ i, AEStronglyMeasurable (e i) μ)
    (hVeq : homoskedasticAsymptoticCovariance μ X e =
      heteroskedasticAsymptoticCovariance μ X e)
    (hse_pos : 0 <
      Real.sqrt ((R * homoskedasticAsymptoticCovariance μ X e * Rᵀ) () ())) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        ((Real.sqrt (n : ℝ) •
          (R *ᵥ
            (olsBetaOrZero (stackRegressors X n ω) (stackOutcomes y n ω) - β))) ⬝ᵥ
            (fun _ : Unit => 1)) /
          Real.sqrt ((R * olsHomoskedasticCovarianceStar
            (stackRegressors X n ω) (stackOutcomes y n ω) * Rᵀ) () ()))
      atTop (fun x : ℝ => x) (fun _ => μ) (gaussianReal 0 1) := by
  simpa [olsBetaOrZero_eq_olsBetaStar] using
    olsHomoskedasticLinearTStatisticStar_tendstoInDistribution_standardNormal
      (μ := μ) (X := X) (e := e) (y := y)
      hclt hvar β R hmodel hX_meas he_meas hVeq hse_pos

/-- Absolute-value CMT for the ordinary homoskedastic scalar t-statistic. -/
theorem olsHomoskedasticLinearTStatisticOrZero_abs_tendstoInDistribution_standardNormalAbs
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (hclt : ScoreCLTConditions μ X e)
    (hvar : ErrorVarianceConsistencyConditions μ X e) (β : k → ℝ)
    (R : Matrix Unit k ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (he_meas : ∀ i, AEStronglyMeasurable (e i) μ)
    (hVeq : homoskedasticAsymptoticCovariance μ X e =
      heteroskedasticAsymptoticCovariance μ X e)
    (hse_pos : 0 <
      Real.sqrt ((R * homoskedasticAsymptoticCovariance μ X e * Rᵀ) () ())) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        abs
          (((Real.sqrt (n : ℝ) •
            (R *ᵥ
              (olsBetaOrZero (stackRegressors X n ω) (stackOutcomes y n ω) - β))) ⬝ᵥ
              (fun _ : Unit => 1)) /
            Real.sqrt ((R * olsHomoskedasticCovarianceStar
              (stackRegressors X n ω) (stackOutcomes y n ω) * Rᵀ) () ())))
      atTop (fun x : ℝ => |x|) (fun _ => μ) (gaussianReal 0 1) := by
  simpa using
    tendstoInDistribution_abs_real
      (olsHomoskedasticLinearTStatisticOrZero_tendstoInDistribution_standardNormal
        (μ := μ) (X := X) (e := e) (y := y)
        hclt hvar β R hmodel hX_meas he_meas hVeq hse_pos)

set_option linter.style.longLine false in
/-- **Hansen Theorem 7.12, homoskedastic confidence-interval coverage.**

For a one-row linear restriction, the ordinary-wrapper homoskedastic symmetric
confidence interval has limiting coverage equal to the absolute standard-normal
mass below the critical value. Sample standard-error positivity is derived from
convergence in probability to the positive population standard error. -/
theorem olsHomoskedasticLinearCIOrZero_coverage_tendsto_standardNormal
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (hclt : ScoreCLTConditions μ X e)
    (hvar : ErrorVarianceConsistencyConditions μ X e) (β : k → ℝ)
    (R : Matrix Unit k ℝ) (crit : ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (he_meas : ∀ i, AEStronglyMeasurable (e i) μ)
    (hVeq : homoskedasticAsymptoticCovariance μ X e =
      heteroskedasticAsymptoticCovariance μ X e)
    (hse_pos : 0 <
      Real.sqrt ((R * homoskedasticAsymptoticCovariance μ X e * Rᵀ) () ())) :
    Tendsto
      (fun n => μ {ω |
        (R *ᵥ β) ⬝ᵥ (fun _ : Unit => 1) ∈ Set.Icc
          (((R *ᵥ olsBetaOrZero (stackRegressors X n ω) (stackOutcomes y n ω)) ⬝ᵥ
              (fun _ : Unit => 1)) -
            crit * Real.sqrt ((R * olsHomoskedasticCovarianceStar
              (stackRegressors X n ω) (stackOutcomes y n ω) * Rᵀ) () ()) /
              Real.sqrt (n : ℝ))
          (((R *ᵥ olsBetaOrZero (stackRegressors X n ω) (stackOutcomes y n ω)) ⬝ᵥ
              (fun _ : Unit => 1)) +
            crit * Real.sqrt ((R * olsHomoskedasticCovarianceStar
              (stackRegressors X n ω) (stackOutcomes y n ω) * Rᵀ) () ()) /
              Real.sqrt (n : ℝ))})
      atTop
      (𝓝 (((gaussianReal 0 1).map (fun x : ℝ => |x|)) (Set.Iic crit))) := by
  let θ : ℝ := (R *ᵥ β) ⬝ᵥ (fun _ : Unit => 1)
  let θhat : ℕ → Ω → ℝ := fun n ω =>
    (R *ᵥ olsBetaOrZero (stackRegressors X n ω) (stackOutcomes y n ω)) ⬝ᵥ
      (fun _ : Unit => 1)
  let se : ℕ → Ω → ℝ := fun n ω =>
    Real.sqrt ((R * olsHomoskedasticCovarianceStar
      (stackRegressors X n ω) (stackOutcomes y n ω) * Rᵀ) () ())
  let root : ℕ → ℝ := fun n => Real.sqrt (n : ℝ)
  let c : ℝ := Real.sqrt ((R * homoskedasticAsymptoticCovariance μ X e * Rᵀ) () ())
  have hroot : ∀ᶠ n in atTop, 0 < root n := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    exact Real.sqrt_pos.mpr hnpos
  have hse : TendstoInMeasure μ se atTop (fun _ => c) := by
    simpa [se, c] using
      olsHomoskedasticLinearStdErrorStar_tendstoInMeasure
        (μ := μ) (X := X) (e := e) (y := y)
        hvar β R () hmodel hX_meas he_meas
  have hAbs := olsHomoskedasticLinearTStatisticOrZero_abs_tendstoInDistribution_standardNormalAbs
    (μ := μ) (X := X) (e := e) (y := y)
    hclt hvar β R hmodel hX_meas he_meas hVeq hse_pos
  have hGeneric : TendstoInDistribution
      (fun n ω => |root n * (θhat n ω - θ) / se n ω|)
      atTop (fun x : ℝ => |x|) (fun _ => μ) (gaussianReal 0 1) := by
    refine TendstoInDistribution.congr ?_ (EventuallyEq.rfl) hAbs
    intro n
    exact ae_of_all μ (fun ω => by
      dsimp [θ, θhat, se, root]
      rw [linearMapUnit_smul_sub_dot_one])
  simpa [θ, θhat, se, root, c] using
    symmetricCI_coverage_tendsto_of_abs_tstat_standardNormal_of_se_tendsto_pos
      (μ := μ) (θ := θ) (crit := crit)
      (θhat := θhat) (se := se) (root := root) (c := c)
      hroot (by simpa [c] using hse_pos) hse hGeneric

set_option linter.style.longLine false in
/-- **Hansen Theorem 7.12, homoskedastic confidence-interval coverage from homoskedasticity.**

This is the variable-facing version: it assumes constant conditional error
variance given regressors, then derives the covariance identity internally. -/
theorem olsHomoskedasticLinearCIOrZero_coverage_tendsto_standardNormal_of_homoskedastic
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (hclt : ScoreCLTConditions μ X e)
    (hvar : ErrorVarianceConsistencyConditions μ X e) (β : k → ℝ)
    (R : Matrix Unit k ℝ) (crit : ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (he_meas : ∀ i, AEStronglyMeasurable (e i) μ)
    (hX0 : Measurable (X 0))
    [SigmaFinite (μ.trim (conditioningSpace_le hX0))]
    (hhomo : HomoskedasticErrorVariance μ X e)
    (hse_pos : 0 <
      Real.sqrt ((R * homoskedasticAsymptoticCovariance μ X e * Rᵀ) () ())) :
    Tendsto
      (fun n => μ {ω |
        (R *ᵥ β) ⬝ᵥ (fun _ : Unit => 1) ∈ Set.Icc
          (((R *ᵥ olsBetaOrZero (stackRegressors X n ω) (stackOutcomes y n ω)) ⬝ᵥ
              (fun _ : Unit => 1)) -
            crit * Real.sqrt ((R * olsHomoskedasticCovarianceStar
              (stackRegressors X n ω) (stackOutcomes y n ω) * Rᵀ) () ()) /
              Real.sqrt (n : ℝ))
          (((R *ᵥ olsBetaOrZero (stackRegressors X n ω) (stackOutcomes y n ω)) ⬝ᵥ
              (fun _ : Unit => 1)) +
            crit * Real.sqrt ((R * olsHomoskedasticCovarianceStar
              (stackRegressors X n ω) (stackOutcomes y n ω) * Rᵀ) () ()) /
              Real.sqrt (n : ℝ))})
      atTop
      (𝓝 (((gaussianReal 0 1).map (fun x : ℝ => |x|)) (Set.Iic crit))) := by
  have hΩ := scoreCovarianceMatrix_eq_errorVariance_smul_popGram_of_homoskedastic
    (μ := μ) (X := X) (e := e) hclt hvar hX0 hhomo
  have hQ : IsUnit (popGram μ X).det := by
    simpa [popGram] using hvar.toSampleMomentAssumption71.Q_nonsing
  exact olsHomoskedasticLinearCIOrZero_coverage_tendsto_standardNormal
    (μ := μ) (X := X) (e := e) (y := y)
    hclt hvar β R crit hmodel hX_meas he_meas
    (homoskedasticAsymptoticCovariance_eq_heteroskedasticAsymptoticCovariance
      (μ := μ) (X := X) (e := e) hQ hΩ)
    hse_pos

/-- **Hansen Theorem 7.14, scalar one-degree-of-freedom homoskedastic Wald statistic.**

Under the explicit covariance bridge `V⁰β = Vβ`, the scalar homoskedastic Wald
statistic for ordinary OLS converges to `χ²(1)`. -/
theorem olsHomoskedasticLinearWaldStatisticOrZero_tendstoInDistribution_chiSquared_one
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (hclt : ScoreCLTConditions μ X e)
    (hvar : ErrorVarianceConsistencyConditions μ X e) (β : k → ℝ)
    (R : Matrix Unit k ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (he_meas : ∀ i, AEStronglyMeasurable (e i) μ)
    (hVeq : homoskedasticAsymptoticCovariance μ X e =
      heteroskedasticAsymptoticCovariance μ X e)
    (hse_pos : 0 <
      Real.sqrt ((R * homoskedasticAsymptoticCovariance μ X e * Rᵀ) () ())) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        (((Real.sqrt (n : ℝ) •
          (R *ᵥ
            (olsBetaOrZero (stackRegressors X n ω) (stackOutcomes y n ω) - β))) ⬝ᵥ
            (fun _ : Unit => 1)) /
          Real.sqrt ((R * olsHomoskedasticCovarianceStar
            (stackRegressors X n ω) (stackOutcomes y n ω) * Rᵀ) () ())) ^ 2)
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared 1) := by
  simpa using
    tendstoInDistribution_sq_standardNormal_chiSquared_one
      (olsHomoskedasticLinearTStatisticOrZero_tendstoInDistribution_standardNormal
        (μ := μ) (X := X) (e := e) (y := y)
        hclt hvar β R hmodel hX_meas he_meas hVeq hse_pos)

set_option linter.style.longLine false in
/-- **Hansen Theorem 7.14, moment-level homoskedastic t-statistic face.**

If the homoskedastic score-covariance identity `Ω = σ²Q` is available, the
ordinary-wrapper scalar homoskedastic t-statistic has a standard-normal limit. -/
theorem olsHomoskedasticLinearTStatisticOrZero_tendstoInDistribution_standardNormal_of_scoreCovariance
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (hclt : ScoreCLTConditions μ X e)
    (hvar : ErrorVarianceConsistencyConditions μ X e) (β : k → ℝ)
    (R : Matrix Unit k ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (he_meas : ∀ i, AEStronglyMeasurable (e i) μ)
    (hΩ : scoreCovarianceMatrix μ X e = errorVariance μ e • popGram μ X)
    (hse_pos : 0 <
      Real.sqrt ((R * homoskedasticAsymptoticCovariance μ X e * Rᵀ) () ())) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        ((Real.sqrt (n : ℝ) •
          (R *ᵥ
            (olsBetaOrZero (stackRegressors X n ω) (stackOutcomes y n ω) - β))) ⬝ᵥ
            (fun _ : Unit => 1)) /
          Real.sqrt ((R * olsHomoskedasticCovarianceStar
            (stackRegressors X n ω) (stackOutcomes y n ω) * Rᵀ) () ()))
      atTop (fun x : ℝ => x) (fun _ => μ) (gaussianReal 0 1) := by
  have hQ : IsUnit (popGram μ X).det := by
    simpa [popGram] using hvar.toSampleMomentAssumption71.Q_nonsing
  exact olsHomoskedasticLinearTStatisticOrZero_tendstoInDistribution_standardNormal
    (μ := μ) (X := X) (e := e) (y := y)
    hclt hvar β R hmodel hX_meas he_meas
    (homoskedasticAsymptoticCovariance_eq_heteroskedasticAsymptoticCovariance
      (μ := μ) (X := X) (e := e) hQ hΩ)
    hse_pos

set_option linter.style.longLine false in
/-- **Hansen Theorem 7.14, homoskedastic t-statistic from homoskedasticity.**

This variable-facing wrapper derives `Ω = σ²Q` from constant conditional error
variance given `X₀`, then applies the covariance-identity bridge. -/
theorem olsHomoskedasticLinearTStatisticOrZero_tendstoInDistribution_standardNormal_of_homoskedastic
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (hclt : ScoreCLTConditions μ X e)
    (hvar : ErrorVarianceConsistencyConditions μ X e) (β : k → ℝ)
    (R : Matrix Unit k ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (he_meas : ∀ i, AEStronglyMeasurable (e i) μ)
    (hX0 : Measurable (X 0))
    [SigmaFinite (μ.trim (conditioningSpace_le hX0))]
    (hhomo : HomoskedasticErrorVariance μ X e)
    (hse_pos : 0 <
      Real.sqrt ((R * homoskedasticAsymptoticCovariance μ X e * Rᵀ) () ())) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        ((Real.sqrt (n : ℝ) •
          (R *ᵥ
            (olsBetaOrZero (stackRegressors X n ω) (stackOutcomes y n ω) - β))) ⬝ᵥ
            (fun _ : Unit => 1)) /
          Real.sqrt ((R * olsHomoskedasticCovarianceStar
            (stackRegressors X n ω) (stackOutcomes y n ω) * Rᵀ) () ()))
      atTop (fun x : ℝ => x) (fun _ => μ) (gaussianReal 0 1) := by
  have hΩ := scoreCovarianceMatrix_eq_errorVariance_smul_popGram_of_homoskedastic
    (μ := μ) (X := X) (e := e) hclt hvar hX0 hhomo
  exact olsHomoskedasticLinearTStatisticOrZero_tendstoInDistribution_standardNormal_of_scoreCovariance
    (μ := μ) (X := X) (e := e) (y := y)
    hclt hvar β R hmodel hX_meas he_meas hΩ hse_pos

set_option linter.style.longLine false in
/-- **Hansen Theorem 7.14, moment-level scalar homoskedastic Wald statistic.**

If `Ω = σ²Q`, the scalar one-degree-of-freedom homoskedastic Wald statistic for
ordinary OLS converges to `χ²(1)`. -/
theorem olsHomoskedasticLinearWaldStatisticOrZero_tendstoInDistribution_chiSquared_one_of_scoreCovariance
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (hclt : ScoreCLTConditions μ X e)
    (hvar : ErrorVarianceConsistencyConditions μ X e) (β : k → ℝ)
    (R : Matrix Unit k ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (he_meas : ∀ i, AEStronglyMeasurable (e i) μ)
    (hΩ : scoreCovarianceMatrix μ X e = errorVariance μ e • popGram μ X)
    (hse_pos : 0 <
      Real.sqrt ((R * homoskedasticAsymptoticCovariance μ X e * Rᵀ) () ())) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        (((Real.sqrt (n : ℝ) •
          (R *ᵥ
            (olsBetaOrZero (stackRegressors X n ω) (stackOutcomes y n ω) - β))) ⬝ᵥ
            (fun _ : Unit => 1)) /
          Real.sqrt ((R * olsHomoskedasticCovarianceStar
            (stackRegressors X n ω) (stackOutcomes y n ω) * Rᵀ) () ())) ^ 2)
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared 1) := by
  simpa using
    tendstoInDistribution_sq_standardNormal_chiSquared_one
      (olsHomoskedasticLinearTStatisticOrZero_tendstoInDistribution_standardNormal_of_scoreCovariance
        (μ := μ) (X := X) (e := e) (y := y)
        hclt hvar β R hmodel hX_meas he_meas hΩ hse_pos)

set_option linter.style.longLine false in
/-- **Hansen Theorem 7.14, scalar homoskedastic Wald statistic from homoskedasticity.** -/
theorem olsHomoskedasticLinearWaldStatisticOrZero_tendstoInDistribution_chiSquared_one_of_homoskedastic
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (hclt : ScoreCLTConditions μ X e)
    (hvar : ErrorVarianceConsistencyConditions μ X e) (β : k → ℝ)
    (R : Matrix Unit k ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (he_meas : ∀ i, AEStronglyMeasurable (e i) μ)
    (hX0 : Measurable (X 0))
    [SigmaFinite (μ.trim (conditioningSpace_le hX0))]
    (hhomo : HomoskedasticErrorVariance μ X e)
    (hse_pos : 0 <
      Real.sqrt ((R * homoskedasticAsymptoticCovariance μ X e * Rᵀ) () ())) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        (((Real.sqrt (n : ℝ) •
          (R *ᵥ
            (olsBetaOrZero (stackRegressors X n ω) (stackOutcomes y n ω) - β))) ⬝ᵥ
            (fun _ : Unit => 1)) /
          Real.sqrt ((R * olsHomoskedasticCovarianceStar
            (stackRegressors X n ω) (stackOutcomes y n ω) * Rᵀ) () ())) ^ 2)
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared 1) := by
  simpa using
    tendstoInDistribution_sq_standardNormal_chiSquared_one
      (olsHomoskedasticLinearTStatisticOrZero_tendstoInDistribution_standardNormal_of_homoskedastic
        (μ := μ) (X := X) (e := e) (y := y)
        hclt hvar β R hmodel hX_meas he_meas hX0 hhomo hse_pos)

/-- **Hansen Theorem 7.11, HC0 t-statistic for a scalar linear function.**

For a one-dimensional fixed linear map `R`, the HC0-studentized totalized OLS
linear function converges in distribution to the Gaussian linear-function limit
divided by the population standard-error scale. A final law-normalization
corollary can turn this displayed limit into `N(0,1)` once the scalar variance
is identified with the corresponding diagonal of `R Vβ Rᵀ`. -/
theorem olsHC0LinearTStatisticStar_tendstoInDistribution
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ν : Measure Ω'} [IsProbabilityMeasure ν]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (h : RobustCovarianceConsistencyConditions μ X e) (β : k → ℝ)
    (R : Matrix Unit k ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (he_meas : ∀ i, AEStronglyMeasurable (e i) μ)
    (hCrossWeight : ∀ a b l : k, BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovarianceCrossWeight
          (stackRegressors X n ω) (stackErrors e n ω) a b l))
    (hQuadWeight : ∀ a b l m : k, BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovarianceQuadraticWeight
          (stackRegressors X n ω) a b l m))
    {Z : Ω' → ℝ}
    (hZ : HasLaw Z
      (gaussianReal 0
        (olsProjectionAsymptoticVariance μ X e (Rᵀ *ᵥ (fun _ : Unit => 1))).toNNReal)
      ν)
    (hse_pos : 0 <
      Real.sqrt ((R * heteroskedasticAsymptoticCovariance μ X e * Rᵀ) () ())) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        ((Real.sqrt (n : ℝ) •
          (R *ᵥ
            (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β))) ⬝ᵥ
            (fun _ : Unit => 1)) /
            Real.sqrt ((R * olsHeteroskedasticCovarianceStar
              (stackRegressors X n ω) (stackOutcomes y n ω) * Rᵀ) () ()))
      atTop
      (fun ω =>
        Z ω / Real.sqrt ((R * heteroskedasticAsymptoticCovariance μ X e * Rᵀ) () ()))
      (fun _ => μ) ν := by
  let c : ℝ := Real.sqrt ((R * heteroskedasticAsymptoticCovariance μ X e * Rᵀ) () ())
  let se : ℕ → Ω → ℝ := fun n ω =>
    Real.sqrt ((R * olsHeteroskedasticCovarianceStar
      (stackRegressors X n ω) (stackOutcomes y n ω) * Rᵀ) () ())
  let num : ℕ → Ω → ℝ := fun n ω =>
    ((Real.sqrt (n : ℝ) •
      (R *ᵥ (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β))) ⬝ᵥ
        (fun _ : Unit => 1))
  have hnum : TendstoInDistribution num atTop Z (fun _ => μ) ν := by
    simpa [num] using
      scoreProjection_linearMap_olsBetaStar_tendstoInDistribution_gaussian_covariance
        (μ := μ) (ν := ν) (X := X) (e := e) (y := y)
        h.toSampleCLTAssumption72 β R (fun _ : Unit => 1) hmodel hZ
  have hse : TendstoInMeasure μ se atTop (fun _ => c) := by
    simpa [se, c] using
      olsHC0LinearStdErrorStar_tendstoInMeasure_of_bounded_weights_and_components
        (μ := μ) (X := X) (e := e) (y := y)
        h β R () hmodel hX_meas he_meas hCrossWeight hQuadWeight
  have hV_meas :=
    olsHeteroskedasticCovarianceStar_stack_aestronglyMeasurable_of_components
      (μ := μ) (X := X) (e := e) (y := y)
      h.toSampleMomentAssumption71 β hmodel hX_meas he_meas
  have hse_meas : ∀ n, AEMeasurable (se n) μ := by
    intro n
    exact linearCovarianceStdError_aemeasurable
      (μ := μ) (R := R)
      (Vhat := fun ω =>
        olsHeteroskedasticCovarianceStar
          (stackRegressors X n ω) (stackOutcomes y n ω))
      (hV_meas n)
  have hratio := studentizedLimit_tendstoInDistribution
    (μ := μ) (ν := ν) (num := num) (se := se) (Z := Z) (c := c)
    (by simpa [c] using hse_pos) hnum hse hse_meas
  simpa [num, se, c] using hratio

/-- **Hansen Theorem 7.11, HC0 scalar t-statistic with standard normal limit.**

This is the textbook-facing form of the HC0 studentized scalar linear-function
CLT: the target is the identity random variable under `N(0,1)`. -/
theorem olsHC0LinearTStatisticStar_tendstoInDistribution_standardNormal
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (h : RobustCovarianceConsistencyConditions μ X e) (β : k → ℝ)
    (R : Matrix Unit k ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (he_meas : ∀ i, AEStronglyMeasurable (e i) μ)
    (hCrossWeight : ∀ a b l : k, BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovarianceCrossWeight
          (stackRegressors X n ω) (stackErrors e n ω) a b l))
    (hQuadWeight : ∀ a b l m : k, BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovarianceQuadraticWeight
          (stackRegressors X n ω) a b l m))
    (hse_pos : 0 <
      Real.sqrt ((R * heteroskedasticAsymptoticCovariance μ X e * Rᵀ) () ())) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        ((Real.sqrt (n : ℝ) •
          (R *ᵥ
            (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β))) ⬝ᵥ
            (fun _ : Unit => 1)) /
          Real.sqrt ((R * olsHeteroskedasticCovarianceStar
            (stackRegressors X n ω) (stackOutcomes y n ω) * Rᵀ) () ()))
      atTop (fun x : ℝ => x) (fun _ => μ) (gaussianReal 0 1) := by
  let c : ℝ := Real.sqrt ((R * heteroskedasticAsymptoticCovariance μ X e * Rᵀ) () ())
  have hentry_pos : 0 < (R * heteroskedasticAsymptoticCovariance μ X e * Rᵀ) () () := by
    exact Real.sqrt_pos.mp hse_pos
  have hentry_eq :
      (R * heteroskedasticAsymptoticCovariance μ X e * Rᵀ) () () =
        olsProjectionAsymptoticVariance μ X e (Rᵀ *ᵥ (fun _ : Unit => 1)) :=
    linearMapCovariance_unit_apply_eq_olsProjectionAsymptoticVariance
      (μ := μ) (X := X) (e := e) h.toSampleMomentAssumption71.int_outer R
  have hσ :
      olsProjectionAsymptoticVariance μ X e (Rᵀ *ᵥ (fun _ : Unit => 1)) = c ^ 2 := by
    calc
      olsProjectionAsymptoticVariance μ X e (Rᵀ *ᵥ (fun _ : Unit => 1))
          = (R * heteroskedasticAsymptoticCovariance μ X e * Rᵀ) () () :=
            hentry_eq.symm
      _ = c ^ 2 := by
            simpa [c] using (Real.sq_sqrt hentry_pos.le).symm
  have hZ : HasLaw (fun x : ℝ => c * x)
      (gaussianReal 0
        (olsProjectionAsymptoticVariance μ X e (Rᵀ *ᵥ (fun _ : Unit => 1))).toNNReal)
      (gaussianReal 0 1) :=
    hasLaw_const_mul_id_gaussianReal_of_variance_eq hσ
  have hbase := olsHC0LinearTStatisticStar_tendstoInDistribution
    (μ := μ) (ν := gaussianReal 0 1) (X := X) (e := e) (y := y)
    h β R hmodel hX_meas he_meas hCrossWeight hQuadWeight hZ hse_pos
  convert hbase using 2
  · rename_i x
    dsimp [c]
    exact (mul_div_cancel_left₀ x hse_pos.ne').symm

/-- **Hansen Theorem 7.11 for ordinary OLS on nonsingular samples, HC0 face.**

The HC0-studentized scalar linear t-statistic transfers from `olsBetaStar` to
`olsBetaOrZero`, the ordinary-OLS wrapper used on nonsingular sample-Gram
events. -/
theorem olsHC0LinearTStatisticOrZero_tendstoInDistribution
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ν : Measure Ω'} [IsProbabilityMeasure ν]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (h : RobustCovarianceConsistencyConditions μ X e) (β : k → ℝ)
    (R : Matrix Unit k ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (he_meas : ∀ i, AEStronglyMeasurable (e i) μ)
    (hCrossWeight : ∀ a b l : k, BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovarianceCrossWeight
          (stackRegressors X n ω) (stackErrors e n ω) a b l))
    (hQuadWeight : ∀ a b l m : k, BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovarianceQuadraticWeight
          (stackRegressors X n ω) a b l m))
    {Z : Ω' → ℝ}
    (hZ : HasLaw Z
      (gaussianReal 0
        (olsProjectionAsymptoticVariance μ X e (Rᵀ *ᵥ (fun _ : Unit => 1))).toNNReal)
      ν)
    (hse_pos : 0 <
      Real.sqrt ((R * heteroskedasticAsymptoticCovariance μ X e * Rᵀ) () ())) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        ((Real.sqrt (n : ℝ) •
          (R *ᵥ
            (olsBetaOrZero (stackRegressors X n ω) (stackOutcomes y n ω) - β))) ⬝ᵥ
            (fun _ : Unit => 1)) /
          Real.sqrt ((R * olsHeteroskedasticCovarianceStar
            (stackRegressors X n ω) (stackOutcomes y n ω) * Rᵀ) () ()))
      atTop
      (fun ω =>
        Z ω / Real.sqrt ((R * heteroskedasticAsymptoticCovariance μ X e * Rᵀ) () ()))
      (fun _ => μ) ν := by
  simpa [olsBetaOrZero_eq_olsBetaStar] using
    olsHC0LinearTStatisticStar_tendstoInDistribution
      (μ := μ) (ν := ν) (X := X) (e := e) (y := y)
      h β R hmodel hX_meas he_meas hCrossWeight hQuadWeight hZ hse_pos

/-- **Hansen Theorem 7.11 for ordinary OLS, HC0 standard-normal face.** -/
theorem olsHC0LinearTStatisticOrZero_tendstoInDistribution_standardNormal
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (h : RobustCovarianceConsistencyConditions μ X e) (β : k → ℝ)
    (R : Matrix Unit k ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (he_meas : ∀ i, AEStronglyMeasurable (e i) μ)
    (hCrossWeight : ∀ a b l : k, BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovarianceCrossWeight
          (stackRegressors X n ω) (stackErrors e n ω) a b l))
    (hQuadWeight : ∀ a b l m : k, BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovarianceQuadraticWeight
          (stackRegressors X n ω) a b l m))
    (hse_pos : 0 <
      Real.sqrt ((R * heteroskedasticAsymptoticCovariance μ X e * Rᵀ) () ())) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        ((Real.sqrt (n : ℝ) •
          (R *ᵥ
            (olsBetaOrZero (stackRegressors X n ω) (stackOutcomes y n ω) - β))) ⬝ᵥ
            (fun _ : Unit => 1)) /
          Real.sqrt ((R * olsHeteroskedasticCovarianceStar
            (stackRegressors X n ω) (stackOutcomes y n ω) * Rᵀ) () ()))
      atTop (fun x : ℝ => x) (fun _ => μ) (gaussianReal 0 1) := by
  simpa [olsBetaOrZero_eq_olsBetaStar] using
    olsHC0LinearTStatisticStar_tendstoInDistribution_standardNormal
      (μ := μ) (X := X) (e := e) (y := y)
      h β R hmodel hX_meas he_meas hCrossWeight hQuadWeight hse_pos

/-- Absolute-value CMT for the ordinary HC0 scalar t-statistic. -/
theorem olsHC0LinearTStatisticOrZero_abs_tendstoInDistribution_standardNormalAbs
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (h : RobustCovarianceConsistencyConditions μ X e) (β : k → ℝ)
    (R : Matrix Unit k ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (he_meas : ∀ i, AEStronglyMeasurable (e i) μ)
    (hCrossWeight : ∀ a b l : k, BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovarianceCrossWeight
          (stackRegressors X n ω) (stackErrors e n ω) a b l))
    (hQuadWeight : ∀ a b l m : k, BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovarianceQuadraticWeight
          (stackRegressors X n ω) a b l m))
    (hse_pos : 0 <
      Real.sqrt ((R * heteroskedasticAsymptoticCovariance μ X e * Rᵀ) () ())) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        abs
          (((Real.sqrt (n : ℝ) •
            (R *ᵥ
              (olsBetaOrZero (stackRegressors X n ω) (stackOutcomes y n ω) - β))) ⬝ᵥ
              (fun _ : Unit => 1)) /
            Real.sqrt ((R * olsHeteroskedasticCovarianceStar
              (stackRegressors X n ω) (stackOutcomes y n ω) * Rᵀ) () ())))
      atTop (fun x : ℝ => |x|) (fun _ => μ) (gaussianReal 0 1) := by
  simpa using
    tendstoInDistribution_abs_real
      (olsHC0LinearTStatisticOrZero_tendstoInDistribution_standardNormal
        (μ := μ) (X := X) (e := e) (y := y)
        h β R hmodel hX_meas he_meas hCrossWeight hQuadWeight hse_pos)

set_option linter.style.longLine false in
/-- **Hansen Theorem 7.12, HC0 confidence-interval coverage.**

The ordinary-wrapper HC0 symmetric confidence interval for a one-row linear
restriction has limiting coverage given by the absolute standard-normal mass
below `crit`; the bad event where the sample HC0 standard error is nonpositive
is negligible because the standard error converges in probability to its
positive population limit. -/
theorem olsHC0LinearCIOrZero_coverage_tendsto_standardNormal
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (h : RobustCovarianceConsistencyConditions μ X e) (β : k → ℝ)
    (R : Matrix Unit k ℝ) (crit : ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (he_meas : ∀ i, AEStronglyMeasurable (e i) μ)
    (hCrossWeight : ∀ a b l : k, BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovarianceCrossWeight
          (stackRegressors X n ω) (stackErrors e n ω) a b l))
    (hQuadWeight : ∀ a b l m : k, BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovarianceQuadraticWeight
          (stackRegressors X n ω) a b l m))
    (hse_pos : 0 <
      Real.sqrt ((R * heteroskedasticAsymptoticCovariance μ X e * Rᵀ) () ())) :
    Tendsto
      (fun n => μ {ω |
        (R *ᵥ β) ⬝ᵥ (fun _ : Unit => 1) ∈ Set.Icc
          (((R *ᵥ olsBetaOrZero (stackRegressors X n ω) (stackOutcomes y n ω)) ⬝ᵥ
              (fun _ : Unit => 1)) -
            crit * Real.sqrt ((R * olsHeteroskedasticCovarianceStar
              (stackRegressors X n ω) (stackOutcomes y n ω) * Rᵀ) () ()) /
              Real.sqrt (n : ℝ))
          (((R *ᵥ olsBetaOrZero (stackRegressors X n ω) (stackOutcomes y n ω)) ⬝ᵥ
              (fun _ : Unit => 1)) +
            crit * Real.sqrt ((R * olsHeteroskedasticCovarianceStar
              (stackRegressors X n ω) (stackOutcomes y n ω) * Rᵀ) () ()) /
              Real.sqrt (n : ℝ))})
      atTop
      (𝓝 (((gaussianReal 0 1).map (fun x : ℝ => |x|)) (Set.Iic crit))) := by
  let θ : ℝ := (R *ᵥ β) ⬝ᵥ (fun _ : Unit => 1)
  let θhat : ℕ → Ω → ℝ := fun n ω =>
    (R *ᵥ olsBetaOrZero (stackRegressors X n ω) (stackOutcomes y n ω)) ⬝ᵥ
      (fun _ : Unit => 1)
  let se : ℕ → Ω → ℝ := fun n ω =>
    Real.sqrt ((R * olsHeteroskedasticCovarianceStar
      (stackRegressors X n ω) (stackOutcomes y n ω) * Rᵀ) () ())
  let root : ℕ → ℝ := fun n => Real.sqrt (n : ℝ)
  let c : ℝ := Real.sqrt ((R * heteroskedasticAsymptoticCovariance μ X e * Rᵀ) () ())
  have hroot : ∀ᶠ n in atTop, 0 < root n := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    exact Real.sqrt_pos.mpr hnpos
  have hse : TendstoInMeasure μ se atTop (fun _ => c) := by
    simpa [se, c] using
      olsHC0LinearStdErrorStar_tendstoInMeasure_of_bounded_weights_and_components
        (μ := μ) (X := X) (e := e) (y := y)
        h β R () hmodel hX_meas he_meas hCrossWeight hQuadWeight
  have hAbs := olsHC0LinearTStatisticOrZero_abs_tendstoInDistribution_standardNormalAbs
    (μ := μ) (X := X) (e := e) (y := y)
    h β R hmodel hX_meas he_meas hCrossWeight hQuadWeight hse_pos
  have hGeneric : TendstoInDistribution
      (fun n ω => |root n * (θhat n ω - θ) / se n ω|)
      atTop (fun x : ℝ => |x|) (fun _ => μ) (gaussianReal 0 1) := by
    refine TendstoInDistribution.congr ?_ (EventuallyEq.rfl) hAbs
    intro n
    exact ae_of_all μ (fun ω => by
      dsimp [θ, θhat, se, root]
      rw [linearMapUnit_smul_sub_dot_one])
  simpa [θ, θhat, se, root, c] using
    symmetricCI_coverage_tendsto_of_abs_tstat_standardNormal_of_se_tendsto_pos
      (μ := μ) (θ := θ) (crit := crit)
      (θhat := θhat) (se := se) (root := root) (c := c)
      hroot (by simpa [c] using hse_pos) hse hGeneric

/-- Scalar one-degree-of-freedom HC0 Wald statistic for ordinary OLS. -/
theorem olsHC0LinearWaldStatisticOrZero_tendstoInDistribution_chiSquared_one
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (h : RobustCovarianceConsistencyConditions μ X e) (β : k → ℝ)
    (R : Matrix Unit k ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (he_meas : ∀ i, AEStronglyMeasurable (e i) μ)
    (hCrossWeight : ∀ a b l : k, BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovarianceCrossWeight
          (stackRegressors X n ω) (stackErrors e n ω) a b l))
    (hQuadWeight : ∀ a b l m : k, BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovarianceQuadraticWeight
          (stackRegressors X n ω) a b l m))
    (hse_pos : 0 <
      Real.sqrt ((R * heteroskedasticAsymptoticCovariance μ X e * Rᵀ) () ())) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        (((Real.sqrt (n : ℝ) •
          (R *ᵥ
            (olsBetaOrZero (stackRegressors X n ω) (stackOutcomes y n ω) - β))) ⬝ᵥ
            (fun _ : Unit => 1)) /
          Real.sqrt ((R * olsHeteroskedasticCovarianceStar
            (stackRegressors X n ω) (stackOutcomes y n ω) * Rᵀ) () ())) ^ 2)
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared 1) := by
  simpa using
    tendstoInDistribution_sq_standardNormal_chiSquared_one
      (olsHC0LinearTStatisticOrZero_tendstoInDistribution_standardNormal
        (μ := μ) (X := X) (e := e) (y := y)
        h β R hmodel hX_meas he_meas hCrossWeight hQuadWeight hse_pos)

/-- **Hansen Theorem 7.11, HC1 t-statistic for a scalar linear function.**

This is the HC1 analogue of
`olsHC0LinearTStatisticStar_tendstoInDistribution`: the studentized totalized
OLS linear function converges to the same Gaussian limit divided by the
population standard-error scale. -/
theorem olsHC1LinearTStatisticStar_tendstoInDistribution
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ν : Measure Ω'} [IsProbabilityMeasure ν]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (h : RobustCovarianceConsistencyConditions μ X e) (β : k → ℝ)
    (R : Matrix Unit k ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (he_meas : ∀ i, AEStronglyMeasurable (e i) μ)
    (hCrossWeight : ∀ a b l : k, BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovarianceCrossWeight
          (stackRegressors X n ω) (stackErrors e n ω) a b l))
    (hQuadWeight : ∀ a b l m : k, BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovarianceQuadraticWeight
          (stackRegressors X n ω) a b l m))
    {Z : Ω' → ℝ}
    (hZ : HasLaw Z
      (gaussianReal 0
        (olsProjectionAsymptoticVariance μ X e (Rᵀ *ᵥ (fun _ : Unit => 1))).toNNReal)
      ν)
    (hse_pos : 0 <
      Real.sqrt ((R * heteroskedasticAsymptoticCovariance μ X e * Rᵀ) () ())) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        ((Real.sqrt (n : ℝ) •
          (R *ᵥ
            (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β))) ⬝ᵥ
            (fun _ : Unit => 1)) /
            Real.sqrt ((R * olsHeteroskedasticCovarianceHC1Star
              (stackRegressors X n ω) (stackOutcomes y n ω) * Rᵀ) () ()))
      atTop
      (fun ω =>
        Z ω / Real.sqrt ((R * heteroskedasticAsymptoticCovariance μ X e * Rᵀ) () ()))
      (fun _ => μ) ν := by
  let c : ℝ := Real.sqrt ((R * heteroskedasticAsymptoticCovariance μ X e * Rᵀ) () ())
  let se : ℕ → Ω → ℝ := fun n ω =>
    Real.sqrt ((R * olsHeteroskedasticCovarianceHC1Star
      (stackRegressors X n ω) (stackOutcomes y n ω) * Rᵀ) () ())
  let num : ℕ → Ω → ℝ := fun n ω =>
    ((Real.sqrt (n : ℝ) •
      (R *ᵥ (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β))) ⬝ᵥ
        (fun _ : Unit => 1))
  have hnum : TendstoInDistribution num atTop Z (fun _ => μ) ν := by
    simpa [num] using
      scoreProjection_linearMap_olsBetaStar_tendstoInDistribution_gaussian_covariance
        (μ := μ) (ν := ν) (X := X) (e := e) (y := y)
        h.toSampleCLTAssumption72 β R (fun _ : Unit => 1) hmodel hZ
  have hse : TendstoInMeasure μ se atTop (fun _ => c) := by
    simpa [se, c] using
      olsHC1LinearStdErrorStar_tendstoInMeasure_of_bounded_weights_and_components
        (μ := μ) (X := X) (e := e) (y := y)
        h β R () hmodel hX_meas he_meas hCrossWeight hQuadWeight
  have hV_meas :=
    olsHC1CovarianceStar_stack_aestronglyMeasurable_of_components
      (μ := μ) (X := X) (e := e) (y := y)
      h.toSampleMomentAssumption71 β hmodel hX_meas he_meas
  have hse_meas : ∀ n, AEMeasurable (se n) μ := by
    intro n
    exact linearCovarianceStdError_aemeasurable
      (μ := μ) (R := R)
      (Vhat := fun ω =>
        olsHeteroskedasticCovarianceHC1Star
          (stackRegressors X n ω) (stackOutcomes y n ω))
      (hV_meas n)
  have hratio := studentizedLimit_tendstoInDistribution
    (μ := μ) (ν := ν) (num := num) (se := se) (Z := Z) (c := c)
    (by simpa [c] using hse_pos) hnum hse hse_meas
  simpa [num, se, c] using hratio

/-- **Hansen Theorem 7.11, HC1 scalar t-statistic with standard normal limit.**

This is the HC1 analogue of
`olsHC0LinearTStatisticStar_tendstoInDistribution_standardNormal`. -/
theorem olsHC1LinearTStatisticStar_tendstoInDistribution_standardNormal
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (h : RobustCovarianceConsistencyConditions μ X e) (β : k → ℝ)
    (R : Matrix Unit k ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (he_meas : ∀ i, AEStronglyMeasurable (e i) μ)
    (hCrossWeight : ∀ a b l : k, BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovarianceCrossWeight
          (stackRegressors X n ω) (stackErrors e n ω) a b l))
    (hQuadWeight : ∀ a b l m : k, BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovarianceQuadraticWeight
          (stackRegressors X n ω) a b l m))
    (hse_pos : 0 <
      Real.sqrt ((R * heteroskedasticAsymptoticCovariance μ X e * Rᵀ) () ())) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        ((Real.sqrt (n : ℝ) •
          (R *ᵥ
            (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β))) ⬝ᵥ
            (fun _ : Unit => 1)) /
          Real.sqrt ((R * olsHeteroskedasticCovarianceHC1Star
            (stackRegressors X n ω) (stackOutcomes y n ω) * Rᵀ) () ()))
      atTop (fun x : ℝ => x) (fun _ => μ) (gaussianReal 0 1) := by
  let c : ℝ := Real.sqrt ((R * heteroskedasticAsymptoticCovariance μ X e * Rᵀ) () ())
  have hentry_pos : 0 < (R * heteroskedasticAsymptoticCovariance μ X e * Rᵀ) () () := by
    exact Real.sqrt_pos.mp hse_pos
  have hentry_eq :
      (R * heteroskedasticAsymptoticCovariance μ X e * Rᵀ) () () =
        olsProjectionAsymptoticVariance μ X e (Rᵀ *ᵥ (fun _ : Unit => 1)) :=
    linearMapCovariance_unit_apply_eq_olsProjectionAsymptoticVariance
      (μ := μ) (X := X) (e := e) h.toSampleMomentAssumption71.int_outer R
  have hσ :
      olsProjectionAsymptoticVariance μ X e (Rᵀ *ᵥ (fun _ : Unit => 1)) = c ^ 2 := by
    calc
      olsProjectionAsymptoticVariance μ X e (Rᵀ *ᵥ (fun _ : Unit => 1))
          = (R * heteroskedasticAsymptoticCovariance μ X e * Rᵀ) () () :=
            hentry_eq.symm
      _ = c ^ 2 := by
            simpa [c] using (Real.sq_sqrt hentry_pos.le).symm
  have hZ : HasLaw (fun x : ℝ => c * x)
      (gaussianReal 0
        (olsProjectionAsymptoticVariance μ X e (Rᵀ *ᵥ (fun _ : Unit => 1))).toNNReal)
      (gaussianReal 0 1) :=
    hasLaw_const_mul_id_gaussianReal_of_variance_eq hσ
  have hbase := olsHC1LinearTStatisticStar_tendstoInDistribution
    (μ := μ) (ν := gaussianReal 0 1) (X := X) (e := e) (y := y)
    h β R hmodel hX_meas he_meas hCrossWeight hQuadWeight hZ hse_pos
  convert hbase using 2
  · rename_i x
    dsimp [c]
    exact (mul_div_cancel_left₀ x hse_pos.ne').symm

/-- **Hansen Theorem 7.11 for ordinary OLS on nonsingular samples, HC1 face.**

The HC1-studentized scalar linear t-statistic transfers from `olsBetaStar` to
the ordinary-on-nonsingular wrapper `olsBetaOrZero`. -/
theorem olsHC1LinearTStatisticOrZero_tendstoInDistribution
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ν : Measure Ω'} [IsProbabilityMeasure ν]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (h : RobustCovarianceConsistencyConditions μ X e) (β : k → ℝ)
    (R : Matrix Unit k ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (he_meas : ∀ i, AEStronglyMeasurable (e i) μ)
    (hCrossWeight : ∀ a b l : k, BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovarianceCrossWeight
          (stackRegressors X n ω) (stackErrors e n ω) a b l))
    (hQuadWeight : ∀ a b l m : k, BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovarianceQuadraticWeight
          (stackRegressors X n ω) a b l m))
    {Z : Ω' → ℝ}
    (hZ : HasLaw Z
      (gaussianReal 0
        (olsProjectionAsymptoticVariance μ X e (Rᵀ *ᵥ (fun _ : Unit => 1))).toNNReal)
      ν)
    (hse_pos : 0 <
      Real.sqrt ((R * heteroskedasticAsymptoticCovariance μ X e * Rᵀ) () ())) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        ((Real.sqrt (n : ℝ) •
          (R *ᵥ
            (olsBetaOrZero (stackRegressors X n ω) (stackOutcomes y n ω) - β))) ⬝ᵥ
            (fun _ : Unit => 1)) /
          Real.sqrt ((R * olsHeteroskedasticCovarianceHC1Star
            (stackRegressors X n ω) (stackOutcomes y n ω) * Rᵀ) () ()))
      atTop
      (fun ω =>
        Z ω / Real.sqrt ((R * heteroskedasticAsymptoticCovariance μ X e * Rᵀ) () ()))
      (fun _ => μ) ν := by
  simpa [olsBetaOrZero_eq_olsBetaStar] using
    olsHC1LinearTStatisticStar_tendstoInDistribution
      (μ := μ) (ν := ν) (X := X) (e := e) (y := y)
      h β R hmodel hX_meas he_meas hCrossWeight hQuadWeight hZ hse_pos

/-- **Hansen Theorem 7.11 for ordinary OLS, HC1 standard-normal face.** -/
theorem olsHC1LinearTStatisticOrZero_tendstoInDistribution_standardNormal
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (h : RobustCovarianceConsistencyConditions μ X e) (β : k → ℝ)
    (R : Matrix Unit k ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (he_meas : ∀ i, AEStronglyMeasurable (e i) μ)
    (hCrossWeight : ∀ a b l : k, BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovarianceCrossWeight
          (stackRegressors X n ω) (stackErrors e n ω) a b l))
    (hQuadWeight : ∀ a b l m : k, BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovarianceQuadraticWeight
          (stackRegressors X n ω) a b l m))
    (hse_pos : 0 <
      Real.sqrt ((R * heteroskedasticAsymptoticCovariance μ X e * Rᵀ) () ())) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        ((Real.sqrt (n : ℝ) •
          (R *ᵥ
            (olsBetaOrZero (stackRegressors X n ω) (stackOutcomes y n ω) - β))) ⬝ᵥ
            (fun _ : Unit => 1)) /
          Real.sqrt ((R * olsHeteroskedasticCovarianceHC1Star
            (stackRegressors X n ω) (stackOutcomes y n ω) * Rᵀ) () ()))
      atTop (fun x : ℝ => x) (fun _ => μ) (gaussianReal 0 1) := by
  simpa [olsBetaOrZero_eq_olsBetaStar] using
    olsHC1LinearTStatisticStar_tendstoInDistribution_standardNormal
      (μ := μ) (X := X) (e := e) (y := y)
      h β R hmodel hX_meas he_meas hCrossWeight hQuadWeight hse_pos

/-- Absolute-value CMT for the ordinary HC1 scalar t-statistic. -/
theorem olsHC1LinearTStatisticOrZero_abs_tendstoInDistribution_standardNormalAbs
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (h : RobustCovarianceConsistencyConditions μ X e) (β : k → ℝ)
    (R : Matrix Unit k ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (he_meas : ∀ i, AEStronglyMeasurable (e i) μ)
    (hCrossWeight : ∀ a b l : k, BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovarianceCrossWeight
          (stackRegressors X n ω) (stackErrors e n ω) a b l))
    (hQuadWeight : ∀ a b l m : k, BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovarianceQuadraticWeight
          (stackRegressors X n ω) a b l m))
    (hse_pos : 0 <
      Real.sqrt ((R * heteroskedasticAsymptoticCovariance μ X e * Rᵀ) () ())) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        abs
          (((Real.sqrt (n : ℝ) •
            (R *ᵥ
              (olsBetaOrZero (stackRegressors X n ω) (stackOutcomes y n ω) - β))) ⬝ᵥ
              (fun _ : Unit => 1)) /
            Real.sqrt ((R * olsHeteroskedasticCovarianceHC1Star
              (stackRegressors X n ω) (stackOutcomes y n ω) * Rᵀ) () ())))
      atTop (fun x : ℝ => |x|) (fun _ => μ) (gaussianReal 0 1) := by
  simpa using
    tendstoInDistribution_abs_real
      (olsHC1LinearTStatisticOrZero_tendstoInDistribution_standardNormal
        (μ := μ) (X := X) (e := e) (y := y)
        h β R hmodel hX_meas he_meas hCrossWeight hQuadWeight hse_pos)

/-- Scalar one-degree-of-freedom HC1 Wald statistic for ordinary OLS. -/
theorem olsHC1LinearWaldStatisticOrZero_tendstoInDistribution_chiSquared_one
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (h : RobustCovarianceConsistencyConditions μ X e) (β : k → ℝ)
    (R : Matrix Unit k ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (he_meas : ∀ i, AEStronglyMeasurable (e i) μ)
    (hCrossWeight : ∀ a b l : k, BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovarianceCrossWeight
          (stackRegressors X n ω) (stackErrors e n ω) a b l))
    (hQuadWeight : ∀ a b l m : k, BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovarianceQuadraticWeight
          (stackRegressors X n ω) a b l m))
    (hse_pos : 0 <
      Real.sqrt ((R * heteroskedasticAsymptoticCovariance μ X e * Rᵀ) () ())) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        (((Real.sqrt (n : ℝ) •
          (R *ᵥ
            (olsBetaOrZero (stackRegressors X n ω) (stackOutcomes y n ω) - β))) ⬝ᵥ
            (fun _ : Unit => 1)) /
          Real.sqrt ((R * olsHeteroskedasticCovarianceHC1Star
            (stackRegressors X n ω) (stackOutcomes y n ω) * Rᵀ) () ())) ^ 2)
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared 1) := by
  simpa using
    tendstoInDistribution_sq_standardNormal_chiSquared_one
      (olsHC1LinearTStatisticOrZero_tendstoInDistribution_standardNormal
        (μ := μ) (X := X) (e := e) (y := y)
        h β R hmodel hX_meas he_meas hCrossWeight hQuadWeight hse_pos)

set_option linter.style.longLine false in
/-- **Hansen Theorem 7.12, HC1 confidence-interval coverage.**

The ordinary-wrapper HC1 symmetric confidence interval for a one-row linear
restriction has limiting coverage given by the absolute standard-normal mass
below `crit`; the bad event where the sample HC1 standard error is nonpositive
is negligible because the standard error converges in probability to its
positive population limit. -/
theorem olsHC1LinearCIOrZero_coverage_tendsto_standardNormal
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (h : RobustCovarianceConsistencyConditions μ X e) (β : k → ℝ)
    (R : Matrix Unit k ℝ) (crit : ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (he_meas : ∀ i, AEStronglyMeasurable (e i) μ)
    (hCrossWeight : ∀ a b l : k, BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovarianceCrossWeight
          (stackRegressors X n ω) (stackErrors e n ω) a b l))
    (hQuadWeight : ∀ a b l m : k, BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovarianceQuadraticWeight
          (stackRegressors X n ω) a b l m))
    (hse_pos : 0 <
      Real.sqrt ((R * heteroskedasticAsymptoticCovariance μ X e * Rᵀ) () ())) :
    Tendsto
      (fun n => μ {ω |
        (R *ᵥ β) ⬝ᵥ (fun _ : Unit => 1) ∈ Set.Icc
          (((R *ᵥ olsBetaOrZero (stackRegressors X n ω) (stackOutcomes y n ω)) ⬝ᵥ
              (fun _ : Unit => 1)) -
            crit * Real.sqrt ((R * olsHeteroskedasticCovarianceHC1Star
              (stackRegressors X n ω) (stackOutcomes y n ω) * Rᵀ) () ()) /
              Real.sqrt (n : ℝ))
          (((R *ᵥ olsBetaOrZero (stackRegressors X n ω) (stackOutcomes y n ω)) ⬝ᵥ
              (fun _ : Unit => 1)) +
            crit * Real.sqrt ((R * olsHeteroskedasticCovarianceHC1Star
              (stackRegressors X n ω) (stackOutcomes y n ω) * Rᵀ) () ()) /
              Real.sqrt (n : ℝ))})
      atTop
      (𝓝 (((gaussianReal 0 1).map (fun x : ℝ => |x|)) (Set.Iic crit))) := by
  let θ : ℝ := (R *ᵥ β) ⬝ᵥ (fun _ : Unit => 1)
  let θhat : ℕ → Ω → ℝ := fun n ω =>
    (R *ᵥ olsBetaOrZero (stackRegressors X n ω) (stackOutcomes y n ω)) ⬝ᵥ
      (fun _ : Unit => 1)
  let se : ℕ → Ω → ℝ := fun n ω =>
    Real.sqrt ((R * olsHeteroskedasticCovarianceHC1Star
      (stackRegressors X n ω) (stackOutcomes y n ω) * Rᵀ) () ())
  let root : ℕ → ℝ := fun n => Real.sqrt (n : ℝ)
  let c : ℝ := Real.sqrt ((R * heteroskedasticAsymptoticCovariance μ X e * Rᵀ) () ())
  have hroot : ∀ᶠ n in atTop, 0 < root n := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    exact Real.sqrt_pos.mpr hnpos
  have hse : TendstoInMeasure μ se atTop (fun _ => c) := by
    simpa [se, c] using
      olsHC1LinearStdErrorStar_tendstoInMeasure_of_bounded_weights_and_components
        (μ := μ) (X := X) (e := e) (y := y)
        h β R () hmodel hX_meas he_meas hCrossWeight hQuadWeight
  have hAbs := olsHC1LinearTStatisticOrZero_abs_tendstoInDistribution_standardNormalAbs
    (μ := μ) (X := X) (e := e) (y := y)
    h β R hmodel hX_meas he_meas hCrossWeight hQuadWeight hse_pos
  have hGeneric : TendstoInDistribution
      (fun n ω => |root n * (θhat n ω - θ) / se n ω|)
      atTop (fun x : ℝ => |x|) (fun _ => μ) (gaussianReal 0 1) := by
    refine TendstoInDistribution.congr ?_ (EventuallyEq.rfl) hAbs
    intro n
    exact ae_of_all μ (fun ω => by
      dsimp [θ, θhat, se, root]
      rw [linearMapUnit_smul_sub_dot_one])
  simpa [θ, θhat, se, root, c] using
    symmetricCI_coverage_tendsto_of_abs_tstat_standardNormal_of_se_tendsto_pos
      (μ := μ) (θ := θ) (crit := crit)
      (θhat := θhat) (se := se) (root := root) (c := c)
      hroot (by simpa [c] using hse_pos) hse hGeneric

/-- **Hansen Theorem 7.3, all scalar projections for totalized OLS with `Ω`.**

For every fixed direction `a`, the scaled totalized OLS error has Gaussian
limit with asymptotic variance `((Q⁻¹)'a)' Ω ((Q⁻¹)'a)`. This is the complete
projection-family form currently available before the vector/Cramér-Wold
wrapper is formalized. -/
theorem scoreProjection_olsBetaStar_tendstoInDistribution_gaussian_covariance_all
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ν : Measure Ω'} [IsProbabilityMeasure ν]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (h : ScoreCLTConditions μ X e) (β : k → ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    {Z : (k → ℝ) → Ω' → ℝ}
    (hZ : ∀ a : k → ℝ,
      HasLaw (Z a)
        (gaussianReal 0 (olsProjectionAsymptoticVariance μ X e a).toNNReal) ν) :
    ∀ a : k → ℝ,
      TendstoInDistribution
        (fun (n : ℕ) ω =>
          (Real.sqrt (n : ℝ) •
            (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β)) ⬝ᵥ a)
        atTop (Z a) (fun _ => μ) ν :=
  fun a =>
    scoreProjection_olsBetaStar_tendstoInDistribution_gaussian_covariance
      (μ := μ) (ν := ν) (X := X) (e := e) (y := y) h β a hmodel (hZ a)

/-- **Hansen Theorem 7.3 for ordinary OLS on nonsingular samples, scalar-projection form.**

This transfers the scalar totalized-OLS CLT to `olsBetaOrZero`, which is ordinary
`olsBeta` on the nonsingular sample-Gram event and `0` otherwise. -/
theorem scoreProjection_olsBetaOrZero_tendstoInDistribution_gaussian_covariance
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ν : Measure Ω'} [IsProbabilityMeasure ν]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (h : ScoreCLTConditions μ X e) (β a : k → ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    {Z : Ω' → ℝ}
    (hZ : HasLaw Z
      (gaussianReal 0 (olsProjectionAsymptoticVariance μ X e a).toNNReal) ν) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        (Real.sqrt (n : ℝ) •
          (olsBetaOrZero (stackRegressors X n ω) (stackOutcomes y n ω) - β)) ⬝ᵥ a)
      atTop Z (fun _ => μ) ν := by
  simpa [olsBetaOrZero_eq_olsBetaStar] using
    scoreProjection_olsBetaStar_tendstoInDistribution_gaussian_covariance
      (μ := μ) (ν := ν) (X := X) (e := e) (y := y) h β a hmodel hZ

/-- **Hansen Theorem 7.3, all scalar projections for ordinary OLS on nonsingular samples.**

This is the textbook-facing projection-family form for `olsBetaOrZero`: for
every fixed direction `a`, ordinary OLS on the nonsingular sample-Gram event has
the same scalar Gaussian limit as the totalized estimator. -/
theorem scoreProjection_olsBetaOrZero_tendstoInDistribution_gaussian_covariance_all
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ν : Measure Ω'} [IsProbabilityMeasure ν]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (h : ScoreCLTConditions μ X e) (β : k → ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    {Z : (k → ℝ) → Ω' → ℝ}
    (hZ : ∀ a : k → ℝ,
      HasLaw (Z a)
        (gaussianReal 0 (olsProjectionAsymptoticVariance μ X e a).toNNReal) ν) :
    ∀ a : k → ℝ,
      TendstoInDistribution
        (fun (n : ℕ) ω =>
          (Real.sqrt (n : ℝ) •
            (olsBetaOrZero (stackRegressors X n ω) (stackOutcomes y n ω) - β)) ⬝ᵥ a)
        atTop (Z a) (fun _ => μ) ν :=
  fun a =>
    scoreProjection_olsBetaOrZero_tendstoInDistribution_gaussian_covariance
      (μ := μ) (ν := ν) (X := X) (e := e) (y := y) h β a hmodel (hZ a)

end Assumption72

end HansenEconometrics
